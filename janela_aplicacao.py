"""
Janela de Aplicação — Passo 1: definir a área e encontrar as estações
=====================================================================

Aplicação de janela (Tkinter) para análise de janelas de pulverização a
partir das estações meteorológicas automáticas do INMET.

A janela tem cinco abas.

  1. ÁREA E ESTAÇÕES — baixa (e guarda em cache) a lista de estações
     automáticas do INMET, deixa você definir a área de três jeitos
     (clicando no mapa, digitando a coordenada ou carregando o arquivo do
     talhão) e mostra as estações mais próximas, com distância e o peso
     que cada uma terá na série combinada.

  2. SÉRIES E DELTA T — baixa a série horária do período escolhido,
     combina as estações pelo inverso do quadrado da distância, calcula o
     Delta T hora a hora e agrupa as horas aptas em janelas contínuas.
     Mostra o resultado em tabela, em gráfico e num mapa de calor
     hora × dia.

  3. PREVISÃO — a mesma conta olhando para a frente, de 1 a 7 dias, para
     responder "quando dá para aplicar esta semana". Sai por conjunto:
     dezenas de rodadas do modelo, com o critério avaliado em cada uma,
     de modo que o resultado é probabilidade e não sentença.

  4. RELATÓRIO — junta as três primeiras num PDF paginado.

  5. VOOS REALIZADOS — o caminho inverso. Lê o arquivo de operações do
     dron, agrupa os voos por local, reconstrói o tempo que fazia na hora
     de cada um e diz com que probabilidade aquele voo pegou condição boa.
     Sai num relatório próprio, separado do outro.

Dado medido e calibração (versão de 24/09/2026)
  A aba 2 lê as tabelas horárias exportadas do portal do INMET. Com elas
  o histórico passa a ser MEDIDO, a ferramenta compara o modelo com as
  estações hora a hora e guarda os pares em calibracao.json, ao lado
  deste arquivo. A previsão (abas 3 e 4) usa essa calibração para
  corrigir o viés local — em setembro de 2026, perto de Feira de Santana,
  o modelo estava seco demais (Delta T ~1 °C acima) e com vento forte
  demais, sobretudo de madrugada. Quanto mais tabelas carregadas ao longo
  do tempo, melhor a correção.

Direção do vento
  Interpolada pelas componentes u e v (nunca pelo ângulo), com rosa dos
  ventos, mapa de setas e a seta "para onde vai a deriva" em cada hora.

Dependências: numpy, matplotlib, tkinter
  pip install numpy matplotlib
  (tkinter já vem com o Python no Windows)

Opcional, só para ler shapefile:
  pip install pyshp

Para rodar:
    python janela_aplicacao.py
"""

# =====================================================================
# BLOCO 1 — IMPORTS
# =====================================================================

import json
import math
import os
import ssl
import sys
import urllib.request
import zipfile
import xml.etree.ElementTree as ET

import numpy as np

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D
from matplotlib.ticker import MaxNLocator, FuncFormatter
from matplotlib.colors import (ListedColormap, BoundaryNorm, TwoSlopeNorm,
                               LinearSegmentedColormap)
from matplotlib.patches import Patch
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk

import tkinter as tk
from tkinter import ttk, messagebox, filedialog


# =====================================================================
# BLOCO 2 — CONSTANTES
# =====================================================================

# Aparece na barra de título. Serve para conferir, num relance, se o que
# está rodando é mesmo a última versão do arquivo — editor com o arquivo
# aberto às vezes regrava a versão antiga por cima ao rodar.
VERSAO = "2026-09-29b · mapa dos voos sem as retas de ida e volta"

API_INMET = "https://apitempo.inmet.gov.br"
API_ELEVACAO = "https://api.open-meteo.com/v1/elevation"
ARQUIVO_CACHE = "estacoes_inmet.json"

# Gradientes usados para levar as estações à altitude da área.
# 0,0065 °C/m é o gradiente térmico padrão da atmosfera (6,5 °C/km).
# O ponto de orvalho cai bem mais devagar com a altitude — cerca de um
# quarto disso — porque a umidade absoluta varia pouco na vertical.
GRADIENTE_TERMICO = 0.0065      # °C por metro
GRADIENTE_ORVALHO = 0.0018      # °C por metro

# Estado que aparece selecionado ao abrir. Deixe "" para abrir no Brasil inteiro.
UF_INICIAL = "BA"

# Contornos de estados e municípios, para servir de fundo ao mapa.
# Coloque BR_UF_2021.zip e BR_Municipios_2021.zip (IBGE) nesta mesma pasta:
# na primeira execução o programa lê, simplifica e guarda um cache leve.
PASTA_CONTORNOS = "contornos"
ZIP_UF = "BR_UF_2021.zip"
ZIP_MUNICIPIOS = "BR_Municipios_2021.zip"
TOL_UF = 0.01          # ~1 km de tolerância no contorno dos estados
TOL_MUNICIPIO = 0.004  # ~400 m no contorno dos municípios

UF_NOMES = {
    "AC": "Acre", "AL": "Alagoas", "AP": "Amapá", "AM": "Amazonas",
    "BA": "Bahia", "CE": "Ceará", "DF": "Distrito Federal",
    "ES": "Espírito Santo", "GO": "Goiás", "MA": "Maranhão",
    "MT": "Mato Grosso", "MS": "Mato Grosso do Sul", "MG": "Minas Gerais",
    "PA": "Pará", "PB": "Paraíba", "PR": "Paraná", "PE": "Pernambuco",
    "PI": "Piauí", "RJ": "Rio de Janeiro", "RN": "Rio Grande do Norte",
    "RS": "Rio Grande do Sul", "RO": "Rondônia", "RR": "Roraima",
    "SC": "Santa Catarina", "SP": "São Paulo", "SE": "Sergipe",
    "TO": "Tocantins",
}

# O certificado do INMET falha em algumas instalações do Windows.
# Como são dados públicos, seguimos sem verificar.
_CTX = ssl.create_default_context()
_CTX.check_hostname = False
_CTX.verify_mode = ssl.CERT_NONE

_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
       "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")


# =====================================================================
# BLOCO 3 — ESTAÇÕES DO INMET
# =====================================================================

def caminho_ao_lado(nome):
    """Caminho de um arquivo na mesma pasta deste script."""
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), nome)


def baixar_estacoes():
    """Busca a lista de estações automáticas na API pública do INMET."""
    req = urllib.request.Request(f"{API_INMET}/estacoes/T",
                                 headers={"User-Agent": _UA,
                                          "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=60, context=_CTX) as r:
        return json.loads(r.read().decode("utf-8"))


def carregar_estacoes(forcar_download=False):
    """Lista de estações, do cache local ou da API.

    Devolve (lista, origem) — origem diz de onde veio, para mostrar na tela.
    """
    cache = caminho_ao_lado(ARQUIVO_CACHE)

    if not forcar_download and os.path.exists(cache):
        try:
            with open(cache, encoding="utf-8") as f:
                return json.load(f), "arquivo local"
        except Exception:
            pass  # cache corrompido: cai para o download

    bruto = baixar_estacoes()
    try:
        with open(cache, "w", encoding="utf-8") as f:
            json.dump(bruto, f, ensure_ascii=False)
    except Exception:
        pass  # sem permissão de escrita: funciona igual, só não guarda

    return bruto, "API do INMET"


def normalizar(bruto):
    """Converte o retorno da API para uma lista de dicionários enxuta."""
    saida = []
    for e in bruto:
        try:
            lat = float(e["VL_LATITUDE"])
            lon = float(e["VL_LONGITUDE"])
        except (TypeError, ValueError, KeyError):
            continue
        try:
            alt = float(e.get("VL_ALTITUDE") or 0)
        except (TypeError, ValueError):
            alt = 0.0
        saida.append({
            "codigo": e.get("CD_ESTACAO", ""),
            "nome": e.get("DC_NOME", ""),
            "uf": e.get("SG_ESTADO", ""),
            "lat": lat,
            "lon": lon,
            "altitude": alt,
            "operante": e.get("CD_SITUACAO") == "Operante",
        })
    return saida


# =====================================================================
# BLOCO 4 — GEOMETRIA
# =====================================================================

def haversine(lat1, lon1, lat2, lon2):
    """Distância em km entre dois pontos. Aceita arrays do numpy."""
    R = 6371.0
    lat1, lon1, lat2, lon2 = map(np.radians, [lat1, lon1, lat2, lon2])
    a = (np.sin((lat2 - lat1) / 2) ** 2
         + np.cos(lat1) * np.cos(lat2) * np.sin((lon2 - lon1) / 2) ** 2)
    return 2 * R * np.arcsin(np.sqrt(a))


def centroide(pontos):
    """Centroide de área de um polígono [(lon, lat), ...]. Devolve (lat, lon)."""
    pts = [(float(x), float(y)) for x, y in pontos]
    if len(pts) < 3:
        return (sum(p[1] for p in pts) / len(pts),
                sum(p[0] for p in pts) / len(pts))
    a = cx = cy = 0.0
    for i in range(len(pts)):
        x1, y1 = pts[i]
        x2, y2 = pts[(i + 1) % len(pts)]
        f = x1 * y2 - x2 * y1
        a += f
        cx += (x1 + x2) * f
        cy += (y1 + y2) * f
    a *= 0.5
    if abs(a) < 1e-12:
        return (sum(p[1] for p in pts) / len(pts),
                sum(p[0] for p in pts) / len(pts))
    return (cy / (6 * a), cx / (6 * a))


def area_hectares(pontos):
    """Área aproximada, em hectares, de um polígono [(lon, lat), ...]."""
    pts = [(float(x), float(y)) for x, y in pontos]
    if len(pts) < 3:
        return None
    lat0 = sum(p[1] for p in pts) / len(pts)
    kx = 111320 * math.cos(math.radians(lat0))
    ky = 110540
    a = 0.0
    for i in range(len(pts)):
        x1, y1 = pts[i]
        x2, y2 = pts[(i + 1) % len(pts)]
        a += (x1 * kx) * (y2 * ky) - (x2 * kx) * (y1 * ky)
    return abs(a / 2) / 10000


def estacoes_proximas(estacoes, lat, lon, n=4, so_operantes=True):
    """As n estações mais próximas, cada uma com a chave 'distancia'."""
    cand = [e for e in estacoes if e["operante"]] if so_operantes else list(estacoes)
    if not cand:
        return []
    lats = np.array([e["lat"] for e in cand])
    lons = np.array([e["lon"] for e in cand])
    dists = haversine(lat, lon, lats, lons)
    ordem = np.argsort(dists)[:n]
    return [dict(cand[i], distancia=float(dists[i])) for i in ordem]


def pesos_idw(proximas):
    """Peso de cada estação pelo inverso do quadrado da distância."""
    if not proximas:
        return {}
    inv = {p["codigo"]: 1.0 / max(p["distancia"], 0.5) ** 2 for p in proximas}
    total = sum(inv.values())
    return {k: v / total for k, v in inv.items()}


# =====================================================================
# BLOCO 5 — LEITURA DO ARQUIVO DA ÁREA
# =====================================================================

def _coords_kml(texto):
    pontos = []
    for t in (texto or "").strip().split():
        partes = t.split(",")
        if len(partes) >= 2:
            try:
                pontos.append((float(partes[0]), float(partes[1])))
            except ValueError:
                pass
    return pontos


def ler_kml(conteudo):
    if isinstance(conteudo, bytes):
        conteudo = conteudo.decode("utf-8", errors="replace")
    raiz = ET.fromstring(conteudo)
    ns = {"k": "http://www.opengis.net/kml/2.2"}

    def acha(el, caminho):
        # KML de GPS costuma vir sem namespace
        return el.findall(caminho, ns) or el.findall(caminho.replace("k:", ""))

    feicoes = []
    for pm in acha(raiz, ".//k:Placemark"):
        nome_el = acha(pm, "k:name")
        nome = nome_el[0].text if nome_el else "área"
        for tag in ("k:Polygon//k:coordinates",
                    "k:LineString/k:coordinates",
                    "k:Point/k:coordinates"):
            achados = acha(pm, f".//{tag}")
            if achados:
                pts = _coords_kml(achados[0].text)
                if pts:
                    feicoes.append((nome, pts))
                break
    if not feicoes:
        for c in acha(raiz, ".//k:coordinates"):
            pts = _coords_kml(c.text)
            if pts:
                feicoes.append(("área", pts))
    return feicoes


def ler_geojson(conteudo):
    j = json.loads(conteudo) if isinstance(conteudo, (str, bytes)) else conteudo
    feats = j.get("features", [j]) if isinstance(j, dict) else []
    saida = []
    for f in feats:
        g = f.get("geometry", f)
        nome = (f.get("properties") or {}).get("name", "área")
        t, c = g.get("type"), g.get("coordinates")
        if t == "Polygon":
            saida.append((nome, [tuple(p[:2]) for p in c[0]]))
        elif t == "MultiPolygon":
            for parte in c:
                saida.append((nome, [tuple(p[:2]) for p in parte[0]]))
        elif t == "LineString":
            saida.append((nome, [tuple(p[:2]) for p in c]))
        elif t == "Point":
            saida.append((nome, [tuple(c[:2])]))
    return saida


def ler_shapefile(caminho):
    try:
        import shapefile  # pyshp
    except ImportError:
        raise RuntimeError(
            "Para ler shapefile é preciso instalar o pyshp:\n\n"
            "    pip install pyshp\n\n"
            "Ou exporte a área como KML, que não precisa de nada.")

    if caminho.lower().endswith(".zip"):
        import io
        with zipfile.ZipFile(caminho) as z:
            nomes = z.namelist()
            base = next((n[:-4] for n in nomes if n.lower().endswith(".shp")), None)
            if not base:
                raise RuntimeError("O .zip não contém nenhum arquivo .shp.")
            partes = {}
            for ext in ("shp", "dbf", "shx"):
                alvo = next((n for n in nomes
                             if n.lower() == f"{base.lower()}.{ext}"), None)
                if alvo:
                    partes[ext] = io.BytesIO(z.read(alvo))
            leitor = shapefile.Reader(**partes)
    else:
        leitor = shapefile.Reader(caminho)

    saida = []
    for i, forma in enumerate(leitor.shapes()):
        pts = [tuple(p) for p in forma.points]
        if pts:
            saida.append((f"feição {i + 1}", pts))
    return saida


def ler_area(caminho):
    """Lê a área de um arquivo. Devolve (nome, pontos [(lon, lat), ...])."""
    ext = os.path.splitext(caminho)[1].lower()

    if ext == ".kml":
        with open(caminho, "rb") as f:
            feicoes = ler_kml(f.read())
    elif ext == ".kmz":
        with zipfile.ZipFile(caminho) as z:
            kml = next((n for n in z.namelist() if n.lower().endswith(".kml")), None)
            if not kml:
                raise RuntimeError("O .kmz não contém nenhum .kml dentro.")
            feicoes = ler_kml(z.read(kml))
    elif ext in (".json", ".geojson"):
        with open(caminho, encoding="utf-8") as f:
            feicoes = ler_geojson(f.read())
    elif ext in (".shp", ".zip"):
        feicoes = ler_shapefile(caminho)
    else:
        raise RuntimeError(f"Formato não reconhecido: {ext}\n"
                           "Use .kml, .kmz, .geojson, .shp ou shapefile em .zip.")

    if not feicoes:
        raise RuntimeError("Nenhuma geometria encontrada no arquivo.")

    nome, pts = feicoes[0]

    # Shapefile agrícola no Brasil quase sempre vem em UTM / SIRGAS 2000.
    # Sem esta conferência, o centroide cairia no oceano em silêncio.
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    if not (all(-180 <= x <= 180 for x in xs) and all(-90 <= y <= 90 for y in ys)):
        raise RuntimeError(
            f"As coordenadas de {os.path.basename(caminho)} não são "
            f"latitude/longitude.\n\n"
            f"X vai de {min(xs):,.0f} a {max(xs):,.0f}\n"
            f"Y vai de {min(ys):,.0f} a {max(ys):,.0f}\n\n"
            "O arquivo provavelmente está em UTM / SIRGAS 2000.\n"
            "No QGIS: clique direito na camada → Exportar → Salvar como, "
            "e escolha EPSG:4326.\n"
            "Ou exporte como KML, que já sai em lat/lon.")

    return nome, pts, len(feicoes)


# =====================================================================
# BLOCO 6 — CONTORNOS DO BRASIL (fundo do mapa)
# =====================================================================
#
# Os arquivos do IBGE são grandes demais para abrir a cada execução: o de
# municípios tem 270 MB e 17 milhões de pontos. Então lemos uma única vez,
# simplificamos por Douglas-Peucker e guardamos um cache por estado — que
# fica na casa de centenas de KB e carrega instantaneamente.


def _simplifica(pontos, tol):
    """Douglas-Peucker: descarta pontos que não mudam o traçado."""
    if len(pontos) < 3:
        return pontos
    manter = [False] * len(pontos)
    manter[0] = manter[-1] = True
    pilha = [(0, len(pontos) - 1)]
    while pilha:
        ini, fim = pilha.pop()
        if fim - ini < 2:
            continue
        x1, y1 = pontos[ini]
        x2, y2 = pontos[fim]
        dx, dy = x2 - x1, y2 - y1
        norma = math.hypot(dx, dy)
        pior, d_pior = -1, 0.0
        for i in range(ini + 1, fim):
            x, y = pontos[i]
            if norma == 0:
                d = math.hypot(x - x1, y - y1)
            else:
                d = abs(dy * x - dx * y + x2 * y1 - y2 * x1) / norma
            if d > d_pior:
                pior, d_pior = i, d
        if d_pior > tol:
            manter[pior] = True
            pilha.append((ini, pior))
            pilha.append((pior, fim))
    return [p for p, m in zip(pontos, manter) if m]


def _le_dbf(caminho, colunas):
    """Lê apenas as colunas pedidas de um .dbf. Os do IBGE são UTF-8."""
    import struct
    with open(caminho, "rb") as f:
        cab = f.read(32)
        n_reg, tam_cab, tam_reg = struct.unpack("<I H H", cab[4:12])
        f.seek(32)
        campos = []
        while True:
            d = f.read(32)
            if d[0:1] in (b"\r", b""):
                break
            nome = d[0:11].split(b"\x00")[0].decode("utf-8", "replace").strip()
            campos.append((nome, d[16]))
        f.seek(tam_cab)
        idx, off = {}, 1
        for nome, tam in campos:
            if nome in colunas:
                idx[nome] = (off, tam)
            off += tam
        saida = []
        for _ in range(n_reg):
            reg = f.read(tam_reg)
            if not reg:
                break
            saida.append({c: reg[o:o + t].decode("utf-8", "replace").strip()
                          for c, (o, t) in idx.items()})
    return saida


def _le_shp_poligonos(caminho, so_maior_parte=False):
    """Percorre um .shp de polígonos, um registro por vez.

    Lê sem carregar o arquivo inteiro na memória — necessário para o de
    municípios. Devolve (partes, bbox) a cada iteração.
    """
    import struct
    with open(caminho, "rb") as f:
        f.seek(100)                      # pula o cabeçalho
        while True:
            cab = f.read(8)
            if len(cab) < 8:
                break
            _, tam = struct.unpack(">ii", cab)
            corpo = f.read(tam * 2)
            if len(corpo) < 44 or struct.unpack("<i", corpo[0:4])[0] != 5:
                yield [], None
                continue
            box = struct.unpack("<4d", corpo[4:36])
            n_partes, n_pontos = struct.unpack("<ii", corpo[36:44])
            p = 44
            idx = struct.unpack(f"<{n_partes}i", corpo[p:p + 4 * n_partes])
            p += 4 * n_partes
            xy = struct.unpack(f"<{2 * n_pontos}d", corpo[p:p + 16 * n_pontos])

            faixas = []
            for k, ini in enumerate(idx):
                fim = idx[k + 1] if k + 1 < n_partes else n_pontos
                faixas.append((ini, fim))
            if so_maior_parte and faixas:
                faixas = [max(faixas, key=lambda t: t[1] - t[0])]

            partes = [list(zip(xy[2 * i:2 * j:2], xy[2 * i + 1:2 * j:2]))
                      for i, j in faixas]
            yield partes, box


def _extrai_do_zip(caminho_zip, destino):
    """Extrai .shp e .dbf de um zip do IBGE, em blocos."""
    nomes = []
    with zipfile.ZipFile(caminho_zip) as z:
        for nome in z.namelist():
            if not nome.lower().endswith((".shp", ".dbf")):
                continue
            alvo = os.path.join(destino, os.path.basename(nome))
            with z.open(nome) as origem, open(alvo, "wb") as saida:
                while True:
                    bloco = origem.read(1 << 22)
                    if not bloco:
                        break
                    saida.write(bloco)
            nomes.append(alvo)
    return nomes


def construir_cache_contornos(avisar=None):
    """Lê os zips do IBGE e grava o cache simplificado. Roda uma vez só.

    avisar: função opcional que recebe o texto de andamento.
    """
    import tempfile

    def diz(t):
        if avisar:
            avisar(t)

    pasta = caminho_ao_lado(PASTA_CONTORNOS)
    os.makedirs(pasta, exist_ok=True)
    temp = tempfile.mkdtemp()
    feito = []

    try:
        # ---- estados ----
        zip_uf = caminho_ao_lado(ZIP_UF)
        if os.path.exists(zip_uf) and not os.path.exists(os.path.join(pasta, "uf.json")):
            diz("Lendo o contorno dos estados…")
            _extrai_do_zip(zip_uf, temp)
            shp = next(f for f in os.listdir(temp) if f.lower().endswith(".shp"))
            base = os.path.join(temp, shp)
            atrib = _le_dbf(base[:-4] + ".dbf", {"SIGLA", "SIGLA_UF", "NM_UF"})
            saida = {}
            for i, (partes, _) in enumerate(_le_shp_poligonos(base)):
                a = atrib[i] if i < len(atrib) else {}
                sigla = a.get("SIGLA") or a.get("SIGLA_UF") or f"?{i}"
                simp = []
                for parte in partes:
                    s = _simplifica(parte, TOL_UF)
                    if len(s) >= 4:
                        simp.append([[round(x, 4), round(y, 4)] for x, y in s])
                if simp:
                    saida[sigla] = simp
            with open(os.path.join(pasta, "uf.json"), "w", encoding="utf-8") as f:
                json.dump(saida, f, separators=(",", ":"), ensure_ascii=False)
            feito.append(f"{len(saida)} estados")
            for f_ in os.listdir(temp):
                os.remove(os.path.join(temp, f_))

        # ---- municípios ----
        zip_mun = caminho_ao_lado(ZIP_MUNICIPIOS)
        if os.path.exists(zip_mun) and not os.path.exists(os.path.join(pasta, "mun_SP.json")):
            diz("Lendo o contorno dos municípios — leva alguns segundos…")
            _extrai_do_zip(zip_mun, temp)
            shp = next(f for f in os.listdir(temp) if f.lower().endswith(".shp"))
            base = os.path.join(temp, shp)
            atrib = _le_dbf(base[:-4] + ".dbf", {"NM_MUN", "SIGLA", "SIGLA_UF"})
            por_uf = {}
            for i, (partes, box) in enumerate(_le_shp_poligonos(base, so_maior_parte=True)):
                if not partes:
                    continue
                a = atrib[i] if i < len(atrib) else {}
                uf = a.get("SIGLA") or a.get("SIGLA_UF") or "??"
                s = _simplifica(partes[0], TOL_MUNICIPIO)
                por_uf.setdefault(uf, []).append({
                    "n": a.get("NM_MUN", ""),
                    "b": [round(v, 3) for v in box],
                    "p": [[round(x, 4), round(y, 4)] for x, y in s],
                })
            for uf, lista in por_uf.items():
                with open(os.path.join(pasta, f"mun_{uf}.json"), "w", encoding="utf-8") as f:
                    json.dump(lista, f, separators=(",", ":"), ensure_ascii=False)
            feito.append(f"{sum(len(v) for v in por_uf.values())} municípios")
    finally:
        try:
            for f_ in os.listdir(temp):
                os.remove(os.path.join(temp, f_))
            os.rmdir(temp)
        except OSError:
            pass

    return feito


def carregar_contorno_ufs():
    """Contorno dos estados, ou {} se o cache não existe."""
    caminho = os.path.join(caminho_ao_lado(PASTA_CONTORNOS), "uf.json")
    if not os.path.exists(caminho):
        return {}
    try:
        with open(caminho, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def carregar_contorno_municipios(uf):
    """Municípios de um estado, ou [] se não houver cache."""
    if not uf:
        return []
    caminho = os.path.join(caminho_ao_lado(PASTA_CONTORNOS), f"mun_{uf}.json")
    if not os.path.exists(caminho):
        return []
    try:
        with open(caminho, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []


# =====================================================================
# BLOCO 7 — ABA DE DEFINIÇÃO DA ÁREA
# =====================================================================

COR_FUNDO = "#fcfcfb"
COR_ESTACAO = "#9a9a9e"
COR_SELECIONADA = "#c4342b"
COR_AREA = "#2f8f5b"
COR_LINHA = "#d98c1f"
COR_UF = "#9aa3ad"          # contorno dos estados
COR_MUNICIPIO = "#d8dde2"   # contorno dos municípios
COR_NOME_MUN = "#8b949e"

# ---------------------------------------------------------------------
# Botões principais
# ---------------------------------------------------------------------
# Cada aba tem UMA ação principal (usar a coordenada, baixar e analisar,
# buscar a previsão, gerar o relatório, analisar os voos). Ela sai em
# verde, com texto branco em negrito, para não se perder entre os outros
# botões. É tk.Button, e não ttk, porque o tema nativo do Windows ignora a
# cor de fundo dos botões ttk. No Mac o tk.Button também ignora a cor, e o
# texto branco sumiria; lá o destaque fica só no negrito.
# Os botões de carregar arquivo e o de "Próxima etapa" ficam em negrito.
COR_BOTAO = "#1f7a4a"
COR_BOTAO_SOBRE = "#155c37"
COR_BOTAO_OFF = "#a3bdae"
FONTE_BOTAO = ("Segoe UI", 10, "bold")    # reserva, se a de baixo falhar
ESTILO_DESTAQUE = "Destaque.TButton"
_FONTE_BOTAO = []


def fonte_botao():
    """A fonte do sistema (Segoe UI no Windows, a do Mac no Mac), em
    negrito e um ponto maior. Criada uma vez, depois da janela principal."""
    if not _FONTE_BOTAO:
        try:
            import tkinter.font as tkfont
            base = tkfont.nametofont("TkDefaultFont")
            tam = int(base.actual().get("size", 9)) or 9
            f = base.copy()
            # tamanho negativo é em pixels: cresce para o mesmo lado
            f.configure(weight="bold", size=tam + 1 if tam > 0 else tam - 1)
            _FONTE_BOTAO.append(f)
        except Exception:
            _FONTE_BOTAO.append(FONTE_BOTAO)
    return _FONTE_BOTAO[0]


def configurar_estilos(raiz):
    """Cria o estilo em negrito dos botões de carregar e de próxima etapa."""
    try:
        estilo = ttk.Style(raiz)
        estilo.configure(ESTILO_DESTAQUE, font=fonte_botao(), padding=(8, 3))
    except Exception as e:
        print("Não consegui criar o estilo dos botões:", e)


class BotaoPrincipal(tk.Button):
    """Botão verde da ação principal da aba. Fica claro quando desligado
    (por exemplo, enquanto baixa) e escurece com o mouse em cima."""

    def __init__(self, pai, text="", command=None, state="normal", **kw):
        super().__init__(pai, text=text, command=command, state=state,
                         bg=COR_BOTAO, fg="white",
                         activebackground=COR_BOTAO_SOBRE,
                         activeforeground="white",
                         disabledforeground="#f4f8f6",
                         font=fonte_botao(), relief="flat", bd=0,
                         highlightthickness=0, padx=16, pady=4,
                         cursor="hand2", **kw)
        self.bind("<Enter>", lambda e: self._pintar(sobre=True))
        self.bind("<Leave>", lambda e: self._pintar())
        self._pintar()

    def _pintar(self, sobre=False):
        try:
            desligado = str(self.cget("state")) == "disabled"
            cor = (COR_BOTAO_OFF if desligado
                   else COR_BOTAO_SOBRE if sobre else COR_BOTAO)
            tk.Button.configure(self, bg=cor)
        except Exception:
            pass

    def configure(self, cnf=None, **kw):
        r = super().configure(cnf, **kw)
        if "state" in kw:
            self._pintar()
        return r

    config = configure


def botao_principal(pai, texto, comando, **kw):
    """Botão da ação principal da aba (verde; no Mac, negrito)."""
    if sys.platform == "darwin":
        return ttk.Button(pai, text=texto, command=comando,
                          style=ESTILO_DESTAQUE, **kw)
    return BotaoPrincipal(pai, text=texto, command=comando, **kw)


class AbaArea(ttk.Frame):
    """Mapa + formulário para definir a área e ver as estações mais próximas."""

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.pontos_area = None      # [(lon, lat), ...] quando vem de arquivo
        # Precisa existir antes de qualquer desenho: a lista de estados só é
        # preenchida depois que as estações carregam, mas o mapa já é desenhado
        # na construção da aba.
        self._uf_por_rotulo = {"Brasil inteiro": ""}
        self._contorno_uf = carregar_contorno_ufs()
        self._contorno_mun = {}          # cache por estado, carregado sob demanda
        # A ordem aqui importa. A tabela é empacotada ANTES do mapa e presa
        # embaixo, para reservar a altura dela primeiro; o mapa fica com o
        # que sobrar. Na ordem inversa, em tela cheia o mapa esticava e
        # espremia a tabela até sobrar só o cabeçalho.
        self._construir_controles()
        self._construir_tabela()
        self._construir_mapa()
        self.atualizar_mapa()

    # ------------------------------------------------------------------
    def _construir_controles(self):
        painel = ttk.LabelFrame(self, text="Área de interesse")
        painel.pack(side="top", fill="x", padx=8, pady=(8, 4))

        # --- linha 1: estado e número de estações ---
        linha1 = ttk.Frame(painel)
        linha1.pack(side="top", fill="x", padx=6, pady=(6, 2))

        ttk.Label(linha1, text="Estado:").pack(side="left")
        self.var_uf = tk.StringVar(value="Brasil inteiro")
        self.cb_uf = ttk.Combobox(linha1, textvariable=self.var_uf, width=26,
                                  state="readonly")
        self.cb_uf.pack(side="left", padx=(4, 14))
        self.cb_uf.bind("<<ComboboxSelected>>", lambda e: self.ao_trocar_uf())

        ttk.Label(linha1, text="Estações:").pack(side="left")
        self.var_n = tk.StringVar(value="4")
        cb_n = ttk.Combobox(linha1, textvariable=self.var_n, width=4,
                            state="readonly", values=("3", "4", "5"))
        cb_n.pack(side="left", padx=(4, 14))
        cb_n.bind("<<ComboboxSelected>>", lambda e: self.recalcular())

        ttk.Label(linha1, text="(clique no mapa para marcar a área)",
                  foreground="#666").pack(side="left")

        # --- linha 2: coordenada e arquivo ---
        linha2 = ttk.Frame(painel)
        linha2.pack(side="top", fill="x", padx=6, pady=(2, 8))

        ttk.Label(linha2, text="Latitude:").pack(side="left")
        self.var_lat = tk.StringVar()
        ttk.Entry(linha2, textvariable=self.var_lat, width=12).pack(side="left", padx=(4, 10))

        ttk.Label(linha2, text="Longitude:").pack(side="left")
        self.var_lon = tk.StringVar()
        ttk.Entry(linha2, textvariable=self.var_lon, width=12).pack(side="left", padx=(4, 10))

        botao_principal(linha2, "Usar coordenada",
                        self.usar_coordenada).pack(side="left")
        ttk.Button(linha2, text="Carregar arquivo do talhão…",
                   style=ESTILO_DESTAQUE,
                   command=self.carregar_arquivo).pack(side="left", padx=(10, 0))
        ttk.Button(linha2, text="Limpar",
                   command=self.limpar).pack(side="left", padx=(10, 0))

    # ------------------------------------------------------------------
    def _construir_mapa(self):
        quadro = ttk.Frame(self)
        quadro.pack(side="top", fill="both", expand=True, padx=8, pady=4)

        self.fig = plt.Figure(figsize=(9, 5.2), facecolor=COR_FUNDO)
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=quadro)
        self.canvas.get_tk_widget().pack(side="top", fill="both", expand=True)
        self.barra = NavigationToolbar2Tk(self.canvas, quadro)
        self.barra.update()

        self.canvas.mpl_connect("button_press_event", self.ao_clicar_mapa)
        self.canvas.mpl_connect("motion_notify_event", self.ao_mover_mouse)

        # anotação que segue o mouse mostrando a estação sob o cursor
        self._dica = self.ax.annotate(
            "", xy=(0, 0), xytext=(12, 12), textcoords="offset points",
            fontsize=8, zorder=20, visible=False,
            bbox=dict(boxstyle="round,pad=0.4", facecolor="#ffffff",
                      edgecolor="#b8b8b4", alpha=0.95))
        self._plotadas = []

    def _construir_tabela(self):
        quadro = ttk.LabelFrame(self, text="Estações mais próximas")
        quadro.pack(side="bottom", fill="x", padx=8, pady=(4, 8))

        colunas = ("codigo", "nome", "uf", "distancia", "peso", "altitude")
        titulos = {"codigo": "Código", "nome": "Estação", "uf": "UF",
                   "distancia": "Distância (km)", "peso": "Peso na série",
                   "altitude": "Altitude (m)"}
        larguras = {"codigo": 70, "nome": 260, "uf": 45,
                    "distancia": 110, "peso": 100, "altitude": 100}

        self.tabela = ttk.Treeview(quadro, columns=colunas, show="headings", height=5)
        for c in colunas:
            self.tabela.heading(c, text=titulos[c])
            self.tabela.column(c, width=larguras[c],
                               anchor="w" if c == "nome" else "center")
        self.tabela.pack(side="top", fill="x", padx=6, pady=6)

        self.lbl_aviso = ttk.Label(quadro, text="", foreground="#8a6116",
                                   wraplength=900, justify="left")
        self.lbl_aviso.pack(side="top", anchor="w", padx=6, pady=(0, 6))

    # ------------------------------------------------------------------
    def preencher_ufs(self):
        ufs = sorted({e["uf"] for e in self.app.estacoes if e["uf"]})
        valores = ["Brasil inteiro"]
        self._uf_por_rotulo = {"Brasil inteiro": ""}
        for uf in ufs:
            n = sum(1 for e in self.app.estacoes if e["uf"] == uf and e["operante"])
            rotulo = f"{UF_NOMES.get(uf, uf)} ({n} operantes)"
            valores.append(rotulo)
            self._uf_por_rotulo[rotulo] = uf
        self.cb_uf["values"] = valores

        # abre já no estado preferido, se ele existir na lista
        if UF_INICIAL and self.var_uf.get() == "Brasil inteiro":
            for rotulo, sigla in self._uf_por_rotulo.items():
                if sigla == UF_INICIAL:
                    self.var_uf.set(rotulo)
                    break

    def uf_atual(self):
        return self._uf_por_rotulo.get(self.var_uf.get(), "")

    def estacoes_visiveis(self):
        uf = self.uf_atual()
        base = [e for e in self.app.estacoes if e["operante"]]
        return [e for e in base if e["uf"] == uf] if uf else base

    # ------------------------------------------------------------------
    def ao_trocar_uf(self):
        self.atualizar_mapa(enquadrar=True)

    def ao_clicar_mapa(self, evento):
        # a barra de ferramentas manda enquanto zoom ou pan estiverem ativos
        if evento.inaxes is not self.ax:
            return
        if getattr(self.barra, "mode", ""):
            return
        if evento.xdata is None or evento.ydata is None:
            return
        self.pontos_area = None
        self.app.definir_area(float(evento.ydata), float(evento.xdata),
                              None, "clique no mapa")

    def ao_mover_mouse(self, evento):
        """Mostra o nome da estação sob o cursor."""
        if evento.inaxes is not self.ax or not self._plotadas:
            if self._dica.get_visible():
                self._dica.set_visible(False)
                self.canvas.draw_idle()
            return

        # distância em pixels, para o alcance não mudar com o zoom
        px_cursor = np.array([evento.x, evento.y])
        pontos = self.ax.transData.transform(
            [(e["lon"], e["lat"]) for e in self._plotadas])
        d = np.hypot(pontos[:, 0] - px_cursor[0], pontos[:, 1] - px_cursor[1])
        i = int(np.argmin(d))

        if d[i] > 14:
            if self._dica.get_visible():
                self._dica.set_visible(False)
                self.canvas.draw_idle()
            return

        e = self._plotadas[i]
        texto = f'{e["nome"]}\n{e["codigo"]} · {e["uf"]} · {e["altitude"]:.0f} m'
        if self.app.lat is not None:
            km = haversine(self.app.lat, self.app.lon, e["lat"], e["lon"])
            texto += f"\n{km:.1f} km da sua área"
        self._dica.xy = (e["lon"], e["lat"])
        self._dica.set_text(texto)
        self._dica.set_visible(True)
        self.canvas.draw_idle()

    def usar_coordenada(self):
        try:
            lat = float(self.var_lat.get().replace(",", "."))
            lon = float(self.var_lon.get().replace(",", "."))
        except ValueError:
            messagebox.showerror("Coordenada inválida",
                                 "Preencha latitude e longitude com números.\n"
                                 "Exemplo: -12.16 e -45.775")
            return
        if not (-90 <= lat <= 90) or not (-180 <= lon <= 180):
            messagebox.showerror("Coordenada fora do mundo",
                                 "Latitude vai de -90 a 90 e longitude de -180 a 180.\n"
                                 "No Brasil as duas são negativas.")
            return
        self.pontos_area = None
        self.app.definir_area(lat, lon, None, "coordenada digitada")

    def carregar_arquivo(self):
        caminho = filedialog.askopenfilename(
            title="Escolha o arquivo do talhão",
            filetypes=[("Todos os formatos aceitos",
                        "*.kml *.kmz *.geojson *.json *.shp *.zip"),
                       ("Google Earth", "*.kml *.kmz"),
                       ("GeoJSON", "*.geojson *.json"),
                       ("Shapefile", "*.shp *.zip"),
                       ("Todos os arquivos", "*.*")])
        if not caminho:
            return
        try:
            nome, pts, quantas = ler_area(caminho)
        except Exception as e:
            messagebox.showerror("Não consegui ler o arquivo", str(e))
            return

        self.pontos_area = pts
        lat, lon = centroide(pts)
        ha = area_hectares(pts) if len(pts) >= 3 else None
        origem = f"arquivo {os.path.basename(caminho)}"
        if quantas > 1:
            origem += f" ({quantas} feições, usando a primeira: {nome})"
        self.app.definir_area(lat, lon, ha, origem)

    def limpar(self):
        self.pontos_area = None
        self.var_lat.set("")
        self.var_lon.set("")
        self.app.limpar_area()

    def recalcular(self):
        if self.app.lat is not None:
            self.app.definir_area(self.app.lat, self.app.lon,
                                  self.app.area_ha, self.app.origem)

    # ------------------------------------------------------------------
    def municipios_do_estado(self, uf):
        """Contorno dos municípios, carregado na primeira vez que o estado é usado."""
        if uf not in self._contorno_mun:
            self._contorno_mun[uf] = carregar_contorno_municipios(uf)
        return self._contorno_mun[uf]

    def _ufs_em_cena(self):
        """Estados cujos municípios vale desenhar: o escolhido e os das
        estações selecionadas — senão uma estação vizinha fica sem contexto."""
        ufs = set()
        atual = self.uf_atual()
        if atual:
            ufs.add(atual)
        for p in self.app.proximas:
            if p.get("uf"):
                ufs.add(p["uf"])
        return ufs

    def _desenhar_fundo(self, uf):
        """Contorno de estados e municípios, por baixo de tudo.

        Uma LineCollection só para centenas de polígonos — desenhar um a um
        deixaria o mapa lento com os 853 municípios de Minas.
        """
        if not self._contorno_uf:
            return

        segs = []
        for sigla in self._ufs_em_cena():
            segs += [m["p"] for m in self.municipios_do_estado(sigla)
                     if len(m["p"]) > 2]
        if segs:
            self.ax.add_collection(LineCollection(
                segs, colors=COR_MUNICIPIO, linewidths=0.6, zorder=0))

        segs_uf = [parte for partes in self._contorno_uf.values()
                   for parte in partes if len(parte) > 2]
        if segs_uf:
            self.ax.add_collection(LineCollection(
                segs_uf, colors=COR_UF, linewidths=0.9, zorder=1))

    def _nomear_municipios(self, uf=None):
        """Nome dos municípios visíveis, só quando são poucos na tela."""
        municipios = []
        for sigla in self._ufs_em_cena():
            municipios += self.municipios_do_estado(sigla)
        if not municipios:
            return
        x0, x1 = self.ax.get_xlim()
        y0, y1 = self.ax.get_ylim()
        largura = x1 - x0

        # sem nome nenhum na visão de país inteiro: viraria borrão
        if largura > 12:
            return

        visiveis = []
        for m in municipios:
            bx0, by0, bx1, by1 = m["b"]
            cx, cy = (bx0 + bx1) / 2, (by0 + by1) / 2
            if x0 < cx < x1 and y0 < cy < y1:
                visiveis.append(((bx1 - bx0) * (by1 - by0), cx, cy, m["n"]))

        # só os maiores da tela, para o rótulo não virar amontoado
        limite = 12 if largura > 3 else 20
        for _, cx, cy, nome in sorted(visiveis, reverse=True)[:limite]:
            self.ax.text(cx, cy, nome, fontsize=6.5, color=COR_NOME_MUN,
                         ha="center", va="center", zorder=1)

    def atualizar_mapa(self, enquadrar=True):
        self.ax.clear()
        self.ax.set_facecolor(COR_FUNDO)
        self._desenhar_fundo(self.uf_atual())

        visiveis = self.estacoes_visiveis()
        selecionadas = {p["codigo"] for p in self.app.proximas}
        # guardadas para o hover saber o que está sob o cursor
        self._plotadas = visiveis + [p for p in self.app.proximas
                                     if p["codigo"] not in
                                     {e["codigo"] for e in visiveis}]

        if visiveis:
            lons = [e["lon"] for e in visiveis if e["codigo"] not in selecionadas]
            lats = [e["lat"] for e in visiveis if e["codigo"] not in selecionadas]
            self.ax.scatter(lons, lats, s=22, c=COR_ESTACAO, linewidths=0,
                            alpha=0.85, zorder=2, label="Estações operantes")

        # linhas do centroide até cada estação escolhida
        if self.app.lat is not None and self.app.proximas:
            for p in self.app.proximas:
                self.ax.plot([self.app.lon, p["lon"]], [self.app.lat, p["lat"]],
                             color=COR_LINHA, linewidth=1, linestyle="--",
                             alpha=0.8, zorder=3)
            self.ax.scatter([p["lon"] for p in self.app.proximas],
                            [p["lat"] for p in self.app.proximas],
                            s=70, c=COR_SELECIONADA, linewidths=0, zorder=5,
                            label="Estações escolhidas")
            for p in self.app.proximas:
                self.ax.annotate(f'{p["nome"][:22]}\n{p["distancia"]:.0f} km',
                                 (p["lon"], p["lat"]),
                                 textcoords="offset points", xytext=(7, 5),
                                 fontsize=7.5, color="#333", zorder=6)

        # a área
        if self.pontos_area and len(self.pontos_area) >= 3:
            xs = [p[0] for p in self.pontos_area]
            ys = [p[1] for p in self.pontos_area]
            self.ax.fill(xs, ys, color=COR_AREA, alpha=0.25, zorder=4)
            self.ax.plot(xs + [xs[0]], ys + [ys[0]], color=COR_AREA,
                         linewidth=1.8, zorder=4)

        if self.app.lat is not None:
            self.ax.scatter([self.app.lon], [self.app.lat], s=130, marker="X",
                            c=COR_AREA, edgecolors="white", linewidths=1.5,
                            zorder=7, label="Sua área")

        self.ax.set_xlabel("Longitude", fontsize=9)
        self.ax.set_ylabel("Latitude", fontsize=9)
        self.ax.grid(True, alpha=0.25, linewidth=0.7)
        self.ax.tick_params(labelsize=8)
        if visiveis or self.app.lat is not None:
            self.ax.legend(loc="upper right", fontsize=8, framealpha=0.9)

        if enquadrar:
            self._enquadrar(visiveis)

        self._nomear_municipios()

        # 1 grau de longitude é menor que 1 de latitude fora do equador
        lat_meio = np.mean(self.ax.get_ylim())
        self.ax.set_aspect(1 / max(0.1, math.cos(math.radians(lat_meio))))

        self._dica = self.ax.annotate(
            "", xy=(0, 0), xytext=(12, 12), textcoords="offset points",
            fontsize=8, zorder=20, visible=False,
            bbox=dict(boxstyle="round,pad=0.4", facecolor="#ffffff",
                      edgecolor="#b8b8b4", alpha=0.95))

        self.fig.tight_layout()
        self.canvas.draw_idle()

    def _enquadrar(self, visiveis):
        """Enquadra na área escolhida, ou no estado, ou no Brasil."""
        if self.app.lat is not None and self.app.proximas:
            lats = [self.app.lat] + [p["lat"] for p in self.app.proximas]
            lons = [self.app.lon] + [p["lon"] for p in self.app.proximas]
        elif visiveis:
            lats = [e["lat"] for e in visiveis]
            lons = [e["lon"] for e in visiveis]
        else:
            return

        folga_y = max(0.25, (max(lats) - min(lats)) * 0.22)
        folga_x = max(0.25, (max(lons) - min(lons)) * 0.22)
        self.ax.set_xlim(min(lons) - folga_x, max(lons) + folga_x)
        self.ax.set_ylim(min(lats) - folga_y, max(lats) + folga_y)

    # ------------------------------------------------------------------
    def atualizar_tabela(self):
        for item in self.tabela.get_children():
            self.tabela.delete(item)

        pesos = pesos_idw(self.app.proximas)
        for p in self.app.proximas:
            self.tabela.insert("", "end", values=(
                p["codigo"], p["nome"], p["uf"],
                f'{p["distancia"]:.1f}',
                f'{pesos.get(p["codigo"], 0) * 100:.0f}%',
                f'{p["altitude"]:.0f}',
            ))

        aviso = ""
        if self.app.proximas:
            d0 = self.app.proximas[0]["distancia"]
            if d0 > 100:
                aviso = (f"A estação mais próxima está a {d0:.0f} km. "
                         "A série vai representar mal o microclima da sua área.")
            elif pesos and max(pesos.values()) > 0.8:
                dom = max(pesos, key=pesos.get)
                nome = next(p["nome"] for p in self.app.proximas if p["codigo"] == dom)
                aviso = (f"{nome} responde por {pesos[dom] * 100:.0f}% da série — "
                         "na prática a análise é dela. As outras entram como "
                         "conferência e cobrem as horas sem dado.")
        self.lbl_aviso.config(text=aviso)


# =====================================================================
# BLOCO 8 — ABA DE SÉRIES E DELTA T
# =====================================================================
#
# Baixa a série horária de cada estação escolhida, combina pelo inverso do
# quadrado da distância, calcula o Delta T hora a hora e agrupa as horas
# aptas em janelas contínuas.
#
# O download roda numa thread separada: sem isso a janela congela enquanto
# espera a resposta da internet, e o Windows marca como "não respondendo".

import queue
import threading
from datetime import datetime, timedelta, timezone

API_OPEN_METEO = "https://api.open-meteo.com/v1/forecast"
API_OPEN_METEO_ARQUIVO = "https://archive-api.open-meteo.com/v1/archive"


def bulbo_umido(T, UR):
    """Temperatura de bulbo úmido pela aproximação de Stull (2011).

    T em °C, UR em %. Desvio de até 0,5 °C frente à equação psicrométrica
    completa — o que não desloca a faixa de 2 a 8 do Delta T.
    """
    if T is None or UR is None:
        return None
    ur = min(99.0, max(5.0, float(UR)))
    t = float(T)
    return (t * math.atan(0.151977 * math.sqrt(ur + 8.313659))
            + math.atan(t + ur) - math.atan(ur - 1.676331)
            + 0.00391838 * ur ** 1.5 * math.atan(0.023101 * ur)
            - 4.686035)


def es_buck(T):
    """Pressão de vapor de saturação, em hPa, pela equação de Buck (1981).

    es(T) = 6,112 · exp[17,62·T / (243,12 + T)]
    """
    return 6.112 * math.exp(17.62 * float(T) / (243.12 + float(T)))


def pressao_na_altitude(altitude_m, p0=1013.25):
    """Pressão atmosférica padrão numa altitude, em hPa (ISA).

    P = P0 · (1 − 2,25577e−5 · h)^5,25588
    """
    h = max(0.0, float(altitude_m))
    return p0 * (1 - 2.25577e-5 * h) ** 5.25588


def bulbo_umido_psicrometrico(T, UR, pressao_hpa, tol=1e-4):
    """Bulbo úmido resolvendo a equação psicrométrica, com a pressão real.

    Resolve por bisseção  e = es(Tw) − γ·P·(T − Tw),  com γ = 6,53e−4 /°C.
    Diferente da aproximação de Stull, esta rota respeita a pressão do
    lugar — o que importa em altitude, onde Stull (calibrada ao nível do
    mar) passa a errar para mais.
    """
    if T is None or UR is None:
        return None
    T = float(T)
    ur = min(100.0, max(1.0, float(UR)))
    e = es_buck(T) * ur / 100.0
    gama = 6.53e-4 * float(pressao_hpa)

    def resto(tw):
        return es_buck(tw) - gama * (T - tw) - e

    lo, hi = T - 60.0, T
    if resto(lo) > 0:                  # fora do domínio: devolve o próprio T
        return T
    for _ in range(80):
        meio = (lo + hi) / 2
        if resto(meio) < 0:
            lo = meio
        else:
            hi = meio
        if hi - lo < tol:
            break
    return (lo + hi) / 2


def delta_t(T, UR, pressao_hpa=None):
    """Delta T = temperatura do ar menos temperatura de bulbo úmido.

    Sem pressão, usa Stull (2011) — rápida e suficiente perto do nível do
    mar. Com pressão, usa a equação psicrométrica completa, que é o que
    vale para área em altitude.
    """
    tw = (bulbo_umido(T, UR) if pressao_hpa is None
          else bulbo_umido_psicrometrico(T, UR, pressao_hpa))
    return None if tw is None else float(T) - tw


# ---------------------------------------------------------------------
# Vento na altura da barra
# ---------------------------------------------------------------------
#
# O modelo entrega vento a 10 m. A barra de pulverização trabalha entre
# 0,5 e 3 m, onde o vento é sensivelmente menor — e é nessa altura que as
# recomendações de 3 a 10 km/h foram escritas. Comparar o vento de 10 m
# com um critério de 2 m descarta horas que na prática serviam.

ALTURA_MODELO = 10.0     # m, altura do vento nos modelos meteorológicos
ALTURA_BARRA = 2.0       # m, altura típica da barra
RUGOSIDADE = 0.03        # m, z0 de grama baixa / cultura rasteira
GRADIENTE_ADIABATICO = 0.0098   # °C/m, gradiente adiabático seco


def fator_altura_vento(altura=ALTURA_BARRA, z0=RUGOSIDADE,
                       altura_modelo=ALTURA_MODELO):
    """Razão entre o vento na altura pedida e o vento do modelo.

    Perfil logarítmico de camada neutra:  u(z) ∝ ln(z/z0).
    Com z0 = 0,03 m, sair de 10 m para 2 m dá fator 0,72.
    """
    z = max(float(z0) * 1.5, float(altura))
    return math.log(z / z0) / math.log(float(altura_modelo) / z0)


def _num(v):
    if v is None or v == "":
        return None
    try:
        return float(str(v).replace(",", "."))
    except (TypeError, ValueError):
        return None


def _pega_json(url, timeout=90):
    req = urllib.request.Request(url, headers={"User-Agent": _UA,
                                               "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout, context=_CTX) as r:
        corpo = r.read()
        if r.status == 204 or not corpo.strip():
            raise RuntimeError("a fonte respondeu sem conteúdo")
        return json.loads(corpo.decode("utf-8"))


HORARIAS_BASE = ("temperature_2m", "relative_humidity_2m",
                 "wind_speed_10m", "precipitation")

# Variáveis que só interessam ao risco de inversão e à rajada. Nem toda
# fonte serve todas — a reanálise tem menos que a previsão — então elas
# são pedidas em separado, e a consulta sabe recuar sem elas.
HORARIAS_EXTRA = ("wind_gusts_10m", "wind_direction_10m", "temperature_80m",
                  "cloud_cover", "shortwave_radiation")
HORARIAS_EXTRA_PREVISAO = HORARIAS_EXTRA + ("boundary_layer_height",
                                            "precipitation_probability")


def _url(base, p):
    return base + "?" + "&".join(f"{k}={v}" for k, v in p.items())


def _em(lista, i):
    """Item i da lista, ou None — a resposta pode vir mais curta."""
    return lista[i] if lista and i < len(lista) else None


def _baixa_horaria(base, p, extras):
    """Pede as variáveis extras e, se a fonte não as servir, repete sem elas.

    Pedir à API uma variável que ela não tem derruba a consulta inteira.
    Em vez de manter duas listas de variáveis que vão divergir com o
    tempo, pedimos tudo e recuamos uma vez. Devolve (json, levou_extras).
    """
    completo = dict(p)
    completo["hourly"] = ",".join(HORARIAS_BASE + tuple(extras))
    try:
        return _pega_json(_url(base, completo)), True
    except Exception:
        if not extras:
            raise
    minimo = dict(p)
    minimo["hourly"] = ",".join(HORARIAS_BASE)
    return _pega_json(_url(base, minimo)), False


def _linha_horaria(h, i, fuso=None):
    """Converte uma hora da resposta do Open-Meteo no nosso dicionário."""
    v = _em(h.get("wind_speed_10m"), i)
    r = _em(h.get("wind_gusts_10m"), i)
    return {
        "temp": _num(_em(h.get("temperature_2m"), i)),
        "ur": _num(_em(h.get("relative_humidity_2m"), i)),
        "vento": None if v is None else _num(v) * 3.6,      # m/s -> km/h
        "rajada": None if r is None else _num(r) * 3.6,
        "direcao": _num(_em(h.get("wind_direction_10m"), i)),
        "chuva": _num(_em(h.get("precipitation"), i)),
        "prob_chuva": _num(_em(h.get("precipitation_probability"), i)),
        "temp_80m": _num(_em(h.get("temperature_80m"), i)),
        "nuvens": _num(_em(h.get("cloud_cover"), i)),
        "radiacao": _num(_em(h.get("shortwave_radiation"), i)),
        "camada_limite": _num(_em(h.get("boundary_layer_height"), i)),
    }


def baixar_open_meteo(lat, lon, ini, fim, fuso=-3):
    """Série horária de reanálise na coordenada. Sem token, sem cadastro."""
    hoje = datetime.now().date().isoformat()
    recente = fim >= hoje

    p = {
        "latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}",
        "wind_speed_unit": "ms", "timezone": "UTC",
    }
    if recente:
        dias = (datetime.now().date()
                - datetime.strptime(ini, "%Y-%m-%d").date()).days + 1
        p["past_days"] = str(max(1, min(92, dias)))
        p["forecast_days"] = "1"
        base = API_OPEN_METEO
    else:
        p["start_date"], p["end_date"] = ini, fim
        base = API_OPEN_METEO_ARQUIVO

    j, _ = _baixa_horaria(base, p, HORARIAS_EXTRA)
    if "hourly" not in j:
        raise RuntimeError(j.get("reason", "resposta sem dados horários"))

    h = j["hourly"]
    t0 = datetime.strptime(ini, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    t1 = (datetime.strptime(fim, "%Y-%m-%d").replace(tzinfo=timezone.utc)
          + timedelta(days=1))

    saida = {}
    for i, iso in enumerate(h["time"]):
        ts = datetime.fromisoformat(iso).replace(tzinfo=timezone.utc)
        local = ts + timedelta(hours=fuso)
        if not (t0 <= local < t1):
            continue
        saida[local] = _linha_horaria(h, i)
    return saida


def baixar_previsao(lat, lon, dias=7, fuso=-3):
    """Previsão horária na coordenada, de agora até `dias` à frente.

    Vem do mesmo Open-Meteo, mas do lado da previsão: ele serve os modelos
    oficiais já interpolados na coordenada. Note a diferença de natureza —
    a aba 2 mostra o que foi medido, esta mostra o que é esperado. Serve
    para programar a semana, não para registrar a operação.
    """
    p = {
        "latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}",
        "wind_speed_unit": "ms", "timezone": "UTC",
        "past_days": "0",
        # peço um dia a mais porque a resposta vem em UTC: ao converter para
        # o horário local, as últimas horas do último dia cairiam fora.
        "forecast_days": str(max(1, min(16, int(dias) + 1))),
    }
    j, _ = _baixa_horaria(API_OPEN_METEO, p, HORARIAS_EXTRA_PREVISAO)
    if "hourly" not in j:
        raise RuntimeError(j.get("reason", "resposta sem dados horários"))

    h = j["hourly"]
    agora = (datetime.now(timezone.utc) + timedelta(hours=fuso))
    corte = agora.replace(minute=0, second=0, microsecond=0)
    limite = corte + timedelta(days=int(dias))

    saida = {}
    for i, iso in enumerate(h["time"]):
        ts = datetime.fromisoformat(iso).replace(tzinfo=timezone.utc)
        local = ts + timedelta(hours=fuso)
        if not (corte <= local < limite):   # hora passada não ajuda a decidir
            continue
        linha = _linha_horaria(h, i)
        if linha["chuva"] is None:
            linha["chuva"] = 0.0
        saida[local] = linha
    if not saida:
        raise RuntimeError("a previsão veio vazia para esta coordenada")
    return saida


# ---------------------------------------------------------------------
# Previsão por conjunto (ensemble)
# ---------------------------------------------------------------------
#
# Uma rodada só de um modelo não carrega informação de confiança: ela diz
# o que vai acontecer com a mesma cara em dia calmo e em dia indeciso. O
# conjunto roda o mesmo modelo dezenas de vezes com perturbações
# pequenas nas condições iniciais; a dispersão entre as rodadas é a
# medida honesta de quanto dá para confiar naquela hora.
#
# A regra que não pode ser quebrada: o critério é avaliado EM CADA
# MEMBRO, e só depois se conta quantos passaram. Calcular o Delta T da
# média dos membros daria um número no meio da faixa mesmo num dia em que
# metade das rodadas está abaixo de 2 e a outra metade acima de 8 — ou
# seja, apontaria janela justamente onde não há nenhuma certeza.

API_ENSEMBLE = "https://ensemble-api.open-meteo.com/v1/ensemble"
MODELOS_ENSEMBLE = ("ecmwf_ifs025", "gfs025", "icon_global")

FAIXAS_P = (
    (0.80, "provavel", "janela provável"),
    (0.50, "possivel", "possível — confirmar no dia"),
    (0.20, "pouco", "pouco provável"),
    (0.00, "improvavel", "improvável"),
)
COR_FAIXA_P = {
    "provavel": "#2e7d32",
    "possivel": "#8dc26f",
    "pouco": "#e8b06a",
    "improvavel": "#c81010",
    "sem_dado": "#d8d8d8",
}
ORDEM_FAIXA_P = ("sem_dado", "improvavel", "pouco", "possivel", "provavel")


def faixa_probabilidade(p):
    """Em que faixa de confiança cai uma probabilidade."""
    if p is None:
        return "sem_dado"
    for limite, nome, _ in FAIXAS_P:
        if p >= limite:
            return nome
    return "improvavel"


def _membros_na_resposta(h, variaveis):
    """Descobre os sufixos de membro que existem em todas as variáveis.

    A API nomeia as rodadas como `temperature_2m_member01`, e o controle
    vem sem sufixo. Descobrir por varredura, em vez de assumir um número
    fixo de membros, deixa o código sobreviver a mudanças na API e a
    combinações diferentes de modelos.
    """
    import re
    conjuntos = []
    for var in variaveis:
        achados = set()
        for chave in h:
            if chave == var:
                achados.add("")
            else:
                casou = re.fullmatch(re.escape(var) + r"(_member\d+)", chave)
                if casou:
                    achados.add(casou.group(1))
        if achados:
            conjuntos.append(achados)
    if not conjuntos:
        return []
    comuns = set.intersection(*conjuntos)
    return sorted(comuns)


def _hourly_da_resposta(j):
    """Tira o bloco horário da resposta, aceitando objeto ou lista.

    Pedindo mais de um modelo na mesma consulta, a API responde com uma
    lista de objetos em vez de um objeto — e foi por aí que a primeira
    versão se perdeu.
    """
    if isinstance(j, list):
        for item in j:
            if isinstance(item, dict) and "hourly" in item:
                return item["hourly"]
        raise RuntimeError("resposta em lista, sem bloco horário")
    if not isinstance(j, dict):
        raise RuntimeError(f"resposta em formato inesperado ({type(j).__name__})")
    if "hourly" not in j:
        raise RuntimeError(j.get("reason") or "resposta sem bloco horário")
    return j["hourly"]


def baixar_ensemble(lat, lon, dias=7, fuso=-3, modelos=MODELOS_ENSEMBLE):
    """Todas as rodadas do conjunto, na coordenada da área.

    Um pedido por modelo, de propósito. Pedindo vários de uma vez a API
    muda o formato da resposta conforme a combinação, e um modelo fora do
    ar derruba a consulta inteira. Separado, o formato é previsível, o que
    respondeu é aproveitado, e a mensagem de erro diz qual falhou.

    Devolve (lista_de_series, modelos_que_responderam).
    """
    agora = datetime.now(timezone.utc) + timedelta(hours=fuso)
    corte = agora.replace(minute=0, second=0, microsecond=0)
    limite = corte + timedelta(days=int(dias))

    membros, usados, problemas, amostra = [], [], [], []

    for modelo in modelos:
        base = {
            "latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}",
            "wind_speed_unit": "ms", "timezone": "UTC",
            "models": modelo,
            "forecast_days": str(max(1, min(16, int(dias) + 1))),
        }
        h, erro = None, None
        # rajada e direção nem sempre vêm por membro; se não vierem,
        # repete sem elas
        for variaveis in (HORARIAS_BASE + ("wind_gusts_10m",
                                           "wind_direction_10m"),
                          HORARIAS_BASE + ("wind_gusts_10m",), HORARIAS_BASE):
            try:
                pedido = dict(base, hourly=",".join(variaveis))
                h = _hourly_da_resposta(_pega_json(_url(API_ENSEMBLE, pedido),
                                                   timeout=180))
                break
            except Exception as e:
                erro = e
        if h is None:
            problemas.append(f"{modelo}: {erro}")
            continue

        sufixos = _membros_na_resposta(h, HORARIAS_BASE)
        if not sufixos:
            if not amostra:
                amostra = sorted(k for k in h if k != "time")[:10]
            problemas.append(f"{modelo}: resposta sem membros")
            continue

        def valor(var, sufixo, i, _h=h):
            lista = _h.get(var + sufixo)
            if lista is None:            # variável servida sem membros
                lista = _h.get(var)
            return _em(lista, i)

        novos = 0
        for sufixo in sufixos:
            serie = {}
            for i, iso in enumerate(h["time"]):
                ts = datetime.fromisoformat(iso).replace(tzinfo=timezone.utc)
                local = ts + timedelta(hours=fuso)
                if not (corte <= local < limite):
                    continue
                v = valor("wind_speed_10m", sufixo, i)
                r = valor("wind_gusts_10m", sufixo, i)
                serie[local] = {
                    "temp": _num(valor("temperature_2m", sufixo, i)),
                    "ur": _num(valor("relative_humidity_2m", sufixo, i)),
                    "vento": None if v is None else _num(v) * 3.6,
                    "rajada": None if r is None else _num(r) * 3.6,
                    "direcao": _num(valor("wind_direction_10m", sufixo, i)),
                    "chuva": _num(valor("precipitation", sufixo, i)) or 0.0,
                    "n_estacoes": 1,
                }
            if serie:
                membros.append(serie)
                novos += 1
        if novos:
            usados.append(modelo)
        else:
            problemas.append(f"{modelo}: {len(sufixos)} membros, mas nenhuma "
                             "hora dentro do período pedido")

    if not membros:
        detalhe = "; ".join(problemas) or "nenhum modelo respondeu"
        if amostra:
            detalhe += " — campos recebidos: " + ", ".join(amostra)
        raise RuntimeError(detalhe)
    return membros, usados


def analisar_ensemble(membros, crit, altitude=None, determinista=None):
    """Roda o critério em cada membro e devolve a série de probabilidade.

    `determinista` é a série da rodada única, usada só para emprestar as
    variáveis que o conjunto não serve por membro — temperatura a 80 m,
    nuvens, radiação — que entram no risco de inversão. Elas são iguais
    para todos os membros, e isso fica dito no relatório.
    """
    emprestado = determinista or {}
    votos = {}
    sig = residuos_efetivos(crit)

    for serie in membros:
        for ts, l in serie.items():
            ref = emprestado.get(ts)
            if ref:
                for chave in ("temp_80m", "nuvens", "radiacao",
                              "camada_limite", "prob_chuva"):
                    l.setdefault(chave, ref.get(chave))
            l["orvalho"] = ponto_de_orvalho(l.get("temp"), l.get("ur"))
            l["delta_t"] = delta_t(l.get("temp"), l.get("ur"),
                                   crit.get("pressao_hpa"))
        qc_serie(serie)
        preparar_serie(serie, crit)

        for ts, l in serie.items():
            motivo = classificar(l, crit)
            d = votos.setdefault(ts, {"n": 0, "aptos": 0, "motivos": {},
                                      "dt": [], "vento": [], "chuva": [],
                                      "temp": [], "ur": [], "inversao": 0,
                                      "linhas_dir": [], "rajada": [],
                                      "p_soma": 0.0, "p_n": 0})
            # cada rodada entra com o erro que sobra da calibração vestido:
            # perto do limite ela vale "talvez", não "sim" ou "não"
            pv = p_vestida(l, crit, ts, sig)
            if pv is not None:
                d["p_soma"] += pv
                d["p_n"] += 1
            if l.get("direcao") is not None or l.get("vento") is not None:
                d["linhas_dir"].append({"vento": l.get("vento"),
                                        "direcao": l.get("direcao")})
            d["n"] += 1
            if (l.get("chuva") or 0.0) > (crit.get("chuva_max") or 0.2):
                d["molhados"] = d.get("molhados", 0) + 1
            if e_apto(motivo):
                d["aptos"] += 1
            else:
                d["motivos"][motivo] = d["motivos"].get(motivo, 0) + 1
            if l.get("inversao") == "alto":
                d["inversao"] += 1
            for chave in ("dt", "vento", "chuva", "temp", "ur", "rajada"):
                v = l.get("delta_t" if chave == "dt" else chave)
                if v is not None:
                    d[chave].append(v)

    def mediana(vs):
        if not vs:
            return None
        ordem = sorted(vs)
        meio = len(ordem) // 2
        return (ordem[meio] if len(ordem) % 2
                else (ordem[meio - 1] + ordem[meio]) / 2)

    def desvio(vs):
        if len(vs) < 2:
            return 0.0
        m = sum(vs) / len(vs)
        return math.sqrt(sum((v - m) ** 2 for v in vs) / (len(vs) - 1))

    saida = {}
    for ts, d in votos.items():
        dominante = (max(d["motivos"].items(), key=lambda kv: kv[1])[0]
                     if d["motivos"] else "apto")
        # direção das rodadas: média vetorial, e a constância entre elas diz
        # se o conjunto concorda de que lado o vento vai soprar
        direcao, concordancia, *_ = media_vetorial(d["linhas_dir"])
        saida[ts] = {
            "direcao": direcao,
            "constancia_dir": concordancia,
            "temp": mediana(d["temp"]),
            "ur": mediana(d["ur"]),
            "vento": mediana(d["vento"]),
            "chuva": mediana(d["chuva"]),
            "delta_t": mediana(d["dt"]),
            "orvalho": ponto_de_orvalho(mediana(d["temp"]), mediana(d["ur"])),
            "p_apto": (d["p_soma"] / d["p_n"] if d["p_n"]
                       else (d["aptos"] / d["n"] if d["n"] else None)),
            # a contagem crua das rodadas, sem o erro vestido, para comparar
            "p_rodadas": d["aptos"] / d["n"] if d["n"] else None,
            "rajada": mediana(d["rajada"]),
            "inversao": ("alto" if d["n"] and d["inversao"] / d["n"] >= 0.5
                         else "moderado" if d["n"] and d["inversao"] / d["n"] >= 0.2
                         else "baixo"),
            # probabilidade de chuva pelo próprio conjunto: fração das
            # rodadas com chuva acima do limite do critério
            "prob_chuva": (100.0 * d.get("molhados", 0) / d["n"]
                           if d["n"] else None),
            "p_inversao": d["inversao"] / d["n"] if d["n"] else None,
            "sd_dt": desvio(d["dt"]),
            "sd_vento": desvio(d["vento"]),
            "motivo_dominante": dominante,
            "n_membros": d["n"],
            "n_estacoes": 1,
        }
    return saida


def incerteza_total(linha, crit):
    """Soma em quadratura a dispersão do conjunto e a das estações.

    São duas fontes independentes: o conjunto mede a incerteza do tempo,
    as estações medem a incerteza de o ponto medido representar o talhão.
    Somar linearmente exageraria; somar em quadratura é o que se faz com
    erros independentes.
    """
    sd_dt = linha.get("sd_dt") or 0.0
    sd_v = linha.get("sd_vento") or 0.0
    rep_dt = crit.get("margem_dt") or 0.0
    rep_v = crit.get("margem_vento") or 0.0
    return (math.hypot(sd_dt, rep_dt), math.hypot(sd_v, rep_v))


def baixar_inmet(codigo, ini, fim, token=None, fuso=-3):
    """Série horária medida pela estação. Exige token desde 2026."""
    caminho = (f"/token/estacao/{ini}/{fim}/{codigo}/{token}" if token
               else f"/estacao/{ini}/{fim}/{codigo}")
    try:
        dados = _pega_json(API_INMET + caminho)
    except RuntimeError:
        raise RuntimeError("o INMET respondeu vazio — falta token, ou o "
                           "serviço está indisponível")
    if isinstance(dados, str) or not dados:
        raise RuntimeError("token inválido ou ausente")

    saida = {}
    for r in dados:
        data = str(r.get("DT_MEDICAO", ""))[:10]
        hora = str(r.get("HR_MEDICAO", "0000")).zfill(4)
        if not data:
            continue
        try:
            ts = datetime.strptime(f"{data} {hora[:2]}:{hora[2:4]}",
                                   "%Y-%m-%d %H:%M").replace(tzinfo=timezone.utc)
        except ValueError:
            continue
        v = _num(r.get("VEN_VEL"))
        saida[ts + timedelta(hours=fuso)] = {
            "temp": _num(r.get("TEM_INS")),
            "ur": _num(r.get("UMD_INS")),
            "vento": None if v is None else v * 3.6,
            "chuva": _num(r.get("CHUVA")),
        }
    if not saida:
        raise RuntimeError("nenhum registro no período")
    return saida


CAMPOS_BASE = ("temp", "ur", "vento")
CAMPOS_PREVISAO = ("temp", "ur", "vento", "chuva", "prob_chuva")

# Campos que atravessam a interpolação sem virar critério direto, mas que
# alimentam o risco de inversão e o de rajada.
CAMPOS_AMBIENTE = ("rajada", "temp_80m", "nuvens", "radiacao",
                   "camada_limite")

# Os dois jeitos de chegar ao valor no talhão.
METODO_IDW = "Interpolar estações (IDW + altitude)"
METODO_PONTO = "Direto no ponto da área"

# Métrica da distância nos mapas de interpolação.
METRICA_KM = "km (geodésica)"
METRICA_GRAU = "grau (como o QGIS em 4326)"

# Como a previsão é apresentada. O conjunto é o padrão porque uma rodada
# só não carrega informação de confiança nenhuma.
MODO_ENSEMBLE = "Conjunto (probabilidade)"
MODO_UNICO = "Rodada única (determinística)"
LIMIAR_P = 0.50


def ponto_de_orvalho(T, UR):
    """Ponto de orvalho pela fórmula de Magnus-Tetens.

    É a temperatura em que o ar saturaria sem ganhar nem perder vapor.
    Diferente da umidade relativa, ela descreve a quantidade de água no
    ar sem depender de quão quente aquele ar está.
    """
    if T is None or UR is None:
        return None
    a, b = 17.625, 243.04
    ur = min(100.0, max(1.0, float(UR)))
    g = math.log(ur / 100.0) + a * float(T) / (b + float(T))
    return b * g / (a - g)


def ur_do_orvalho(T, Td):
    """Caminho de volta: de temperatura e ponto de orvalho para UR."""
    if T is None or Td is None:
        return None
    a, b = 17.625, 243.04
    e = math.exp(a * Td / (b + Td))
    es = math.exp(a * T / (b + T))
    return min(100.0, max(1.0, 100.0 * e / es))


def interpolar_area(series, estacoes, alt_area, campos=CAMPOS_BASE):
    """Interpola as estações para o ponto da área, hora a hora.

    Não é uma média das leituras. Três cuidados mudam o resultado:

    1. TEMPERATURA cai com a altitude, cerca de 0,65 °C a cada 100 m.
       Interpolar o valor bruto de estações mais altas ou mais baixas que
       o talhão embute esse desnível na estimativa. Então cada estação é
       primeiro trazida ao nível do mar, a interpolação acontece nesse
       plano comum, e o valor volta para a altitude da área.

    2. UMIDADE RELATIVA não se interpola: ela depende da temperatura do
       lugar onde foi medida. O que se conserva numa massa de ar é o
       PONTO DE ORVALHO. Convertemos (T, UR) de cada estação em ponto de
       orvalho, interpolamos isso, e recalculamos a UR já na temperatura
       da área. Como o Delta T sai justamente de T e UR, esse cuidado
       aparece direto no número final.

    3. VENTO fica no escalar, sem decompor em componentes u e v.
       Decompor daria a direção média certa, mas subestimaria a
       velocidade quando as estações discordam de direção — e subestimar
       vento é justamente o erro perigoso numa decisão de pulverização.

    A chuva entra pelo maior valor entre as estações, não pela média: se
    uma prevê pancada e as outras nada, a média diluiria e a hora passaria
    no filtro.

    Guarda ainda a DISPERSÃO entre estações em cada hora. Quando elas
    discordam muito, a estimativa vale pouco — e isso precisa aparecer em
    vez de ficar escondido atrás de um número único.
    """
    por_codigo = {e["codigo"]: e for e in estacoes}
    inv = {c: 1.0 / max(por_codigo[c].get("distancia", 1.0), 0.5) ** 2
           for c in series if c in por_codigo}

    horas = set()
    for s in series.values():
        horas |= set(s.keys())

    saida = {}
    for ts in sorted(horas):
        pontos = []
        for cod, s in series.items():
            r = s.get(ts)
            est = por_codigo.get(cod)
            if not r or est is None:
                continue
            T, UR = r.get("temp"), r.get("ur")
            alt = est.get("altitude") or 0.0
            td = r.get("orvalho") if r.get("medido") else None
            if td is None:
                td = ponto_de_orvalho(T, UR)
            t80 = r.get("temp_80m")
            # direção: só pelas componentes, nunca pelo ângulo
            _vel, _dir = r.get("vento"), r.get("direcao")
            if _vel is not None and _dir is not None:
                _u, _v = componentes(_vel, _dir)
            elif _vel is not None and _vel <= 0.5:
                _u = _v = 0.0          # calmaria: vetor nulo
            else:
                _u = _v = None
            pontos.append({
                "peso": inv.get(cod, 0.0),
                # levados ao nível do mar, para poderem ser comparados
                "t_nm": None if T is None else T + GRADIENTE_TERMICO * alt,
                "td_nm": None if td is None else td + GRADIENTE_ORVALHO * alt,
                # o de 80 m recebe a mesma correção do de 2 m, de propósito:
                # o que interessa é a diferença entre os dois, e corrigir
                # igual preserva essa diferença
                "t80_nm": None if t80 is None else t80 + GRADIENTE_TERMICO * alt,
                "vento": r.get("vento"),
                "u": _u, "v": _v,
                "preenchida": bool(r.get("origem")),
                "rajada": r.get("rajada"),
                "nuvens": r.get("nuvens"),
                "radiacao": r.get("radiacao"),
                "camada_limite": r.get("camada_limite"),
                "chuva": r.get("chuva"),
                "prob_chuva": r.get("prob_chuva"),
                "dt": delta_t(T, UR),
            })

        if not pontos:
            saida[ts] = {"temp": None, "ur": None, "vento": None,
                         "delta_t": None, "n_estacoes": 0}
            continue

        def media(chave):
            """Média ponderada, renormalizada entre quem tem o dado."""
            num = den = 0.0
            for p in pontos:
                v = p.get(chave)
                if v is None:
                    continue
                num += v * p["peso"]
                den += p["peso"]
            return num / den if den else None

        t_nm, td_nm = media("t_nm"), media("td_nm")
        temp = None if t_nm is None else t_nm - GRADIENTE_TERMICO * alt_area
        orvalho = None if td_nm is None else td_nm - GRADIENTE_ORVALHO * alt_area
        if temp is not None and orvalho is not None:
            orvalho = min(orvalho, temp)      # orvalho nunca passa da temperatura
        ur = ur_do_orvalho(temp, orvalho)

        t80_nm = media("t80_nm")
        u_m, v_m, vel_m = media("u"), media("v"), media("vento")
        direcao = direcao_das_componentes(u_m, v_m) \
            if u_m is not None and math.hypot(u_m, v_m) > 0.3 else None
        linha = {
            "direcao": direcao,
            "constancia_dir": (math.hypot(u_m, v_m) / vel_m
                               if direcao is not None and vel_m else None),
            "n_preenchidas": sum(1 for p in pontos if p.get("preenchida")),
            "temp": temp,
            "ur": ur,
            "orvalho": orvalho,
            "vento": media("vento"),
            "rajada": media("rajada"),
            "temp_80m": (None if t80_nm is None
                         else t80_nm - GRADIENTE_TERMICO * alt_area),
            "nuvens": media("nuvens"),
            "radiacao": media("radiacao"),
            "camada_limite": media("camada_limite"),
            "n_estacoes": sum(1 for p in pontos if p["t_nm"] is not None),
            "delta_t": delta_t(temp, ur),
        }

        chs = [p["chuva"] for p in pontos if p.get("chuva") is not None]
        pbs = [p["prob_chuva"] for p in pontos if p.get("prob_chuva") is not None]
        if chs:
            linha["chuva"] = max(chs)
        if pbs:
            linha["prob_chuva"] = max(pbs)

        dts = [p["dt"] for p in pontos if p.get("dt") is not None]
        vts = [p["vento"] for p in pontos if p.get("vento") is not None]
        linha["disp_dt"] = (max(dts) - min(dts)) if len(dts) > 1 else 0.0
        linha["disp_vento"] = (max(vts) - min(vts)) if len(vts) > 1 else 0.0

        saida[ts] = linha
    return saida


def serie_do_ponto(bruta):
    """Adapta uma série baixada na própria coordenada da área.

    Aqui não há o que interpolar: o modelo já entrega o valor no ponto,
    levando em conta relevo e cobertura do terreno. Só falta calcular o
    Delta T e marcar a dispersão como zero — não há estações discordando.
    """
    saida = {}
    for ts, r in bruta.items():
        linha = dict(r)
        linha["n_estacoes"] = 1
        linha["orvalho"] = ponto_de_orvalho(r.get("temp"), r.get("ur"))
        linha["delta_t"] = delta_t(r.get("temp"), r.get("ur"))
        linha["disp_dt"] = 0.0
        linha["disp_vento"] = 0.0
        saida[ts] = linha
    return saida


def buscar_altitude(lat, lon, estacoes=()):
    """Altitude do ponto, em metros.

    Vem do modelo de terreno do Open-Meteo, que é gratuito e não pede
    cadastro. Se a consulta falhar, cai na média das altitudes das
    estações escolhidas — pior, mas melhor do que assumir nível do mar,
    que jogaria a temperatura vários graus para cima.
    """
    try:
        j = _pega_json(f"{API_ELEVACAO}?latitude={lat:.5f}&longitude={lon:.5f}",
                       timeout=30)
        v = (j.get("elevation") or [None])[0]
        if v is not None:
            return float(v), "modelo de terreno"
    except Exception:
        pass
    alts = [e.get("altitude") or 0.0 for e in estacoes]
    if alts:
        return sum(alts) / len(alts), "média das estações"
    return 0.0, "sem dado"


# ---------------------------------------------------------------------
# Inversão térmica, chuva posterior e controle de qualidade
# ---------------------------------------------------------------------

def risco_inversao(linha):
    """Risco de inversão térmica de superfície na hora, em três níveis.

    Sob inversão a temperatura cresce com a altura: a camada junto ao solo
    fica mais fria e densa que a de cima, o ar para de se misturar na
    vertical, e a gota fina não desce — fica suspensa e caminha
    quilômetros. É o modo de deriva mais grave, e não aparece nem no
    Delta T nem na velocidade do vento. Uma madrugada de vento calmo e céu
    limpo passa nos dois critérios e é exatamente a pior hora do dia.

    O indicador direto é o gradiente entre 2 e 80 m. Faltando ele, valem
    os indícios indiretos: vento fraco, sem radiação solar e céu limpo,
    que é a receita do resfriamento radiativo noturno.

    Devolve (nível, motivo). Modelo global representa mal inversão rasa,
    então isto é indicador de risco, não medição: a confirmação é no
    campo, com termômetros a 0,5 e 3 m ou teste de fumaça.
    """
    t2 = linha.get("temp")
    t80 = linha.get("temp_80m")
    vento = linha.get("vento_10m")
    if vento is None:
        vento = linha.get("vento")
    radiacao = linha.get("radiacao")
    nuvens = linha.get("nuvens")
    camada = linha.get("camada_limite")

    if t2 is not None and t80 is not None:
        gradiente = (t80 - t2) / 78.0
        if gradiente > 0:
            return "alto", "temperatura sobe com a altura"
    else:
        gradiente = None

    de_dia = radiacao is not None and radiacao > 50
    if de_dia:
        return "baixo", "sol mantendo a mistura vertical"

    pontos, razoes = 0, []
    if gradiente is not None and gradiente > -GRADIENTE_ADIABATICO:
        pontos += 2
        razoes.append("estratificação estável")
    if vento is not None and vento < 4.0:
        pontos += 2
        razoes.append("vento fraco demais para misturar")
    if radiacao is not None and radiacao <= 0:
        pontos += 1
        razoes.append("sem radiação solar")
    if nuvens is not None and nuvens < 30 and (radiacao is None or radiacao <= 0):
        pontos += 1
        razoes.append("céu limpo à noite")
    if camada is not None and camada < 200:
        pontos += 2
        razoes.append("camada limite rasa")

    if pontos >= 4:
        return "alto", ", ".join(razoes)
    if pontos >= 2:
        return "moderado", ", ".join(razoes)
    return "baixo", ""


def qc_serie(serie):
    """Barra valores fisicamente impossíveis antes de qualquer conta.

    Dado ruim que passa silenciosamente vira decisão ruim. Aqui ele vira
    buraco declarado, que o resto do programa já sabe tratar.
    """
    problemas = 0
    anterior = None
    for ts in sorted(serie):
        l = serie[ts]
        ur = l.get("ur")
        if ur is not None and not (0 <= ur <= 100):
            l["ur"] = min(100.0, max(0.0, ur))
            problemas += 1
        if l.get("orvalho") is not None and l.get("temp") is not None \
                and l["orvalho"] > l["temp"] + 0.1:
            l["orvalho"] = l["temp"]
            problemas += 1
        for chave in ("vento", "vento_10m", "rajada", "chuva"):
            if l.get(chave) is not None and l[chave] < 0:
                l[chave] = None
                problemas += 1
        # salto horário impossível: mais de 10 °C de temperatura numa hora
        if anterior is not None and l.get("temp") is not None \
                and anterior.get("temp") is not None:
            if abs(l["temp"] - anterior["temp"]) > 10:
                l["temp"] = None
                l["delta_t"] = None
                problemas += 1
        anterior = l
    return problemas


def preparar_serie(serie, crit):
    """Aplica a física que depende dos critérios, antes de classificar.

    Três coisas acontecem aqui, e todas mudam a decisão:

    1. o vento do modelo, que vem a 10 m, é levado à altura da barra;
    2. cada hora ganha o acumulado de chuva das horas seguintes, para o
       critério poder exigir um período livre de chuva depois da
       aplicação, e não só na hora dela;
    3. cada hora ganha o risco de inversão térmica.

    É idempotente: guarda o vento original em `vento_10m` e sempre
    recalcula a partir dele, então rodar duas vezes não converte duas.
    """
    fator = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA),
                               crit.get("z0", RUGOSIDADE))
    pressao = crit.get("pressao_hpa")
    horas = sorted(serie)
    adiante = int(crit.get("rainfast_h", 0) or 0)

    for i, ts in enumerate(horas):
        l = serie[ts]

        if "vento_10m" not in l:
            l["vento_10m"] = l.get("vento")
        if l.get("vento_10m") is not None:
            l["vento"] = l["vento_10m"] * fator
        if "rajada_10m" not in l:
            l["rajada_10m"] = l.get("rajada")
        if l.get("rajada_10m") is not None:
            l["rajada"] = l["rajada_10m"] * fator

        if pressao is not None and l.get("temp") is not None:
            l["delta_t"] = delta_t(l["temp"], l.get("ur"), pressao)

        if adiante > 0:
            soma, vistas = 0.0, 0
            for k in range(i + 1, min(i + 1 + adiante, len(horas))):
                v = serie[horas[k]].get("chuva")
                if v is not None:
                    soma += v
                    vistas += 1
            l["chuva_prox"] = soma if vistas else None
        else:
            l["chuva_prox"] = None

        nivel, razao = risco_inversao(l)
        l["inversao"] = nivel
        l["inversao_motivo"] = razao

    return serie


def classificar(linha, crit):
    """Diz por que a hora serve ou não serve.

    A ordem é a da gravidade, e ela importa. Chuva e inversão vêm antes
    de tudo porque são impedimentos absolutos: debaixo de chuva não se
    aplica, e sob inversão a gota não desce — por melhor que esteja o
    Delta T. Só depois entram vento e Delta T, que são questão de faixa.

    Uma hora que passa em tudo mas com folga menor que a incerteza da
    estimativa sai como "apto_limitrofe": serve, mas não dá para garantir.
    """
    if linha.get("delta_t") is None or linha.get("vento") is None:
        return "sem_dado"

    # Série de conjunto: o critério já foi avaliado membro a membro, e
    # refazer a conta na mediana contradiria o resultado. Aqui só se
    # traduz a probabilidade — e, quando ela não basta, o motivo que mais
    # apareceu entre as rodadas que reprovaram.
    p = linha.get("p_apto")
    if p is not None and crit.get("limiar_p") is not None:
        if p >= crit["limiar_p"]:
            return "apto" if p >= 0.80 else "apto_limitrofe"
        return linha.get("motivo_dominante") or "vento"

    lim = crit.get("chuva_max")
    if lim is not None and (linha.get("chuva") or 0.0) > lim:
        return "chuva"
    if crit.get("rainfast_h") and linha.get("chuva_prox") is not None \
            and linha["chuva_prox"] > crit.get("rainfast_mm", 0.5):
        return "chuva"

    if crit.get("bloquear_inversao", True) and linha.get("inversao") == "alto":
        return "inversao"

    if linha["vento"] > crit["vento_max"] or linha["vento"] < crit["vento_min"]:
        return "vento"
    rmax = crit.get("rajada_max")
    if rmax and linha.get("rajada") is not None and linha["rajada"] > rmax:
        return "vento"

    if linha["delta_t"] < crit["dt_min"]:
        return "dt_baixo"
    if linha["delta_t"] > crit["dt_max"]:
        return "dt_alto"

    # folga até o limite mais próximo, comparada com a incerteza conhecida
    margem_dt = crit.get("margem_dt") or 0.0
    margem_v = crit.get("margem_vento") or 0.0
    if margem_dt or margem_v:
        folga_dt = min(linha["delta_t"] - crit["dt_min"],
                       crit["dt_max"] - linha["delta_t"])
        folga_v = min(linha["vento"] - crit["vento_min"],
                      crit["vento_max"] - linha["vento"])
        if folga_dt < margem_dt or folga_v < margem_v:
            return "apto_limitrofe"
    if linha.get("inversao") == "moderado":
        return "apto_limitrofe"
    return "apto"


def e_apto(motivo):
    """As duas categorias em que dá para aplicar."""
    return motivo in ("apto", "apto_limitrofe")


def margens_da_serie(serie):
    """Incerteza de representatividade, medida na própria série.

    As estações discordam entre si; essa discordância é o quanto a
    estimativa na área pode estar errada, e não some com mais conta. Uso
    metade da discordância média como margem — a amplitude entre estações
    é uma medida grosseira de duas vezes o desvio, então a metade é a
    leitura conservadora sem ser paranoica.
    """
    dts = [l["disp_dt"] for l in serie.values() if l.get("disp_dt")]
    vts = [l["disp_vento"] for l in serie.values() if l.get("disp_vento")]
    return (sum(dts) / len(dts) / 2 if dts else 0.0,
            sum(vts) / len(vts) / 2 if vts else 0.0)


def cobertura(serie, esperadas=None):
    """Quantas horas têm dado, de quantas deveriam ter.

    Buraco em série meteorológica não pode passar em silêncio: 357 horas
    de 360 tanto pode ser o dia corrente ainda incompleto quanto estação
    fora do ar. Devolve (com_dado, esperadas, porcentagem).
    """
    com_dado = sum(1 for l in serie.values()
                   if l.get("temp") is not None and l.get("vento") is not None)
    if esperadas is None and serie:
        horas = sorted(serie)
        esperadas = int((horas[-1] - horas[0]).total_seconds() // 3600) + 1
    esperadas = esperadas or len(serie) or 1
    return com_dado, esperadas, 100.0 * com_dado / esperadas


# ---------------------------------------------------------------------
# Controles de segurança, compartilhados pelas abas 2 e 3
# ---------------------------------------------------------------------

OPCOES_INVERSAO = ("Bloquear risco alto", "Só avisar")
OPCOES_BULBO = ("Stull (2011)", "Psicrométrico (usa a pressão)")


def montar_controles_seguranca(painel, alvo, com_chuva=True, pref=None):
    """Linha de parâmetros de segurança, igual nas abas 2 e 3.

    Ficam visíveis de propósito. São eles que decidem se uma madrugada
    calma entra ou não como janela, e esconder isso num menu faria a
    ferramenta parecer mais certa do que é.
    """
    linha = ttk.Frame(painel)
    linha.pack(side="top", fill="x", padx=6, pady=2)

    pref = pref or {}
    ttk.Label(linha, text="Inversão térmica:").pack(side="left")
    alvo.var_inversao = tk.StringVar(value=pref.get("inversao",
                                                    OPCOES_INVERSAO[0]))
    ttk.Combobox(linha, textvariable=alvo.var_inversao, width=18,
                 state="readonly",
                 values=OPCOES_INVERSAO).pack(side="left", padx=(4, 12))

    # A rajada é o MÁXIMO da hora, e numa tarde normal ela passa de duas
    # vezes a média (2,4 vezes nas estações de setembro). O padrão é 20
    # km/h na altura de aplicação, o limite de operação usado em campo;
    # perto dele a previsão sai como probabilidade, não como sim ou não.
    # 0 desliga o critério.
    ttk.Label(linha, text="Rajada máx (pico da hora):").pack(side="left")
    alvo.var_rajada = tk.StringVar(value=pref.get("rajada", "20"))
    ttk.Entry(linha, textvariable=alvo.var_rajada, width=5).pack(side="left", padx=4)
    ttk.Label(linha, text="km/h").pack(side="left", padx=(0, 12))

    if com_chuva:
        ttk.Label(linha, text="Sem chuva por:").pack(side="left")
        alvo.var_rainfast = tk.StringVar(value=pref.get("rainfast", "2"))
        ttk.Entry(linha, textvariable=alvo.var_rainfast,
                  width=4).pack(side="left", padx=4)
        ttk.Label(linha, text="h após aplicar").pack(side="left", padx=(0, 12))
    else:
        alvo.var_rainfast = tk.StringVar(value="0")

    ttk.Label(linha, text="Vento a:").pack(side="left")
    alvo.var_altura = tk.StringVar(value=pref.get("altura", "2,0"))
    ttk.Entry(linha, textvariable=alvo.var_altura, width=5).pack(side="left", padx=4)
    ttk.Label(linha, text="m  (z0").pack(side="left")
    alvo.var_z0 = tk.StringVar(value=pref.get("z0", "0,03"))
    ttk.Entry(linha, textvariable=alvo.var_z0, width=5).pack(side="left", padx=4)
    ttk.Label(linha, text="m)").pack(side="left", padx=(0, 12))

    ttk.Label(linha, text="Bulbo úmido:").pack(side="left")
    alvo.var_bulbo = tk.StringVar(value=pref.get("bulbo", OPCOES_BULBO[0]))
    ttk.Combobox(linha, textvariable=alvo.var_bulbo, width=26, state="readonly",
                 values=OPCOES_BULBO).pack(side="left", padx=4)
    return linha


def ler_seguranca(alvo, crit, altitude=None):
    """Acrescenta ao critério os parâmetros de segurança. True se deu certo."""
    def num(var, padrao=None):
        texto = var.get().strip().replace(",", ".")
        return padrao if not texto else float(texto)

    try:
        crit["rajada_max"] = num(alvo.var_rajada) or None
        crit["rainfast_h"] = int(num(alvo.var_rainfast, 0) or 0)
        crit["rainfast_mm"] = 0.5
        crit["altura_vento"] = num(alvo.var_altura, ALTURA_BARRA)
        crit["z0"] = num(alvo.var_z0, RUGOSIDADE)
    except ValueError:
        messagebox.showerror("Parâmetro inválido",
                             "Rajada, horas sem chuva, altura e z0 precisam "
                             "ser números.")
        return False

    if not (0.05 <= crit["altura_vento"] <= ALTURA_MODELO):
        messagebox.showerror("Altura inválida",
                             "A altura da barra tem que ficar entre 0,05 e "
                             f"{ALTURA_MODELO:.0f} m.")
        return False
    if not (0.0001 < crit["z0"] < 1.0):
        messagebox.showerror("Rugosidade inválida",
                             "O z0 típico vai de 0,005 m (solo nu) a 0,3 m "
                             "(cultura alta).")
        return False

    crit["bloquear_inversao"] = alvo.var_inversao.get().startswith("Bloquear")
    # só a escolha fica registrada aqui; a pressão depende da altitude da
    # área, que só é conhecida depois do download
    crit["usar_psicrometrico"] = alvo.var_bulbo.get().startswith("Psicro")
    crit["pressao_hpa"] = (pressao_na_altitude(altitude)
                           if crit["usar_psicrometrico"] and altitude is not None
                           else None)
    return True


def fechar_criterios(serie, crit, altitude=None):
    """Últimos ajustes do critério, agora que a série existe.

    A pressão depende da altitude e as margens dependem da discordância
    entre estações — nenhuma das duas é conhecida na hora de ler os
    campos da tela.
    """
    if crit.get("usar_psicrometrico") and altitude is not None:
        crit["pressao_hpa"] = pressao_na_altitude(altitude)
    crit["margem_dt"], crit["margem_vento"] = margens_da_serie(serie)
    qc_serie(serie)
    preparar_serie(serie, crit)
    return serie


def texto_do_vento(crit):
    """Como o critério de vento está expresso — vai no resumo e no PDF."""
    f = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA),
                           crit.get("z0", RUGOSIDADE))
    return (f"Vento expresso a {_fmt(crit.get('altura_vento', ALTURA_BARRA))} m "
            f"(altura da barra): valor do modelo a {ALTURA_MODELO:.0f} m "
            f"convertido pelo perfil logarítmico, fator {_fmt(f, 2)}.")


NOME_MOTIVO = {
    "apto": "apta", "apto_limitrofe": "apta, mas no limite",
    "dt_baixo": "Delta T baixo", "dt_alto": "Delta T alto",
    "vento": "vento fora da faixa", "chuva": "chuva",
    "inversao": "risco de inversão térmica",
    "sem_dado": "sem dado",
}

# Uma cor por motivo, usada tanto no gráfico quanto no mapa de calor.
COR_MOTIVO = {
    "apto": "#2e7d32",           # verde
    "apto_limitrofe": "#8dc26f", # verde claro — serve, mas sem folga
    "dt_baixo": "#5b8def",       # azul  — úmido demais, a gota escorre
    "dt_alto": "#e08a1e",        # âmbar — seco demais, a gota evapora
    "vento": "#c81010",          # vermelho
    "chuva": "#6a3fa0",          # roxo
    "inversao": "#22304f",       # azul-noite — a hora que engana
    "sem_dado": "#d8d8d8",       # cinza
}
ORDEM_MOTIVO = ("sem_dado", "apto", "apto_limitrofe", "dt_baixo", "dt_alto",
                "vento", "chuva", "inversao")

# Rótulos das legendas dos gráficos. O verde é a informação que importa e
# precisa se anunciar sozinho: quem olha o relatório sem ler o texto tem que
# entender, só pela legenda, que verde é hora em que se pode aplicar.
ROTULO_LEGENDA = {
    "apto": "VERDE = hora apta para aplicar",
    "apto_limitrofe": "apta, porém no limite",
    "dt_baixo": "Delta T abaixo do mínimo",
    "dt_alto": "Delta T acima do máximo",
    "vento": "vento fora da faixa",
    "chuva": "chuva na hora ou logo depois",
    "inversao": "risco de inversão térmica",
    "sem_dado": "sem dado",
}


def _fmt(v, casas=1):
    return "—" if v is None else f"{v:.{casas}f}".replace(".", ",")


def encontrar_janelas(serie, crit):
    """Agrupa horas aptas consecutivas. Buraco na série quebra a janela."""
    horas = sorted(serie.keys())
    janelas, atual = [], None

    for ts in horas:
        linha = serie[ts]
        if not e_apto(classificar(linha, crit)):
            if atual:
                janelas.append(atual)
                atual = None
            continue
        if atual and (ts - atual["fim"]) <= timedelta(hours=1):
            atual["fim"] = ts
            atual["pontos"].append(linha)
        else:
            if atual:
                janelas.append(atual)
            atual = {"ini": ts, "fim": ts, "pontos": [linha]}
    if atual:
        janelas.append(atual)

    def med(pontos, chave):
        v = [p[chave] for p in pontos if p.get(chave) is not None]
        return sum(v) / len(v) if v else None

    saida = []
    for j in janelas:
        p = j["pontos"]
        dts = [x["delta_t"] for x in p if x.get("delta_t") is not None]
        vts = [x["vento"] for x in p if x.get("vento") is not None]
        chs = [x["chuva"] for x in p if x.get("chuva") is not None]
        pbs = [x["prob_chuva"] for x in p if x.get("prob_chuva") is not None]
        pas = [x["p_apto"] for x in p if x.get("p_apto") is not None]
        direcao, constancia, *_ = media_vetorial(p)
        saida.append({
            "direcao": direcao,
            "constancia": constancia,
            "ini": j["ini"],
            "fim": j["fim"] + timedelta(hours=1),   # a hora cheia vale até a próxima
            "horas": len(p),
            "dt_medio": med(p, "delta_t"),
            "dt_min": min(dts) if dts else None,
            "dt_max": max(dts) if dts else None,
            "vento_medio": med(p, "vento"),
            "vento_max": max(vts) if vts else None,
            "temp_media": med(p, "temp"),
            "ur_media": med(p, "ur"),
            "chuva": sum(chs) if chs else None,       # acumulado na janela
            "prob_chuva": max(pbs) if pbs else None,  # a pior hora da janela
            "p_apto": sum(pas) / len(pas) if pas else None,
            "p_min": min(pas) if pas else None,
        })
    return saida


# ---------------------------------------------------------------------
# Gráficos — servem tanto à aba de séries quanto à de previsão
# ---------------------------------------------------------------------

def _faixas_aptas(serie, crit):
    """Trechos contínuos de horas aptas, para sombrear no gráfico.

    Mesma regra de encontrar_janelas: buraco na série quebra o trecho.
    """
    faixas = []
    ini = fim = None
    for ts in sorted(serie):
        if not e_apto(classificar(serie[ts], crit)):
            continue
        if ini is not None and (ts - fim) <= timedelta(hours=1):
            fim = ts
        else:
            if ini is not None:
                faixas.append((ini, fim + timedelta(hours=1)))
            ini = fim = ts
    if ini is not None:
        faixas.append((ini, fim + timedelta(hours=1)))
    return faixas


def _sem_dados(fig, recado):
    fig.clear()
    ax = fig.add_subplot(111)
    ax.text(0.5, 0.5, recado, ha="center", va="center",
            fontsize=10, color="#888")
    ax.axis("off")


def _limpo(ts):
    """Tira o fuso do timestamp para o matplotlib não reinterpretar a hora.

    As horas já foram convertidas para o horário local lá no download; se o
    matplotlib visse o tzinfo, converteria de novo e o gráfico sairia
    deslocado em relação à tabela.
    """
    return ts.replace(tzinfo=None)


def desenhar_serie(fig, serie, crit, titulo=""):
    """Delta T, vento e temperatura/UR empilhados, com as janelas em verde.

    O sombreado verde atravessa todas as faixas de uma vez: onde ele
    aparece, as três condições estão satisfeitas ao mesmo tempo. É a
    leitura de relance que a tabela não dá.
    """
    fig.clear()
    if not serie:
        _sem_dados(fig, "Baixe a série para ver o gráfico.")
        return

    ts = sorted(serie)
    x = [_limpo(t) for t in ts]
    tem_chuva = any(serie[t].get("chuva") is not None for t in ts)

    eixos = fig.subplots(4 if tem_chuva else 3, 1, sharex=True)
    a_dt, a_v, a_t = eixos[0], eixos[1], eixos[2]

    faixas = _faixas_aptas(serie, crit)
    for ax in eixos:
        # fundo levemente acinzentado para o verde das janelas se destacar;
        # sobre branco a faixa fica lavada e some na impressão
        ax.set_facecolor("#f2f1ef")
        for f0, f1 in faixas:
            ax.axvspan(_limpo(f0), _limpo(f1), color=COR_MOTIVO["apto"],
                       alpha=0.30, lw=0, zorder=0)
        ax.grid(True, color="#ffffff", lw=0.8)
        ax.set_axisbelow(True)
        ax.tick_params(labelsize=8)

    # --- Delta T ---
    a_dt.axhspan(crit["dt_min"], crit["dt_max"], color=COR_MOTIVO["apto"],
                 alpha=0.10, lw=0, zorder=0)
    a_dt.axhline(crit["dt_min"], color="#aaa", lw=0.8, ls="--")
    a_dt.axhline(crit["dt_max"], color="#aaa", lw=0.8, ls="--")
    a_dt.plot(x, [serie[t].get("delta_t") for t in ts], color="#222", lw=1.3)
    a_dt.set_ylabel("Delta T (°C)", fontsize=8)

    # --- vento ---
    a_v.axhspan(crit["vento_min"], crit["vento_max"], color=COR_MOTIVO["apto"],
                alpha=0.10, lw=0, zorder=0)
    a_v.axhline(crit["vento_max"], color="#aaa", lw=0.8, ls="--")
    if crit["vento_min"] > 0:
        a_v.axhline(crit["vento_min"], color="#aaa", lw=0.8, ls="--")
    a_v.plot(x, [serie[t].get("vento") for t in ts],
             color=COR_MOTIVO["vento"], lw=1.3)
    a_v.set_ylabel("Vento (km/h)", fontsize=8)

    # setas da direção, apontando para onde o vento leva a gota
    com_dir = [t for t in ts if serie[t].get("direcao") is not None]
    if com_dir:
        passo = max(1, len(ts) // 72)
        sel = com_dir[::passo]
        topo = max([serie[t].get("vento") or 0.0 for t in ts]
                   + [crit["vento_max"]])
        a_v.quiver([mdates.date2num(_limpo(t)) for t in sel],
                   [topo * 1.13] * len(sel),
                   [math.sin(math.radians(serie[t]["direcao"] + 180))
                    for t in sel],
                   [math.cos(math.radians(serie[t]["direcao"] + 180))
                    for t in sel],
                   angles="uv", pivot="middle", scale=60, width=0.0016,
                   headwidth=4, headlength=4, headaxislength=3.6,
                   color="#4a4744", zorder=5)
        a_v.set_ylim(bottom=0, top=topo * 1.27)

    # --- temperatura e umidade, no mesmo eixo ---
    a_t.plot(x, [serie[t].get("temp") for t in ts],
             color=COR_MOTIVO["dt_alto"], lw=1.3)
    a_t.set_ylabel("Temp. (°C)", fontsize=8, color=COR_MOTIVO["dt_alto"])
    a_ur = a_t.twinx()
    a_ur.plot(x, [serie[t].get("ur") for t in ts],
              color=COR_MOTIVO["dt_baixo"], lw=1.3)
    a_ur.set_ylabel("UR (%)", fontsize=8, color=COR_MOTIVO["dt_baixo"])
    a_ur.set_ylim(0, 100)
    a_ur.tick_params(labelsize=8)

    # --- chuva, só quando a fonte traz previsão ---
    if tem_chuva:
        a_c = eixos[3]
        a_c.bar([_limpo(t - timedelta(hours=1)) for t in ts],
                [serie[t].get("chuva") or 0.0 for t in ts],
                width=1 / 24 * 0.9, align="edge",
                color=COR_MOTIVO["chuva"], zorder=2)
        if crit.get("chuva_max"):
            a_c.axhline(crit["chuva_max"], color="#aaa", lw=0.8, ls="--")
        a_c.set_ylabel("Chuva (mm)", fontsize=8)

    _formatar_eixo_tempo(eixos[-1], ts)

    # A legenda existe por um motivo só: deixar explícito o que a faixa verde
    # significa. Sem ela o leitor vê listras coloridas e tem que adivinhar.
    marcas = [Patch(facecolor=COR_MOTIVO["apto"], alpha=0.30,
                    label="FAIXA VERDE = janela de aplicação "
                          "(Delta T e vento dentro do critério ao mesmo tempo)"),
              Line2D([0], [0], color="#aaa", lw=0.9, ls="--",
                     label="limites do critério")]
    if any(serie[t].get("direcao") is not None for t in ts):
        marcas.append(Line2D([0], [0], color="#4a4744", lw=0, marker=r"$\rightarrow$",
                             markersize=9,
                             label="seta = para onde o vento leva a gota"))
    a_dt.legend(handles=marcas, loc="lower center", bbox_to_anchor=(0.5, 1.02),
                ncol=len(marcas), frameon=False, fontsize=8)

    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.075, ha="left",
                     y=0.985)
    fig.subplots_adjust(left=0.075, right=0.925, top=0.885, bottom=0.09,
                        hspace=0.22)


def _formatar_eixo_tempo(ax, ts):
    """Escolhe a marcação do eixo conforme o tamanho do período."""
    dias = max(1, (ts[-1] - ts[0]).days + 1)
    if dias <= 3:
        ax.xaxis.set_major_locator(mdates.HourLocator(interval=6))
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%d/%m %Hh"))
    elif dias <= 10:
        ax.xaxis.set_major_locator(mdates.DayLocator())
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%d/%m"))
    else:
        ax.xaxis.set_major_locator(mdates.DayLocator(interval=max(1, dias // 10)))
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%d/%m"))


def desenhar_mapa_calor(fig, serie, crit, titulo=""):
    """Grade hora × dia pintada pelo motivo, com o perfil do dia ao lado.

    Cada coluna é um dia e cada linha uma hora. Lido na horizontal, mostra
    se um horário se repete dia após dia — que é o que permite programar a
    operação em vez de decidir na véspera.
    """
    fig.clear()
    if not serie:
        _sem_dados(fig, "Baixe a série para ver o mapa de calor.")
        return

    ts = sorted(serie)
    dias = sorted({t.date() for t in ts})
    coluna = {d: i for i, d in enumerate(dias)}
    codigo = {m: i for i, m in enumerate(ORDEM_MOTIVO)}

    grade = np.zeros((24, len(dias)))
    aptas_por_hora = [[0, 0] for _ in range(24)]
    for t in ts:
        motivo = classificar(serie[t], crit)
        grade[t.hour, coluna[t.date()]] = codigo[motivo]
        if motivo != "sem_dado":
            aptas_por_hora[t.hour][1] += 1
            if e_apto(motivo):
                aptas_por_hora[t.hour][0] += 1

    cores = ListedColormap([COR_MOTIVO[k] for k in ORDEM_MOTIVO])
    norma = BoundaryNorm(list(range(len(ORDEM_MOTIVO) + 1)), cores.N)

    ax, ax_h = fig.subplots(1, 2, gridspec_kw={"width_ratios": [5, 1],
                                               "wspace": 0.04})

    # origin="lower" põe a meia-noite embaixo e o dia sobe pela grade, que é
    # como se lê um dia de trabalho: começa cedo, embaixo, e avança para cima.
    ax.imshow(grade, cmap=cores, norm=norma, aspect="auto",
              interpolation="nearest", origin="lower")
    ax.set_xticks(range(len(dias)))
    ax.set_xticklabels([d.strftime("%d/%m") for d in dias],
                       fontsize=7, rotation=90 if len(dias) > 10 else 0)
    ax.set_yticks(range(0, 24, 2))
    ax.set_yticklabels([f"{h:02d}h" for h in range(0, 24, 2)], fontsize=8)
    ax.set_ylabel("Hora do dia", fontsize=9)

    # linhas brancas separando as células
    ax.set_xticks(np.arange(-0.5, len(dias), 1), minor=True)
    ax.set_yticks(np.arange(-0.5, 24, 1), minor=True)
    ax.grid(which="minor", color="white", lw=0.6)
    ax.tick_params(which="minor", length=0)

    # perfil do dia: em que fração dos dias cada hora esteve apta
    taxa = [100 * a / b if b else 0 for a, b in aptas_por_hora]
    melhor = int(np.argmax(taxa)) if max(taxa) > 0 else None
    cores_barra = [COR_MOTIVO["apto"] if h != melhor else "#1b5e20"
                   for h in range(24)]
    ax_h.barh(range(24), taxa, height=0.86, color=cores_barra)
    ax_h.set_ylim(-0.5, 23.5)          # mesma orientação da grade ao lado
    ax_h.set_xlim(0, 100)
    ax_h.set_yticks([])
    ax_h.set_xticks([0, 50, 100])
    ax_h.set_xticklabels(["0", "50", "100%"], fontsize=7)
    ax_h.set_title("% dos dias em que\naquela hora esteve apta",
                   fontsize=7, color="#555", pad=8)
    ax_h.grid(True, axis="x", color="#e8e8e8", lw=0.7)
    ax_h.set_axisbelow(True)
    for lado in ("top", "right", "left"):
        ax_h.spines[lado].set_visible(False)
    if melhor is not None:
        ax_h.annotate(f"{melhor:02d}h · {taxa[melhor]:.0f}%",
                      (taxa[melhor], melhor), xytext=(4, 0),
                      textcoords="offset points", va="center", fontsize=7.5,
                      color="#1b5e20", fontweight="bold")

    presentes = [k for k in ORDEM_MOTIVO if codigo[k] in set(grade.ravel().astype(int))]
    # com muitos motivos a legenda numa linha só invade o painel da direita,
    # então ela quebra em duas
    ax.legend(handles=[Patch(facecolor=COR_MOTIVO[k], label=ROTULO_LEGENDA[k])
                       for k in presentes],
              loc="lower center", bbox_to_anchor=(0.5, 1.02),
              ncol=3 if len(presentes) > 4 else len(presentes),
              frameon=False, fontsize=7.5, columnspacing=1.4,
              handlelength=1.4, handletextpad=0.5)

    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.075, ha="left")
    fig.subplots_adjust(left=0.075, right=0.97, top=0.86,
                        bottom=0.16 if len(dias) > 10 else 0.10)


# ---------------------------------------------------------------------
# Mapas de interpolação — para inspecionar a própria interpolação
# ---------------------------------------------------------------------
#
# Aqui a interpolação deixa de ser um número e vira superfície. Serve para
# olhar o método, não para decidir aplicação: dá para ver o alcance de cada
# estação, o efeito da potência do IDW e os "olhos de boi" que aparecem em
# volta de cada ponto quando a potência sobe demais.

# Uma escala por mapa, porque são grandezas diferentes — escala única entre
# elas não significaria nada. Vento e chuva são magnitude: um tom só, do
# claro ao escuro. Delta T tem polaridade — o bom é a faixa do meio, e errar
# para baixo (gota escorre da folha) é problema diferente de errar para cima
# (gota evapora no caminho). Por isso ele ganha escala divergente, com cinza
# neutro no centro da faixa apta e as pontas nas mesmas cores do mapa de calor.
ESCALA_VENTO = LinearSegmentedColormap.from_list(
    "vento", ["#fdf4f3", "#f2b8b3", "#dc6b61", "#c81010", "#6b0a0a"])
ESCALA_CHUVA = LinearSegmentedColormap.from_list(
    "chuva", ["#f5f2fb", "#cbbce6", "#977bca", "#6a3fa0", "#3c2263"])
ESCALA_DELTA_T = LinearSegmentedColormap.from_list(
    "delta_t", ["#26509c", "#5b8def", "#bacbea", "#eeeeec",
                "#f2d6a6", "#e08a1e", "#8a4f08"])
# Metades da divergente, para quando o período inteiro cai de um lado só do
# centro da faixa. Aí não há polaridade para mostrar, e insistir na escala
# divergente jogaria todo o mapa num tom só — perdendo justamente o contraste
# que serve para enxergar a superfície interpolada.
ESCALA_DT_UMIDA = LinearSegmentedColormap.from_list(
    "dt_umida", ["#26509c", "#5b8def", "#bacbea", "#eeeeec"])
ESCALA_DT_SECA = LinearSegmentedColormap.from_list(
    "dt_seca", ["#eeeeec", "#f2d6a6", "#e08a1e", "#8a4f08"])

KM_POR_GRAU_LAT = 110.57


def resumo_por_estacao(por_estacao, estacoes):
    """O que cada estação viu no período inteiro, resumido num número.

    É o que os mapas interpolam: vento médio, Delta T médio e chuva
    acumulada. O Delta T é calculado hora a hora e só depois promediado —
    a média de T e a média de UR dariam outro valor, porque a relação
    entre eles não é linear.
    """
    por_codigo = {e["codigo"]: e for e in estacoes}
    saida = []
    for cod, serie in por_estacao.items():
        est = por_codigo.get(cod)
        if est is None:
            continue
        # estação medida: o mapa mostra o que ela MEDIU. As horas que o
        # modelo completou ficam de fora — senão um sensor quebrado
        # apareceria no mapa com o valor do modelo, como se fosse medição.
        if any(r.get("medido") for r in serie.values()):
            serie = {ts: r for ts, r in serie.items() if not r.get("origem")}
        ventos = [r["vento"] for r in serie.values() if r.get("vento") is not None]
        dts = [d for d in (delta_t(r.get("temp"), r.get("ur"))
                           for r in serie.values()) if d is not None]
        chuvas = [r["chuva"] for r in serie.values() if r.get("chuva") is not None]
        direcao, constancia, _, _, n_dir = media_vetorial(
            [r for r in serie.values() if not r.get("origem")])
        tem_dir = n_dir and any(r.get("direcao") is not None
                                for r in serie.values())
        u = v = None
        if tem_dir and direcao is not None:
            vel_vet = media_vetorial(list(serie.values()))[2] or 0.0
            u, v = componentes(vel_vet, direcao)
        elif tem_dir:
            u = v = 0.0
        saida.append({
            "direcao": direcao if tem_dir else None,
            "constancia": constancia if tem_dir else None,
            "u": u, "v": v,
            "codigo": cod,
            "nome": est.get("nome", cod),
            "uf": est.get("uf", ""),
            "lat": est["lat"],
            "lon": est["lon"],
            "altitude": est.get("altitude") or 0.0,
            "distancia": est.get("distancia"),
            "vento": sum(ventos) / len(ventos) if ventos else None,
            "delta_t": sum(dts) / len(dts) if dts else None,
            "chuva": sum(chuvas) if chuvas else None,
            "horas": len(serie),
        })
    return saida


def extensao_comum(pontos, area=None, margem=0.08):
    """Retângulo de todas as estações (e da área), com folga.

    Com dado medido, cada variável tem o seu conjunto de estações — a de
    Salvador não mede vento, a de Feira não mede umidade. Se cada mapa
    usasse o retângulo das suas, os três sairiam com enquadramentos
    diferentes e a área poderia cair fora de um deles.
    """
    lons = [p["lon"] for p in pontos]
    lats = [p["lat"] for p in pontos]
    if area:
        lats.append(area[0])
        lons.append(area[1])
    if not lons:
        return None
    dx = (max(lons) - min(lons)) or 0.2
    dy = (max(lats) - min(lats)) or 0.2
    return (min(lons) - margem * dx, max(lons) + margem * dx,
            min(lats) - margem * dy, max(lats) + margem * dy)


def grade_idw(pontos, chave, celulas=140, potencia=2.0, em_km=True, margem=0.08,
              extensao=None):
    """Interpola um valor dos pontos numa grade regular, por IDW.

    As células saem quadradas em grau, que é o formato que o QGIS gera e o
    que o ASCII grid exige — assim a mesma grade serve para desenhar aqui e
    para exportar e conferir lá.

    `em_km` escolhe a métrica da distância. Em quilômetros a interpolação
    fica isotrópica de verdade; em grau ela reproduz o que o QGIS faz numa
    camada em EPSG:4326, que é o que permite comparar resultado com
    resultado. Perto do Equador a diferença é pequena, mas existe.
    """
    validos = [p for p in pontos if p.get(chave) is not None]
    if len(validos) < 2:
        return None

    lons = [p["lon"] for p in validos]
    lats = [p["lat"] for p in validos]
    if extensao:
        x0, x1, y0, y1 = extensao
    else:
        dx = (max(lons) - min(lons)) or 0.2
        dy = (max(lats) - min(lats)) or 0.2
        x0, x1 = min(lons) - margem * dx, max(lons) + margem * dx
        y0, y1 = min(lats) - margem * dy, max(lats) + margem * dy

    cell = max(x1 - x0, y1 - y0) / max(10, int(celulas))
    nx = max(2, int(round((x1 - x0) / cell)) + 1)
    ny = max(2, int(round((y1 - y0) / cell)) + 1)
    gx = x0 + np.arange(nx) * cell
    gy = y0 + np.arange(ny) * cell
    X, Y = np.meshgrid(gx, gy)

    num = np.zeros_like(X, dtype=float)
    den = np.zeros_like(X, dtype=float)
    lat_media = sum(lats) / len(lats)
    fator_x = KM_POR_GRAU_LAT * math.cos(math.radians(lat_media)) if em_km else 1.0
    fator_y = KM_POR_GRAU_LAT if em_km else 1.0
    piso = 0.3 if em_km else 0.003      # evita divisão por zero em cima do ponto

    for p in validos:
        d = np.hypot((X - p["lon"]) * fator_x, (Y - p["lat"]) * fator_y)
        peso = 1.0 / np.maximum(d, piso) ** potencia
        num += peso * p[chave]
        den += peso

    return {"gx": gx, "gy": gy, "z": num / den, "cell": cell,
            "extensao": (x0, x0 + (nx - 1) * cell, y0, y0 + (ny - 1) * cell)}


_PASSOS = [1, 2, 2.5, 5, 10]


def _redondos(vmin, vmax, n):
    """Faixas em números redondos que cobrem a extensão pedida."""
    if vmax - vmin < 1e-9:
        vmin, vmax = vmin - 0.5, vmax + 0.5
    v = MaxNLocator(nbins=n, steps=_PASSOS).tick_values(vmin, vmax)
    return np.asarray(v, dtype=float)


def _niveis(vmin, vmax, centro=None, n=8):
    """Faixas do contorno, sempre em números redondos.

    Com um centro definido, ele entra como faixa e cada metade é quebrada
    por conta própria — senão a escala divergente marcaria o neutro num
    lugar que não é o neutro.
    """
    if centro is None:
        return _redondos(vmin, vmax, n)
    metade = max(2, n // 2)
    baixo = _redondos(vmin, centro, metade)
    alto = _redondos(centro, vmax, metade)
    juntos = np.concatenate([baixo[baixo < centro], [centro],
                             alto[alto > centro]])
    return np.unique(juntos)


def _formata_barra(barra, casas=1):
    """Vírgula decimal na barra de cor, como no resto da janela."""
    barra.ax.yaxis.set_major_formatter(
        FuncFormatter(lambda v, _: f"{v:.{casas}f}".replace(".", ",")))


def escala_do_delta_t(vmin, vmax, centro):
    """Escolhe a escala de cor do Delta T conforme os dados.

    Divergente só faz sentido quando o período de fato atravessa o centro
    da faixa apta. Quando tudo ficou de um lado — todo úmido ou todo seco —
    a escala divergente comprimiria o mapa inteiro num tom só. Nesse caso
    usamos só a metade que interessa, aproveitando a amplitude toda para
    mostrar a superfície, e mantendo o significado da cor: azul é o lado
    úmido, âmbar é o lado seco.
    """
    if centro is None:
        return ESCALA_DELTA_T, None
    if vmin < centro < vmax:
        return ESCALA_DELTA_T, centro
    if vmax <= centro:
        return ESCALA_DT_UMIDA, None
    return ESCALA_DT_SECA, None


def _um_mapa(ax, grade, pontos, chave, titulo, unidade, escala,
             centro=None, area=None, casas=1, extensao=None):
    """Desenha um painel: superfície interpolada, estações e área."""
    if grade is None:
        ax.text(0.5, 0.5, f"{titulo}\n(sem dado suficiente)", ha="center",
                va="center", fontsize=9, color="#888")
        ax.axis("off")
        return None, casas

    z = grade["z"]
    valores = [p[chave] for p in pontos if p.get(chave) is not None]
    vmin = min(float(z.min()), min(valores))
    vmax = max(float(z.max()), max(valores))
    if centro is not None:
        escala, centro = escala_do_delta_t(vmin, vmax, centro)
    niveis = _niveis(vmin, vmax, centro)
    norma = (TwoSlopeNorm(vmin=niveis[0], vcenter=centro, vmax=niveis[-1])
             if centro is not None else None)

    # Quando o período todo varia pouco, uma casa decimal repete o mesmo
    # rótulo em faixas diferentes. A precisão acompanha a amplitude.
    amplitude = niveis[-1] - niveis[0]
    if amplitude < 0.1:
        casas += 2
    elif amplitude < 1:
        casas += 1

    sup = ax.contourf(grade["gx"], grade["gy"], z, levels=niveis,
                      cmap=escala, norm=norma, extend="neither")
    ax.contour(grade["gx"], grade["gy"], z, levels=niveis,
               colors="white", linewidths=0.5, alpha=0.7)

    cor = ({"norm": norma} if norma is not None
           else {"vmin": niveis[0], "vmax": niveis[-1]})
    for p in pontos:
        v = p.get(chave)
        if v is None:
            continue
        ax.scatter([p["lon"]], [p["lat"]], s=70, c=[v], cmap=escala,
                   edgecolors="#33302e", linewidths=1.1, zorder=5, **cor)
        ax.annotate(f"{v:.{casas}f}".replace(".", ","),
                    (p["lon"], p["lat"]), textcoords="offset points",
                    xytext=(0, 9), ha="center", fontsize=7.5, zorder=6,
                    color="#2b2b2b",
                    bbox=dict(boxstyle="round,pad=0.18", fc="white",
                              ec="none", alpha=0.75))

    if area:
        ax.scatter([area[1]], [area[0]], marker="X", s=130, c=COR_AREA,
                   edgecolors="white", linewidths=1.6, zorder=7)

    for p in pontos:
        if p.get(chave) is None:
            # estação sem o sensor: aparece, vazia, para não parecer esquecida
            ax.scatter([p["lon"]], [p["lat"]], s=40, facecolors="white",
                       edgecolors="#9a9a9e", linewidths=1.0, zorder=5)
            ax.annotate("sem sensor", (p["lon"], p["lat"]),
                        textcoords="offset points", xytext=(0, 8),
                        ha="center", fontsize=6.5, color="#888", zorder=6)
    if extensao:
        ax.set_xlim(extensao[0], extensao[1])
        ax.set_ylim(extensao[2], extensao[3])
    ax.set_title(f"{titulo}\n({unidade})", fontsize=9, color="#444")
    ax.tick_params(labelsize=7)
    ax.set_aspect("equal", adjustable="box")
    return sup, casas


def desenhar_mapas_interpolacao(fig, pontos, area=None, crit=None,
                                potencia=2.0, celulas=140, em_km=True,
                                periodo="", y_rodape=0.035):
    """Os três mapas lado a lado: vento, Delta T e chuva."""
    fig.clear()
    if len(pontos) < 2:
        _sem_dados(fig,
                   "Os mapas interpolam as estações, então precisam de pelo "
                   "menos duas.\n\nSe o método estiver em “Direto no ponto da "
                   "área”, existe um ponto só:\ntroque para “Interpolar "
                   "estações” e baixe de novo.")
        return

    eixos = fig.subplots(1, 3)
    centro_dt = None
    if crit:
        centro_dt = (crit["dt_min"] + crit["dt_max"]) / 2.0

    unidade_dt = "°C"
    if crit:
        unidade_dt += (f" · faixa apta {_fmt(crit['dt_min'], 0)}"
                       f"–{_fmt(crit['dt_max'], 0)}")

    receitas = [
        ("vento", "Vento médio", "km/h", ESCALA_VENTO, None, 1),
        ("delta_t", "Delta T médio", unidade_dt, ESCALA_DELTA_T, centro_dt, 1),
        ("chuva", "Chuva acumulada", "mm no período", ESCALA_CHUVA, None, 1),
    ]
    ext = extensao_comum(pontos, area)
    for ax, (chave, titulo, unidade, escala, centro, casas) in zip(eixos, receitas):
        grade = grade_idw(pontos, chave, celulas, potencia, em_km, extensao=ext)
        sup, casas_usadas = _um_mapa(ax, grade, pontos, chave, titulo, unidade,
                                     escala, centro, area, casas, ext)
        if sup is not None:
            barra = fig.colorbar(sup, ax=ax, fraction=0.046, pad=0.03)
            barra.ax.tick_params(labelsize=7, length=2)
            barra.outline.set_visible(False)
            _formata_barra(barra, casas_usadas)

    metrica = "distância em km" if em_km else "distância em grau (como o QGIS em 4326)"
    rodape = (f"IDW · potência {potencia:g} · {len(pontos)} estações · "
              f"{metrica}")
    if periodo:
        rodape = f"{periodo} · {rodape}"
    # y_rodape sobe quando a figura vira página de relatório, para a linha
    # dos parâmetros não cair em cima do rodapé da página
    fig.suptitle(rodape, fontsize=8.5, color="#666", y=y_rodape)
    fig.subplots_adjust(left=0.05, right=0.97, top=0.88, bottom=0.14, wspace=0.28)


# ---------------------------------------------------------------------
# Exportação para o QGIS — para validar a ferramenta fora dela
# ---------------------------------------------------------------------

PRJ_WGS84 = ('GEOGCS["GCS_WGS_1984",DATUM["D_WGS_1984",SPHEROID["WGS_1984",'
             '6378137.0,298.257223563]],PRIMEM["Greenwich",0.0],'
             'UNIT["Degree",0.0174532925199433]]')


def _grava_asc(caminho, grade):
    """Grava a grade em ESRI ASCII (.asc), que o QGIS abre direto.

    As linhas vão de cima para baixo, que é a ordem do formato — ao
    contrário do array, onde a primeira linha é a de menor latitude.
    """
    z = grade["z"]
    ny, nx = z.shape
    with open(caminho, "w", encoding="ascii") as f:
        f.write(f"ncols {nx}\n")
        f.write(f"nrows {ny}\n")
        f.write(f"xllcorner {grade['gx'][0] - grade['cell'] / 2:.10f}\n")
        f.write(f"yllcorner {grade['gy'][0] - grade['cell'] / 2:.10f}\n")
        f.write(f"cellsize {grade['cell']:.10f}\n")
        f.write("NODATA_value -9999\n")
        for i in range(ny - 1, -1, -1):
            f.write(" ".join(f"{v:.4f}" for v in z[i]) + "\n")
    with open(caminho[:-4] + ".prj", "w", encoding="ascii") as f:
        f.write(PRJ_WGS84)


def exportar_para_qgis(pasta, pontos, area=None, potencia=2.0, celulas=140,
                       em_km=True, periodo=""):
    """Grava os pontos das estações e as grades, para refazer tudo no QGIS.

    O GeoJSON é a camada de entrada; os .asc são o resultado desta
    ferramenta. Rodando o IDW do QGIS sobre o mesmo GeoJSON e comparando
    com o .asc correspondente, dá para checar a implementação em vez de
    confiar nela.
    """
    os.makedirs(pasta, exist_ok=True)
    gerados = []

    feicoes = []
    for p in pontos:
        feicoes.append({
            "type": "Feature",
            "geometry": {"type": "Point", "coordinates": [p["lon"], p["lat"]]},
            "properties": {
                "codigo": p["codigo"], "nome": p["nome"], "uf": p["uf"],
                "altitude_m": round(p["altitude"], 1),
                "distancia_km": (None if p.get("distancia") is None
                                 else round(p["distancia"], 2)),
                "horas": p["horas"],
                "vento_kmh": None if p["vento"] is None else round(p["vento"], 3),
                "delta_t_c": None if p["delta_t"] is None else round(p["delta_t"], 3),
                "chuva_mm": None if p["chuva"] is None else round(p["chuva"], 2),
                "u_kmh": None if p.get("u") is None else round(p["u"], 3),
                "v_kmh": None if p.get("v") is None else round(p["v"], 3),
                "dir_graus": (None if p.get("direcao") is None
                              else round(p["direcao"], 1)),
                "vento_de": (None if p.get("direcao") is None
                             else rumo(p["direcao"])),
                "constancia": (None if p.get("constancia") is None
                               else round(p["constancia"], 3)),
            },
        })
    if area:
        feicoes.append({
            "type": "Feature",
            "geometry": {"type": "Point", "coordinates": [area[1], area[0]]},
            "properties": {"codigo": "AREA", "nome": "área de interesse",
                           "uf": "", "altitude_m": None, "distancia_km": 0.0,
                           "horas": None, "vento_kmh": None,
                           "delta_t_c": None, "chuva_mm": None,
                           "u_kmh": None, "v_kmh": None, "dir_graus": None,
                           "vento_de": None, "constancia": None},
        })

    caminho = os.path.join(pasta, "estacoes_medias.geojson")
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump({"type": "FeatureCollection",
                   "crs": {"type": "name",
                           "properties": {"name": "urn:ogc:def:crs:OGC:1.3:CRS84"}},
                   "features": feicoes}, f, ensure_ascii=False, indent=1)
    gerados.append(os.path.basename(caminho))

    ext = extensao_comum(pontos, area)
    for chave, nome in (("vento", "idw_vento"), ("delta_t", "idw_delta_t"),
                        ("chuva", "idw_chuva"), ("u", "idw_vento_u"),
                        ("v", "idw_vento_v")):
        grade = grade_idw(pontos, chave, celulas, potencia, em_km, extensao=ext)
        if grade is None:
            continue
        alvo = os.path.join(pasta, nome + ".asc")
        _grava_asc(alvo, grade)
        gerados.append(os.path.basename(alvo))

    metrica = ("quilômetros (geodésica)" if em_km
               else "graus decimais (igual ao QGIS em EPSG:4326)")
    modelo = (grade_idw(pontos, "vento", celulas, potencia, em_km, extensao=ext)
              or grade_idw(pontos, "delta_t", celulas, potencia, em_km,
                           extensao=ext))
    with open(os.path.join(pasta, "leia-me.txt"), "w", encoding="utf-8") as f:
        f.write(
            "Validação da interpolação no QGIS\n"
            "=================================\n\n"
            f"Período: {periodo or 'ver a aba 2'}\n"
            f"Estações: {len(pontos)}\n\n"
            "Arquivos\n"
            "--------\n"
            "estacoes_medias.geojson  camada de pontos (EPSG:4326) com, por\n"
            "                         estação: vento_kmh (média do período),\n"
            "                         delta_t_c (média das horas) e chuva_mm\n"
            "                         (acumulado). É a entrada da interpolação.\n"
            "                         u_kmh, v_kmh: componentes do vento\n"
            "                         médio (u para leste, v para norte);\n"
            "                         dir_graus / vento_de: de onde ele vem.\n"
            "idw_vento.asc            \\\n"
            "idw_delta_t.asc           > saída desta ferramenta, para comparar\n"
            "idw_chuva.asc            /\n"
            "idw_vento_u.asc          \\  componentes interpoladas do vento —\n"
            "idw_vento_v.asc          /   a direção sai delas, não do ângulo\n\n"
            "Parâmetros usados aqui\n"
            "----------------------\n"
            "Método .................. IDW (ponderação pelo inverso da distância)\n"
            f"Coeficiente P ........... {potencia:g}\n"
            f"Distância medida em ..... {metrica}\n")
        if modelo:
            x0, x1, y0, y1 = modelo["extensao"]
            f.write(
                f"Tamanho do pixel ........ {modelo['cell']:.6f} grau\n"
                f"Colunas x linhas ........ {len(modelo['gx'])} x {len(modelo['gy'])}\n"
                f"Extensão ................ {x0:.6f},{x1:.6f},{y0:.6f},{y1:.6f}\n"
                "                          (retângulo das estações e da área + 8%\n"
                "                          de folga — o mesmo para as cinco grades)\n")
        f.write(
            "\nComo refazer no QGIS\n"
            "--------------------\n"
            "1. Arraste estacoes_medias.geojson para o QGIS.\n"
            "2. Processamento > Caixa de ferramentas > Interpolação > Interpolação IDW.\n"
            "3. Camada vetorial: estacoes_medias · Atributo: vento_kmh\n"
            "   (depois repita com delta_t_c e com chuva_mm).\n"
            "4. Clique no + para adicionar o atributo à lista.\n"
            "5. Distância para coeficiente P: o valor acima.\n"
            "6. Extensão: cole a extensão acima.\n"
            "7. Tamanho do pixel X e Y: o valor acima.\n"
            "8. Execute e compare com o .asc correspondente — o raster\n"
            "   calculadora do QGIS faz a diferença entre os dois.\n\n"
            "Observação sobre a métrica\n"
            "--------------------------\n"
            "O QGIS mede distância nas unidades da camada. Em EPSG:4326 isso é\n"
            "grau, e um grau de longitude é mais curto que um de latitude fora\n"
            "do Equador. Para bater exatamente com o modo em quilômetros, primeiro\n"
            "reprojete os pontos para UTM/SIRGAS 2000 e rode o IDW já em metros.\n"
            "Rodando direto em 4326, use o modo 'graus' aqui na ferramenta.\n"
            "A ponta solta: o ponto marcado como AREA não tem valor e deve ser\n"
            "removido da camada antes de interpolar, ou o QGIS o trata como zero.\n\n"
            "Direção do vento\n"
            "----------------\n"
            "Direção é ângulo: a média de 350° e 10° é 0°, não 180°. Por isso\n"
            "NÃO interpole dir_graus. Interpole u_kmh e v_kmh (mesmos parâmetros\n"
            "acima) e recomponha na Calculadora Raster:\n"
            "  direção (de onde vem) = (atan2(-\"u@1\", -\"v@1\") * 180 / pi() + 360) % 360\n"
            "  para onde vai a deriva = a mesma conta + 180 (mod 360)\n"
            "  intensidade vetorial   = sqrt(\"u@1\"^2 + \"v@1\"^2)\n"
            "Para desenhar setas: Propriedades da camada de pontos > Simbologia >\n"
            "marcador de seta com rotação definida por dados = dir_graus + 180.\n")
    gerados.append("leia-me.txt")
    return gerados


def desenhar_mapa_calor_prob(fig, serie, crit, titulo="", fuso=-3):
    """Mapa de calor da previsão por conjunto: probabilidade, não certeza.

    A mesma grade hora x dia do histórico, mas pintada pela fração de
    rodadas do conjunto que aprovaram aquela hora. Verde escuro é acordo
    entre as rodadas; laranja é discordância; vermelho é acordo de que
    não dá. Vale mais do que um verde chapado que esconde se a previsão
    tinha 95% ou 51% de convicção.

    A partir do sexto dia a coluna sai esmaecida: para vento de superfície
    em escala local a habilidade cai rápido depois de uns cinco dias, e
    mostrar o dia 7 com a mesma cara do dia 1 seria mentir pela forma.
    """
    fig.clear()
    if not serie:
        _sem_dados(fig, "Busque a previsão para ver o mapa de confiança.")
        return

    ts = sorted(serie)
    dias = sorted({t.date() for t in ts})
    coluna = {d: i for i, d in enumerate(dias)}
    codigo = {f: i for i, f in enumerate(ORDEM_FAIXA_P)}

    grade = np.zeros((24, len(dias)))
    por_hora = [[] for _ in range(24)]
    for t in ts:
        faixa = faixa_probabilidade(serie[t].get("p_apto"))
        grade[t.hour, coluna[t.date()]] = codigo[faixa]
        p = serie[t].get("p_apto")
        if p is not None:
            por_hora[t.hour].append(p)

    cores = ListedColormap([COR_FAIXA_P[k] for k in ORDEM_FAIXA_P])
    norma = BoundaryNorm(list(range(len(ORDEM_FAIXA_P) + 1)), cores.N)

    ax, ax_h = fig.subplots(1, 2, gridspec_kw={"width_ratios": [5, 1],
                                               "wspace": 0.04})
    ax.imshow(grade, cmap=cores, norm=norma, aspect="auto",
              interpolation="nearest", origin="lower")

    # esmaece os dias em que a previsão já não tem habilidade útil
    hoje = (datetime.now(timezone.utc) + timedelta(hours=fuso)).date()
    for d, i in coluna.items():
        if (d - hoje).days >= 5:
            ax.axvspan(i - 0.5, i + 0.5, color="white", alpha=0.42, zorder=3)

    ax.set_xticks(range(len(dias)))
    ax.set_xticklabels([d.strftime("%d/%m") for d in dias],
                       fontsize=7, rotation=90 if len(dias) > 10 else 0)
    ax.set_yticks(range(0, 24, 2))
    ax.set_yticklabels([f"{h:02d}h" for h in range(0, 24, 2)], fontsize=8)
    ax.set_ylabel("Hora do dia", fontsize=9)
    ax.set_xticks(np.arange(-0.5, len(dias), 1), minor=True)
    ax.set_yticks(np.arange(-0.5, 24, 1), minor=True)
    ax.grid(which="minor", color="white", lw=0.6)
    ax.tick_params(which="minor", length=0)

    medias = [100 * sum(v) / len(v) if v else 0 for v in por_hora]
    melhor = int(np.argmax(medias)) if max(medias) > 0 else None
    ax_h.barh(range(24), medias, height=0.86,
              color=[COR_FAIXA_P["provavel"] if h == melhor else "#7fb069"
                     for h in range(24)])
    ax_h.set_ylim(-0.5, 23.5)
    ax_h.set_xlim(0, 100)
    ax_h.set_yticks([])
    ax_h.set_xticks([0, 50, 100])
    ax_h.set_xticklabels(["0", "50", "100%"], fontsize=7)
    ax_h.set_title("probabilidade média\nde a hora servir", fontsize=7,
                   color="#555", pad=8)
    ax_h.grid(True, axis="x", color="#e8e8e8", lw=0.7)
    ax_h.set_axisbelow(True)
    for lado in ("top", "right", "left"):
        ax_h.spines[lado].set_visible(False)
    if melhor is not None:
        ax_h.annotate(f"{melhor:02d}h · {medias[melhor]:.0f}%",
                      (medias[melhor], melhor), xytext=(4, 0),
                      textcoords="offset points", va="center", fontsize=7.5,
                      color="#1b5e20", fontweight="bold")

    rotulos = {"provavel": "provável (≥ 80% das rodadas)",
               "possivel": "possível (50 a 80%) — confirmar no dia",
               "pouco": "pouco provável (20 a 50%)",
               "improvavel": "improvável (< 20%)",
               "sem_dado": "sem dado"}
    presentes = [k for k in reversed(ORDEM_FAIXA_P)
                 if codigo[k] in set(grade.ravel().astype(int))]
    ax.legend(handles=[Patch(facecolor=COR_FAIXA_P[k], label=rotulos[k])
                       for k in presentes],
              loc="lower center", bbox_to_anchor=(0.5, 1.02),
              ncol=2 if len(presentes) > 3 else len(presentes),
              frameon=False, fontsize=7.5, columnspacing=1.4,
              handlelength=1.4, handletextpad=0.5)

    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.075, ha="left")
    fig.subplots_adjust(left=0.075, right=0.97, top=0.84,
                        bottom=0.16 if len(dias) > 10 else 0.10)


def montar_figura(pai):
    """Cria figura, tela e barra de navegação do matplotlib dentro de um frame."""
    fig = plt.Figure(figsize=(10, 5.4), facecolor=COR_FUNDO)
    tela = FigureCanvasTkAgg(fig, master=pai)
    tela.get_tk_widget().pack(side="top", fill="both", expand=True)
    barra = NavigationToolbar2Tk(tela, pai)
    barra.update()
    return fig, tela


def montar_tabela_janelas(pai, com_chuva=False, com_prob=False):
    """Treeview das janelas. A previsão ganha chuva e, no conjunto, confiança."""
    colunas = ["ini", "fim", "horas", "dtm", "dtf", "vm", "vmax", "dir",
               "t", "ur"]
    titulos = {"ini": "Início", "fim": "Fim", "horas": "Duração",
               "dtm": "Delta T médio", "dtf": "Delta T faixa",
               "vm": "Vento médio", "vmax": "Vento máx", "dir": "Vento de",
               "t": "Temp. média", "ur": "UR média", "ch": "Chuva (mm)",
               "pa": "Confiança"}
    larguras = {"ini": 125, "fim": 125, "horas": 70, "dtm": 100,
                "dtf": 100, "vm": 90, "vmax": 85, "dir": 90, "t": 90, "ur": 80,
                "ch": 85, "pa": 90}
    if com_chuva:
        colunas.append("ch")
    if com_prob:
        colunas.append("pa")

    moldura = ttk.Frame(pai)
    moldura.pack(side="top", fill="both", expand=True, padx=6, pady=6)

    tabela = ttk.Treeview(moldura, columns=tuple(colunas), show="headings")
    for c in colunas:
        tabela.heading(c, text=titulos[c])
        tabela.column(c, width=larguras[c],
                      anchor="w" if c in ("ini", "fim") else "center")
    rolagem = ttk.Scrollbar(moldura, orient="vertical", command=tabela.yview)
    tabela.configure(yscrollcommand=rolagem.set)
    tabela.pack(side="left", fill="both", expand=True)
    rolagem.pack(side="right", fill="y")
    return tabela


def preencher_tabela_janelas(tabela, janelas, com_chuva=False, com_prob=False):
    for item in tabela.get_children():
        tabela.delete(item)
    for j in janelas:
        valores = [
            j["ini"].strftime("%d/%m %H:%M"),
            j["fim"].strftime("%d/%m %H:%M"),
            f'{j["horas"]} h',
            _fmt(j["dt_medio"]),
            f'{_fmt(j["dt_min"])}–{_fmt(j["dt_max"])}',
            _fmt(j["vento_medio"]),
            _fmt(j["vento_max"]),
            _rotulo_dir(j.get("direcao")),
            _fmt(j["temp_media"]),
            _fmt(j["ur_media"], 0),
        ]
        if com_chuva:
            valores.append(_fmt(j.get("chuva")))
        if com_prob:
            pa = j.get("p_apto")
            valores.append("—" if pa is None else f"{100 * pa:.0f}%")
        tabela.insert("", "end", values=tuple(valores))


def _rotulo_dir(graus):
    return "—" if graus is None else f"{rumo(graus)} {graus:.0f}°"


def gravar_csv(caminho, serie, crit, com_chuva=False):
    """Série horária em CSV com ponto e vírgula e vírgula decimal.

    É o formato que o Excel em português abre com duplo clique, sem passar
    pelo assistente de importação.
    """
    def br(v, casas=2):
        return "" if v is None else f"{v:.{casas}f}".replace(".", ",")

    cabecalho = ("Data;Hora;Temp_C;UR_pct;Orvalho_C;BulboUmido_C;DeltaT_C;"
                 "Vento_kmh;Estacoes;DispDeltaT_C;DispVento_kmh;Situacao")
    if com_chuva:
        cabecalho += ";Chuva_mm;ProbChuva_pct"
    cabecalho += (";Rajada_kmh;DirVento_graus;VentoDe;DerivaPara;Inversao;"
                  "P_apto_pct;Origem")

    with open(caminho, "w", encoding="utf-8-sig", newline="") as f:
        f.write(cabecalho + "\n")
        for ts in sorted(serie):
            l = serie[ts]
            campos = [
                ts.strftime("%d/%m/%Y"), ts.strftime("%H:%M"),
                br(l.get("temp")), br(l.get("ur"), 0),
                br(l.get("orvalho")),
                br(bulbo_umido(l.get("temp"), l.get("ur"))),
                br(l.get("delta_t")), br(l.get("vento")),
                str(l.get("n_estacoes", "")),
                br(l.get("disp_dt")), br(l.get("disp_vento")),
                NOME_MOTIVO.get(classificar(l, crit), ""),
            ]
            if com_chuva:
                campos += [br(l.get("chuva")), br(l.get("prob_chuva"), 0)]
            d = l.get("direcao")
            campos += [br(l.get("rajada")),
                       "" if d is None else f"{d:.0f}",
                       "" if d is None else rumo(d),
                       "" if d is None else rumo(d + 180),
                       str(l.get("inversao") or ""),
                       "" if l.get("p_apto") is None
                       else br(100 * l["p_apto"], 0),
                       str(l.get("origem") or ("medido" if l.get("medido")
                                               else ""))]
            f.write(";".join(campos) + "\n")


def linha_do_metodo(metodo, altitude, por_estacao, serie):
    """Primeira linha do resumo: como o número foi obtido e quanto confiar nele.

    A discordância média entre estações é o que diz se a estimativa é
    sólida. Delta T interpolado de 5 °C com as estações variando 0,4 °C
    entre si é uma coisa; o mesmo 5 °C com elas variando 3 °C é outra
    bem diferente, e sem esse aviso as duas apareceriam iguais na tela.
    """
    if metodo == METODO_PONTO:
        return ("Método: série do modelo na própria coordenada da área — "
                "o relevo e a cobertura do terreno já entram no cálculo dele.")

    partes = [f"{len(por_estacao)} estações interpoladas por IDW"]
    if altitude:
        alt, origem = altitude
        partes.append(f"trazidas para {alt:.0f} m de altitude ({origem})")

    dts = [l["disp_dt"] for l in serie.values() if l.get("disp_dt") is not None]
    vts = [l["disp_vento"] for l in serie.values() if l.get("disp_vento") is not None]
    if dts and vts:
        m_dt, m_v = sum(dts) / len(dts), sum(vts) / len(vts)
        partes.append(f"discordância média entre elas: Delta T {_fmt(m_dt)} °C "
                      f"e vento {_fmt(m_v)} km/h")
    return "Método: " + " · ".join(partes) + "."


def linha_do_conjunto(conjunto, serie, crit):
    """Diz de quantas rodadas veio a probabilidade e quanto elas divergem."""
    if not conjunto:
        return ("Saída determinística: uma rodada só, sem medida de "
                "confiança. Para saber o quanto confiar, use o conjunto.")
    sds_dt = [l["sd_dt"] for l in serie.values() if l.get("sd_dt") is not None]
    sds_v = [l["sd_vento"] for l in serie.values()
             if l.get("sd_vento") is not None]
    partes = [f"Conjunto de {conjunto['membros']} rodadas "
              f"({', '.join(conjunto['modelos'])})"]
    if sds_dt and sds_v:
        partes.append(f"divergência entre elas: Delta T "
                      f"±{_fmt(sum(sds_dt) / len(sds_dt))} °C e vento "
                      f"±{_fmt(sum(sds_v) / len(sds_v))} km/h")
    partes.append(f"janela contada a partir de "
                  f"{100 * crit.get('limiar_p', LIMIAR_P):.0f}% das rodadas")
    return " · ".join(partes) + "."


def resumir(serie, janelas, crit, falhas=()):
    """Texto do painel de resumo, igual para as duas abas."""
    validas = [l for l in serie.values() if classificar(l, crit) != "sem_dado"]
    aptas = [l for l in serie.values() if e_apto(classificar(l, crit))]
    pct = 100 * len(aptas) / len(validas) if validas else 0
    maior = max((j["horas"] for j in janelas), default=0)

    por_hora = {}
    for ts, l in serie.items():
        st = classificar(l, crit)
        if st == "sem_dado":
            continue
        d = por_hora.setdefault(ts.hour, [0, 0])
        d[1] += 1
        if e_apto(st):
            d[0] += 1
    melhor = max(por_hora.items(), key=lambda kv: kv[1][0] / kv[1][1],
                 default=(None, (0, 1)))

    motivos = {}
    for l in serie.values():
        motivos.setdefault(classificar(l, crit), 0)
        motivos[classificar(l, crit)] += 1

    com_dado, esperadas, pct_cob = cobertura(serie)
    cabecalho = (f"{len(validas)} horas analisadas · {len(aptas)} aptas "
                 f"({pct:.0f}%) · {len(janelas)} janelas · maior de {maior} h")
    if pct_cob < 99.5:
        cabecalho += (f" · cobertura {pct_cob:.0f}% "
                      f"({esperadas - com_dado} h sem dado)")
    linhas = [cabecalho]
    if melhor[0] is not None and melhor[1][0]:
        taxa = 100 * melhor[1][0] / melhor[1][1]
        linhas.append(f"Melhor hora do dia: {melhor[0]:02d}h, apta em "
                      f"{taxa:.0f}% dos dias.")
    descartes = ", ".join(f"{NOME_MOTIVO.get(k, k)} {v}"
                          for k, v in sorted(motivos.items())
                          if not e_apto(k))
    if descartes:
        linhas.append("Por que as horas foram descartadas: " + descartes)
    if falhas:
        linhas.append("Estações que ficaram de fora: " + "; ".join(falhas))
    return "\n".join(linhas), len(validas), len(aptas)


# =====================================================================
# BLOCO 8B — DADO MEDIDO DO INMET, CALIBRAÇÃO LOCAL E VERIFICAÇÃO
# =====================================================================
#
# Até aqui, "estação" queria dizer "o modelo rodado na coordenada da
# estação". É o que dá para ter sem token do INMET, mas não é medição. A
# conferência com as tabelas das estações de Feira de Santana, Salvador-
# Rádio Farol e Cruz das Almas (10 a 24/09/2026) mostrou três erros
# sistemáticos do modelo naquela região:
#
#   - ar SECO demais: ponto de orvalho 1,4 °C abaixo do medido, umidade
#     7 pontos abaixo, e por isso Delta T cerca de 1 °C ACIMA do real;
#   - vento FORTE demais: 1,1 a 1,3 vez o medido de dia e 2 a 2,6 vezes
#     de madrugada, quando as estações registram calmaria;
#   - GAROA que não houve: três vezes mais chuva acumulada que o medido.
#
# A temperatura, ao contrário, bate: erro médio de meio grau.
#
# Este bloco faz três coisas com isso:
#
#   1. lê as tabelas que o portal do INMET exporta, para o histórico
#      passar a ser MEDIDO e não modelado;
#   2. compara, hora a hora, o medido com o modelo no mesmo ponto e
#      guarda os pares — daí sai a calibração local, que corrige o viés
#      por hora do dia antes de a previsão virar janela;
#   3. mede o acerto: das horas aptas pelo modelo, quantas foram aptas de
#      fato — antes e depois da correção, e a cada dia de antecedência.

import csv
import re
import unicodedata

FONTE_MEDIDO = "Medido (tabelas do INMET)"
FONTE_CORRIGIDO = "Modelo corrigido (calibração local)"
FONTE_MODELO = "Modelo bruto (Open-Meteo)"
FONTE_API = "INMET pela API (exige token)"
FONTES_HISTORICO = (FONTE_MEDIDO, FONTE_CORRIGIDO, FONTE_MODELO, FONTE_API)
FONTES_VOOS = (FONTE_MEDIDO, FONTE_CORRIGIDO, FONTE_MODELO)

CORRECAO_SIM = "Aplicar calibração local"
CORRECAO_NAO = "Sem correção"

ARQUIVO_CALIBRACAO = "calibracao.json"
DIAS_CALIBRACAO = 60        # só os dias mais recentes: o viés muda com a estação do ano
MIN_HORAS_CALIBRACAO = 72   # abaixo disso a correção seria ruído
ENCOLHIMENTO = 12.0         # horas "virtuais" que puxam cada hora para a média geral
LIMIAR_CHUVA_MEDIDA = 0.2   # mm/h — abaixo disso a estação não diferencia de orvalho

API_RODADAS_ANTERIORES = "https://previous-runs-api.open-meteo.com/v1/forecast"


# ---------------------------------------------------------------------
# Leitura das tabelas do portal
# ---------------------------------------------------------------------
#
# Aceita os dois formatos que o INMET entrega:
#   - a "Tabela de dados das estações" do portal tempo.inmet.gov.br
#     (arquivo generatedBy_react-csv), com cabeçalho "Data;Hora (UTC);
#     Temp. Ins. (C);...";
#   - o arquivo anual dos "Dados históricos" (portal.inmet.gov.br), com
#     oito linhas de identificação antes do cabeçalho.
# O primeiro não traz o código da estação; o segundo traz.

def _sem_acento(texto):
    base = unicodedata.normalize("NFD", str(texto))
    return "".join(c for c in base if unicodedata.category(c) != "Mn").lower().strip()


_CABECALHOS_INMET = (
    ("data", ("data",)),
    ("hora", ("hora",)),
    ("temp", ("temp. ins", "temperatura do ar - bulbo seco")),
    ("ur", ("umi. ins", "umidade relativa do ar, horaria")),
    ("orvalho", ("pto orvalho ins", "temperatura do ponto de orvalho")),
    ("pressao", ("pressao ins", "pressao atmosferica ao nivel da estacao")),
    ("vento", ("vel. vento", "vento, velocidade horaria")),
    ("direcao", ("dir. vento", "vento, direcao horaria")),
    ("rajada", ("raj. vento", "vento, rajada maxima")),
    ("radiacao", ("radiacao",)),
    ("chuva", ("chuva", "precipitacao total")),
)

NOME_VARIAVEL = {"temp": "temperatura", "ur": "umidade", "orvalho": "orvalho",
                 "pressao": "pressão", "vento": "vento", "direcao": "direção",
                 "rajada": "rajada", "radiacao": "radiação", "chuva": "chuva"}


def _colunas_inmet(cabecalho):
    """Mapeia cada variável para o índice da coluna, pelo começo do nome."""
    indices = {}
    nomes = [_sem_acento(c) for c in cabecalho]
    for chave, prefixos in _CABECALHOS_INMET:
        for i, nome in enumerate(nomes):
            if i in indices.values():
                continue
            if any(nome.startswith(p) for p in prefixos):
                indices[chave] = i
                break
    return indices


def _data_hora_inmet(data, hora):
    data = str(data).strip()
    digitos = re.sub(r"\D", "", str(hora))[:4].zfill(4)
    for formato in ("%d/%m/%Y", "%Y/%m/%d", "%Y-%m-%d", "%d-%m-%Y"):
        try:
            dia = datetime.strptime(data, formato)
            break
        except ValueError:
            continue
    else:
        return None
    try:
        return dia.replace(hour=int(digitos[:2]), minute=int(digitos[2:]),
                           tzinfo=timezone.utc)
    except ValueError:
        return None


def _valor_inmet(texto):
    v = _num(texto)
    if v is None or v <= -9999:
        return None
    return v


def codigo_do_arquivo(nome):
    """Código da estação no nome do arquivo (A413, A456...), se houver."""
    casou = re.search(r"(?<![A-Z0-9])([A-Z]\d{3})(?!\d)",
                      os.path.basename(str(nome)).upper())
    return casou.group(1) if casou else None


def altitude_pela_pressao(p_media):
    """Altitude aproximada pela pressão média, na atmosfera padrão.

    Serve só de pista para associar arquivo e estação: a pressão ao nível
    do mar varia alguns hPa com o tempo, então o erro é de dezenas de
    metros. Mas separa bem uma estação do litoral de uma do planalto.
    """
    if not p_media or p_media <= 0:
        return None
    return 44330.8 * (1 - (p_media / 1013.25) ** 0.190263)


def ler_tabela_inmet(caminho, fuso=-3):
    """Lê uma tabela horária exportada do INMET e devolve a série medida.

    Horários do arquivo vêm em UTC e saem no horário local. As variáveis
    saem nas mesmas unidades das séries do modelo (vento e rajada em km/h a
    10 m, radiação em W/m²), para as duas poderem ser comparadas e
    interpoladas pelo mesmo código.
    """
    bruto = open(caminho, "rb").read()
    for cod in ("utf-8-sig", "latin-1"):
        try:
            texto = bruto.decode(cod)
            break
        except UnicodeDecodeError:
            continue
    linhas = list(csv.reader(texto.splitlines(), delimiter=";", quotechar='"'))

    codigo, nome, meta = None, None, {}
    inicio = None
    for i, linha in enumerate(linhas):
        if not linha:
            continue
        primeira = _sem_acento(linha[0])
        if primeira.startswith("data") and len(linha) > 3:
            inicio = i
            break
        if len(linha) >= 2:
            meta[primeira.rstrip(":")] = linha[1].strip()
    if inicio is None:
        raise ValueError("não achei o cabeçalho (a linha que começa por "
                         "“Data”) — o arquivo é mesmo uma tabela do INMET?")
    for chave, valor in meta.items():
        if chave.startswith("codigo") and re.fullmatch(r"[A-Za-z]\d{3}", valor):
            codigo = valor.upper()
        if chave.startswith("estacao"):
            nome = valor

    col = _colunas_inmet(linhas[inicio])
    if "data" not in col or "hora" not in col:
        raise ValueError("a tabela não tem as colunas de data e hora")

    serie = {}
    for linha in linhas[inicio + 1:]:
        if len(linha) <= max(col.values()):
            continue
        ts = _data_hora_inmet(linha[col["data"]], linha[col["hora"]])
        if ts is None:
            continue
        v = {k: _valor_inmet(linha[i]) for k, i in col.items()
             if k not in ("data", "hora")}
        if all(v.get(k) is None for k in ("temp", "ur", "vento", "chuva")):
            continue          # hora ainda não medida (fim do dia corrente)
        local = ts + timedelta(hours=fuso)
        rad = v.get("radiacao")
        serie[local] = {
            "temp": v.get("temp"),
            "ur": v.get("ur"),
            "orvalho": v.get("orvalho"),
            "pressao": v.get("pressao"),
            "vento": None if v.get("vento") is None else v["vento"] * 3.6,
            "direcao": v.get("direcao"),
            "rajada": None if v.get("rajada") is None else v["rajada"] * 3.6,
            "radiacao": None if rad is None else max(0.0, rad / 3.6),
            "chuva": v.get("chuva"),
            "medido": True,
        }
    if not serie:
        raise ValueError("nenhuma hora com dado medido no arquivo")

    diag = qc_medido(serie)
    return {"serie": serie, "codigo": codigo or codigo_do_arquivo(caminho),
            "nome": nome, "arquivo": os.path.basename(caminho), "diag": diag}


def qc_medido(serie):
    """Controle de qualidade da série medida. Devolve o diagnóstico.

    O que a conferência mostrou é que estação automática raramente
    falha inteira: falha um sensor. Nas três tabelas de setembro, uma
    estava sem umidade, outra sem anemômetro, a terceira sem pluviômetro.
    Por isso o diagnóstico é por variável — e a interpolação depois usa,
    em cada variável, só as estações que a mediram.
    """
    horas = sorted(serie)
    avisos = []
    corrigidos = 0

    limites = {"temp": (-5, 48), "ur": (3, 100), "orvalho": (-25, 35),
               "pressao": (500, 1100), "vento": (0, 180),
               "direcao": (0, 360), "rajada": (0, 250), "chuva": (0, 150),
               "radiacao": (0, 1500)}
    for ts in horas:
        l = serie[ts]
        for k, (a, b) in limites.items():
            if l.get(k) is not None and not (a <= l[k] <= b):
                l[k] = None
                corrigidos += 1
        if l.get("orvalho") is not None and l.get("temp") is not None \
                and l["orvalho"] > l["temp"] + 0.5:
            l["orvalho"] = None
            corrigidos += 1
        if l.get("rajada") is not None and l.get("vento") is not None \
                and l["vento"] > 1 and l["rajada"] < 0.9 * l["vento"]:
            l["rajada"] = None            # rajada menor que a média: sensor
            corrigidos += 1

    # pico isolado de temperatura: sobe e desce mais de 8 °C em uma hora
    for i in range(1, len(horas) - 1):
        a, b, c = (serie[horas[i - 1]].get("temp"), serie[horas[i]].get("temp"),
                   serie[horas[i + 1]].get("temp"))
        if None not in (a, b, c) and abs(b - a) > 8 and abs(b - c) > 8:
            serie[horas[i]]["temp"] = None
            corrigidos += 1

    # sensor travado: o mesmo valor por 6 horas seguidas ou mais
    for chave, minimo in (("temp", 6), ("ur", 8)):
        seguidas = []
        for ts in horas + [None]:
            v = serie[ts].get(chave) if ts is not None else None
            if seguidas and v is not None and v == serie[seguidas[-1]].get(chave):
                seguidas.append(ts)
                continue
            if len(seguidas) >= minimo:
                valor = serie[seguidas[0]].get(chave)
                if not (chave == "ur" and valor is not None and valor >= 98):
                    for t in seguidas:
                        serie[t][chave] = None
                    corrigidos += len(seguidas)
                    avisos.append(f"{NOME_VARIAVEL[chave]} parada em "
                                  f"{_fmt(valor)} por {len(seguidas)} h — "
                                  "descartada")
            seguidas = [ts] if v is not None else []

    # umidade e orvalho se completam: com um e a temperatura sai o outro
    for ts in horas:
        l = serie[ts]
        if l.get("ur") is None and l.get("orvalho") is not None \
                and l.get("temp") is not None:
            l["ur"] = ur_do_orvalho(l["temp"], l["orvalho"])
        if l.get("orvalho") is None and l.get("ur") is not None \
                and l.get("temp") is not None:
            l["orvalho"] = ponto_de_orvalho(l["temp"], l["ur"])

    # radiação: o INMET deixa em branco à noite em vez de gravar zero
    if any(serie[t].get("radiacao") is not None for t in horas):
        for ts in horas:
            l = serie[ts]
            if l.get("radiacao") is None and l.get("temp") is not None \
                    and (ts.hour >= 19 or ts.hour <= 5):
                l["radiacao"] = 0.0

    contagem = {k: sum(1 for t in horas if serie[t].get(k) is not None)
                for k in ("temp", "ur", "vento", "direcao", "rajada",
                          "chuva", "radiacao", "pressao")}
    faltam = [NOME_VARIAVEL[k] for k in ("temp", "ur", "vento", "chuva")
              if contagem[k] == 0]
    if faltam:
        avisos.insert(0, "sem " + ", ".join(faltam) + " no período inteiro "
                      "(sensor fora) — a estação fica de fora dessa variável")

    # anemômetro: zero cravado de dia é defeito; de madrugada é calmaria
    ventos_dia = [serie[t]["vento"] for t in horas
                  if serie[t].get("vento") is not None and 10 <= t.hour <= 16]
    ventos_noite = [serie[t]["vento"] for t in horas
                    if serie[t].get("vento") is not None
                    and (t.hour >= 21 or t.hour <= 5)]
    zero_dia = (sum(1 for v in ventos_dia if v == 0) / len(ventos_dia)
                if ventos_dia else 0.0)
    zero_noite = (sum(1 for v in ventos_noite if v == 0) / len(ventos_noite)
                  if ventos_noite else 0.0)
    if zero_dia > 0.30:
        avisos.append(f"anemômetro zerado em {100 * zero_dia:.0f}% das horas "
                      "entre 10 e 16h — possível sensor travado")
    elif zero_noite > 0.50:
        avisos.append(f"calmaria em {100 * zero_noite:.0f}% das horas da "
                      "madrugada (vento abaixo do limiar do anemômetro)")

    pressoes = [serie[t]["pressao"] for t in horas
                if serie[t].get("pressao") is not None]
    return {"horas": len(horas), "inicio": horas[0], "fim": horas[-1],
            "contagem": contagem, "faltam": faltam, "avisos": avisos,
            "corrigidos": corrigidos,
            "pressao_media": sum(pressoes) / len(pressoes) if pressoes else None,
            "zero_noite": zero_noite, "zero_dia": zero_dia}


def descrever_tabela(tab):
    """Uma linha dizendo o que o arquivo trouxe — vai para o resumo."""
    d = tab["diag"]
    c = d["contagem"]
    partes = [f'{tab.get("codigo") or "?"} · {tab["arquivo"]}: '
              f'{d["horas"]} h de {d["inicio"]:%d/%m %Hh} a {d["fim"]:%d/%m %Hh}']
    tem = [NOME_VARIAVEL[k] for k in ("temp", "ur", "vento", "direcao", "chuva")
           if c.get(k)]
    partes.append("mede " + ", ".join(tem))
    if d["avisos"]:
        partes.append("; ".join(d["avisos"]))
    return " · ".join(partes)


def sugerir_associacao(tabelas, estacoes):
    """Liga cada tabela a uma estação.

    Primeiro vale o código que vier no arquivo (no nome ou no cabeçalho).
    O que sobrar vai, pela ordem, para as estações ainda livres — é a
    ordem em que a aba 1 as lista, que costuma ser a ordem em que se
    baixa as tabelas do portal. O usuário confirma na janela seguinte.
    """
    codigos = [e["codigo"] for e in estacoes]
    usados = {t["codigo"] for t in tabelas if t.get("codigo") in codigos}
    livres = [c for c in codigos if c not in usados]
    saida = []
    for t in tabelas:
        if t.get("codigo"):
            saida.append((t, t["codigo"]))
        else:
            saida.append((t, livres.pop(0) if livres else None))
    return saida


def pedir_associacao(master, pendentes, estacoes):
    """Janela para confirmar a qual estação pertence cada arquivo.

    `pendentes` é a lista de (tabela, código sugerido). Devolve a lista
    confirmada, ou None se o usuário cancelar.
    """
    rotulos = {e["codigo"]: f'{e["codigo"]} · {e["nome"][:24]} · '
                            f'{e.get("altitude", 0):.0f} m'
               for e in estacoes}
    opcoes = list(rotulos.values()) + ["(ignorar este arquivo)"]
    janela = tk.Toplevel(master)
    janela.title("A qual estação pertence cada tabela?")
    janela.transient(master)
    ttk.Label(janela, wraplength=620, justify="left",
              text="As tabelas do portal do INMET não trazem o código da "
                   "estação. Confira a sugestão abaixo (feita pela ordem das "
                   "estações na aba 1). A pressão média dá uma pista da "
                   "altitude de cada arquivo. Para pular esta janela da "
                   "próxima vez, ponha o código no nome do arquivo "
                   "(ex.: A413.csv).").pack(padx=12, pady=(12, 6), anchor="w")
    grade = ttk.Frame(janela)
    grade.pack(padx=12, pady=6, fill="x")
    variaveis = []
    for i, (tab, cod) in enumerate(pendentes):
        d = tab["diag"]
        alt = altitude_pela_pressao(d.get("pressao_media"))
        pista = (f"pressão {d['pressao_media']:.1f} hPa ≈ {alt:.0f} m"
                 if alt is not None else "sem pressão")
        ttk.Label(grade, text=f'{tab["arquivo"]}  ({pista})').grid(
            row=i, column=0, sticky="w", pady=3)
        var = tk.StringVar(value=rotulos.get(cod, opcoes[-1]))
        ttk.Combobox(grade, textvariable=var, values=opcoes, width=42,
                     state="readonly").grid(row=i, column=1, padx=8, pady=3)
        variaveis.append(var)

    resposta = {"ok": False}

    def confirmar():
        resposta["ok"] = True
        janela.destroy()

    botoes = ttk.Frame(janela)
    botoes.pack(padx=12, pady=(6, 12), fill="x")
    ttk.Button(botoes, text="Confirmar", command=confirmar).pack(side="right")
    ttk.Button(botoes, text="Cancelar",
               command=janela.destroy).pack(side="right", padx=6)
    janela.grab_set()
    master.wait_window(janela)
    if not resposta["ok"]:
        return None
    inverso = {v: k for k, v in rotulos.items()}
    return [(tab, inverso.get(var.get())) for (tab, _), var
            in zip(pendentes, variaveis)]


def recortar(serie, ini, fim):
    """Horas da série entre as datas (texto AAAA-MM-DD), inclusive."""
    d0 = datetime.strptime(ini, "%Y-%m-%d").date()
    d1 = datetime.strptime(fim, "%Y-%m-%d").date()
    return {ts: dict(l) for ts, l in serie.items() if d0 <= ts.date() <= d1}


def completar_com_modelo(medida, modelo, coef=None, preencher=True):
    """Acrescenta à série medida o que a estação não mede.

    - temperatura a 80 m, nuvens e camada limite só existem no modelo.
      A 80 m entra como o GRADIENTE do modelo somado à temperatura
      medida, porque misturar o valor absoluto do modelo com o medido
      criaria inversão onde há só viés.
    - horas inteiras sem medição (atraso do INMET, estação fora do ar)
      recebem o modelo corrigido pela calibração, marcadas como tal. Hora
      em que falta um sensor só NÃO é completada: nessa variável a estação
      simplesmente não entra na interpolação.
    Devolve (série, horas_preenchidas).
    """
    modelo = modelo or {}
    saida = {}
    for ts, l in medida.items():
        linha = dict(l)
        m = modelo.get(ts)
        if m:
            if m.get("temp_80m") is not None and m.get("temp") is not None \
                    and linha.get("temp") is not None:
                linha["temp_80m"] = linha["temp"] + (m["temp_80m"] - m["temp"])
            for chave in ("nuvens", "camada_limite"):
                if m.get(chave) is not None:
                    linha[chave] = m[chave]
            if linha.get("radiacao") is None and m.get("radiacao") is not None:
                linha["radiacao"] = m["radiacao"]
        saida[ts] = linha

    preenchidas = 0
    if medida and preencher:
        faltando = {ts: dict(m) for ts, m in modelo.items()
                    if ts not in medida}
        if faltando:
            if coef:
                aplicar_calibracao(faltando, coef)
            for ts, m in faltando.items():
                m["origem"] = "modelo corrigido" if coef else "modelo"
                saida[ts] = m
                preenchidas += 1
    return saida, preenchidas


# ---------------------------------------------------------------------
# Pares medido × modelo e calibração
# ---------------------------------------------------------------------
#
# Cada estação guarda, por dia e hora, dez números: temperatura, orvalho,
# vento, rajada e chuva, medidos e do modelo. Guardar os pares, e não só
# o viés já calculado, é o que permite:
#   - somar períodos: tabela nova acrescenta dias, dia repetido substitui;
#   - usar só os últimos 60 dias, porque o viés da seca não é o das águas;
#   - validar de forma honesta, deixando cada dia de fora do cálculo que
#     vai corrigi-lo (validação cruzada por dia).

IDX_PAR = {"temp": (0, 1), "orvalho": (2, 3), "vento": (4, 5),
           "rajada": (6, 7), "chuva": (8, 9)}


def pares_da_estacao(medida, modelo):
    """{'AAAA-MM-DD': [24 × [t_o, t_m, td_o, td_m, v_o, v_m, r_o, r_m, c_o, c_m]]}"""
    pares = {}
    for ts, o in medida.items():
        if o.get("origem"):          # hora preenchida pelo modelo não é medição
            continue
        m = modelo.get(ts)
        if not m:
            continue
        td_o = o.get("orvalho")
        if td_o is None:
            td_o = ponto_de_orvalho(o.get("temp"), o.get("ur"))
        v_m = m.get("vento_10m", m.get("vento"))
        r_m = m.get("rajada_10m", m.get("rajada"))
        par = [o.get("temp"), m.get("temp"),
               td_o, ponto_de_orvalho(m.get("temp"), m.get("ur")),
               o.get("vento"), v_m, o.get("rajada"), r_m,
               o.get("chuva"), m.get("chuva")]
        par = [None if v is None else round(float(v), 2) for v in par]
        dia = pares.setdefault(ts.strftime("%Y-%m-%d"), [None] * 24)
        dia[ts.hour] = par
    return pares


def _dias_de_calibracao(pares, dias_max=DIAS_CALIBRACAO, excluir=None):
    dias = sorted(d for d in pares if d != excluir)
    return dias[-dias_max:] if dias_max else dias


def coeficientes_da_estacao(pares, dias_max=DIAS_CALIBRACAO, excluir=None):
    """Correção por hora do dia, a partir dos pares guardados.

    Temperatura e orvalho: viés aditivo (modelo − medido) por hora.
    Vento e rajada: razão (medido ÷ modelo) por hora — erro de vento é
    proporcional, e de madrugada o modelo erra por fator, não por soma.
    Cada hora usa a vizinha de cada lado (±1 h) e é puxada para a média
    geral na proporção de quão poucos dados tem: com 15 dias, uma hora
    isolada teria só 15 amostras, e o encolhimento evita que um dia
    atípico vire correção.
    Chuva: o modelo garoa em horas em que não chove. O limiar é escolhido
    para que ele tenha tantas horas de chuva quantas a estação mediu, e o
    volume é reescalado pelo total. Com menos de 3 horas de chuva medida
    não há evento para calibrar e a chuva fica como está.
    """
    dias = _dias_de_calibracao(pares, dias_max, excluir)
    saida = {"dias": len(dias),
             "periodo": (dias[0], dias[-1]) if dias else None}
    if not dias:
        return saida

    def coletar(i_o, i_m):
        por_hora = [[] for _ in range(24)]
        for d in dias:
            for h, par in enumerate(pares[d]):
                if par and par[i_o] is not None and par[i_m] is not None:
                    por_hora[h].append((par[i_o], par[i_m]))
        return por_hora

    for chave in ("temp", "orvalho"):
        por_hora = coletar(*IDX_PAR[chave])
        tudo = [m - o for hs in por_hora for o, m in hs]
        if len(tudo) < MIN_HORAS_CALIBRACAO:
            saida[chave] = None
            continue
        geral = sum(tudo) / len(tudo)
        vies = []
        for h in range(24):
            amostra = [m - o for k in (h - 1, h, (h + 1) % 24)
                       for o, m in por_hora[k]]
            vies.append((sum(amostra) + ENCOLHIMENTO * geral)
                        / (len(amostra) + ENCOLHIMENTO))
        saida[chave] = [round(v, 3) for v in vies]
        saida["n_" + chave] = len(tudo)

    for chave in ("vento", "rajada"):
        por_hora = coletar(*IDX_PAR[chave])
        tudo = [(o, m) for hs in por_hora for o, m in hs]
        soma_m = sum(m for _, m in tudo)
        if len(tudo) < MIN_HORAS_CALIBRACAO or soma_m < 1:
            saida[chave] = None
            continue
        geral = sum(o for o, _ in tudo) / soma_m
        media_m = soma_m / len(tudo)
        razoes = []
        for h in range(24):
            amostra = [(o, m) for k in (h - 1, h, (h + 1) % 24)
                       for o, m in por_hora[k]]
            so = sum(o for o, _ in amostra) + ENCOLHIMENTO * geral * media_m
            sm = sum(m for _, m in amostra) + ENCOLHIMENTO * media_m
            razoes.append(min(2.0, max(0.25, so / sm)))
        saida[chave] = [round(r, 3) for r in razoes]
        saida["n_" + chave] = len(tudo)

    i_o, i_m = IDX_PAR["chuva"]
    horas = [(par[i_o], par[i_m]) for d in dias for par in pares[d]
             if par and par[i_o] is not None and par[i_m] is not None]
    molhadas = sum(1 for o, _ in horas if o >= LIMIAR_CHUVA_MEDIDA)
    saida["chuva"] = None
    saida["chuva_eventos"] = molhadas
    if len(horas) >= MIN_HORAS_CALIBRACAO and molhadas >= 3:
        modelo = sorted((m for _, m in horas), reverse=True)
        limiar = min(5.0, max(0.1, modelo[min(molhadas, len(modelo)) - 1]))
        acima = sum(m for _, m in horas if m >= limiar)
        medido = sum(o for o, _ in horas)
        fator = min(2.0, max(0.2, medido / acima)) if acima > 0 else 1.0
        saida["chuva"] = {"limiar": round(limiar, 2), "fator": round(fator, 3)}
    return saida


def aplicar_calibracao(serie, coef):
    """Corrige uma série do modelo (ainda com o vento a 10 m), no lugar.

    Temperatura e orvalho são corrigidos separadamente e a umidade é
    recalculada deles — corrigir a umidade direto misturaria o erro de
    temperatura com o de vapor, e o Delta T sai justamente dos dois.
    """
    if not coef:
        return serie
    b_t, b_td = coef.get("temp"), coef.get("orvalho")
    r_v, r_r = coef.get("vento"), coef.get("rajada")
    chuva = coef.get("chuva")
    for ts, l in serie.items():
        if l.get("calibrado"):
            continue
        h = ts.hour
        T, UR = l.get("temp"), l.get("ur")
        td = ponto_de_orvalho(T, UR)
        if T is not None and b_t:
            l["temp"] = T - b_t[h]
            if l.get("temp_80m") is not None:
                l["temp_80m"] = l["temp_80m"] - b_t[h]
        if td is not None:
            if b_td:
                td -= b_td[h]
            td = min(td, l["temp"])
            l["ur"] = ur_do_orvalho(l["temp"], td)
        if r_v and l.get("vento") is not None:
            l["vento"] = l["vento"] * r_v[h]
        if r_r and l.get("rajada") is not None:
            l["rajada"] = l["rajada"] * r_r[h]
        if chuva and l.get("chuva") is not None:
            l["chuva"] = (0.0 if l["chuva"] < chuva["limiar"]
                          else l["chuva"] * chuva["fator"])
        l["calibrado"] = True
    return serie


def combinar_coeficientes(coefs, estacoes):
    """Coeficientes da área: média das estações, pelos pesos do IDW.

    Cada variável é combinada só entre as estações que têm correção para
    ela — a de Salvador sem anemômetro não entra no fator do vento.
    """
    usadas = [e for e in estacoes if coefs.get(e["codigo"])]
    if not usadas:
        return None
    pesos = pesos_idw(usadas)
    saida = {"estacoes": [e["codigo"] for e in usadas]}
    for chave in ("temp", "orvalho", "vento", "rajada"):
        tem = [(coefs[e["codigo"]][chave], pesos.get(e["codigo"], 0.0))
               for e in usadas if coefs[e["codigo"]].get(chave)]
        soma = sum(p for _, p in tem)
        if not tem or soma <= 0:
            saida[chave] = None
            continue
        saida[chave] = [sum(v[h] * p for v, p in tem) / soma for h in range(24)]
    tem = [(coefs[e["codigo"]]["chuva"], pesos.get(e["codigo"], 0.0))
           for e in usadas if coefs[e["codigo"]].get("chuva")]
    soma = sum(p for _, p in tem)
    saida["chuva"] = ({"limiar": sum(c["limiar"] * p for c, p in tem) / soma,
                       "fator": sum(c["fator"] * p for c, p in tem) / soma}
                      if tem and soma > 0 else None)
    return saida


def carregar_calibracao():
    """Lê o calibracao.json ao lado do programa, se existir."""
    caminho = caminho_ao_lado(ARQUIVO_CALIBRACAO)
    if not os.path.exists(caminho):
        return {"versao": 2, "estacoes": {}}
    try:
        with open(caminho, encoding="utf-8") as f:
            cal = json.load(f)
        if not isinstance(cal, dict) or "estacoes" not in cal:
            raise ValueError
        return cal
    except Exception:
        return {"versao": 2, "estacoes": {}}


def gravar_calibracao(cal):
    caminho = caminho_ao_lado(ARQUIVO_CALIBRACAO)
    cal["atualizada"] = datetime.now().isoformat(timespec="minutes")
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump(cal, f, ensure_ascii=False)
    return caminho


def somar_pares(cal, codigo, nome, pares):
    """Acrescenta os pares novos aos guardados. Dia repetido é substituído."""
    est = cal.setdefault("estacoes", {}).setdefault(
        codigo, {"nome": nome, "pares": {}})
    est["nome"] = nome or est.get("nome")
    novos = 0
    for dia, horas in pares.items():
        if dia not in est["pares"]:
            novos += 1
        est["pares"][dia] = horas
    return novos


def coeficientes_da_calibracao(cal, excluir=None):
    """{codigo: coeficientes} de todas as estações guardadas."""
    return {cod: coeficientes_da_estacao(est.get("pares", {}), excluir=excluir)
            for cod, est in (cal or {}).get("estacoes", {}).items()}


def resumo_calibracao(cal, estacoes):
    """Texto curto: o que a calibração guardada corrige nesta área."""
    coefs = coeficientes_da_calibracao(cal)
    area = combinar_coeficientes(coefs, estacoes)
    if not area:
        return None, "Sem calibração local para as estações desta área."

    def media(v):
        return sum(v) / len(v) if v else None

    partes = []
    if area.get("orvalho"):
        partes.append(f"orvalho {_fmt(-media(area['orvalho']), 1)} °C")
    if area.get("temp"):
        partes.append(f"temperatura {_fmt(-media(area['temp']), 1)} °C")
    if area.get("vento"):
        partes.append(f"vento ×{_fmt(min(area['vento']), 2)} a "
                      f"×{_fmt(max(area['vento']), 2)} conforme a hora")
    if area.get("chuva"):
        partes.append(f"chuva abaixo de {_fmt(area['chuva']['limiar'], 1)} "
                      "mm/h desconsiderada")
    dias = [coefs[c]["dias"] for c in area["estacoes"]]
    texto = (f"Calibração local ({', '.join(area['estacoes'])}, "
             f"{max(dias)} dias): " + "; ".join(partes) + ".")
    return area, texto


def corrigir_series(series, coefs):
    """Aplica a cada estação a sua própria correção (cópias)."""
    saida = {}
    for cod, s in series.items():
        copia = {ts: dict(l) for ts, l in s.items()}
        if coefs.get(cod):
            aplicar_calibracao(copia, coefs[cod])
        saida[cod] = copia
    return saida


def corrigir_por_dia(serie_modelo, pares, coef_por_dia_cache=None):
    """Correção com validação cruzada: cada dia corrigido SEM ele mesmo.

    É o número honesto do quanto a calibração ajuda. Corrigir um dia com
    um coeficiente que já o viu mediria só a capacidade de decorar.
    """
    cache = coef_por_dia_cache if coef_por_dia_cache is not None else {}
    saida = {}
    for ts, l in serie_modelo.items():
        dia = ts.strftime("%Y-%m-%d")
        if dia not in cache:
            cache[dia] = coeficientes_da_estacao(pares, excluir=dia)
        copia = {ts: dict(l)}
        aplicar_calibracao(copia, cache[dia])
        saida[ts] = copia[ts]
    return saida


def mascarar_como(modelo, medida):
    """Apaga do modelo o que a estação não mediu naquela hora.

    Para comparar a área medida com a área do modelo, as duas têm de ser
    feitas com as mesmas estações em cada variável; senão a diferença
    mistura erro do modelo com troca de estação.
    """
    saida = {}
    for ts, m in modelo.items():
        o = medida.get(ts)
        if not o or o.get("origem"):
            continue
        linha = dict(m)
        if o.get("temp") is None:
            linha["temp"] = None
        if o.get("ur") is None:
            linha["ur"] = None
        if o.get("vento") is None:
            linha["vento"] = None
            linha["direcao"] = None
        if o.get("rajada") is None:
            linha["rajada"] = None
        if o.get("chuva") is None:
            linha["chuva"] = None
        saida[ts] = linha
    return saida


# ---------------------------------------------------------------------
# Métricas de acerto
# ---------------------------------------------------------------------

def _estatisticas(diferencas, obs=None, mod=None):
    n = len(diferencas)
    if not n:
        return None
    vies = sum(diferencas) / n
    mae = sum(abs(d) for d in diferencas) / n
    rmse = math.sqrt(sum(d * d for d in diferencas) / n)
    r = None
    if obs and mod and len(obs) > 2:
        mo, mm = sum(obs) / len(obs), sum(mod) / len(mod)
        so = math.sqrt(sum((x - mo) ** 2 for x in obs))
        sm = math.sqrt(sum((x - mm) ** 2 for x in mod))
        if so > 0 and sm > 0:
            r = sum((a - mo) * (b - mm) for a, b in zip(obs, mod)) / (so * sm)
    return {"n": n, "vies": vies, "mae": mae, "rmse": rmse, "r": r}


def comparar_series(obs, mod, chaves=("temp", "orvalho", "ur", "delta_t",
                                      "vento", "rajada")):
    """Viés, erro médio absoluto, RMSE e correlação, hora a hora.

    `obs` e `mod` já preparados (vento na altura de aplicação). Devolve
    também o viés por hora do dia, que é o que o gráfico mostra.
    """
    saida = {"por_hora": {}}
    for k in chaves:
        pares = [(obs[ts][k], mod[ts][k]) for ts in obs
                 if ts in mod and obs[ts].get(k) is not None
                 and mod[ts].get(k) is not None]
        saida[k] = _estatisticas([m - o for o, m in pares],
                                 [o for o, _ in pares], [m for _, m in pares])
        por_hora = []
        for h in range(24):
            ds = [mod[ts][k] - obs[ts][k] for ts in obs
                  if ts.hour == h and ts in mod
                  and obs[ts].get(k) is not None and mod[ts].get(k) is not None]
            os_ = [obs[ts][k] for ts in obs if ts.hour == h and ts in mod
                   and obs[ts].get(k) is not None and mod[ts].get(k) is not None]
            por_hora.append({"vies": sum(ds) / len(ds) if ds else None,
                             "obs": sum(os_) / len(os_) if os_ else None,
                             "n": len(ds)})
        saida["por_hora"][k] = por_hora
    return saida


def tabela_de_acerto(obs, mod, crit, crit_mod=None):
    """Horas aptas pelo modelo contra horas aptas pelo medido.

    acerto (POD): das horas que de fato serviram, quantas o modelo viu;
    alarme falso (FAR): das que o modelo aprovou, quantas não serviram;
    CSI: acerto descontando os dois erros — a nota única mais honesta
    quando o evento (hora apta) é minoria.
    """
    crit_mod = crit_mod or crit
    a = b = c = d = 0
    cruzado = {}
    for ts, o in obs.items():
        if ts not in mod:
            continue
        mo = classificar(o, crit)
        mm = classificar(mod[ts], crit_mod)
        if "sem_dado" in (mo, mm):
            continue
        ao, am = e_apto(mo), e_apto(mm)
        if am and ao:
            a += 1
        elif am:
            b += 1
        elif ao:
            c += 1
        else:
            d += 1
        cruzado[(mm, mo)] = cruzado.get((mm, mo), 0) + 1
    n = a + b + c + d
    return {"n": n, "acertos": a, "alarmes": b, "perdidas": c,
            "negativos": d,
            "pod": a / (a + c) if a + c else None,
            "far": b / (a + b) if a + b else None,
            "csi": a / (a + b + c) if a + b + c else None,
            "acerto_total": (a + d) / n if n else None,
            "aptas_obs": a + c, "aptas_mod": a + b, "cruzado": cruzado}


def verificar_historico(obs_area, mod_area, cor_area, crit):
    """Junta as comparações da área: modelo bruto e corrigido contra medido."""
    saida = {"bruto": comparar_series(obs_area, mod_area),
             "acerto_bruto": tabela_de_acerto(obs_area, mod_area, crit)}
    if cor_area:
        saida["corrigido"] = comparar_series(obs_area, cor_area)
        saida["acerto_corrigido"] = tabela_de_acerto(obs_area, cor_area, crit)

    chuva_o = sum(1 for l in obs_area.values()
                  if (l.get("chuva") or 0) >= LIMIAR_CHUVA_MEDIDA)
    chuva_m = sum(1 for ts, l in mod_area.items() if ts in obs_area
                  and obs_area[ts].get("chuva") is not None
                  and (l.get("chuva") or 0) > crit.get("chuva_max", 0.2))
    saida["horas_chuva"] = (chuva_o, chuva_m)
    return saida


def texto_verificacao(v):
    """Resumo em três linhas do que a conferência mostrou."""
    if not v:
        return ""
    b = v["bruto"]
    linhas = []
    partes = []
    for chave, nome, un in (("temp", "temperatura", "°C"),
                            ("orvalho", "orvalho", "°C"),
                            ("delta_t", "Delta T", "°C"),
                            ("vento", "vento", "km/h")):
        e = b.get(chave)
        if e:
            partes.append(f"{nome} {'+' if e['vies'] >= 0 else ''}"
                          f"{_fmt(e['vies'])} {un} (erro médio {_fmt(e['mae'])})")
    if partes:
        linhas.append("Modelo × medido na área, viés: " + " · ".join(partes) + ".")
    ab = v["acerto_bruto"]
    if ab["n"]:
        linha = (f"Horas aptas: o modelo aprovou {ab['aptas_mod']}, o medido "
                 f"{ab['aptas_obs']}; coincidiram {ab['acertos']} "
                 f"(acerto {_pct(ab['pod'])}, alarme falso {_pct(ab['far'])}, "
                 f"CSI {_pct(ab['csi'])})")
        ac = v.get("acerto_corrigido")
        if ac and ac["n"]:
            linha += (f". Com a calibração (validação cruzada por dia): "
                      f"acerto {_pct(ac['pod'])}, alarme falso "
                      f"{_pct(ac['far'])}, CSI {_pct(ac['csi'])}")
        linhas.append(linha + ".")
    co, cm = v.get("horas_chuva", (0, 0))
    if cm or co:
        linhas.append(f"Chuva: {cm} h com chuva no modelo, {co} h medidas "
                      f"acima de {_fmt(LIMIAR_CHUVA_MEDIDA)} mm.")
    if v.get("probabilidade"):
        linhas.append(texto_probabilidades(
            v["probabilidade"], "Probabilidade (modelo corrigido com o erro "
                                "vestido, validação cruzada)"))
    if v.get("arquivadas"):
        partes = [f"{a['antecedencia']} d: Brier {_fmt(a['brier'], 3)}"
                  + (f", CSI {_pct(a['csi'])}" if a.get('csi') is not None else "")
                  + f" (n={a['n']})" for a in v["arquivadas"]]
        linhas.append(f"Previsões da própria ferramenta ({v['n_arquivadas']} "
                      "emitidas e arquivadas): " + "; ".join(partes) + ".")
    return "\n".join(linhas)


def _pct(v):
    return "—" if v is None else f"{100 * v:.0f}%"


# ---------------------------------------------------------------------
# Verificação por antecedência — o quanto a previsão acerta
# ---------------------------------------------------------------------
#
# O Open-Meteo guarda o que cada rodada passada previu. Com isso dá para
# perguntar, para os dias em que há medição: o que o modelo dizia 1 dia
# antes? E 3? E 5? Comparando com o que a estação mediu, sai o acerto por
# antecedência — que é o que diz até quantos dias à frente vale a pena
# programar a operação por esta ferramenta.

ANTECEDENCIAS = (1, 2, 3, 4, 5, 6, 7)
VARIAVEIS_RODADAS = ("temperature_2m", "relative_humidity_2m",
                     "wind_speed_10m", "wind_direction_10m", "precipitation")


def baixar_rodadas_anteriores(lat, lon, dias_passados, fuso=-3,
                              antecedencias=ANTECEDENCIAS):
    """{antecedência: série} com o que cada rodada previa para as horas passadas."""
    def pedido(variaveis):
        hourly = ",".join(f"{v}_previous_day{n}" for v in variaveis
                          for n in antecedencias)
        p = {"latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}",
             "wind_speed_unit": "ms", "timezone": "UTC",
             "past_days": str(max(1, min(92, int(dias_passados)))),
             "forecast_days": "1", "hourly": hourly}
        return _hourly_da_resposta(_pega_json(_url(API_RODADAS_ANTERIORES, p),
                                              timeout=180))
    try:
        h = pedido(VARIAVEIS_RODADAS + ("wind_gusts_10m",))
    except Exception:
        h = pedido(VARIAVEIS_RODADAS)

    def valor(var, n, i):
        return _num(_em(h.get(f"{var}_previous_day{n}"), i))

    saida = {}
    for n in antecedencias:
        if not any(h.get(f"{v}_previous_day{n}") for v in VARIAVEIS_RODADAS):
            continue
        serie = {}
        for i, iso in enumerate(h.get("time", [])):
            ts = datetime.fromisoformat(iso).replace(tzinfo=timezone.utc)
            v, r = valor("wind_speed_10m", n, i), valor("wind_gusts_10m", n, i)
            linha = {"temp": valor("temperature_2m", n, i),
                     "ur": valor("relative_humidity_2m", n, i),
                     "vento": None if v is None else v * 3.6,
                     "rajada": None if r is None else r * 3.6,
                     "direcao": valor("wind_direction_10m", n, i),
                     "chuva": valor("precipitation", n, i)}
            if linha["temp"] is None:
                continue
            serie[ts + timedelta(hours=fuso)] = linha
        if serie:
            saida[n] = serie
    if not saida:
        raise RuntimeError("a fonte não devolveu rodadas anteriores")
    return saida


def verificar_antecedencias(obs_area, medidas, rodadas, usadas, alt, crit,
                            pares_por_estacao):
    """Acerto das horas aptas e erro de Delta T e vento, por antecedência.

    `rodadas` é {codigo: {antecedência: série}}. Para cada antecedência,
    monta a área com as previsões daquela antecedência, do mesmo jeito que
    a área medida foi montada, e compara — sem e com a calibração, esta
    sempre em validação cruzada por dia.
    """
    linhas = []
    for n in ANTECEDENCIAS:
        brutas, corrigidas = {}, {}
        for e in usadas:
            cod = e["codigo"]
            s = (rodadas.get(cod) or {}).get(n)
            if not s or cod not in medidas:
                continue
            m = mascarar_como(s, medidas[cod])
            brutas[cod] = m
            pares = pares_por_estacao.get(cod)
            corrigidas[cod] = (corrigir_por_dia(m, pares) if pares
                               else {ts: dict(l) for ts, l in m.items()})
        if not brutas:
            continue
        est = [e for e in usadas if e["codigo"] in brutas]
        area_b = fechar_criterios(interpolar_area(brutas, est, alt),
                                  dict(crit), alt)
        area_c = fechar_criterios(interpolar_area(corrigidas, est, alt),
                                  dict(crit), alt)
        comp_b = comparar_series(obs_area, area_b, ("delta_t", "vento"))
        comp_c = comparar_series(obs_area, area_c, ("delta_t", "vento"))
        linhas.append({
            "antecedencia": n,
            "acerto_bruto": tabela_de_acerto(obs_area, area_b, crit),
            "acerto_corrigido": tabela_de_acerto(obs_area, area_c, crit),
            "dt_bruto": comp_b.get("delta_t"), "dt_corrigido": comp_c.get("delta_t"),
            "vento_bruto": comp_b.get("vento"),
            "vento_corrigido": comp_c.get("vento"),
        })
    return linhas


def desenhar_verificacao(fig, verif, antecedencias=None, titulo=""):
    """Painéis da conferência modelo × medido.

    Em cima, o viés hora a hora de orvalho, Delta T e vento — é onde se vê
    que o erro não é constante: o modelo erra de um jeito de dia e de
    outro de madrugada, e é por isso que a correção é por hora. Embaixo, o
    acerto das horas aptas, e, se tiver sido calculado, como ele cai com a
    antecedência da previsão.
    """
    fig.clear()
    if not verif:
        _sem_dados(fig, "Carregue as tabelas do INMET, escolha a fonte "
                        "“Medido” e baixe o período\npara ver o modelo "
                        "comparado com o que as estações mediram.")
        return

    grade = fig.add_gridspec(2, 3, height_ratios=[1, 1], hspace=0.55,
                             wspace=0.32)
    horas = list(range(24))
    receitas = (("orvalho", "Ponto de orvalho: modelo − medido (°C)", "#5b8def"),
                ("delta_t", "Delta T: modelo − medido (°C)", "#e08a1e"),
                ("vento", "Vento: modelo − medido (km/h)", COR_MOTIVO["vento"]))
    for j, (chave, nome, cor) in enumerate(receitas):
        ax = fig.add_subplot(grade[0, j])
        ph = verif["bruto"]["por_hora"].get(chave) or []
        ys = [p["vies"] for p in ph] if ph else []
        if ys and any(y is not None for y in ys):
            ax.bar(horas, [0 if y is None else y for y in ys], color=cor,
                   alpha=0.75, width=0.8, label="bruto")
        if verif.get("corrigido"):
            ph2 = verif["corrigido"]["por_hora"].get(chave) or []
            ys2 = [p["vies"] for p in ph2]
            if ys2 and any(y is not None for y in ys2):
                ax.plot(horas, [None if y is None else y for y in ys2],
                        color="#1d1d1b", lw=1.4, marker="o", ms=2.5,
                        label="corrigido")
        ax.axhline(0, color="#888", lw=0.8)
        ax.set_title(nome, fontsize=8.5, color="#444")
        ax.set_xticks(range(0, 24, 3))
        ax.set_xticklabels([f"{h:02d}h" for h in range(0, 24, 3)], fontsize=7)
        ax.tick_params(labelsize=7)
        ax.grid(True, axis="y", color="#e8e8e8", lw=0.7)
        ax.set_axisbelow(True)
        ax.legend(fontsize=7, frameon=False, loc="best")

    # --- acerto das horas aptas ---
    ax = fig.add_subplot(grade[1, 0])
    ax.axis("off")
    ab, ac = verif["acerto_bruto"], verif.get("acerto_corrigido")
    linhas = [["", "Modelo bruto", "Corrigido"]]

    def cel(t, k, pct=True):
        if not t or t.get(k) is None:
            return "—"
        return _pct(t[k]) if pct else str(t[k])

    for rotulo, k, pct in (("Horas aptas medidas", "aptas_obs", False),
                           ("Horas aptas no modelo", "aptas_mod", False),
                           ("Coincidiram", "acertos", False),
                           ("Acerto (POD)", "pod", True),
                           ("Alarme falso (FAR)", "far", True),
                           ("CSI", "csi", True)):
        linhas.append([rotulo, cel(ab, k, pct), cel(ac, k, pct)])
    prob = verif.get("probabilidade")
    if prob:
        linhas.append(["Brier (prob. vestida)", "—",
                       _fmt(prob["brier"], 3)])
        linhas.append(["Brier da climatologia", "—",
                       _fmt(prob["brier_clima"], 3)])
    tab = ax.table(cellText=linhas[1:], colLabels=linhas[0], loc="center",
                   cellLoc="center", colWidths=[0.46, 0.27, 0.27])
    tab.auto_set_font_size(False)
    tab.set_fontsize(7.5)
    for (i, j), c in tab.get_celld().items():
        c.set_edgecolor("#e4e2df")
        if i == 0:
            c.set_facecolor("#33302e")
            c.set_text_props(color="white", fontweight="bold")
    ax.set_title("Horas aptas: modelo × medido na área", fontsize=8.5,
                 color="#444")

    # --- antecedência ---
    ax1 = fig.add_subplot(grade[1, 1])
    ax2 = fig.add_subplot(grade[1, 2])
    if antecedencias:
        ns = [l["antecedencia"] for l in antecedencias]

        def serie_de(chave, sub):
            return [None if not l.get(chave) or l[chave].get(sub) is None
                    else l[chave][sub] for l in antecedencias]

        csi_b = [l["acerto_bruto"]["csi"] for l in antecedencias]
        csi_c = [l["acerto_corrigido"]["csi"] for l in antecedencias]
        ax1.plot(ns, [None if v is None else 100 * v for v in csi_b],
                 marker="o", color="#b0aca6", label="bruto")
        ax1.plot(ns, [None if v is None else 100 * v for v in csi_c],
                 marker="o", color=COR_MOTIVO["apto"], label="corrigido")
        arq = verif.get("arquivadas") or []
        if arq:
            ax1.plot([a["antecedencia"] for a in arq if a.get("csi") is not None],
                     [100 * a["csi"] for a in arq if a.get("csi") is not None],
                     marker="D", color="#26509c", label="previsões da ferramenta")
        ax1.set_ylim(0, 100)
        ax1.set_title("CSI das horas aptas por antecedência (%)",
                      fontsize=8.5, color="#444")
        ax2.plot(ns, serie_de("dt_bruto", "mae"), marker="o", color="#e0b27a",
                 label="Delta T bruto (°C)")
        ax2.plot(ns, serie_de("dt_corrigido", "mae"), marker="o",
                 color="#8a4f08", label="Delta T corrigido (°C)")
        ax2.plot(ns, serie_de("vento_bruto", "mae"), marker="s",
                 color="#e7a39c", label="vento bruto (km/h)")
        ax2.plot(ns, serie_de("vento_corrigido", "mae"), marker="s",
                 color=COR_MOTIVO["vento"], label="vento corrigido (km/h)")
        ax2.set_title("Erro médio absoluto por antecedência", fontsize=8.5,
                      color="#444")
        for ax in (ax1, ax2):
            ax.set_xticks(ns)
            ax.set_xticklabels([f"{n} d" for n in ns], fontsize=7)
            ax.tick_params(labelsize=7)
            ax.grid(True, color="#e8e8e8", lw=0.7)
            ax.set_axisbelow(True)
            ax.legend(fontsize=6.5, frameon=False, loc="best")
            ax.set_xlabel("dias de antecedência da rodada", fontsize=7.5)
    else:
        for ax in (ax1, ax2):
            ax.axis("off")
        ax1.text(0.0, 0.6, "Acerto por antecedência ainda não calculado.\n"
                           "Clique em “Verificar previsões passadas”: a "
                           "ferramenta busca\no que as rodadas de 1 a 7 dias "
                           "antes previam para as horas\nmedidas e mede o "
                           "acerto de cada uma.",
                 fontsize=8, color="#777", va="top", transform=ax1.transAxes)

    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.06, ha="left")
    fig.subplots_adjust(left=0.06, right=0.98, top=0.90, bottom=0.08)


# =====================================================================
# BLOCO 8C — DIREÇÃO DO VENTO
# =====================================================================
#
# A velocidade diz QUANTO a gota deriva; a direção diz PARA ONDE — e é a
# direção que decide se a deriva cai no pasto do vizinho, na lavoura
# sensível ou na mata ciliar. Três cuidados:
#
# 1. Direção é variável circular. A média de 350° e 10° é 0°, não 180°.
#    Por isso nada aqui tira média de ângulo: o vento é decomposto nas
#    componentes u (leste) e v (norte), as componentes é que são
#    interpoladas e promediadas, e a direção é recomposta no fim.
# 2. A convenção meteorológica dá a direção DE ONDE o vento vem (vento
#    "de SE" sopra para NO). A deriva vai para o lado oposto. As setas
#    dos gráficos apontam para onde a gota vai, que é o que interessa em
#    campo, e os textos dizem as duas coisas.
# 3. A média vetorial vem com a constância: o comprimento do vetor médio
#    dividido pela velocidade média. Perto de 1, o vento soprou sempre do
#    mesmo lado; perto de 0, girou — e a direção média não quer dizer nada.

SETORES_16 = ("N", "NNE", "NE", "ENE", "L", "ESE", "SE", "SSE",
              "S", "SSO", "SO", "OSO", "O", "ONO", "NO", "NNO")
FAIXAS_ROSA = (0.0, 3.0, 7.0, 10.0, 15.0, float("inf"))
ROTULOS_ROSA = ("< 3", "3–7", "7–10", "10–15", "> 15")
CORES_ROSA = ("#d9d6d0", "#8dc26f", "#2e7d32", "#e08a1e", "#c81010")


def rumo(graus):
    """Nome do rumo em 16 setores (L = leste, O = oeste)."""
    if graus is None:
        return "—"
    return SETORES_16[int(((graus % 360) + 11.25) // 22.5) % 16]


def componentes(vel, direcao):
    """(u, v) do vento que vem de `direcao` graus com velocidade `vel`."""
    rad = math.radians(direcao)
    return -vel * math.sin(rad), -vel * math.cos(rad)


def direcao_das_componentes(u, v):
    """Direção de onde o vento vem, em graus, a partir de (u, v)."""
    if u is None or v is None or math.hypot(u, v) < 1e-9:
        return None
    return (math.degrees(math.atan2(-u, -v)) + 360.0) % 360.0


def texto_direcao(graus, constancia=None):
    """'de SE (128°) → deriva para NO'."""
    if graus is None:
        return "direção indefinida"
    texto = f"de {rumo(graus)} ({graus:.0f}°) → deriva para {rumo(graus + 180)}"
    if constancia is not None:
        texto += f", constância {_fmt(constancia, 2)}"
    return texto


def media_vetorial(linhas, pesos=None, chave_v="vento", chave_d="direcao"):
    """Direção média, constância e velocidades média vetorial e escalar.

    Devolve (direção, constância, vel_vetorial, vel_escalar, n). Horas de
    calmaria entram com vetor zero: puxam a constância para baixo, que é
    o certo — vento que ora sopra, ora para, não é vento firme.
    """
    su = sv = sw = sesc = 0.0
    n = 0
    for i, l in enumerate(linhas):
        vel, d = l.get(chave_v), l.get(chave_d)
        if vel is None:
            continue
        w = 1.0 if pesos is None else pesos[i]
        if d is None:
            if vel > 0.5:
                continue          # soprou mas sem direção registrada
            u = v = 0.0
        else:
            u, v = componentes(vel, d)
        su += w * u
        sv += w * v
        sesc += w * vel
        sw += w
        n += 1
    if not sw:
        return None, None, None, None, 0
    u, v = su / sw, sv / sw
    vetorial = math.hypot(u, v)
    escalar = sesc / sw
    direcao = direcao_das_componentes(u, v) if vetorial > 0.3 else None
    constancia = vetorial / escalar if escalar > 0 else None
    return direcao, constancia, vetorial, escalar, n


def rosa_dos_ventos(serie, crit=None, so_aptas=False):
    """Contagem de horas por setor (16) e faixa de velocidade (5).

    A velocidade é a da série já preparada, isto é, na altura de
    aplicação. Horas de calmaria sem direção ficam de fora da rosa mas
    são contadas à parte.
    """
    contagem = np.zeros((16, len(ROTULOS_ROSA)))
    calmas = 0
    for ts, l in serie.items():
        if so_aptas and (crit is None or not e_apto(classificar(l, crit))):
            continue
        vel, d = l.get("vento"), l.get("direcao")
        if vel is None:
            continue
        if d is None:
            calmas += 1
            continue
        setor = int(((d % 360) + 11.25) // 22.5) % 16
        faixa = next(i for i in range(len(ROTULOS_ROSA))
                     if FAIXAS_ROSA[i] <= vel < FAIXAS_ROSA[i + 1])
        contagem[setor, faixa] += 1
    return contagem, calmas


def _desenhar_rosa(ax, contagem, calmas, titulo):
    """Rosa dos ventos: de onde o vento veio, empilhado por velocidade."""
    total = contagem.sum() + calmas
    ax.set_theta_zero_location("N")
    ax.set_theta_direction(-1)
    if total <= 0:
        ax.set_title(f"{titulo}\n(sem horas)", fontsize=8.5, color="#444",
                     pad=14)
        ax.set_yticklabels([])
        return
    largura = 2 * math.pi / 16 * 0.9
    angulos = np.radians(np.arange(16) * 22.5)
    base = np.zeros(16)
    for j in range(contagem.shape[1]):
        alturas = 100 * contagem[:, j] / total
        if alturas.any():
            ax.bar(angulos, alturas, width=largura, bottom=base,
                   color=CORES_ROSA[j], edgecolor="white", linewidth=0.5,
                   label=f"{ROTULOS_ROSA[j]} km/h")
        base += alturas
    ax.set_xticks(np.radians(np.arange(0, 360, 45)))
    ax.set_xticklabels(["N", "NE", "L", "SE", "S", "SO", "O", "NO"],
                       fontsize=7.5)
    ax.tick_params(axis="y", labelsize=6.5, colors="#888")
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:.0f}%"))
    ax.set_rlabel_position(112.5)
    ax.grid(color="#dddddd", lw=0.6)
    extra = (f"\n{100 * calmas / total:.0f}% de calmaria"
             if calmas else "")
    ax.set_title(f"{titulo}{extra}", fontsize=8, color="#444", pad=10)


def _grade_de_setas(ax, serie, crit, fuso=None):
    """Hora × dia com uma seta por célula, apontando para onde vai a deriva.

    A cor da seta é a da classificação da hora (verde = apta), então a
    figura responde de uma vez: nas horas boas, para que lado a gota vai.
    """
    ts = sorted(serie)
    dias = sorted({t.date() for t in ts})
    col = {d: i for i, d in enumerate(dias)}
    xs, ys, us, vs, cores = [], [], [], [], []
    calmas_x, calmas_y = [], []
    for t in ts:
        l = serie[t]
        motivo = classificar(l, crit)
        p = l.get("p_apto")
        if p is not None and crit.get("limiar_p") is not None:
            cor = COR_FAIXA_P.get(faixa_probabilidade(p), "#999")
        else:
            cor = COR_MOTIVO.get(motivo, "#999")
        d = l.get("direcao")
        if d is None:
            if l.get("vento") is not None:
                calmas_x.append(col[t.date()])
                calmas_y.append(t.hour)
            continue
        para = math.radians(d + 180.0)
        xs.append(col[t.date()])
        ys.append(t.hour)
        us.append(math.sin(para))
        vs.append(math.cos(para))
        cores.append(cor)

    ax.set_facecolor("#f7f6f4")
    if xs:
        # comprimento em fração da largura do eixo: cabe na célula tanto na
        # horizontal (1 dia) quanto na vertical (cerca de 2 horas)
        fig = ax.get_figure()
        pos = ax.get_position()
        larg = max(pos.width * fig.get_size_inches()[0], 0.1)
        alt = max(pos.height * fig.get_size_inches()[1], 0.1)
        comprimento = min(0.85 / max(1, len(dias)), 2.0 / 24 * alt / larg)
        ax.quiver(xs, ys, us, vs, color=cores, angles="uv", pivot="middle",
                  scale=1.0 / comprimento, scale_units="width", width=0.0026,
                  headwidth=4.0, headlength=4.2, headaxislength=3.8)
    if calmas_x:
        ax.scatter(calmas_x, calmas_y, s=6, c="#9a9a9e", zorder=3)
    ax.set_xlim(-0.6, len(dias) - 0.4)
    ax.set_ylim(-0.6, 23.6)
    ax.set_xticks(range(len(dias)))
    ax.set_xticklabels([d.strftime("%d/%m") for d in dias], fontsize=7,
                       rotation=90 if len(dias) > 10 else 0)
    ax.set_yticks(range(0, 24, 2))
    ax.set_yticklabels([f"{h:02d}h" for h in range(0, 24, 2)], fontsize=7.5)
    ax.set_ylabel("Hora do dia", fontsize=8)
    ax.grid(True, color="white", lw=0.8)
    ax.set_axisbelow(True)


def _mapa_de_setas(ax, pontos, area=None, potencia=2.0, em_km=True,
                   serie=None, crit=None):
    """Vento médio do período: fundo com a velocidade, setas com a direção.

    As setas da grade vêm das componentes interpoladas (IDW de u e de v),
    nunca de ângulo interpolado. As das estações são o vetor médio de
    cada uma. Na área, a seta larga mostra para onde foi a deriva nas
    horas aptas.
    """
    validos = [p for p in pontos if p.get("u") is not None]
    ext = extensao_comum(pontos, area)
    grade_v = grade_idw(pontos, "vento", 80, potencia, em_km, extensao=ext)
    if grade_v is not None:
        sup = ax.contourf(grade_v["gx"], grade_v["gy"], grade_v["z"],
                          levels=_niveis(float(grade_v["z"].min()),
                                         float(grade_v["z"].max())),
                          cmap=ESCALA_VENTO, alpha=0.55)
    else:
        sup = None
    if len(validos) >= 2:
        gu = grade_idw(validos, "u", 12, potencia, em_km, extensao=ext)
        gv = grade_idw(validos, "v", 12, potencia, em_km, extensao=ext)
        X, Y = np.meshgrid(gu["gx"], gu["gy"])
        mod = np.hypot(gu["z"], gv["z"])
        escala = max(float(mod.max()), 0.1)
        # seta para onde o ar vai: é exatamente o vetor (u, v)
        ax.quiver(X, Y, gu["z"] / escala, gv["z"] / escala, color="#33302e",
                  alpha=0.55, angles="uv", pivot="middle", scale=22,
                  width=0.0028)
    for p in validos:
        vel = math.hypot(p["u"], p["v"])
        if vel > 0.05:
            ax.quiver([p["lon"]], [p["lat"]], [p["u"] / vel], [p["v"] / vel],
                      color="#1d1d1b", angles="uv", pivot="middle", scale=11,
                      width=0.007, zorder=6)
        ax.annotate(f'{p["nome"][:16]}\nde {rumo(p.get("direcao"))} · '
                    f'{_fmt(p.get("constancia"), 2)}',
                    (p["lon"], p["lat"]), textcoords="offset points",
                    xytext=(0, -22), ha="center", fontsize=6.5, zorder=7,
                    bbox=dict(boxstyle="round,pad=0.18", fc="white",
                              ec="none", alpha=0.8))
    for p in pontos:
        if p.get("u") is None:
            ax.scatter([p["lon"]], [p["lat"]], s=30, c="#9a9a9e", zorder=5)
            ax.annotate(f'{p["nome"][:16]}\nsem direção',
                        (p["lon"], p["lat"]), textcoords="offset points",
                        xytext=(0, -20), ha="center", fontsize=6.5,
                        color="#777", zorder=7)
    if area:
        ax.scatter([area[1]], [area[0]], marker="X", s=130, c=COR_AREA,
                   edgecolors="white", linewidths=1.6, zorder=8)
        if serie and crit:
            aptas = [l for l in serie.values() if e_apto(classificar(l, crit))]
            d, cst, *_ = media_vetorial(aptas)
            if d is not None:
                para = math.radians(d + 180)
                ax.quiver([area[1]], [area[0]], [math.sin(para)],
                          [math.cos(para)], color=COR_AREA, angles="uv",
                          pivot="tail", scale=7, width=0.012, zorder=9)
                ax.annotate(f"deriva nas horas aptas → {rumo(d + 180)}",
                            (area[1], area[0]), textcoords="offset points",
                            xytext=(8, 10), fontsize=7, color=COR_AREA,
                            fontweight="bold", zorder=9)
    if ext:
        ax.set_xlim(ext[0], ext[1])
        ax.set_ylim(ext[2], ext[3])
    ax.set_aspect("equal", adjustable="box")
    ax.tick_params(labelsize=7)
    ax.set_title("Vento médio do período\n(fundo: velocidade · seta: para "
                 "onde vai a deriva)", fontsize=8.5, color="#444")
    return sup


def desenhar_direcao(fig, serie, crit, pontos=None, area=None, titulo="",
                     potencia=2.0, em_km=True, topo=0.86):
    """Página da direção: mapa (se houver estações), duas rosas e a grade.

    Rosa de todas as horas e rosa só das horas aptas lado a lado: a
    diferença entre as duas é a informação. O vento do período pode ser de
    leste, e o das horas em que se aplica ser de sudeste.
    """
    fig.clear()
    if not serie or not any(l.get("direcao") is not None
                            for l in serie.values()):
        _sem_dados(fig, "Sem direção do vento nesta série.\n\nA direção vem "
                        "com o download do modelo e com as tabelas do INMET;"
                        "\nbaixe de novo para ela aparecer.")
        return

    com_mapa = bool(pontos) and sum(1 for p in pontos
                                    if p.get("u") is not None) >= 2
    grade = fig.add_gridspec(2, 3, height_ratios=[1.05, 1], hspace=0.50,
                             wspace=0.30, left=0.06, right=0.95, top=topo,
                             bottom=0.10)
    if com_mapa:
        ax_m = fig.add_subplot(grade[0, 0])
        sup = _mapa_de_setas(ax_m, pontos, area, potencia, em_km, serie, crit)
        if sup is not None:
            barra = fig.colorbar(sup, ax=ax_m, fraction=0.046, pad=0.03)
            barra.ax.tick_params(labelsize=6.5, length=2)
            barra.outline.set_visible(False)
            _formata_barra(barra, 0)
        ax_r1 = fig.add_subplot(grade[0, 1], projection="polar")
        ax_r2 = fig.add_subplot(grade[0, 2], projection="polar")
    else:
        ax_r1 = fig.add_subplot(grade[0, 0], projection="polar")
        ax_r2 = fig.add_subplot(grade[0, 1], projection="polar")
        ax_txt = fig.add_subplot(grade[0, 2])
        ax_txt.axis("off")

    cont, calm = rosa_dos_ventos(serie)
    _desenhar_rosa(ax_r1, cont, calm, "Todas as horas — de onde vem")
    cont_a, calm_a = rosa_dos_ventos(serie, crit, so_aptas=True)
    _desenhar_rosa(ax_r2, cont_a, calm_a, "Só as horas aptas — de onde vem")
    if ax_r2.get_legend_handles_labels()[0] or ax_r1.get_legend_handles_labels()[0]:
        fonte_leg = ax_r2 if ax_r2.get_legend_handles_labels()[0] else ax_r1
        h, l = fonte_leg.get_legend_handles_labels()
        ax_r2.legend(h, l, loc="upper center", bbox_to_anchor=(0.5, -0.10),
                     ncol=min(3, len(h)), fontsize=6.5, frameon=False,
                     title="vento na altura de aplicação (km/h)",
                     title_fontsize=6.5, handlelength=1.2, columnspacing=0.8)

    todas = list(serie.values())
    aptas = [l for l in todas if e_apto(classificar(l, crit))]
    d_all, c_all, *_ = media_vetorial(todas)
    d_apt, c_apt, *_ = media_vetorial(aptas)
    resumo = [f"Período: {texto_direcao(d_all, c_all)}",
              f"Horas aptas: {texto_direcao(d_apt, c_apt)}"
              if aptas else "Horas aptas: nenhuma"]
    if not com_mapa:
        import textwrap
        ax_txt.text(0.0, 0.85, "\n\n".join(textwrap.fill(t, 42) for t in resumo),
                    fontsize=8, va="top", color="#333")

    ax_g = fig.add_subplot(grade[1, :])
    _grade_de_setas(ax_g, serie, crit)
    titulo_g = ("Seta = para onde o vento leva a gota, hora a hora · cor = "
                "condição da hora (verde = apta) · ponto cinza = calmaria")
    if com_mapa:
        titulo_g += "\n" + "   ·   ".join(resumo)
    ax_g.set_title(titulo_g, fontsize=7.8, color="#555", loc="left")

    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.06, ha="left",
                     y=0.985)


def direcao_por_hora(serie, crit=None, so_aptas=False):
    """Vetor médio de cada hora do dia ao longo do período."""
    saida = []
    for h in range(24):
        ls = [l for ts, l in serie.items() if ts.hour == h
              and (not so_aptas or e_apto(classificar(l, crit)))]
        d, c, _, esc, n = media_vetorial(ls)
        saida.append({"hora": h, "direcao": d, "constancia": c,
                      "vento": esc, "n": n})
    return saida


# =====================================================================
# BLOCO 8D — MONTAGEM DO HISTÓRICO E DA PREVISÃO
# =====================================================================
#
# As abas 2, 3, 4 e 5 fazem a mesma sequência — baixar, corrigir,
# interpolar, classificar — com fontes diferentes. Ela mora aqui, uma vez
# só, para as quatro não divergirem: o relatório tem de dizer exatamente
# o que a tela mostrou.

ARQUIVO_PREFERENCIAS = "preferencias.json"


def ler_preferencias():
    """Critérios da última vez, para não ter de redigitar a cada sessão."""
    if os.environ.get("JANELA_SEM_PREFERENCIAS"):
        return {}
    try:
        with open(caminho_ao_lado(ARQUIVO_PREFERENCIAS), encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def gravar_preferencias(chave, valores):
    if os.environ.get("JANELA_SEM_PREFERENCIAS"):
        return
    d = ler_preferencias()
    d[chave] = valores
    try:
        with open(caminho_ao_lado(ARQUIVO_PREFERENCIAS), "w",
                  encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
    except Exception:
        pass


def preferencias_da_tela(alvo, extras=()):
    """Lê os campos de critério de uma aba, como texto, para guardar."""
    campos = {"dt_min": "var_dtmin", "dt_max": "var_dtmax",
              "vento_min": "var_vmin", "vento_max": "var_vmax",
              "rajada": "var_rajada", "rainfast": "var_rainfast",
              "altura": "var_altura", "z0": "var_z0",
              "inversao": "var_inversao", "bulbo": "var_bulbo"}
    campos.update(dict(extras))
    saida = {}
    for chave, nome in campos.items():
        var = getattr(alvo, nome, None)
        if var is not None and var.get() is not None:
            saida[chave] = str(var.get())
    return saida


def _copia_calibracao(cal):
    return json.loads(json.dumps(cal or {"versao": 2, "estacoes": {}}))


def montar_historico(alvo, ini, fim, fuso, crit, lat, lon, fonte=FONTE_MODELO,
                     metodo=METODO_IDW, medidos=None, calibracao=None,
                     token=None, avisar=None, recuar=False):
    """Histórico da área, da fonte escolhida. Devolve um dicionário.

    Com a fonte medida, faz ainda a conferência: baixa o modelo nas
    mesmas estações, guarda os pares medido × modelo na calibração (uma
    cópia, que quem chamou decide gravar) e compara as duas áreas.
    """
    avisar = avisar or (lambda texto: None)
    medidos = medidos or {}
    falhas = []
    r = {"fonte": fonte, "metodo": metodo, "falhas": falhas, "verif": None,
         "calibracao": None, "pares": {}, "preenchidas": 0, "medidas": {},
         "novos_dias": 0, "modelo": {}, "pesos": {}}

    if fonte == FONTE_MEDIDO:
        cobre = [p for p in alvo if p["codigo"] in medidos
                 and recortar(medidos[p["codigo"]]["serie"], ini, fim)]
        if not cobre:
            if not recuar:
                raise RuntimeError(
                    "Nenhuma das estações escolhidas tem tabela do INMET "
                    "carregada que cubra esse período.\n\nCarregue as "
                    "tabelas (botão “Carregar tabelas do INMET”) ou troque a "
                    "fonte para o modelo.")
            tem_cal = combinar_coeficientes(
                coeficientes_da_calibracao(calibracao), alvo)
            fonte = FONTE_CORRIGIDO if tem_cal else FONTE_MODELO
            falhas.append("sem tabela medida para estas estações — usei "
                          + fonte[0].lower() + fonte[1:])
            r["fonte"] = fonte

    if metodo == METODO_PONTO and fonte in (FONTE_MODELO, FONTE_CORRIGIDO) \
            and lat is not None:
        # o modelo já entrega o valor na coordenada, com relevo e cobertura
        # do terreno embutidos — não há o que interpolar
        avisar("Baixando a série no ponto da área…")
        bruta = baixar_open_meteo(lat, lon, ini, fim, fuso)
        avisar("Buscando a altitude da área…")
        alt, origem_alt = buscar_altitude(lat, lon)
        base = {ts: dict(l) for ts, l in bruta.items()}
        if fonte == FONTE_CORRIGIDO:
            coef = combinar_coeficientes(
                coeficientes_da_calibracao(calibracao), alvo)
            if coef:
                aplicar_calibracao(base, coef)
            else:
                falhas.append("sem calibração para estas estações — série "
                              "sem correção")
        serie = fechar_criterios(serie_do_ponto(base), crit, alt)
        r.update(serie=serie, janelas=encontrar_janelas(serie, crit),
                 series={"PONTO": bruta}, usadas=[], alt=(alt, origem_alt))
        return r

    modelo = {}
    if fonte != FONTE_API:
        for i, p in enumerate(alvo):
            avisar(f"Baixando o modelo em {p['nome']} ({i + 1} de {len(alvo)})…")
            try:
                s = baixar_open_meteo(p["lat"], p["lon"], ini, fim, fuso)
                if not s:
                    raise RuntimeError("série vazia")
                modelo[p["codigo"]] = s
            except Exception as e:
                falhas.append(f"{p['nome']}: {e}")
    r["modelo"] = modelo

    medidas = {}
    if fonte == FONTE_API:
        series = {}
        for i, p in enumerate(alvo):
            avisar(f"Baixando {p['nome']} do INMET ({i + 1} de {len(alvo)})…")
            try:
                series[p["codigo"]] = baixar_inmet(p["codigo"], ini, fim,
                                                   token, fuso)
            except Exception as e:
                falhas.append(f"{p['nome']}: {e}")
    elif fonte == FONTE_MODELO:
        series = modelo
    elif fonte == FONTE_CORRIGIDO:
        coefs = coeficientes_da_calibracao(calibracao)
        sem = [p["nome"] for p in alvo
               if p["codigo"] in modelo and not coefs.get(p["codigo"])]
        if sem:
            falhas.append("sem calibração, entraram sem correção: "
                          + ", ".join(sem))
        series = corrigir_series(modelo, coefs)
    else:
        cal = _copia_calibracao(calibracao)
        for p in alvo:
            cod = p["codigo"]
            if cod not in medidos:
                continue
            obs = recortar(medidos[cod]["serie"], ini, fim)
            if not obs:
                continue
            medidas[cod] = obs
            if cod in modelo:
                r["novos_dias"] += somar_pares(
                    cal, cod, p["nome"], pares_da_estacao(obs, modelo[cod]))
        coefs = coeficientes_da_calibracao(cal)
        series = {}
        for cod, obs in medidas.items():
            s, n = completar_com_modelo(obs, modelo.get(cod), coefs.get(cod))
            series[cod] = s
            r["preenchidas"] += n
        fora = [p["nome"] for p in alvo if p["codigo"] not in medidas]
        if fora:
            falhas.append("sem tabela medida, ficaram de fora: "
                          + ", ".join(fora))
        r["calibracao"] = cal
        r["pares"] = {cod: cal["estacoes"][cod]["pares"] for cod in medidas
                      if cod in cal.get("estacoes", {})}
        r["medidas"] = medidas

    if not series:
        raise RuntimeError("Nenhuma estação retornou dados.\n\n"
                           + "\n".join(falhas))

    usadas = [p for p in alvo if p["codigo"] in series]
    avisar("Buscando a altitude da área…")
    alt, origem_alt = buscar_altitude(lat, lon, usadas)
    serie = fechar_criterios(interpolar_area(series, usadas, alt), crit, alt)
    r.update(serie=serie, janelas=encontrar_janelas(serie, crit),
             series=series, usadas=usadas, alt=(alt, origem_alt),
             pesos=pesos_idw(usadas))

    if fonte == FONTE_MEDIDO and medidas and modelo:
        avisar("Comparando o modelo com o que as estações mediram…")
        mod_masc = {cod: mascarar_como(modelo[cod], medidas[cod])
                    for cod in medidas if cod in modelo}
        est_v = [p for p in usadas if p["codigo"] in mod_masc]
        if est_v:
            so_medido = {cod: completar_com_modelo(medidas[cod], modelo[cod],
                                                   None, preencher=False)[0]
                         for cod in mod_masc}
            obs_area = fechar_criterios(interpolar_area(so_medido, est_v, alt),
                                        dict(crit), alt)
            mod_area = fechar_criterios(interpolar_area(mod_masc, est_v, alt),
                                        dict(crit), alt)
            cor = {cod: corrigir_por_dia(m, r["pares"].get(cod) or {})
                   for cod, m in mod_masc.items()}
            cor_area = fechar_criterios(interpolar_area(cor, est_v, alt),
                                        dict(crit), alt)
            r["verif"] = verificar_historico(obs_area, mod_area, cor_area, crit)
            r["obs_area"] = obs_area
            r["est_verif"] = est_v
            # o erro que sobra, por bloco do dia, vira o "vestido" da previsão
            res = residuos_por_bloco(obs_area, cor_area, crit)
            res["estacoes"] = [e["codigo"] for e in est_v]
            res["periodo"] = [ini, fim]
            if r.get("calibracao") is not None:
                r["calibracao"]["residuos"] = res
            crit_p = dict(crit, residuos=res)
            vest = vestir_serie({ts: dict(l) for ts, l in cor_area.items()},
                                crit_p)
            r["verif"]["probabilidade"] = avaliar_probabilidades(
                obs_area, vest, crit)
            r["verif"]["residuos"] = res
            arquivadas = carregar_arquivo_previsoes(lat, lon)
            if arquivadas:
                r["verif"]["arquivadas"] = verificar_arquivo(obs_area, crit,
                                                              arquivadas)
                r["verif"]["n_arquivadas"] = len(arquivadas)
    return r


def texto_fonte(r):
    """Primeira linha do resumo: de onde veio o histórico."""
    fonte = r.get("fonte")
    if fonte == FONTE_MEDIDO:
        n = len(r.get("medidas") or {})
        texto = (f"Fonte: MEDIDO em {n} estação(ões) do INMET (tabelas "
                 "carregadas)")
        if r.get("preenchidas"):
            texto += (f"; {r['preenchidas']} horas sem medição completadas "
                      "com o modelo corrigido")
        return texto + "."
    if fonte == FONTE_CORRIGIDO:
        return ("Fonte: modelo (Open-Meteo) nas estações, corrigido pela "
                "calibração local contra o medido.")
    if fonte == FONTE_API:
        return "Fonte: INMET pela API (medido)."
    return ("Fonte: modelo (Open-Meteo) nas estações, sem correção — é "
            "reanálise, não medição.")


def montar_previsao(alvo, dias, fuso, crit, metodo, lat, lon,
                    conjunto=MODO_ENSEMBLE, calibracao=None, corrigir=True,
                    avisar=None):
    """Previsão da área, com a calibração local aplicada antes do critério.

    A correção entra em cada rodada do conjunto, antes de o critério ser
    avaliado nela — corrigir a probabilidade depois não teria sentido.
    """
    avisar = avisar or (lambda texto: None)
    avisos = []
    coefs = coeficientes_da_calibracao(calibracao) if corrigir else {}
    coef_area = combinar_coeficientes(coefs, alvo) if coefs else None
    if not corrigir:
        correcao = "Previsão sem correção local (desligada)."
    elif coef_area:
        correcao = resumo_calibracao(calibracao, alvo)[1]
    else:
        correcao = ("Sem calibração local para estas estações — previsão "
                    "sem correção. Carregue as tabelas do INMET na aba 2 "
                    "para criá-la.")
    r = {"avisos": avisos, "metodo": metodo, "conjunto": None,
         "correcao": correcao, "corrigida": bool(coef_area), "pesos": {}}
    # o erro típico que sobra da calibração, medido nesta área (ou o padrão)
    crit["residuos"] = residuos_da_calibracao(calibracao, alvo) \
        if corrigir else None

    if metodo == METODO_PONTO and lat is not None:
        avisar("Buscando a previsão no ponto da área…")
        bruta = baixar_previsao(lat, lon, dias, fuso)
        alt, origem_alt = buscar_altitude(lat, lon)
        base = {ts: dict(l) for ts, l in bruta.items()}
        if coef_area:
            aplicar_calibracao(base, coef_area)
        r.update(por_estacao={"PONTO": bruta}, alt=(alt, origem_alt))

        if conjunto == MODO_ENSEMBLE:
            avisar("Baixando o conjunto — são dezenas de rodadas, leva "
                   "alguns segundos…")
            try:
                membros, modelos = baixar_ensemble(lat, lon, dias, fuso)
                if coef_area:
                    for m in membros:
                        aplicar_calibracao(m, coef_area)
                if crit.get("usar_psicrometrico"):
                    crit["pressao_hpa"] = pressao_na_altitude(alt)
                crit["margem_dt"] = crit["margem_vento"] = 0.0
                determinista = fechar_criterios(serie_do_ponto(base),
                                                dict(crit), alt)
                serie = analisar_ensemble(membros, crit, alt, determinista)
                r.update(serie=serie, janelas=encontrar_janelas(serie, crit),
                         crit=crit, conjunto={"membros": len(membros),
                                              "modelos": modelos})
                return r
            except Exception as e:
                # sem conjunto ainda dá para entregar a rodada única, desde
                # que fique dito que a confiança não foi medida
                avisos.append(f"conjunto indisponível ({e}); caiu para a "
                              "rodada única")
                crit.pop("limiar_p", None)

        serie = vestir_serie(fechar_criterios(serie_do_ponto(base), crit, alt),
                             crit)
        r.update(serie=serie, janelas=encontrar_janelas(serie, crit), crit=crit)
        return r

    series = {}
    for i, p in enumerate(alvo):
        avisar(f"Previsão de {p['nome']} ({i + 1} de {len(alvo)})…")
        try:
            s = baixar_previsao(p["lat"], p["lon"], dias, fuso)
            if not s:
                raise RuntimeError("previsão vazia")
            series[p["codigo"]] = s
        except Exception as e:
            avisos.append(f"{p['nome']}: {e}")
    if not series:
        raise RuntimeError("Nenhum ponto retornou previsão.\n\n"
                           + "\n".join(avisos))
    if coefs:
        series = corrigir_series(series, coefs)
    usadas = [p for p in alvo if p["codigo"] in series]
    alt, origem_alt = buscar_altitude(lat, lon, usadas)
    serie = fechar_criterios(
        interpolar_area(series, usadas, alt, CAMPOS_PREVISAO), crit, alt)
    crit.pop("limiar_p", None)   # IDW entre estações não é conjunto
    vestir_serie(serie, crit)
    r.update(serie=serie, janelas=encontrar_janelas(serie, crit), crit=crit,
             por_estacao=series, pesos=pesos_idw(usadas),
             alt=(alt, origem_alt))
    return r


# =====================================================================
# BLOCO 8E — MEDIÇÃO DE CAMPO
# =====================================================================
#
# A estação mais próxima está a 44 km. A única medição que representa o
# talhão é a feita no talhão: termo-higrômetro e anemômetro de mão (ou
# Kestrel) na hora da aplicação. Poucas leituras bastam para dizer se a
# estimativa da ferramenta está deslocada NAQUELE lugar — é o que a
# estação não consegue dizer.
#
# Formato aceito (CSV com ; ou ,): uma linha por leitura, com
#   Data; Hora; Temp_C; UR_pct; Vento_kmh; Direcao_graus; Altura_m; Obs
# Hora em horário local. Direção é DE ONDE o vento vem, como a biruta
# aponta. Altura é a do anemômetro (padrão 2 m). Colunas extras são
# ignoradas; os nomes aceitam variações (temperatura, umidade, wind...).

MODELO_CAMPO = ("Data;Hora;Fim;Avaliacao;Temp_C;UR_pct;Vento_kmh;Direcao_graus;"
                "Altura_m;Obs\n"
                "24/09/2026;17:00;20:00;boa;;;;;;janela muito boa na área\n"
                "23/09/2026;08:10;;;25,1;78;4,2;120;2;leitura antes do 1o voo\n"
                "23/09/2026;10:05;;;28,4;61;6,8;135;2;\n")

_CABECALHOS_CAMPO = (
    ("data", ("data", "date", "dia")),
    ("fim", ("fim", "hora_fim", "hora fim", "ate", "termino", "end")),
    ("avaliacao", ("avaliacao", "qualidade", "resultado", "condicao",
                   "janela")),
    ("hora", ("hora", "time", "horario", "inicio")),
    ("temp", ("temp", "temperatura", "t_c", "temperature")),
    ("ur", ("ur", "umidade", "rh", "relative humidity", "umi")),
    ("vento", ("vento", "wind speed", "velocidade", "wind")),
    ("direcao", ("direcao", "dir", "direction", "rumo")),
    ("altura", ("altura", "height", "alt")),
)


def ler_medicao_campo(caminho):
    """Lê as leituras de campo. Devolve a lista de dicionários."""
    bruto = open(caminho, "rb").read()
    for cod in ("utf-8-sig", "latin-1"):
        try:
            texto = bruto.decode(cod)
            break
        except UnicodeDecodeError:
            continue
    linhas = [l for l in texto.splitlines() if l.strip()]
    if not linhas:
        raise ValueError("arquivo vazio")
    sep = ";" if linhas[0].count(";") >= linhas[0].count(",") else ","
    tabela = list(csv.reader(linhas, delimiter=sep, quotechar='"'))
    nomes = [_sem_acento(c) for c in tabela[0]]
    col = {}
    for chave, prefixos in _CABECALHOS_CAMPO:
        for i, n in enumerate(nomes):
            if i not in col.values() and any(n.startswith(p) for p in prefixos):
                col[chave] = i
                break
    if "data" not in col or not ({"temp", "vento", "avaliacao"} & set(col)):
        raise ValueError("preciso de pelo menos Data, Hora e temperatura, "
                         "vento ou a avaliação da janela — veja o modelo de "
                         "planilha")

    leituras = []
    for linha in tabela[1:]:
        def pega(chave):
            i = col.get(chave)
            return _num(linha[i]) if i is not None and i < len(linha) else None
        data = linha[col["data"]].strip() if col["data"] < len(linha) else ""
        hora = (linha[col["hora"]].strip()
                if "hora" in col and col["hora"] < len(linha) else "")
        if " " in data and not hora:
            data, hora = data.split(" ", 1)
        ts = None
        for fmt in ("%d/%m/%Y %H:%M", "%d/%m/%Y %H:%M:%S", "%Y-%m-%d %H:%M",
                    "%Y-%m-%d %H:%M:%S", "%d/%m/%y %H:%M"):
            try:
                ts = datetime.strptime(f"{data} {hora}".strip(), fmt)
                break
            except ValueError:
                continue
        if ts is None:
            continue
        fim = None
        if "fim" in col and col["fim"] < len(linha) and linha[col["fim"]].strip():
            try:
                hf = datetime.strptime(linha[col["fim"]].strip()[:5], "%H:%M")
                fim = ts.replace(hour=hf.hour, minute=hf.minute)
                if fim <= ts:
                    fim += timedelta(days=1)
                fim = fim.replace(tzinfo=timezone.utc)
            except ValueError:
                fim = None
        aval = (_avaliacao(linha[col["avaliacao"]])
                if "avaliacao" in col and col["avaliacao"] < len(linha) else None)
        leituras.append({
            "ts": ts.replace(tzinfo=timezone.utc),      # local, rotulado UTC
            "temp": pega("temp"), "ur": pega("ur"), "vento": pega("vento"),
            "direcao": pega("direcao"), "altura": pega("altura") or 2.0,
            "fim": fim, "avaliacao": aval,
        })
    if not leituras:
        raise ValueError("nenhuma linha com data e hora legíveis")
    return sorted(leituras, key=lambda l: l["ts"])


def comparar_campo(leituras, serie, crit):
    """Estimativa da ferramenta contra a leitura no talhão.

    Cada leitura é comparada com a hora cheia mais próxima da série. O
    vento lido na altura do anemômetro é levado à altura do critério pelo
    mesmo perfil logarítmico, para comparar coisa com coisa.
    """
    z0 = crit.get("z0", RUGOSIDADE)
    alvo = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA), z0)
    janelas = comparar_janelas_campo(leituras, serie, crit)
    leituras = [l for l in leituras
                if any(l.get(k) is not None for k in ("temp", "vento", "direcao"))]
    pares = []
    for l in leituras:
        ts = (l["ts"] + timedelta(minutes=30)).replace(minute=0, second=0,
                                                       microsecond=0)
        s = serie.get(ts)
        if not s:
            continue
        dt_campo = (delta_t(l["temp"], l["ur"], crit.get("pressao_hpa"))
                    if l.get("temp") is not None and l.get("ur") is not None
                    else None)
        v_campo = None
        if l.get("vento") is not None:
            v_campo = l["vento"] * alvo / fator_altura_vento(l["altura"], z0)
        dif_dir = None
        if l.get("direcao") is not None and s.get("direcao") is not None:
            dif_dir = (s["direcao"] - l["direcao"] + 180) % 360 - 180
        linha_campo = dict(s, delta_t=dt_campo if dt_campo is not None
                           else s.get("delta_t"),
                           vento=v_campo if v_campo is not None else s.get("vento"),
                           p_apto=None)
        pares.append({"ts": l["ts"], "hora": ts, "dt_campo": dt_campo,
                      "dt_serie": s.get("delta_t"), "v_campo": v_campo,
                      "v_serie": s.get("vento"), "dir_campo": l.get("direcao"),
                      "dir_serie": s.get("direcao"), "dif_dir": dif_dir,
                      "apto_campo": e_apto(classificar(linha_campo, crit)),
                      "apto_serie": e_apto(classificar(s, crit))})

    def stats(a, b):
        ds = [p[b] - p[a] for p in pares if p[a] is not None and p[b] is not None]
        return _estatisticas(ds)

    concordam = sum(1 for p in pares if p["apto_campo"] == p["apto_serie"])
    difs = [abs(p["dif_dir"]) for p in pares if p["dif_dir"] is not None]
    return {"pares": pares, "n": len(pares), "fora": len(leituras) - len(pares),
            "janelas": janelas,
            "delta_t": stats("dt_campo", "dt_serie"),
            "vento": stats("v_campo", "v_serie"),
            "direcao_mae": sum(difs) / len(difs) if difs else None,
            "concordancia": concordam / len(pares) if pares else None}


def texto_campo(c):
    if c and c.get("janelas") and not c["n"]:
        return texto_janelas_campo(c["janelas"])
    if c and c.get("janelas"):
        return texto_campo(dict(c, janelas=None)) + "\n" + \
            texto_janelas_campo(c["janelas"])
    if not c or not c["n"]:
        return ("Medição de campo carregada, mas nenhuma leitura cai no "
                "período analisado.") if c else ""
    partes = [f"Medição de campo ({c['n']} leituras)"]
    if c["delta_t"]:
        partes.append(f"Delta T da ferramenta {'+' if c['delta_t']['vies'] >= 0 else ''}"
                      f"{_fmt(c['delta_t']['vies'])} °C em relação ao talhão "
                      f"(erro médio {_fmt(c['delta_t']['mae'])})")
    if c["vento"]:
        partes.append(f"vento {'+' if c['vento']['vies'] >= 0 else ''}"
                      f"{_fmt(c['vento']['vies'])} km/h (erro médio "
                      f"{_fmt(c['vento']['mae'])})")
    if c["direcao_mae"] is not None:
        partes.append(f"direção difere {c['direcao_mae']:.0f}° em média")
    if c["concordancia"] is not None:
        partes.append(f"apta/não apta concorda em {100 * c['concordancia']:.0f}% "
                      "das leituras")
    if len(partes) == 1:
        return partes[0] + "."
    return partes[0] + ": " + "; ".join(partes[1:]) + "."


def marcar_campo_no_grafico(fig, leituras, crit):
    """Põe as leituras de campo por cima do meteorograma, como losangos."""
    if not leituras or len(fig.axes) < 2:
        return
    a_dt, a_v = fig.axes[0], fig.axes[1]
    x0, x1 = a_dt.get_xlim()
    z0 = crit.get("z0", RUGOSIDADE)
    alvo = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA), z0)
    for l in leituras:
        x = mdates.date2num(_limpo(l["ts"]))
        if not (x0 <= x <= x1):
            continue
        if l.get("temp") is not None and l.get("ur") is not None:
            a_dt.plot([x], [delta_t(l["temp"], l["ur"])], marker="D", ms=5,
                      color="#1d1d1b", markeredgecolor="white", zorder=7)
        if l.get("vento") is not None:
            a_v.plot([x], [l["vento"] * alvo / fator_altura_vento(l["altura"], z0)],
                     marker="D", ms=5, color="#1d1d1b",
                     markeredgecolor="white", zorder=7)


# =====================================================================
# BLOCO 8F — PROBABILIDADE "VESTIDA", ARQUIVO DE PREVISÕES E JANELAS DE CAMPO
# =====================================================================
#
# O teste com os pares medido × modelo das três estações (10 a 24/09)
# mostrou uma coisa incômoda: mesmo corrigido, o modelo classificado em
# sim/não teve nota de Brier PIOR que a climatologia (0,197 contra 0,166)
# — ou seja, dizer "apta" ou "não apta" com certeza, perto dos limites,
# erra mais do que simplesmente usar a frequência histórica de cada hora.
# Com o erro que sobra depois da calibração vestido em cada valor, a
# mesma série virou probabilidade confiável: Brier 0,139 (melhor que a
# climatologia em 16%), e quando ela diz 35% acontece 33%, quando diz
# 64% acontece 59%, quando diz 89% acontece 82%.
#
# O caso de 24/09 mostra o porquê: das 14 às 17h a rajada corrigida ficou
# em 20 a 21 km/h contra o teto de 20, e a hora saía "não apta" — mas a
# rajada medida foi 18 a 20, e a janela em campo foi boa. Perto do
# limite, o honesto é "35 a 50%", não "não".

# erro que sobra depois da calibração, por bloco do dia (desvio padrão),
# quando a calibração local ainda não mediu o seu. Vento e rajada a 10 m.
BLOCOS_DIA = ((22, 6), (6, 10), (10, 17), (17, 22))
NOME_BLOCO = ("madrugada", "manhã", "meio do dia", "fim de tarde")
RESIDUOS_PADRAO = {"dt": [0.6, 0.7, 0.7, 0.6],
                   "vento10": [1.5, 1.9, 2.5, 2.1],
                   "rajada10": [3.5, 3.4, 3.5, 3.7]}
PASTA_PREVISOES = "previsoes"


def bloco_do_dia(h):
    for i, (a, b) in enumerate(BLOCOS_DIA):
        if (a < b and a <= h < b) or (a > b and (h >= a or h < b)):
            return i
    return 0


def _phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def p_na_faixa(x, sigma, a, b):
    """Chance de o valor verdadeiro estar em [a, b], dado x ± sigma."""
    if x is None:
        return None
    if not sigma or sigma <= 0:
        return 1.0 if a <= x <= b else 0.0
    return max(0.0, _phi((b - x) / sigma) - _phi((a - x) / sigma))


def residuos_efetivos(crit):
    """Desvios padrão na altura de aplicação, por bloco do dia."""
    r = crit.get("residuos") or RESIDUOS_PADRAO
    fator = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA),
                               crit.get("z0", RUGOSIDADE))
    return {"dt": r.get("dt") or RESIDUOS_PADRAO["dt"],
            "vento": [s * fator for s in (r.get("vento10")
                                          or RESIDUOS_PADRAO["vento10"])],
            "rajada": [s * fator for s in (r.get("rajada10")
                                           or RESIDUOS_PADRAO["rajada10"])]}


def p_vestida(linha, crit, ts=None, sig=None):
    """Probabilidade de a hora servir, com o erro conhecido vestido.

    Chuva e inversão (se bloqueada) continuam impedimento: probabilidade
    zero. Delta T, vento e rajada entram cada um com o seu erro típico
    daquele bloco do dia, e as três chances se multiplicam.
    """
    motivo = classificar(dict(linha, p_apto=None), crit)
    if motivo == "sem_dado":
        return None
    if motivo in ("chuva", "inversao"):
        return 0.0
    sig = sig or residuos_efetivos(crit)
    b = bloco_do_dia(ts.hour) if ts is not None else 2
    p = p_na_faixa(linha["delta_t"], sig["dt"][b], crit["dt_min"], crit["dt_max"])
    p *= p_na_faixa(linha["vento"], sig["vento"][b], crit["vento_min"],
                    crit["vento_max"])
    if crit.get("rajada_max") and linha.get("rajada") is not None:
        p *= p_na_faixa(linha["rajada"], sig["rajada"][b], -1e9,
                        crit["rajada_max"])
    return p


def vestir_serie(serie, crit):
    """Põe p_apto (vestida) em cada hora de uma série determinística."""
    sig = residuos_efetivos(crit)
    for ts, l in serie.items():
        l["p_apto"] = p_vestida(l, crit, ts, sig)
    return serie


def residuos_por_bloco(obs_area, cor_area, crit):
    """Erro que sobrou depois da calibração (validação cruzada), por bloco.

    Vento e rajada voltam para 10 m, para valerem em qualquer altura de
    aplicação que o usuário escolher depois.
    """
    fator = fator_altura_vento(crit.get("altura_vento", ALTURA_BARRA),
                               crit.get("z0", RUGOSIDADE))
    difs = {k: [[] for _ in BLOCOS_DIA] for k in ("dt", "vento", "rajada")}
    for ts, o in obs_area.items():
        c = cor_area.get(ts)
        if not c:
            continue
        b = bloco_do_dia(ts.hour)
        for k, ch in (("dt", "delta_t"), ("vento", "vento"), ("rajada", "rajada")):
            if o.get(ch) is not None and c.get(ch) is not None:
                difs[k][b].append(c[ch] - o[ch])

    def dp(vs, padrao):
        if len(vs) < 20:
            return padrao
        m = sum(vs) / len(vs)
        return math.sqrt(sum((v - m) ** 2 for v in vs) / (len(vs) - 1))

    return {"dt": [round(dp(difs["dt"][i], RESIDUOS_PADRAO["dt"][i]), 3)
                   for i in range(4)],
            "vento10": [round(dp(difs["vento"][i],
                                 RESIDUOS_PADRAO["vento10"][i] * fator) / fator, 3)
                        for i in range(4)],
            "rajada10": [round(dp(difs["rajada"][i],
                                  RESIDUOS_PADRAO["rajada10"][i] * fator) / fator, 3)
                         for i in range(4)],
            "n": sum(len(v) for v in difs["dt"])}


def residuos_da_calibracao(cal, estacoes):
    """Os resíduos guardados, se foram medidos com estas estações."""
    r = (cal or {}).get("residuos")
    if not r:
        return None
    codigos = {e["codigo"] for e in estacoes}
    if not codigos & set(r.get("estacoes", [])):
        return None
    return r


def avaliar_probabilidades(obs_area, prob_area, crit):
    """Brier, habilidade sobre a climatologia e confiabilidade."""
    clima = {}
    for ts, o in obs_area.items():
        m = classificar(o, crit)
        if m == "sem_dado":
            continue
        c = clima.setdefault(ts.hour, [0, 0])
        c[1] += 1
        c[0] += 1 if e_apto(m) else 0
    pares, ref = [], []
    for ts, o in obs_area.items():
        p = (prob_area.get(ts) or {}).get("p_apto")
        m = classificar(o, crit)
        if p is None or m == "sem_dado":
            continue
        y = 1.0 if e_apto(m) else 0.0
        a, n = clima[ts.hour]
        # climatologia sem o próprio dia (validação cruzada)
        pc = (a - y) / (n - 1) if n > 1 else 0.5
        pares.append((p, y))
        ref.append((pc, y))
    if not pares:
        return None
    brier = sum((p - y) ** 2 for p, y in pares) / len(pares)
    brier_c = sum((p - y) ** 2 for p, y in ref) / len(ref)
    faixas = []
    for lo, hi in ((0, .2), (.2, .5), (.5, .8), (.8, 1.01)):
        sel = [(p, y) for p, y in pares if lo <= p < hi]
        if sel:
            faixas.append({"faixa": (lo, min(hi, 1.0)), "n": len(sel),
                           "prevista": sum(p for p, _ in sel) / len(sel),
                           "observada": sum(y for _, y in sel) / len(sel)})
    return {"n": len(pares), "brier": brier, "brier_clima": brier_c,
            "bss": 1 - brier / brier_c if brier_c > 0 else None,
            "confiabilidade": faixas}


def texto_probabilidades(av, rotulo="Probabilidade"):
    if not av:
        return ""
    conf = "; ".join(f"diz {100 * f['prevista']:.0f}% → aconteceu "
                     f"{100 * f['observada']:.0f}% (n={f['n']})"
                     for f in av["confiabilidade"])
    bss = av.get("bss")
    return (f"{rotulo}: nota de Brier {_fmt(av['brier'], 3)} contra "
            f"{_fmt(av['brier_clima'], 3)} da climatologia"
            + (f" ({'+' if bss >= 0 else ''}{100 * bss:.0f}% de habilidade)"
               if bss is not None else "") + f". Confiabilidade: {conf}.")


# ---------------------------------------------------------------------
# Arquivo das previsões emitidas — para conferir depois com o medido
# ---------------------------------------------------------------------

def arquivar_previsao(r, lat, lon, crit, fuso=-3):
    """Grava a previsão emitida agora, hora a hora, na pasta previsoes/.

    Só assim dá para, dias depois, perguntar: quando a ferramenta disse
    70%, aconteceu? Rodadas antigas do Open-Meteo não bastam — elas não
    têm a calibração local nem o critério do usuário.
    """
    if not r or not r.get("serie") or lat is None:
        return None
    pasta = caminho_ao_lado(PASTA_PREVISOES)
    os.makedirs(pasta, exist_ok=True)
    agora = datetime.now()
    horas = []
    for ts in sorted(r["serie"]):
        l = r["serie"][ts]
        def arred(v, c=2):
            return None if v is None else round(float(v), c)
        horas.append([ts.strftime("%Y-%m-%dT%H:%M"), arred(l.get("p_apto"), 3),
                      arred(l.get("delta_t")), arred(l.get("vento")),
                      arred(l.get("rajada")), arred(l.get("chuva")),
                      arred(l.get("direcao"), 0),
                      classificar(l, crit)])
    dados = {"emissao": agora.strftime("%Y-%m-%dT%H:%M"),
             "lat": round(lat, 5), "lon": round(lon, 5), "fuso": fuso,
             "metodo": r.get("metodo"), "conjunto": bool(r.get("conjunto")),
             "corrigida": bool(r.get("corrigida")),
             "criterio": {k: crit.get(k) for k in (
                 "dt_min", "dt_max", "vento_min", "vento_max", "rajada_max",
                 "chuva_max", "altura_vento")},
             "campos": ["hora", "p_apto", "delta_t", "vento", "rajada",
                        "chuva", "direcao", "classe"],
             "horas": horas}
    caminho = os.path.join(pasta, f"prev_{agora:%Y%m%d_%H%M%S}.json")
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump(dados, f, ensure_ascii=False)
    return caminho


def carregar_arquivo_previsoes(lat, lon, raio_km=5.0):
    """Previsões arquivadas para esta área."""
    pasta = caminho_ao_lado(PASTA_PREVISOES)
    if lat is None or not os.path.isdir(pasta):
        return []
    saida = []
    for nome in sorted(os.listdir(pasta)):
        if not (nome.startswith("prev_") and nome.endswith(".json")):
            continue
        try:
            with open(os.path.join(pasta, nome), encoding="utf-8") as f:
                d = json.load(f)
            if haversine(lat, lon, d["lat"], d["lon"]) <= raio_km:
                saida.append(d)
        except Exception:
            continue
    return saida


def verificar_arquivo(obs_area, crit, arquivadas):
    """Acerto das previsões que a ferramenta emitiu, por antecedência."""
    grupos = {}
    for d in arquivadas:
        emissao = datetime.strptime(d["emissao"], "%Y-%m-%dT%H:%M")
        for linha in d["horas"]:
            ts = datetime.strptime(linha[0], "%Y-%m-%dT%H:%M")
            lead = int((ts - emissao).total_seconds() // 86400)
            if lead < 0:
                continue
            chave = ts.replace(tzinfo=timezone.utc)
            o = obs_area.get(chave)
            if not o or linha[1] is None:
                continue
            m = classificar(o, crit)
            if m == "sem_dado":
                continue
            g = grupos.setdefault(lead, {"pares": [], "prob": {}})
            g["pares"].append((linha[1], 1.0 if e_apto(m) else 0.0))
            g["prob"][chave] = {"p_apto": linha[1]}
    saida = []
    for lead in sorted(grupos):
        g = grupos[lead]
        av = avaliar_probabilidades(
            {ts: obs_area[ts] for ts in g["prob"]}, g["prob"], crit)
        pares = g["pares"]
        a = sum(1 for p, y in pares if p >= LIMIAR_P and y)
        b = sum(1 for p, y in pares if p >= LIMIAR_P and not y)
        c = sum(1 for p, y in pares if p < LIMIAR_P and y)
        saida.append({"antecedencia": lead, "n": len(pares),
                      "csi": a / (a + b + c) if a + b + c else None,
                      "brier": av["brier"] if av else None,
                      "bss": av.get("bss") if av else None})
    return saida


# ---------------------------------------------------------------------
# Janelas avaliadas em campo
# ---------------------------------------------------------------------

def _avaliacao(texto):
    """'boa', 'ruim' ou o próprio texto — pela primeira palavra."""
    t = _sem_acento(texto or "")
    if not t:
        return None
    if t.startswith(("ruim", "pessim", "inapt", "nao", "ma ", "ma,", "fraca",
                     "impropri")) or t == "ma":
        return "ruim"
    if t.startswith(("boa", "bom", "otim", "excel", "muito boa", "apta",
                     "perfeit", "adequad")):
        return "boa"
    return t


def comparar_janelas_campo(leituras, serie, crit):
    """Janelas que o operador avaliou em campo contra o que a ferramenta disse."""
    saida = []
    for l in leituras:
        if not l.get("avaliacao") or not l.get("fim"):
            continue
        ini, fim = l["ts"], l["fim"]
        horas = [ts for ts in sorted(serie) if ini <= ts < fim]
        if not horas:
            continue
        aptas = sum(1 for ts in horas if e_apto(classificar(serie[ts], crit)))
        ps = [serie[ts].get("p_apto") for ts in horas
              if serie[ts].get("p_apto") is not None]
        saida.append({"ini": ini, "fim": fim, "avaliacao": l["avaliacao"],
                      "horas": len(horas), "aptas": aptas,
                      "p_media": sum(ps) / len(ps) if ps else None,
                      "acertou": (aptas / len(horas) >= 0.5)
                      == (l["avaliacao"] == "boa")})
    return saida


def texto_janelas_campo(jan):
    if not jan:
        return ""
    partes = []
    for j in jan:
        partes.append(f'{j["ini"]:%d/%m %H:%M}–{j["fim"]:%H:%M} ({j["avaliacao"]}): '
                      f'a ferramenta deu apta em {j["aptas"]} de {j["horas"]} h'
                      + (f', {100 * j["p_media"]:.0f}% em média'
                         if j["p_media"] is not None else "")
                      + (" ✓" if j["acertou"] else " ✗"))
    certos = sum(1 for j in jan if j["acertou"])
    return (f"Janelas avaliadas em campo ({certos} de {len(jan)} coerentes): "
            + "; ".join(partes) + ".")


def urls_tabelas_inmet(estacoes):
    return [f"https://tempo.inmet.gov.br/TabelaDeDadosDasEstacoes/{e['codigo']}"
            for e in estacoes]


# ---------------------------------------------------------------------
# A aba propriamente dita
# ---------------------------------------------------------------------

class AbaSeries(ttk.Frame):
    """Monta o histórico da área e acha as janelas de aplicação.

    O histórico pode vir de três jeitos: medido (as tabelas do INMET que o
    usuário carrega), do modelo corrigido pela calibração local, ou do
    modelo bruto. Com o medido, a aba ainda compara o modelo com as
    estações e guarda a calibração que a previsão vai usar.
    """

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.serie = {}          # série combinada da área
        self.janelas = []
        self.por_estacao = {}
        self.crit = None
        self.resultado = None
        self.antecedencias = None
        self.fila = queue.Queue()
        self._baixando = False
        self._construir_parametros()
        self._construir_resumo()
        self._construir_tabela()

    # ------------------------------------------------------------------
    def _construir_parametros(self):
        pref = ler_preferencias().get("series", {})
        painel = ttk.LabelFrame(self, text="Período e critérios")
        painel.pack(side="top", fill="x", padx=8, pady=(8, 4))

        # --- linha 1: período ---
        l1 = ttk.Frame(painel)
        l1.pack(side="top", fill="x", padx=6, pady=(6, 2))

        hoje = datetime.now().date()
        ttk.Label(l1, text="De:").pack(side="left")
        self.var_ini = tk.StringVar(value=(hoje - timedelta(days=14)).isoformat())
        ttk.Entry(l1, textvariable=self.var_ini, width=12).pack(side="left", padx=(4, 10))

        ttk.Label(l1, text="até:").pack(side="left")
        self.var_fim = tk.StringVar(value=hoje.isoformat())
        ttk.Entry(l1, textvariable=self.var_fim, width=12).pack(side="left", padx=(4, 14))

        ttk.Label(l1, text="Atalho:").pack(side="left")
        for dias in (7, 15, 30):
            ttk.Button(l1, text=f"{dias} dias", width=8,
                       command=lambda d=dias: self.ultimos_dias(d)).pack(side="left", padx=2)

        ttk.Label(l1, text="  Fuso:").pack(side="left")
        self.var_fuso = tk.StringVar(value="-3")
        ttk.Combobox(l1, textvariable=self.var_fuso, width=4, state="readonly",
                     values=("-2", "-3", "-4", "-5")).pack(side="left", padx=(4, 0))

        # --- linha 2: critérios ---
        l2 = ttk.Frame(painel)
        l2.pack(side="top", fill="x", padx=6, pady=2)

        ttk.Label(l2, text="Delta T de").pack(side="left")
        self.var_dtmin = tk.StringVar(value=pref.get("dt_min", "2"))
        ttk.Entry(l2, textvariable=self.var_dtmin, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="a").pack(side="left")
        self.var_dtmax = tk.StringVar(value=pref.get("dt_max", "8"))
        ttk.Entry(l2, textvariable=self.var_dtmax, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="°C     Vento de").pack(side="left")
        self.var_vmin = tk.StringVar(value=pref.get("vento_min", "3"))
        ttk.Entry(l2, textvariable=self.var_vmin, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="a").pack(side="left")
        self.var_vmax = tk.StringVar(value=pref.get("vento_max", "15"))
        ttk.Entry(l2, textvariable=self.var_vmax, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="km/h").pack(side="left")
        ttk.Label(l2, text="   (o mínimo de vento já descarta parte das horas "
                           "de inversão; o bloqueio abaixo cuida do resto)",
                  foreground="#666").pack(side="left")

        montar_controles_seguranca(painel, self, pref=pref)

        # --- linha 3: fonte e ação ---
        l3 = ttk.Frame(painel)
        l3.pack(side="top", fill="x", padx=6, pady=(2, 2))

        ttk.Label(l3, text="Fonte:").pack(side="left")
        self.var_fonte = tk.StringVar(value=FONTE_MODELO)
        ttk.Combobox(l3, textvariable=self.var_fonte, width=34, state="readonly",
                     values=FONTES_HISTORICO).pack(side="left", padx=(4, 10))

        ttk.Label(l3, text="Método:").pack(side="left")
        self.var_metodo = tk.StringVar(value=METODO_IDW)
        ttk.Combobox(l3, textvariable=self.var_metodo, width=30, state="readonly",
                     values=(METODO_IDW, METODO_PONTO)).pack(side="left", padx=(4, 10))

        ttk.Label(l3, text="Token INMET:").pack(side="left")
        self.var_token = tk.StringVar()
        ttk.Entry(l3, textvariable=self.var_token, width=12).pack(side="left", padx=(4, 10))

        # --- linha 4: dado medido e ações ---
        l4 = ttk.Frame(painel)
        l4.pack(side="top", fill="x", padx=6, pady=(2, 8))
        ttk.Button(l4, text="Abrir tabelas no portal",
                   command=self.abrir_portal).pack(side="left")
        ttk.Button(l4, text="Carregar tabelas do INMET…", style=ESTILO_DESTAQUE,
                   command=self.carregar_tabelas).pack(side="left", padx=(6, 0))
        self.btn_baixar = botao_principal(l4, "Baixar e analisar",
                                          self.baixar)
        self.btn_baixar.pack(side="left", padx=(10, 0))
        self.btn_csv = ttk.Button(l4, text="Exportar CSV…", state="disabled",
                                  command=self.exportar)
        self.btn_csv.pack(side="left", padx=(10, 0))
        ttk.Button(l4, text="Medição de campo…",
                   command=self.carregar_campo).pack(side="left", padx=(10, 0))
        ttk.Button(l4, text="Modelo de planilha…",
                   command=self.gravar_modelo_campo).pack(side="left", padx=(4, 0))
        self.lbl_medidos = ttk.Label(l4, foreground="#666",
                                     text="   Nenhuma tabela medida carregada — "
                                          "o histórico sai do modelo.")
        self.lbl_medidos.pack(side="left", padx=(10, 0))

    def _construir_resumo(self):
        quadro = ttk.LabelFrame(self, text="Resumo")
        quadro.pack(side="top", fill="x", padx=8, pady=4)
        self.lbl_resumo = ttk.Label(
            quadro, justify="left", wraplength=1040,
            text="Defina a área na aba 1 e clique em “Baixar e analisar”.")
        self.lbl_resumo.pack(side="top", anchor="w", padx=8, pady=8)

    def _construir_tabela(self):
        """Tabela, gráficos e mapas, em abas internas.

        São leituras do mesmo resultado: a tabela para conferir número
        por número, o gráfico para ver o comportamento ao longo do período,
        o mapa de calor para o padrão de horário, a direção para saber para
        onde vai a deriva, e a conferência para saber o quanto confiar.
        """
        quadro = ttk.LabelFrame(self, text="Resultado")
        quadro.pack(side="top", fill="both", expand=True, padx=8, pady=(4, 8))

        self.vistas = ttk.Notebook(quadro)
        self.vistas.pack(fill="both", expand=True, padx=6, pady=6)

        aba_tabela = ttk.Frame(self.vistas)
        self.vistas.add(aba_tabela, text="  Janelas  ")
        self.tabela = montar_tabela_janelas(aba_tabela)

        aba_grafico = ttk.Frame(self.vistas)
        self.vistas.add(aba_grafico, text="  Gráfico  ")
        self.fig_serie, self.canvas_serie = montar_figura(aba_grafico)

        aba_calor = ttk.Frame(self.vistas)
        self.vistas.add(aba_calor, text="  Mapa de calor  ")
        self.fig_calor, self.canvas_calor = montar_figura(aba_calor)

        aba_mapas = ttk.Frame(self.vistas)
        self.vistas.add(aba_mapas, text="  Mapas  ")
        self._construir_mapas(aba_mapas)

        aba_dir = ttk.Frame(self.vistas)
        self.vistas.add(aba_dir, text="  Direção do vento  ")
        self.fig_dir, self.canvas_dir = montar_figura(aba_dir)

        aba_verif = ttk.Frame(self.vistas)
        self.vistas.add(aba_verif, text="  Modelo × medido  ")
        barra = ttk.Frame(aba_verif)
        barra.pack(side="top", fill="x", padx=6, pady=(6, 0))
        self.btn_passadas = ttk.Button(barra, text="Verificar previsões passadas",
                                       state="disabled",
                                       command=self.verificar_passadas)
        self.btn_passadas.pack(side="left")
        ttk.Label(barra, foreground="#666",
                  text="   Busca o que as rodadas de 1 a 7 dias antes previam "
                       "para as horas medidas e mede o acerto de cada "
                       "antecedência.").pack(side="left")
        self.fig_verif, self.canvas_verif = montar_figura(aba_verif)

    def _construir_mapas(self, pai):
        """Os três mapas de interpolação, com os parâmetros à mão.

        Os controles ficam expostos de propósito: o objetivo desta vista é
        olhar o método, e para isso é preciso poder mexer na potência e ver
        o desenho mudar.
        """
        ctrl = ttk.Frame(pai)
        ctrl.pack(side="top", fill="x", padx=6, pady=(6, 0))

        ttk.Label(ctrl, text="Potência do IDW:").pack(side="left")
        self.var_potencia = tk.StringVar(value="2")
        ttk.Combobox(ctrl, textvariable=self.var_potencia, width=4,
                     state="readonly",
                     values=("1", "1,5", "2", "2,5", "3", "4", "5")
                     ).pack(side="left", padx=(4, 14))

        ttk.Label(ctrl, text="Células:").pack(side="left")
        self.var_celulas = tk.StringVar(value="140")
        ttk.Combobox(ctrl, textvariable=self.var_celulas, width=5,
                     state="readonly",
                     values=("60", "100", "140", "200", "300")
                     ).pack(side="left", padx=(4, 14))

        ttk.Label(ctrl, text="Distância em:").pack(side="left")
        self.var_metrica = tk.StringVar(value=METRICA_KM)
        ttk.Combobox(ctrl, textvariable=self.var_metrica, width=26,
                     state="readonly", values=(METRICA_KM, METRICA_GRAU)
                     ).pack(side="left", padx=(4, 14))

        ttk.Button(ctrl, text="Redesenhar",
                   command=self.desenhar_mapas).pack(side="left")
        self.btn_qgis = ttk.Button(ctrl, text="Exportar para o QGIS…",
                                   state="disabled", command=self.exportar_qgis)
        self.btn_qgis.pack(side="left", padx=(10, 0))

        self.fig_mapas, self.canvas_mapas = montar_figura(pai)

    # ------------------------------------------------------------------
    def carregar_tabelas(self):
        """Lê as tabelas do INMET e as liga às estações da área."""
        caminhos = filedialog.askopenfilenames(
            title="Tabelas horárias das estações (exportadas do INMET)",
            filetypes=[("CSV", "*.csv"), ("Todos os arquivos", "*.*")])
        if not caminhos:
            return
        if isinstance(caminhos, str):
            caminhos = [caminhos]
        fuso = int(self.var_fuso.get())
        tabelas, erros = [], []
        for c in caminhos:
            try:
                tabelas.append(ler_tabela_inmet(c, fuso))
            except Exception as e:
                erros.append(f"{os.path.basename(c)}: {e}")
        if not tabelas:
            messagebox.showerror("Não consegui ler as tabelas", "\n".join(erros))
            return

        estacoes = list(self.app.proximas)
        # estações fora da área também valem, se o código vier no arquivo
        por_codigo = {e["codigo"]: e for e in self.app.estacoes}
        for t in tabelas:
            e = por_codigo.get(t.get("codigo") or "")
            if e and e["codigo"] not in {x["codigo"] for x in estacoes}:
                estacoes.append(e)
        sugestao = sugerir_associacao(tabelas, estacoes)
        if any(not t.get("codigo") for t in tabelas):
            if not estacoes:
                messagebox.showwarning(
                    "Defina a área primeiro",
                    "As tabelas do portal não trazem o código da estação. "
                    "Marque a área na aba 1 para eu sugerir a qual estação "
                    "cada arquivo pertence — ou ponha o código no nome do "
                    "arquivo (ex.: A413.csv).")
                return
            sugestao = pedir_associacao(self, sugestao, estacoes)
            if sugestao is None:
                self.app.status("Carregamento das tabelas cancelado.")
                return

        nomes = {e["codigo"]: e["nome"] for e in estacoes}
        for tab, cod in sugestao:
            if not cod:
                continue
            tab["codigo"] = cod
            tab["nome"] = tab.get("nome") or nomes.get(cod, cod)
            self.app.medidos[cod] = tab
        self._atualizar_rotulo_medidos()
        ajustado = self._periodo_das_tabelas()
        self.var_fonte.set(FONTE_MEDIDO)
        if hasattr(self.app, "aba_voos"):
            self.app.aba_voos.var_fonte.set(FONTE_MEDIDO)

        linhas = [descrever_tabela(t) for t, c in sugestao if c]
        if erros:
            linhas.append("Não li: " + "; ".join(erros))
        if ajustado:
            linhas.append(f"O período passou para {ajustado}, o das tabelas.")
        self.lbl_resumo.config(text="Tabelas carregadas:\n" + "\n".join(linhas)
                               + "\n\nA fonte passou para “Medido”. Clique em "
                                 "“Baixar e analisar”.")
        self.app.status(f"{len(self.app.medidos)} estação(ões) com dado medido.")

    def _periodo_das_tabelas(self):
        """Se o período escolhido sai do que as tabelas cobrem (o padrão,
        "últimos 14 dias até hoje", quase sempre sai), passa a ser o das
        tabelas: fora dele não há dado medido.

        Se o escolhido cabe dentro das tabelas, fica como está. Devolve o
        texto do período novo, ou None quando não mexeu.
        """
        inicios = [t["diag"]["inicio"] for t in self.app.medidos.values()
                   if (t.get("diag") or {}).get("inicio")]
        fins = [t["diag"]["fim"] for t in self.app.medidos.values()
                if (t.get("diag") or {}).get("fim")]
        if not inicios or not fins:
            return None
        t_ini, t_fim = min(inicios).date(), max(fins).date()
        try:
            ini = datetime.strptime(self.var_ini.get().strip(), "%Y-%m-%d").date()
            fim = datetime.strptime(self.var_fim.get().strip(), "%Y-%m-%d").date()
            if t_ini <= ini <= fim <= t_fim:
                return None
        except ValueError:
            pass          # data digitada inválida: fica a das tabelas
        self.var_ini.set(t_ini.isoformat())
        self.var_fim.set(t_fim.isoformat())
        return f"{t_ini:%d/%m/%Y} a {t_fim:%d/%m/%Y}"

    def abrir_portal(self):
        """Abre, no navegador, a tabela de cada estação escolhida.

        O portal pede a verificação de "não sou robô", então o download é
        manual: gere a tabela, clique em Baixar CSV e salve com o código da
        estação no nome (ex.: A413.csv) — assim a ferramenta reconhece o
        arquivo sozinha.
        """
        if not self.app.proximas:
            messagebox.showwarning("Sem área definida",
                                   "Marque a área na aba 1 primeiro.")
            return
        import webbrowser
        for url in urls_tabelas_inmet(self.app.proximas):
            try:
                webbrowser.open_new_tab(url)
            except Exception:
                pass
        self.app.status("Abri a tabela de cada estação no navegador. Escolha o "
                        "período, gere a tabela, baixe o CSV e salve com o "
                        "código no nome (ex.: A413.csv).")

    def carregar_campo(self):
        """Leituras feitas no talhão, para conferir a estimativa ali."""
        caminho = filedialog.askopenfilename(
            title="Medições de campo (CSV)",
            filetypes=[("CSV", "*.csv *.txt"), ("Todos os arquivos", "*.*")])
        if not caminho:
            return
        try:
            self.app.campo = ler_medicao_campo(caminho)
        except Exception as e:
            messagebox.showerror("Não consegui ler as medições de campo",
                                 f"{e}\n\nUse “Modelo de planilha…” para ver o "
                                 "formato esperado.")
            return
        n = len(self.app.campo)
        self.app.status(f"{n} leituras de campo carregadas "
                        f"({self.app.campo[0]['ts']:%d/%m %H:%M} a "
                        f"{self.app.campo[-1]['ts']:%d/%m %H:%M}).")
        self._atualizar_rotulo_medidos()
        if self.resultado:
            self._mostrar(self.resultado)

    def gravar_modelo_campo(self):
        caminho = filedialog.asksaveasfilename(
            title="Salvar o modelo de planilha de campo",
            defaultextension=".csv", initialfile="medicoes_campo.csv",
            filetypes=[("CSV", "*.csv")])
        if not caminho:
            return
        try:
            with open(caminho, "w", encoding="utf-8-sig", newline="") as f:
                f.write(MODELO_CAMPO)
        except Exception as e:
            messagebox.showerror("Não consegui salvar", str(e))
            return
        messagebox.showinfo(
            "Modelo gravado",
            f"{caminho}\n\nUma linha por leitura, hora local. Direção = de "
            "onde o vento vem (para onde a biruta aponta é o contrário). "
            "Altura = altura do anemômetro em metros. Anote também leituras "
            "em hora sem aplicação: são elas que mostram se a ferramenta "
            "erra de madrugada ou à tarde.")

    def _atualizar_rotulo_medidos(self):
        campo = (f" · campo: {len(self.app.campo)} leituras"
                 if getattr(self.app, "campo", None) else "")
        if not self.app.medidos:
            self.lbl_medidos.config(text="   Nenhuma tabela medida carregada — "
                                         "o histórico sai do modelo." + campo)
            return
        partes = []
        for cod, t in sorted(self.app.medidos.items()):
            d = t["diag"]
            partes.append(f"{cod} ({d['inicio']:%d/%m}–{d['fim']:%d/%m}"
                          + (", sem " + "/".join(d["faltam"]) if d["faltam"]
                             else "") + ")")
        self.lbl_medidos.config(text="   Medido: " + " · ".join(partes) + campo)

    # ------------------------------------------------------------------
    def _parametros_mapa(self):
        """Lê os três controles da vista de mapas."""
        try:
            potencia = float(self.var_potencia.get().replace(",", "."))
            celulas = int(self.var_celulas.get())
        except ValueError:
            messagebox.showerror("Parâmetro inválido",
                                 "Potência e número de células precisam ser "
                                 "números.")
            return None
        return potencia, celulas, self.var_metrica.get().startswith("km")

    def pontos_das_estacoes(self):
        """Médias do período por estação — a entrada dos mapas e do QGIS."""
        if not self.por_estacao or "PONTO" in self.por_estacao:
            return []
        usadas = (self.resultado or {}).get("usadas") or self.app.proximas
        return resumo_por_estacao(self.por_estacao, usadas)

    def desenhar_mapas(self):
        par = self._parametros_mapa()
        if par is None:
            return
        potencia, celulas, em_km = par
        pontos = self.pontos_das_estacoes()
        area = (self.app.lat, self.app.lon) if self.app.lat is not None else None
        periodo = f"{self.var_ini.get()} a {self.var_fim.get()}"
        desenhar_mapas_interpolacao(self.fig_mapas, pontos, area, self.crit,
                                    potencia, celulas, em_km, periodo)
        self.canvas_mapas.draw_idle()
        self.btn_qgis.config(state="normal" if len(pontos) >= 2 else "disabled")
        if self.serie and self.crit:
            desenhar_direcao(self.fig_dir, self.serie, self.crit, pontos, area,
                             f"{periodo} · direção do vento", potencia, em_km)
            self.canvas_dir.draw_idle()

    def exportar_qgis(self):
        pontos = self.pontos_das_estacoes()
        if len(pontos) < 2:
            messagebox.showwarning(
                "Nada para exportar",
                "Os mapas e a exportação precisam de pelo menos duas estações.\n"
                "Escolha o método “Interpolar estações” e baixe de novo.")
            return
        par = self._parametros_mapa()
        if par is None:
            return

        pasta = filedialog.askdirectory(
            title="Onde gravar os arquivos para o QGIS")
        if not pasta:
            return
        destino = os.path.join(pasta, f"qgis_{datetime.now():%Y%m%d_%H%M}")
        area = (self.app.lat, self.app.lon) if self.app.lat is not None else None
        try:
            gerados = exportar_para_qgis(
                destino, pontos, area, par[0], par[1], par[2],
                f"{self.var_ini.get()} a {self.var_fim.get()}")
        except Exception as e:
            messagebox.showerror("Não consegui exportar", str(e))
            return

        messagebox.showinfo(
            "Arquivos gravados",
            f"Gravei em:\n{destino}\n\n" + "\n".join(gerados) +
            "\n\nO leia-me.txt traz os parâmetros exatos para repetir a "
            "interpolação no QGIS.")
        self.app.status(f"{len(gerados)} arquivos gravados em "
                        f"{os.path.basename(destino)}.")

    # ------------------------------------------------------------------
    def ultimos_dias(self, dias):
        hoje = datetime.now().date()
        self.var_ini.set((hoje - timedelta(days=dias - 1)).isoformat())
        self.var_fim.set(hoje.isoformat())

    def ler_criterios(self):
        try:
            crit = {
                "dt_min": float(self.var_dtmin.get().replace(",", ".")),
                "dt_max": float(self.var_dtmax.get().replace(",", ".")),
                "vento_min": float(self.var_vmin.get().replace(",", ".")),
                "vento_max": float(self.var_vmax.get().replace(",", ".")),
            }
        except ValueError:
            messagebox.showerror("Critério inválido",
                                 "Delta T e vento precisam ser números.")
            return None
        if crit["dt_min"] >= crit["dt_max"]:
            messagebox.showerror("Faixa invertida",
                                 "O Delta T mínimo tem que ser menor que o máximo.")
            return None
        if crit["vento_min"] >= crit["vento_max"]:
            messagebox.showerror("Faixa invertida",
                                 "O vento mínimo tem que ser menor que o máximo.")
            return None
        if not ler_seguranca(self, crit):
            return None
        # a chuva medida também derruba a hora; o limite é o da aba 3
        try:
            crit["chuva_max"] = float(
                self.app.aba_previsao.var_chuva.get().replace(",", "."))
        except Exception:
            crit["chuva_max"] = 0.2
        gravar_preferencias("series", preferencias_da_tela(self))
        return crit

    # ------------------------------------------------------------------
    def baixar(self):
        if self._baixando:
            return
        if not self.app.proximas:
            messagebox.showwarning(
                "Sem área definida",
                "Volte à aba 1 e marque a área — no mapa, por coordenada "
                "ou carregando o arquivo do talhão.")
            return
        crit = self.ler_criterios()
        if crit is None:
            return

        ini, fim = self.var_ini.get().strip(), self.var_fim.get().strip()
        try:
            d0 = datetime.strptime(ini, "%Y-%m-%d").date()
            d1 = datetime.strptime(fim, "%Y-%m-%d").date()
        except ValueError:
            messagebox.showerror("Data inválida",
                                 "Use o formato AAAA-MM-DD, por exemplo 2026-09-18.")
            return
        if d1 < d0:
            messagebox.showerror("Período invertido",
                                 "A data final é anterior à inicial.")
            return

        self._baixando = True
        self.btn_baixar.config(state="disabled", text="Baixando…")
        self.app.status(f"Baixando {len(self.app.proximas)} estações…")

        threading.Thread(
            target=self._trabalho,
            args=(list(self.app.proximas), ini, fim, int(self.var_fuso.get()),
                  crit, self.var_fonte.get(), self.var_metodo.get(),
                  self.app.lat, self.app.lon, dict(self.app.medidos),
                  self.app.calibracao, self.var_token.get().strip() or None),
            daemon=True).start()
        self.after(150, self._checar_fila)

    def _trabalho(self, alvo, ini, fim, fuso, crit, fonte, metodo, lat, lon,
                  medidos, calibracao, token):
        """Roda na thread: só baixa e calcula, não toca em widget nenhum."""
        try:
            r = montar_historico(alvo, ini, fim, fuso, crit, lat, lon, fonte,
                                 metodo, medidos, calibracao, token,
                                 avisar=lambda t: self.fila.put(("andamento", t)))
            r["crit"] = crit
            self.fila.put(("pronto", r))
        except Exception as e:
            self.fila.put(("erro", str(e)))

    def _checar_fila(self):
        """Roda na thread da interface, lendo o que a outra produziu."""
        try:
            while True:
                tipo, carga = self.fila.get_nowait()
                if tipo == "andamento":
                    self.app.status(carga)
                elif tipo == "erro":
                    self._terminar()
                    messagebox.showerror("Falha ao baixar", carga)
                    self.app.status("Nada baixado.")
                    return
                elif tipo == "pronto":
                    self._terminar()
                    self._mostrar(carga)
                    return
                elif tipo == "antecedencias":
                    self._fim_passadas(carga)
                    return
        except queue.Empty:
            pass
        if self._baixando:
            self.after(150, self._checar_fila)

    def _terminar(self):
        self._baixando = False
        self.btn_baixar.config(state="normal", text="Baixar e analisar")
        self.btn_passadas.config(text="Verificar previsões passadas")

    # ------------------------------------------------------------------
    def _mostrar(self, r):
        r["area"] = (self.app.lat, self.app.lon)
        self.resultado = r
        self.antecedencias = None
        serie, janelas, crit = r["serie"], r["janelas"], r["crit"]
        self.serie, self.janelas, self.por_estacao = serie, janelas, r["series"]
        self.crit = crit
        metodo = r["metodo"] if r["usadas"] or r["metodo"] == METODO_PONTO \
            else METODO_IDW
        if r["fonte"] == FONTE_MEDIDO:
            metodo = METODO_IDW

        # a calibração nova vale para a sessão e fica gravada para as próximas
        aviso_cal = ""
        if r.get("calibracao"):
            self.app.calibracao = r["calibracao"]
            try:
                gravar_calibracao(self.app.calibracao)
                aviso_cal = (f"Calibração local atualizada ({r['novos_dias']} "
                             f"dia(s) novo(s)) e gravada em {ARQUIVO_CALIBRACAO}.")
            except Exception as e:
                aviso_cal = f"Calibração calculada, mas não gravada: {e}"

        texto, n_validas, n_aptas = resumir(serie, janelas, crit, r["falhas"])
        linhas = [texto_fonte(r),
                  linha_do_metodo(metodo, r["alt"], r["series"], serie),
                  texto_do_vento(crit), texto]
        todas = list(serie.values())
        aptas = [l for l in todas if e_apto(classificar(l, crit))]
        d_apt, c_apt, *_ = media_vetorial(aptas)
        if d_apt is not None:
            linhas.append("Vento nas horas aptas: " + texto_direcao(d_apt, c_apt)
                          + ".")
        if r.get("verif"):
            linhas.append(texto_verificacao(r["verif"]))
        if getattr(self.app, "campo", None):
            self.campo_comparado = comparar_campo(self.app.campo, serie, crit)
            linhas.append(texto_campo(self.campo_comparado))
        if aviso_cal:
            linhas.append(aviso_cal)
        self.lbl_resumo.config(text="\n".join(t for t in linhas if t))
        preencher_tabela_janelas(self.tabela, janelas)

        if metodo == METODO_PONTO:
            alvo = "série no ponto da área"
        else:
            alvo = f"{len(r['series'])} estações interpoladas"
        rotulo = {FONTE_MEDIDO: "medido", FONTE_CORRIGIDO: "modelo corrigido",
                  FONTE_API: "medido (API)"}.get(r["fonte"], "modelo")
        titulo = (f"{self.var_ini.get()} a {self.var_fim.get()} · {alvo} · "
                  f"{rotulo}")
        desenhar_serie(self.fig_serie, serie, crit, titulo)
        marcar_campo_no_grafico(self.fig_serie, getattr(self.app, "campo", None),
                                crit)
        self.canvas_serie.draw_idle()
        desenhar_mapa_calor(self.fig_calor, serie, crit, titulo)
        self.canvas_calor.draw_idle()
        self.desenhar_mapas()
        if metodo == METODO_PONTO:
            area = (self.app.lat, self.app.lon)
            desenhar_direcao(self.fig_dir, serie, crit, None, area,
                             f"{titulo} · direção do vento")
            self.canvas_dir.draw_idle()
        desenhar_verificacao(self.fig_verif, r.get("verif"), None,
                             "Modelo (Open-Meteo) × medido nas estações, na área")
        self.canvas_verif.draw_idle()
        self.btn_passadas.config(state="normal" if r.get("verif") else "disabled")

        self.btn_csv.config(state="normal" if serie else "disabled")
        self.app.status(f"{n_aptas} horas aptas de {n_validas} · "
                        f"{len(janelas)} janelas encontradas.")

    # ------------------------------------------------------------------
    def verificar_passadas(self):
        """Acerto da previsão por antecedência, nas horas que foram medidas."""
        r = self.resultado
        if self._baixando or not r or not r.get("obs_area"):
            return
        self._baixando = True
        self.btn_passadas.config(state="disabled", text="Buscando rodadas…")
        dias = (datetime.now().date()
                - min(r["obs_area"]).date()).days + 1
        threading.Thread(target=self._trabalho_passadas,
                         args=(r, dias, int(self.var_fuso.get())),
                         daemon=True).start()
        self.after(150, self._checar_fila)

    def _trabalho_passadas(self, r, dias, fuso):
        try:
            rodadas, falhas = {}, []
            for i, e in enumerate(r["est_verif"]):
                self.fila.put(("andamento", f"Rodadas anteriores em {e['nome']} "
                                            f"({i + 1} de {len(r['est_verif'])})…"))
                try:
                    rodadas[e["codigo"]] = baixar_rodadas_anteriores(
                        e["lat"], e["lon"], dias, fuso)
                except Exception as erro:
                    falhas.append(f"{e['nome']}: {erro}")
            if not rodadas:
                raise RuntimeError("nenhuma estação devolveu rodadas "
                                   "anteriores.\n\n" + "\n".join(falhas))
            self.fila.put(("andamento", "Medindo o acerto por antecedência…"))
            linhas = verificar_antecedencias(
                r["obs_area"], r["medidas"], rodadas, r["est_verif"],
                r["alt"][0], dict(r["crit"]), r["pares"])
            self.fila.put(("antecedencias", (linhas, falhas)))
        except Exception as e:
            self.fila.put(("erro", f"Verificação das previsões passadas: {e}"))

    def _fim_passadas(self, carga):
        linhas, falhas = carga
        self._terminar()
        self.antecedencias = linhas
        desenhar_verificacao(self.fig_verif, self.resultado.get("verif"), linhas,
                             "Modelo (Open-Meteo) × medido nas estações, na área")
        self.canvas_verif.draw_idle()
        self.btn_passadas.config(state="normal")
        partes = []
        for l in linhas:
            b, c = l["acerto_bruto"], l["acerto_corrigido"]
            partes.append(f"{l['antecedencia']} d: CSI {_pct(b['csi'])} → "
                          f"{_pct(c['csi'])}")
        self.app.status("Acerto das horas aptas por antecedência (bruto → "
                        "corrigido): " + " · ".join(partes)
                        + (f" · avisos: {'; '.join(falhas)}" if falhas else ""))

    # ------------------------------------------------------------------
    def exportar(self):
        if not self.serie:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar a série horária",
            defaultextension=".csv",
            initialfile=f"janelas_{datetime.now():%Y%m%d_%H%M}.csv",
            filetypes=[("CSV", "*.csv")])
        if not caminho:
            return

        crit = self.crit or self.ler_criterios() or {
            "dt_min": 2, "dt_max": 8, "vento_min": 3, "vento_max": 15}
        try:
            gravar_csv(caminho, self.serie, crit,
                       com_chuva=any(l.get("chuva") is not None
                                     for l in self.serie.values()))
        except Exception as e:
            messagebox.showerror("Não consegui salvar", str(e))
            return

        self.app.status(f"Série gravada em {os.path.basename(caminho)}.")


# =====================================================================
# BLOCO 9 — ABA DE PREVISÃO
# =====================================================================
#
# A aba 2 olha para trás e diz o que aconteceu. Esta olha para frente e
# responde a pergunta que decide a operação: quando dá para aplicar nos
# próximos dias.
#
# A conta é a mesma — Delta T por Stull, vento na faixa, combinação das
# estações pelo inverso do quadrado da distância. Muda a fonte (previsão
# em vez de reanálise) e entra a chuva, que sozinha já derruba a hora.


class AbaPrevisao(ttk.Frame):
    """Projeta as janelas de aplicação para os próximos dias."""

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.serie = {}
        self.janelas = []
        self.por_estacao = {}
        self.crit = None
        self.conjunto = None
        self.resultado = None
        self.fila = queue.Queue()
        self._baixando = False
        self._construir_parametros()
        self._construir_resumo()
        self._construir_saida()

    # ------------------------------------------------------------------
    def _construir_parametros(self):
        pref = ler_preferencias().get("previsao", {})
        painel = ttk.LabelFrame(self, text="Previsão e critérios")
        painel.pack(side="top", fill="x", padx=8, pady=(8, 4))

        l1 = ttk.Frame(painel)
        l1.pack(side="top", fill="x", padx=6, pady=(6, 2))

        ttk.Label(l1, text="Próximos:").pack(side="left")
        self.var_dias = tk.StringVar(value="7")
        ttk.Combobox(l1, textvariable=self.var_dias, width=4, state="readonly",
                     values=("1", "2", "3", "4", "5", "6", "7")).pack(
                         side="left", padx=4)
        ttk.Label(l1, text="dias").pack(side="left", padx=(0, 14))

        ttk.Label(l1, text="Fuso:").pack(side="left")
        self.var_fuso = tk.StringVar(value="-3")
        ttk.Combobox(l1, textvariable=self.var_fuso, width=4, state="readonly",
                     values=("-2", "-3", "-4", "-5")).pack(side="left", padx=(4, 14))

        ttk.Label(l1, text="Método:").pack(side="left")
        self.var_metodo = tk.StringVar(value=METODO_PONTO)
        ttk.Combobox(l1, textvariable=self.var_metodo, width=30, state="readonly",
                     values=(METODO_PONTO, METODO_IDW)).pack(side="left", padx=(4, 14))

        ttk.Label(l1, text="Saída:").pack(side="left")
        self.var_conjunto = tk.StringVar(value=MODO_ENSEMBLE)
        ttk.Combobox(l1, textvariable=self.var_conjunto, width=28,
                     state="readonly",
                     values=(MODO_ENSEMBLE, MODO_UNICO)).pack(side="left", padx=(4, 14))

        ttk.Label(l1, text="Correção:").pack(side="left")
        self.var_correcao = tk.StringVar(value=pref.get("correcao", CORRECAO_SIM))
        ttk.Combobox(l1, textvariable=self.var_correcao, width=24,
                     state="readonly",
                     values=(CORRECAO_SIM, CORRECAO_NAO)).pack(side="left", padx=4)

        l2 = ttk.Frame(painel)
        l2.pack(side="top", fill="x", padx=6, pady=2)

        ttk.Label(l2, text="Delta T de").pack(side="left")
        self.var_dtmin = tk.StringVar(value=pref.get("dt_min", "2"))
        ttk.Entry(l2, textvariable=self.var_dtmin, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="a").pack(side="left")
        self.var_dtmax = tk.StringVar(value=pref.get("dt_max", "8"))
        ttk.Entry(l2, textvariable=self.var_dtmax, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="°C     Vento de").pack(side="left")
        self.var_vmin = tk.StringVar(value=pref.get("vento_min", "3"))
        ttk.Entry(l2, textvariable=self.var_vmin, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="a").pack(side="left")
        self.var_vmax = tk.StringVar(value=pref.get("vento_max", "15"))
        ttk.Entry(l2, textvariable=self.var_vmax, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="km/h     Descartar chuva acima de").pack(side="left")
        self.var_chuva = tk.StringVar(value=pref.get("chuva", "0,2"))
        ttk.Entry(l2, textvariable=self.var_chuva, width=5).pack(side="left", padx=4)
        ttk.Label(l2, text="mm/h").pack(side="left")

        montar_controles_seguranca(painel, self, pref=pref)

        l3 = ttk.Frame(painel)
        l3.pack(side="top", fill="x", padx=6, pady=(2, 8))

        self.btn_buscar = botao_principal(l3, "Buscar previsão",
                                          self.buscar)
        self.btn_buscar.pack(side="left")
        self.btn_csv = ttk.Button(l3, text="Exportar CSV…", state="disabled",
                                  command=self.exportar)
        self.btn_csv.pack(side="left", padx=(10, 0))
        ttk.Label(l3, text="   Previsão é estimativa: confirme no dia, "
                           "principalmente o vento.",
                  foreground="#666").pack(side="left")

    def _construir_resumo(self):
        quadro = ttk.LabelFrame(self, text="Resumo")
        quadro.pack(side="top", fill="x", padx=8, pady=4)
        self.lbl_resumo = ttk.Label(
            quadro, justify="left", wraplength=1040,
            text="Defina a área na aba 1 e clique em “Buscar previsão”.")
        self.lbl_resumo.pack(side="top", anchor="w", padx=8, pady=8)

    def _construir_saida(self):
        quadro = ttk.LabelFrame(self, text="Resultado")
        quadro.pack(side="top", fill="both", expand=True, padx=8, pady=(4, 8))

        self.vistas = ttk.Notebook(quadro)
        self.vistas.pack(fill="both", expand=True, padx=6, pady=6)

        aba_tabela = ttk.Frame(self.vistas)
        self.vistas.add(aba_tabela, text="  Janelas  ")
        self.tabela = montar_tabela_janelas(aba_tabela, com_chuva=True)

        aba_grafico = ttk.Frame(self.vistas)
        self.vistas.add(aba_grafico, text="  Gráfico  ")
        self.fig_serie, self.canvas_serie = montar_figura(aba_grafico)

        aba_calor = ttk.Frame(self.vistas)
        self.vistas.add(aba_calor, text="  Mapa de calor  ")
        self.fig_calor, self.canvas_calor = montar_figura(aba_calor)

        aba_dir = ttk.Frame(self.vistas)
        self.vistas.add(aba_dir, text="  Direção do vento  ")
        self.fig_dir, self.canvas_dir = montar_figura(aba_dir)

    # ------------------------------------------------------------------
    def ler_criterios(self):
        try:
            crit = {
                "dt_min": float(self.var_dtmin.get().replace(",", ".")),
                "dt_max": float(self.var_dtmax.get().replace(",", ".")),
                "vento_min": float(self.var_vmin.get().replace(",", ".")),
                "vento_max": float(self.var_vmax.get().replace(",", ".")),
                "chuva_max": float(self.var_chuva.get().replace(",", ".")),
            }
        except ValueError:
            messagebox.showerror("Critério inválido",
                                 "Delta T, vento e chuva precisam ser números.")
            return None
        if crit["dt_min"] >= crit["dt_max"]:
            messagebox.showerror("Faixa invertida",
                                 "O Delta T mínimo tem que ser menor que o máximo.")
            return None
        if crit["vento_min"] >= crit["vento_max"]:
            messagebox.showerror("Faixa invertida",
                                 "O vento mínimo tem que ser menor que o máximo.")
            return None
        if not ler_seguranca(self, crit):
            return None
        if self.var_conjunto.get() == MODO_ENSEMBLE:
            crit["limiar_p"] = LIMIAR_P
        gravar_preferencias("previsao", preferencias_da_tela(
            self, (("chuva", "var_chuva"), ("correcao", "var_correcao"))))
        return crit

    def corrigir(self):
        return self.var_correcao.get() == CORRECAO_SIM

    # ------------------------------------------------------------------
    def buscar(self):
        if self._baixando:
            return
        if not self.app.proximas:
            messagebox.showwarning(
                "Sem área definida",
                "Volte à aba 1 e marque a área — no mapa, por coordenada "
                "ou carregando o arquivo do talhão.")
            return
        crit = self.ler_criterios()
        if crit is None:
            return

        self._baixando = True
        self.btn_buscar.config(state="disabled", text="Buscando…")
        self.app.status("Buscando a previsão…")

        threading.Thread(target=self._trabalho,
                         args=(list(self.app.proximas), int(self.var_dias.get()),
                               int(self.var_fuso.get()), crit,
                               self.var_metodo.get(), self.app.lat, self.app.lon,
                               self.var_conjunto.get(), self.app.calibracao,
                               self.corrigir()),
                         daemon=True).start()
        self.after(150, self._checar_fila)

    def _trabalho(self, alvo, dias, fuso, crit, metodo=METODO_IDW,
                  lat=None, lon=None, conjunto=MODO_UNICO, calibracao=None,
                  corrigir=True):
        """Roda na thread: só baixa e calcula, não toca em widget nenhum."""
        try:
            r = montar_previsao(alvo, dias, fuso, crit, metodo, lat, lon,
                                conjunto, calibracao, corrigir,
                                avisar=lambda t: self.fila.put(("andamento", t)))
            self.fila.put(("pronto", r))
        except Exception as e:
            self.fila.put(("erro", f"Não consegui a previsão: {e}"))

    def _checar_fila(self):
        try:
            while True:
                tipo, carga = self.fila.get_nowait()
                if tipo == "andamento":
                    self.app.status(carga)
                elif tipo == "erro":
                    self._terminar()
                    messagebox.showerror("Falha na previsão", carga)
                    self.app.status("Previsão não obtida.")
                    return
                elif tipo == "pronto":
                    self._terminar()
                    self._mostrar(carga)
                    return
        except queue.Empty:
            pass
        if self._baixando:
            self.after(150, self._checar_fila)

    def _terminar(self):
        self._baixando = False
        self.btn_buscar.config(state="normal", text="Buscar previsão")

    # ------------------------------------------------------------------
    def _mostrar(self, r):
        self.resultado = r
        serie, janelas, crit = r["serie"], r["janelas"], r["crit"]
        self.serie, self.janelas = serie, janelas
        # toda previsão emitida fica guardada, para ser conferida depois
        try:
            arquivar_previsao(r, self.app.lat, self.app.lon, crit,
                              int(self.var_fuso.get()))
        except Exception as e:
            print("Não consegui arquivar a previsão:", e)
        self.por_estacao = r.get("por_estacao", {})
        self.crit = crit
        self.conjunto = r.get("conjunto")
        conjunto = self.conjunto
        metodo = r["metodo"]
        fuso = int(self.var_fuso.get())

        texto, n_validas, n_aptas = resumir(serie, janelas, crit, r["avisos"])
        linhas = [proxima_janela(janelas, fuso),
                  r.get("correcao"),
                  linha_do_conjunto(conjunto, serie, crit),
                  linha_do_metodo(metodo, r.get("alt"), self.por_estacao, serie),
                  texto_do_vento(crit), texto]
        aptas = [l for l in serie.values() if e_apto(classificar(l, crit))]
        d_apt, c_apt, *_ = media_vetorial(aptas)
        if d_apt is not None:
            linhas.append("Vento previsto nas horas aptas: "
                          + texto_direcao(d_apt, c_apt) + ".")
        self.lbl_resumo.config(text="\n".join(t for t in linhas if t))
        preencher_tabela_janelas(self.tabela, janelas, com_chuva=True,
                                 com_prob=bool(conjunto))

        alvo = ("no ponto da área" if metodo == METODO_PONTO
                else f"{len(self.por_estacao)} estações interpoladas")
        corr = " · corrigida" if r.get("corrigida") else ""
        titulo = (f"Previsão dos próximos {self.var_dias.get()} dias · "
                  f"{alvo}{corr}")
        desenhar_serie(self.fig_serie, serie, crit, titulo)
        self.canvas_serie.draw_idle()
        if conjunto:
            desenhar_mapa_calor_prob(self.fig_calor, serie, crit, titulo, fuso)
        else:
            desenhar_mapa_calor(self.fig_calor, serie, crit, titulo)
        self.canvas_calor.draw_idle()
        area = (self.app.lat, self.app.lon) if self.app.lat is not None else None
        desenhar_direcao(self.fig_dir, serie, crit, None, area,
                         f"{titulo} · direção do vento")
        self.canvas_dir.draw_idle()

        self.btn_csv.config(state="normal" if serie else "disabled")
        self.app.status(f"Previsão: {n_aptas} horas aptas de {n_validas} · "
                        f"{len(janelas)} janelas.")

    # ------------------------------------------------------------------
    def exportar(self):
        if not self.serie:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar a previsão horária",
            defaultextension=".csv",
            initialfile=f"previsao_{datetime.now():%Y%m%d_%H%M}.csv",
            filetypes=[("CSV", "*.csv")])
        if not caminho:
            return
        crit = self.crit or self.ler_criterios()
        if crit is None:
            return
        try:
            gravar_csv(caminho, self.serie, crit, com_chuva=True)
        except Exception as e:
            messagebox.showerror("Não consegui salvar", str(e))
            return
        self.app.status(f"Previsão gravada em {os.path.basename(caminho)}.")


def proxima_janela(janelas, fuso=-3):
    """A linha mais útil da aba: quando abre a próxima janela.

    Sem ela, o usuário teria que varrer a tabela para achar a primeira
    linha — que é justamente a informação que ele veio buscar.

    O `fuso` precisa entrar aqui porque os horários da série são locais,
    e comparar com o relógio em UTC deslocaria a conta em três horas.
    """
    if not janelas:
        return "Nenhuma janela nos próximos dias com os critérios atuais."

    agora = datetime.now(timezone.utc) + timedelta(hours=fuso)
    j = janelas[0]
    quando = j["ini"].strftime("%d/%m às %H:%M")
    horas = (j["ini"] - agora).total_seconds() / 3600

    if horas <= 0:
        prefixo = "Janela aberta agora"
    elif horas < 24:
        prefixo = f"Próxima janela em {horas:.0f} h"
    else:
        prefixo = f"Próxima janela em {horas / 24:.0f} dia(s)"

    return (f"{prefixo}: {quando}, por {j['horas']} h · "
            f"Delta T médio {_fmt(j['dt_medio'])} · "
            f"vento médio {_fmt(j['vento_medio'])} km/h")


# =====================================================================
# BLOCO 10 — RELATÓRIO EM PDF
# =====================================================================
#
# O PDF sai pelo PdfPages do próprio matplotlib. Não entra biblioteca
# nova — nem reportlab, nem conversor de HTML: cada página é uma figura,
# desenhada pelas mesmas funções que alimentam a tela. O que se vê na
# janela é exatamente o que se imprime, e o programa continua sendo um
# arquivo só que roda com matplotlib e numpy.
#
# Tudo em A4 deitado. O relatório é feito de gráficos largos — série de
# 15 dias, grade de 24 horas por 15 dias, três mapas lado a lado — e em
# retrato eles sairiam espremidos a ponto de não servirem.

from matplotlib.backends.backend_pdf import PdfPages

A4_DEITADO = (11.69, 8.27)
LINHAS_POR_PAGINA = 22
COR_TINTA = "#1d1d1b"
COR_APOIO = "#6f6c68"


def _pagina(titulo, subtitulo=""):
    """Figura nova, no tamanho da página, com o cabeçalho já posto."""
    fig = plt.Figure(figsize=A4_DEITADO, facecolor="white")
    fig.text(0.045, 0.962, titulo, fontsize=15, color=COR_TINTA,
             fontweight="bold", va="top")
    if subtitulo:
        fig.text(0.045, 0.924, subtitulo, fontsize=8.5, color=COR_APOIO,
                 va="top")
    fig.add_artist(Line2D([0.045, 0.955], [0.898, 0.898],
                          color=COR_SELECIONADA, lw=1.8,
                          transform=fig.transFigure))
    return fig


def _cabecalho_sobre(fig, titulo, subtitulo="", topo=0.80):
    """Põe o cabeçalho numa figura que já foi desenhada por outra função.

    As funções de gráfico começam limpando a figura, então o cabeçalho só
    pode entrar depois delas — e aí é preciso reabrir espaço no topo.
    """
    fig.set_size_inches(*A4_DEITADO)
    fig.patch.set_facecolor("white")
    fig.subplots_adjust(top=topo)
    fig.text(0.045, 0.972, titulo, fontsize=15, color=COR_TINTA,
             fontweight="bold", va="top")
    if subtitulo:
        fig.text(0.045, 0.934, subtitulo, fontsize=8.5, color=COR_APOIO,
                 va="top")
    fig.add_artist(Line2D([0.045, 0.955], [0.908, 0.908],
                          color=COR_SELECIONADA, lw=1.8,
                          transform=fig.transFigure))


def _fecha(pdf, fig, rodape, numero):
    fig.text(0.045, 0.028, rodape, fontsize=7, color=COR_APOIO, va="center")
    fig.text(0.955, 0.028, f"página {numero}", fontsize=7, color=COR_APOIO,
             va="center", ha="right")
    pdf.savefig(fig)
    fig.clear()
    return numero + 1


def _tabela(ax, colunas, larguras, linhas, destaques=(), fonte=7.5,
            encher=False):
    """Tabela simples no eixo. `destaques` são índices de linha a realçar.

    Com `encher`, as linhas se esticam para ocupar a caixa inteira — útil
    quando o número de linhas varia e o que vem abaixo precisa de uma
    posição previsível na página.
    """
    ax.axis("off")
    if not linhas:
        ax.text(0.5, 0.6, "Nenhuma janela encontrada no período com os "
                          "critérios adotados.",
                ha="center", va="center", color=COR_APOIO, fontsize=9)
        return

    tab = ax.table(cellText=linhas, colLabels=colunas, colWidths=larguras,
                   cellLoc="center", loc="upper center")
    tab.auto_set_font_size(False)
    tab.set_fontsize(fonte)
    altura = (0.95 / (len(linhas) + 1) if encher
              else min(0.048, 0.95 / (len(linhas) + 1)))
    for (i, j), celula in tab.get_celld().items():
        celula.set_edgecolor("#e4e2df")
        celula.set_linewidth(0.6)
        celula.set_height(altura)
        if i == 0:
            celula.set_facecolor("#33302e")
            celula.set_text_props(color="white", fontweight="bold")
        elif (i - 1) in destaques:
            celula.set_facecolor("#cfe5c9")
            celula.set_text_props(fontweight="bold", color="#14421a")
        elif i % 2 == 0:
            celula.set_facecolor("#f7f6f4")


def maiores_janelas(janelas, quantas=5):
    """Índices das janelas mais longas, para realçar sem reordenar a tabela.

    A ordem cronológica é o que serve para programar a operação; o realce
    é só para o olho achar as boas sem perder a linha do tempo.
    """
    ordem = sorted(range(len(janelas)),
                   key=lambda i: (-janelas[i]["horas"], janelas[i]["ini"]))
    return set(ordem[:quantas])


def desenhar_mapa_localizacao(ax, proximas, lat, lon, pontos_area=None,
                              segs_uf=(), segs_mun=()):
    """Mapa da página 1: onde fica a área e quais estações a alimentam."""
    ax.set_facecolor(COR_FUNDO)
    if segs_mun:
        ax.add_collection(LineCollection(list(segs_mun), colors=COR_MUNICIPIO,
                                         linewidths=0.6, zorder=0))
    if segs_uf:
        ax.add_collection(LineCollection(list(segs_uf), colors=COR_UF,
                                         linewidths=0.9, zorder=1))

    for p in proximas:
        ax.plot([lon, p["lon"]], [lat, p["lat"]], color=COR_LINHA,
                linewidth=1, linestyle="--", alpha=0.8, zorder=3)
    if proximas:
        ax.scatter([p["lon"] for p in proximas], [p["lat"] for p in proximas],
                   s=70, c=COR_SELECIONADA, linewidths=0, zorder=5,
                   label="Estações usadas")
        for p in proximas:
            ax.annotate(f'{p["nome"][:22]}\n{p["distancia"]:.0f} km',
                        (p["lon"], p["lat"]), textcoords="offset points",
                        xytext=(7, 5), fontsize=7, color="#333", zorder=6)

    if pontos_area and len(pontos_area) >= 3:
        xs = [p[0] for p in pontos_area]
        ys = [p[1] for p in pontos_area]
        ax.fill(xs, ys, color=COR_AREA, alpha=0.30, zorder=4)
        ax.plot(xs + [xs[0]], ys + [ys[0]], color=COR_AREA, linewidth=1.8,
                zorder=4)

    ax.scatter([lon], [lat], s=140, marker="X", c=COR_AREA,
               edgecolors="white", linewidths=1.5, zorder=7, label="Área")

    lats = [lat] + [p["lat"] for p in proximas]
    lons = [lon] + [p["lon"] for p in proximas]
    folga_y = max(0.2, (max(lats) - min(lats)) * 0.20)
    folga_x = max(0.2, (max(lons) - min(lons)) * 0.20)
    ax.set_xlim(min(lons) - folga_x, max(lons) + folga_x)
    ax.set_ylim(min(lats) - folga_y, max(lats) + folga_y)

    ax.set_xlabel("Longitude", fontsize=8)
    ax.set_ylabel("Latitude", fontsize=8)
    ax.tick_params(labelsize=7)
    ax.grid(True, alpha=0.25, linewidth=0.7)
    ax.legend(loc="upper right", fontsize=7.5, framealpha=0.92)
    lat_meio = (ax.get_ylim()[0] + ax.get_ylim()[1]) / 2
    ax.set_aspect(1 / max(0.1, math.cos(math.radians(lat_meio))))


def _linhas_janelas(janelas, com_chuva=False, com_prob=False):
    linhas = []
    for j in janelas:
        linha = [j["ini"].strftime("%d/%m  %H:%M"),
                 j["fim"].strftime("%d/%m  %H:%M"),
                 f'{j["horas"]} h',
                 _fmt(j["dt_medio"]),
                 f'{_fmt(j["dt_min"])} – {_fmt(j["dt_max"])}',
                 _fmt(j["vento_medio"]),
                 _fmt(j["vento_max"]),
                 _rotulo_dir(j.get("direcao")),
                 _fmt(j["temp_media"]),
                 _fmt(j["ur_media"], 0)]
        if com_chuva:
            linha.append(_fmt(j.get("chuva")))
        if com_prob:
            pa = j.get("p_apto")
            linha.append("—" if pa is None else f"{100 * pa:.0f}%")
        linhas.append(linha)
    return linhas


COLUNAS_JANELAS = ["Início", "Fim", "Duração", "Delta T médio",
                   "Delta T faixa", "Vento médio", "Vento máx", "Vento de",
                   "Temp. média", "UR média"]
LARGURAS_JANELAS = [0.12, 0.12, 0.07, 0.10, 0.12, 0.09, 0.08, 0.09, 0.09, 0.07]


def _paginas_de_tabela(pdf, titulo, subtitulo, janelas, destaques, rodape,
                       numero, com_chuva=False, nota="", com_prob=False):
    """Quebra a tabela em quantas páginas forem necessárias."""
    colunas = list(COLUNAS_JANELAS)
    larguras = list(LARGURAS_JANELAS)
    if com_chuva:
        colunas.append("Chuva (mm)")
        larguras.append(0.08)
    if com_prob:
        colunas.append("Confiança")
        larguras.append(0.08)

    linhas = _linhas_janelas(janelas, com_chuva, com_prob)
    if not linhas:
        linhas = []

    blocos = [list(range(i, min(i + LINHAS_POR_PAGINA, len(linhas))))
              for i in range(0, max(1, len(linhas)), LINHAS_POR_PAGINA)]
    for k, bloco in enumerate(blocos):
        sub = subtitulo
        if len(blocos) > 1:
            sub += f"  ·  parte {k + 1} de {len(blocos)}"
        fig = _pagina(titulo, sub)
        caixa = [0.045, 0.10, 0.91, 0.76]
        ax = fig.add_axes(caixa)
        _tabela(ax, colunas, larguras, [linhas[i] for i in bloco],
                {i - bloco[0] for i in bloco if i in destaques})
        if nota and k == 0:
            # a nota acompanha o fim da tabela: com poucas janelas ela subiria
            # sozinha para o pé da página e pareceria solta
            altura = min(0.048, 0.95 / (len(bloco) + 1)) * caixa[3]
            fim = caixa[1] + caixa[3] - (len(bloco) + 1) * altura
            fig.text(0.045, max(0.06, fim - 0.035), nota, fontsize=7.5,
                     color=COR_APOIO)
        numero = _fecha(pdf, fig, rodape, numero)
    return numero


def gerar_relatorio_pdf(caminho, d):
    """Monta o relatório inteiro. `d` traz tudo já calculado.

    A ordem das páginas é a da conversa: onde é, quando deu, como foi o
    tempo, que horas costumam servir, como a interpolação se comporta no
    espaço, para onde o vento levou a deriva, o quanto o modelo acerta ali
    — e o que vem pela frente. A numeração das seções acompanha as páginas
    que de fato existirem.
    """
    agora = datetime.now()
    rodape = (f"Janela de Aplicação · gerado em {agora:%d/%m/%Y às %H:%M} · "
              f"dados: {d['fonte']} · Delta T por "
              f"{d.get('bulbo', 'Stull (2011)').split(',')[0]}")
    numero = 1
    secao = [0]

    def sec(titulo):
        secao[0] += 1
        return f"{secao[0]}.  {titulo}"

    with PdfPages(caminho) as pdf:
        pdf.infodict().update({
            "Title": "Relatório de janelas de aplicação",
            "Subject": f"Área em {d['lat']:.5f}, {d['lon']:.5f} · "
                       f"{d['ini']} a {d['fim']}",
            "Creator": f"Janela de Aplicação v. {VERSAO}",
        })

        # ---- localização e estações ----
        sub = (f"Área em {d['lat']:.5f}, {d['lon']:.5f}"
               + (f"  ·  {_fmt(d['area_ha'])} ha" if d.get("area_ha") else "")
               + f"  ·  {d['origem']}")
        fig = _pagina(sec("Localização e estações utilizadas"), sub)
        ax_mapa = fig.add_axes([0.045, 0.09, 0.50, 0.76])
        desenhar_mapa_localizacao(ax_mapa, d["proximas"], d["lat"], d["lon"],
                                  d.get("pontos_area"), d.get("segs_uf", ()),
                                  d.get("segs_mun", ()))

        ax_tab = fig.add_axes([0.575, 0.62, 0.385, 0.23])
        pesos = pesos_idw(d["proximas"])
        medidos = d.get("medidos_codigos") or set()
        _tabela(ax_tab,
                ["Código", "Estação", "Dist. (km)", "Peso", "Alt. (m)", "Dado"],
                [0.12, 0.34, 0.14, 0.11, 0.12, 0.17],
                [[p["codigo"], p["nome"][:22],
                  _fmt(p["distancia"]),
                  f'{100 * pesos.get(p["codigo"], 0):.0f}%',
                  f'{p.get("altitude", 0):.0f}',
                  "medido" if p["codigo"] in medidos else "modelo"]
                 for p in d["proximas"]], fonte=7.2, encher=True)

        crit = d["crit"]
        texto = [
            f"Período analisado:  {d['ini']} a {d['fim']}  "
            f"({d['n_validas']} horas com dado)",
            d.get("texto_fonte", ""),
            f"Método:  {d['metodo']}",
            f"Altitude adotada para a área:  {d['altitude']}",
            "",
            f"Critérios de aptidão:  Delta T entre {_fmt(crit['dt_min'], 0)} "
            f"e {_fmt(crit['dt_max'], 0)} °C;  vento entre "
            f"{_fmt(crit['vento_min'], 0)} e "
            f"{_fmt(crit['vento_max'], 0)} km/h"
            + (f";  rajada (pico da hora) até {_fmt(crit['rajada_max'], 0)} km/h."
               if crit.get("rajada_max") else "."),
            texto_do_vento(crit),
            (f"Chuva acima de {_fmt(d['crit_previsao']['chuva_max'])} mm/h "
             "descarta a hora"
             + (f", e a hora também cai se chover mais de "
                f"{_fmt(crit.get('rainfast_mm', 0.5))} mm nas "
                f"{crit.get('rainfast_h')} h seguintes."
                if crit.get("rainfast_h") else ".")
             if d.get("crit_previsao") else ""),
            ("Horas de risco alto de inversão térmica foram bloqueadas."
             if crit.get("bloquear_inversao", True)
             else "Inversão térmica apenas sinalizada, sem bloquear horas."),
            f"Bulbo úmido:  {d.get('bulbo', 'Stull (2011)')}.",
            "",
            f"Resultado:  {d['n_aptas']} horas aptas de {d['n_validas']} "
            f"({100 * d['n_aptas'] / max(1, d['n_validas']):.0f}%), "
            f"em {len(d['janelas'])} janelas."
            + (f"  Cobertura de dados {d['cobertura']:.0f}%."
               if d.get("cobertura") is not None and d["cobertura"] < 99.5
               else ""),
            d.get("direcao_texto", ""),
            d["dispersao"],
            d.get("campo_texto", ""),
            d.get("conjunto_texto", ""),
            d.get("correcao_texto", ""),
        ]
        fig.text(0.575, 0.585, "\n".join(t for t in texto if t is not None),
                 fontsize=7.4, color=COR_TINTA, va="top", linespacing=1.6,
                 wrap=True)
        numero = _fecha(pdf, fig, rodape, numero)

        # ---- janelas encontradas ----
        destaques = maiores_janelas(d["janelas"])
        numero = _paginas_de_tabela(
            pdf, sec("Janelas de aplicação encontradas"),
            f"{d['ini']} a {d['fim']}  ·  ordenadas por data e hora",
            d["janelas"], destaques, rodape, numero,
            nota="Em verde, as cinco janelas mais longas do período. "
                 "A ordem da tabela continua sendo a cronológica. “Vento de” "
                 "é de onde o vento veio; a deriva vai para o lado oposto.")

        # ---- meteorograma ----
        fig = plt.Figure(figsize=A4_DEITADO)
        desenhar_serie(fig, d["serie"], crit)
        marcar_campo_no_grafico(fig, d.get("campo"), crit)
        _cabecalho_sobre(fig, sec("Meteorograma do período"),
                         f"{d['ini']} a {d['fim']}  ·  faixa verde = janela "
                         "de aplicação  ·  setas = para onde o vento leva a "
                         "gota", topo=0.80)
        numero = _fecha(pdf, fig, rodape, numero)

        # ---- mapa de calor ----
        fig = plt.Figure(figsize=A4_DEITADO)
        desenhar_mapa_calor(fig, d["serie"], crit)
        _cabecalho_sobre(fig, sec("Horários aptos, dia a dia"),
                         "Cada coluna é um dia, cada linha uma hora, "
                         "meia-noite embaixo. Verde é hora apta; a barra à "
                         "direita dá, por hora, o % dos dias em que ela serviu.",
                         topo=0.78)
        numero = _fecha(pdf, fig, rodape, numero)

        # ---- mapas de interpolação ----
        if len(d.get("pontos_mapa", [])) >= 2:
            fig = plt.Figure(figsize=A4_DEITADO)
            desenhar_mapas_interpolacao(
                fig, d["pontos_mapa"], (d["lat"], d["lon"]), crit,
                d["potencia"], d["celulas"], d["em_km"], y_rodape=0.075)
            _cabecalho_sobre(fig, sec("Interpolação espacial no período"),
                             "Médias do período em cada estação, interpoladas "
                             "por IDW sobre o retângulo das estações.",
                             topo=0.86)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- direção do vento ----
        if any(l.get("direcao") is not None for l in d["serie"].values()):
            fig = plt.Figure(figsize=A4_DEITADO)
            desenhar_direcao(fig, d["serie"], crit, d.get("pontos_mapa"),
                             (d["lat"], d["lon"]), "", d["potencia"],
                             d["em_km"], topo=0.80)
            _cabecalho_sobre(fig, sec("Direção do vento no período"),
                             "Rosa = de onde o vento veio. Setas = para onde "
                             "ele levou a gota. A comparação das duas rosas "
                             "mostra o vento das horas em que se aplica.",
                             topo=0.80)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- conferência com o medido ----
        if d.get("verif"):
            fig = plt.Figure(figsize=A4_DEITADO)
            desenhar_verificacao(fig, d["verif"], d.get("antecedencias"))
            _cabecalho_sobre(
                fig, sec("Conferência: modelo × medido nas estações"),
                "Barras: erro do modelo hora a hora (acima de zero = modelo "
                "maior que o medido). Linha: o que sobra depois da calibração, "
                "validada deixando cada dia fora do próprio cálculo.",
                topo=0.84)
            fig.subplots_adjust(bottom=0.19)
            import textwrap
            nota = "\n".join(textwrap.fill(t, 190) for t in
                             texto_verificacao(d["verif"]).split("\n"))
            fig.text(0.045, 0.058, nota, fontsize=6.8, color=COR_APOIO,
                     va="bottom", linespacing=1.4)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- previsão ----
        if d.get("serie_previsao"):
            conj = d.get("conjunto")
            corr = "  Corrigida pela calibração local." \
                if d.get("previsao_corrigida") else ""
            fig = plt.Figure(figsize=A4_DEITADO)
            if conj:
                desenhar_mapa_calor_prob(fig, d["serie_previsao"],
                                         d["crit_previsao"], "", d.get("fuso", -3))
                sub = (f"Cor é a fração das {conj['membros']} rodadas do "
                       "conjunto que aprovaram a hora, não uma certeza. "
                       "As colunas esmaecidas são os dias em que a previsão "
                       "de vento já perdeu habilidade útil." + corr)
            else:
                desenhar_mapa_calor(fig, d["serie_previsao"], d["crit_previsao"])
                sub = ("Mesma leitura do mapa de calor do histórico, olhando "
                       "para frente. Rodada única: não há medida de "
                       "confiança." + corr)
            _cabecalho_sobre(
                fig, sec(f"Previsão para os próximos {d['dias_previsao']} dias"),
                sub, topo=0.78)
            numero = _fecha(pdf, fig, rodape, numero)

            if any(l.get("direcao") is not None
                   for l in d["serie_previsao"].values()):
                fig = plt.Figure(figsize=A4_DEITADO)
                desenhar_direcao(fig, d["serie_previsao"], d["crit_previsao"],
                                 None, (d["lat"], d["lon"]), topo=0.80)
                _cabecalho_sobre(fig, sec("Direção do vento prevista"),
                                 "Para onde a deriva vai em cada hora dos "
                                 "próximos dias. Cor da seta = chance de a "
                                 "hora servir." if conj else
                                 "Para onde a deriva vai em cada hora dos "
                                 "próximos dias.", topo=0.80)
                numero = _fecha(pdf, fig, rodape, numero)

            nota = "Em verde, as cinco janelas previstas mais longas."
            if conj:
                nota += ("  A coluna de confiança é a média, na janela, da "
                         "fração de rodadas que aprovaram cada hora.")
            numero = _paginas_de_tabela(
                pdf, sec("Janelas previstas"),
                f"Próximos {d['dias_previsao']} dias  ·  {d['proxima']}",
                d["janelas_previsao"], maiores_janelas(d["janelas_previsao"]),
                rodape, numero, com_chuva=True, com_prob=bool(conj),
                nota=nota)

    return numero - 1


# =====================================================================
# BLOCO 11 — ABA DE RELATÓRIO
# =====================================================================


class AbaRelatorio(ttk.Frame):
    """Junta tudo e grava o relatório em PDF."""

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.fila = queue.Queue()
        self._gerando = False
        self._construir()

    def _construir(self):
        painel = ttk.LabelFrame(self, text="Relatório padrão")
        painel.pack(side="top", fill="x", padx=8, pady=(8, 4))

        l1 = ttk.Frame(painel)
        l1.pack(side="top", fill="x", padx=6, pady=(6, 2))
        hoje = datetime.now().date()

        ttk.Label(l1, text="Histórico de:").pack(side="left")
        self.var_ini = tk.StringVar(value=(hoje - timedelta(days=14)).isoformat())
        ttk.Entry(l1, textvariable=self.var_ini, width=12).pack(side="left", padx=(4, 8))
        ttk.Label(l1, text="até:").pack(side="left")
        self.var_fim = tk.StringVar(value=hoje.isoformat())
        ttk.Entry(l1, textvariable=self.var_fim, width=12).pack(side="left", padx=(4, 12))
        for dias in (15, 30):
            ttk.Button(l1, text=f"{dias} dias", width=8,
                       command=lambda x=dias: self.ultimos_dias(x)).pack(side="left", padx=2)

        ttk.Label(l1, text="   Previsão:").pack(side="left")
        self.var_dias = tk.StringVar(value="7")
        ttk.Combobox(l1, textvariable=self.var_dias, width=4, state="readonly",
                     values=("1", "2", "3", "4", "5", "6", "7")).pack(side="left", padx=4)
        ttk.Label(l1, text="dias").pack(side="left", padx=(0, 12))

        ttk.Label(l1, text="Fuso:").pack(side="left")
        self.var_fuso = tk.StringVar(value="-3")
        ttk.Combobox(l1, textvariable=self.var_fuso, width=4, state="readonly",
                     values=("-2", "-3", "-4", "-5")).pack(side="left", padx=4)

        l2 = ttk.Frame(painel)
        l2.pack(side="top", fill="x", padx=6, pady=(2, 8))
        self.btn_gerar = botao_principal(l2, "Gerar relatório PDF…",
                                         self.gerar)
        self.btn_gerar.pack(side="left")
        ttk.Label(l2, text="   Usa os critérios da aba 2 (Delta T e vento), o "
                           "limite de chuva da aba 3 e os parâmetros de "
                           "interpolação da vista de mapas.",
                  foreground="#666").pack(side="left")

        quadro = ttk.LabelFrame(self, text="Andamento")
        quadro.pack(side="top", fill="both", expand=True, padx=8, pady=(4, 8))
        self.txt = tk.Text(quadro, height=18, wrap="word", relief="flat",
                           background="#fbfbfa", font=("Consolas", 9))
        self.txt.pack(side="top", fill="both", expand=True, padx=6, pady=6)
        self.anotar("O relatório sai com estas seções, nesta ordem:\n"
                    "  • localização da área e estações utilizadas\n"
                    "  • tabela das janelas do período, com as cinco maiores "
                    "destacadas\n"
                    "  • meteorograma com as janelas em verde e as setas do "
                    "vento\n"
                    "  • mapa de calor hora × dia\n"
                    "  • os três mapas de interpolação lado a lado\n"
                    "  • direção do vento: mapa, rosas e para onde vai a deriva\n"
                    "  • conferência modelo × medido (quando há tabelas do "
                    "INMET)\n"
                    "  • previsão dos próximos dias em mapa de calor e em "
                    "direção\n"
                    "  • tabela das janelas previstas\n\n"
                    "O histórico usa a fonte escolhida na aba 2 (medido, "
                    "modelo corrigido ou modelo), e a previsão usa a correção "
                    "escolhida na aba 3.\n\n"
                    "Marque a área na aba 1 e clique em “Gerar relatório PDF”.")

    def anotar(self, texto):
        self.txt.insert("end", texto + "\n")
        self.txt.see("end")

    def ultimos_dias(self, dias):
        hoje = datetime.now().date()
        self.var_ini.set((hoje - timedelta(days=dias - 1)).isoformat())
        self.var_fim.set(hoje.isoformat())

    # ------------------------------------------------------------------
    def gerar(self):
        if self._gerando:
            return
        if not self.app.proximas:
            messagebox.showwarning(
                "Sem área definida",
                "Volte à aba 1 e marque a área antes de gerar o relatório.")
            return

        crit = self.app.aba_series.ler_criterios()
        if crit is None:
            return
        crit_prev = self.app.aba_previsao.ler_criterios()
        if crit_prev is None:
            return

        ini, fim = self.var_ini.get().strip(), self.var_fim.get().strip()
        try:
            if datetime.strptime(fim, "%Y-%m-%d") < datetime.strptime(ini, "%Y-%m-%d"):
                raise ValueError
        except ValueError:
            messagebox.showerror("Período inválido",
                                 "Use AAAA-MM-DD, com a data final depois da "
                                 "inicial.")
            return

        caminho = filedialog.asksaveasfilename(
            title="Salvar o relatório",
            defaultextension=".pdf",
            initialfile=f"relatorio_janela_{datetime.now():%Y%m%d_%H%M}.pdf",
            filetypes=[("PDF", "*.pdf")])
        if not caminho:
            return

        self._gerando = True
        self.btn_gerar.config(state="disabled", text="Gerando…")
        self.txt.delete("1.0", "end")
        self.anotar(f"Gerando {os.path.basename(caminho)}…")

        series_aba = self.app.aba_series
        previsao_aba = self.app.aba_previsao
        fonte = series_aba.var_fonte.get()
        if fonte == FONTE_API:
            fonte = FONTE_MODELO
        # a conferência por antecedência só vale se foi feita para esta área
        antecedencias = None
        if series_aba.antecedencias and series_aba.resultado \
                and series_aba.resultado.get("area") == (self.app.lat,
                                                         self.app.lon):
            antecedencias = series_aba.antecedencias
        threading.Thread(
            target=self._trabalho,
            args=(caminho, list(self.app.proximas), ini, fim,
                  int(self.var_fuso.get()), int(self.var_dias.get()),
                  crit, crit_prev, self.app.lat, self.app.lon,
                  series_aba._parametros_mapa() or (2.0, 140, True),
                  fonte, dict(self.app.medidos), self.app.calibracao,
                  previsao_aba.corrigir(), antecedencias,
                  list(getattr(self.app, "campo", None) or [])),
            daemon=True).start()
        self.after(150, self._checar_fila)

    def _trabalho(self, caminho, alvo, ini, fim, fuso, dias, crit, crit_prev,
                  lat, lon, par_mapa, fonte=FONTE_MODELO, medidos=None,
                  calibracao=None, corrigir=True, antecedencias=None,
                  campo=None):
        """Baixa tudo, monta as páginas e grava. Fora da thread da interface."""
        try:
            def avisar(t):
                self.fila.put(("andamento", "  " + t))

            h = montar_historico(alvo, ini, fim, fuso, crit, lat, lon, fonte,
                                 METODO_IDW, medidos, calibracao, avisar=avisar,
                                 recuar=True)
            serie, janelas, usadas = h["serie"], h["janelas"], h["usadas"]
            falhas = list(h["falhas"])
            alt, origem_alt = h["alt"]
            if h.get("calibracao"):
                calibracao = h["calibracao"]
                self.fila.put(("calibracao", calibracao))

            # A previsão vai direto no ponto da área: o modelo já interpola
            # para a coordenada, e passar três saídas dele por IDW só
            # importaria o viés de lugares que não são o talhão.
            avisar(f"previsão de {dias} dias no ponto, com o conjunto…")
            serie_prev, janelas_prev, conjunto = {}, [], None
            correcao_texto, corrigida = "", False
            try:
                crit_prev["limiar_p"] = LIMIAR_P
                p = montar_previsao(usadas or alvo, dias, fuso, crit_prev,
                                    METODO_PONTO, lat, lon, MODO_ENSEMBLE,
                                    calibracao, corrigir, avisar=avisar)
                serie_prev, janelas_prev = p["serie"], p["janelas"]
                conjunto, crit_prev = p.get("conjunto"), p["crit"]
                try:
                    arquivar_previsao(p, lat, lon, crit_prev, fuso)
                except Exception:
                    pass
                correcao_texto, corrigida = p.get("correcao", ""), p["corrigida"]
                falhas += p["avisos"]
            except Exception as e:
                falhas.append(f"previsão: {e}")

            _, n_validas, n_aptas = resumir(serie, janelas, crit)
            disp_dt = [l["disp_dt"] for l in serie.values()
                       if l.get("disp_dt") is not None]
            disp_v = [l["disp_vento"] for l in serie.values()
                      if l.get("disp_vento") is not None]
            dispersao = ""
            if disp_dt and disp_v:
                dispersao = (
                    f"Discordância média entre as estações:  Delta T "
                    f"{_fmt(sum(disp_dt) / len(disp_dt))} °C e vento "
                    f"{_fmt(sum(disp_v) / len(disp_v))} km/h.")

            aptas = [l for l in serie.values() if e_apto(classificar(l, crit))]
            d_apt, c_apt, *_ = media_vetorial(aptas)
            direcao_texto = ("Vento nas horas aptas:  "
                             + texto_direcao(d_apt, c_apt) + "."
                             if d_apt is not None else "")

            avisar("montando as páginas…")
            com_dado, esperadas, pct_cob = cobertura(serie)
            conj_txt = ""
            if conjunto:
                conj_txt = (f"Previsão por conjunto de {conjunto['membros']} "
                            f"rodadas ({', '.join(conjunto['modelos'])}).")
            rotulo_fonte = {
                FONTE_MEDIDO: "estações do INMET (medido) e Open-Meteo "
                              "(previsão)",
                FONTE_CORRIGIDO: "Open-Meteo corrigido pela calibração local",
            }.get(h["fonte"], "Open-Meteo (modelos oficiais)")
            dados = {
                "lat": lat, "lon": lon, "ini": ini, "fim": fim,
                "fuso": fuso, "conjunto": conjunto, "conjunto_texto": conj_txt,
                "cobertura": pct_cob,
                "bulbo": ("Psicrométrico, com a pressão da altitude"
                          if crit.get("usar_psicrometrico") else "Stull (2011)"),
                "area_ha": self.app.area_ha, "origem": self.app.origem or "—",
                "proximas": usadas,
                "medidos_codigos": set(h.get("medidas") or {}),
                "pontos_area": self.app.aba_area.pontos_area,
                "segs_uf": self._segs_uf(), "segs_mun": self._segs_mun(),
                "crit": crit, "crit_previsao": crit_prev,
                "serie": serie, "janelas": janelas,
                "serie_previsao": serie_prev, "janelas_previsao": janelas_prev,
                "previsao_corrigida": corrigida,
                "correcao_texto": correcao_texto,
                "dias_previsao": dias,
                "proxima": proxima_janela(janelas_prev, fuso),
                "pontos_mapa": resumo_por_estacao(h["series"], usadas),
                "potencia": par_mapa[0], "celulas": par_mapa[1],
                "em_km": par_mapa[2],
                "n_validas": n_validas, "n_aptas": n_aptas,
                "metodo": f"{len(usadas)} estações interpoladas por IDW "
                          f"(potência {par_mapa[0]:g}), com correção de altitude",
                "altitude": f"{alt:.0f} m ({origem_alt})",
                "dispersao": dispersao,
                "direcao_texto": direcao_texto,
                "texto_fonte": texto_fonte(h),
                "campo": campo,
                "campo_texto": (texto_campo(comparar_campo(campo, serie, crit))
                                if campo else ""),
                "verif": h.get("verif"),
                "antecedencias": antecedencias,
                "fonte": rotulo_fonte,
            }
            paginas = gerar_relatorio_pdf(caminho, dados)
            self.fila.put(("pronto", (caminho, paginas, falhas)))
        except Exception as e:
            self.fila.put(("erro", str(e)))

    def _segs_uf(self):
        cont = self.app.aba_area._contorno_uf or {}
        return [parte for partes in cont.values() for parte in partes
                if len(parte) > 2]

    def _segs_mun(self):
        aba = self.app.aba_area
        segs = []
        try:
            for sigla in aba._ufs_em_cena():
                segs += [m["p"] for m in aba.municipios_do_estado(sigla)
                         if len(m["p"]) > 2]
        except Exception:
            pass
        return segs

    def _checar_fila(self):
        try:
            while True:
                tipo, carga = self.fila.get_nowait()
                if tipo == "andamento":
                    self.anotar(carga)
                    self.app.status(carga.strip())
                elif tipo == "calibracao":
                    self.app.calibracao = carga
                    try:
                        gravar_calibracao(carga)
                    except Exception as e:
                        self.anotar(f"  (calibração não gravada: {e})")
                elif tipo == "erro":
                    self._terminar()
                    self.anotar("\nFalhou: " + carga)
                    messagebox.showerror("Não consegui gerar o relatório", carga)
                    return
                elif tipo == "pronto":
                    caminho, paginas, falhas = carga
                    self._terminar()
                    self.anotar(f"\nPronto: {paginas} páginas em {caminho}")
                    if falhas:
                        self.anotar("Ficaram de fora: " + "; ".join(falhas))
                    self.app.status(f"Relatório com {paginas} páginas gravado "
                                    f"em {os.path.basename(caminho)}.")
                    messagebox.showinfo(
                        "Relatório pronto",
                        f"{paginas} páginas gravadas em:\n{caminho}")
                    return
        except queue.Empty:
            pass
        if self._gerando:
            self.after(150, self._checar_fila)

    def _terminar(self):
        self._gerando = False
        self.btn_gerar.config(state="normal", text="Gerar relatório PDF…")


# =====================================================================
# BLOCO 12 — ANÁLISE DE VOOS
# =====================================================================
#
# Aqui a ferramenta vira para trás e olha o que já foi aplicado. O arquivo
# de operações do dron traz, por voo, onde, quando e por quanto tempo — e
# com isso dá para reconstruir em que condição cada voo aconteceu.
#
# Duas diferenças em relação ao resto do programa, e as duas importam:
#
# 1. Os voos não estão num lugar só. Este arquivo tem operações separadas
#    por mais de mil quilômetros, então cada agrupamento precisa das suas
#    próprias estações. Usar as estações de uma fazenda para julgar o voo
#    de outra seria pior do que não julgar.
#
# 2. O dron voa a 4 ou 5 m, não aos 2 m da barra terrestre. O vento nessa
#    altura é uns 20% maior, e como cada voo registra a própria altura,
#    dá para usar a dele em vez de um valor fixo.
#
# E o veredito é probabilidade, não sentença: a condição no talhão foi
# estimada de estações a dezenas de quilômetros, e a discordância entre
# elas — que a ferramenta já mede — vira a incerteza dessa estimativa.

RAIO_LOCAL_KM = 25.0        # agrupamento de voos no mesmo local
# Simplificação do traçado: ~0,5 m. Era 0,00012 (~13 m), maior que a
# distância entre faixas (7 a 10 m): as manobras de uma faixa para a outra
# sumiam e o mapa ganhava diagonais cortando várias faixas.
TOL_ROTA = 0.000005

CLASSES_VOO = (
    (0.80, "apta", "condição apta"),
    (0.50, "limite", "no limite"),
    (0.00, "impropria", "condição imprópria"),
)
COR_VOO = {
    "apta": "#2e7d32",
    "limite": "#8dc26f",
    "impropria": "#c81010",
    "chuva": "#6a3fa0",
    "inversao": "#22304f",
    "sem_dado": "#b9b9b9",
}
NOME_CLASSE_VOO = {
    "apta": "condição apta",
    "limite": "no limite",
    "impropria": "condição imprópria",
    "chuva": "chuva na hora do voo",
    "inversao": "risco de inversão térmica",
    "sem_dado": "sem dado meteorológico",
}
ORDEM_CLASSE_VOO = ("apta", "limite", "impropria", "chuva", "inversao",
                    "sem_dado")


def _campo(props, *nomes):
    """Primeiro campo presente, entre variações de nome possíveis."""
    for nome in nomes:
        if nome in props and props[nome] not in (None, ""):
            return props[nome]
    return None


def _vertices(geometria):
    """Lista de (lon, lat) de qualquer geometria de linha."""
    t = geometria.get("type")
    c = geometria.get("coordinates") or []
    if t == "LineString":
        return [(p[0], p[1]) for p in c if len(p) >= 2]
    if t == "MultiLineString":
        return [(p[0], p[1]) for parte in c for p in parte if len(p) >= 2]
    if t == "Point":
        return [(c[0], c[1])] if len(c) >= 2 else []
    if t == "Polygon":
        return [(p[0], p[1]) for p in (c[0] if c else []) if len(p) >= 2]
    return []


# ---------------------------------------------------------------------
# Trechos do voo: aplicação × ida e volta
# ---------------------------------------------------------------------
# O traçado gravado pelo dron inclui a ida da base até a área e a volta
# para trocar bateria e reabastecer. No mapa, essas retas saíam todas da
# base, em leque, por cima das faixas aplicadas. Aqui o traçado é separado:
# a subida, o pairado e as manobras curtas junto da base, mais a primeira
# reta longa que sai de lá, são a ida; o mesmo, de trás para a frente, é a
# volta. O resto é aplicação. O arquivo não diz quando o bico estava
# aberto, então isto é uma leitura do traçado, não registro do equipamento.
R_BASE_M = 50.0          # raio das manobras de decolagem e de pouso
L_TRANSITO_M = 40.0      # reta a partir deste comprimento pode ser ida ou volta
ANG_RETA = 12.0          # mudança de rumo que ainda conta como a mesma reta


def _em_metros(pontos):
    """(lon, lat) → (x, y) em metros, a partir do primeiro ponto."""
    lon0, lat0 = pontos[0]
    kx = 111320.0 * math.cos(math.radians(lat0))
    return [((x - lon0) * kx, (y - lat0) * 110540.0) for x, y in pontos]


def _retas(pm):
    """Vértices agrupados em retas: lista de (índice inicial, índice final)."""
    retas, i0, ref = [], 0, None
    for i in range(1, len(pm)):
        dx, dy = pm[i][0] - pm[i - 1][0], pm[i][1] - pm[i - 1][1]
        if dx == 0 and dy == 0:
            continue
        r = math.degrees(math.atan2(dx, dy))
        if ref is not None and abs((r - ref + 180) % 360 - 180) > ANG_RETA:
            retas.append((i0, i - 1))
            i0, ref = i - 1, r
            continue
        cx, cy = pm[i][0] - pm[i0][0], pm[i][1] - pm[i0][1]
        ref = math.degrees(math.atan2(cx, cy)) if math.hypot(cx, cy) > 3 else r
    retas.append((i0, len(pm) - 1))
    return [(a, b) for a, b in retas if b > a]


def separar_trechos(rota):
    """Separa o traçado em aplicação e deslocamento (ida e volta à base).

    Devolve {"aplicacao": [linhas], "deslocamento": [linhas], "base": ponto}.
    Se não der para separar, o traçado inteiro fica como aplicação — melhor
    mostrar uma reta a mais do que esconder faixa aplicada.
    """
    if not rota or len(rota) < 3:
        return {"aplicacao": [list(rota or [])], "deslocamento": [],
                "base": rota[0] if rota else None}
    pm = _em_metros(rota)
    info = []
    for a, b in _retas(pm):
        info.append({"a": a, "b": b, "p0": pm[a], "p1": pm[b],
                     "L": math.hypot(pm[b][0] - pm[a][0], pm[b][1] - pm[a][1])})
    base, pouso = pm[0], pm[-1]

    def perto(p, q):
        return math.hypot(p[0] - q[0], p[1] - q[1]) <= R_BASE_M

    n = len(info)
    k = 0
    while k < n and info[k]["L"] < L_TRANSITO_M and perto(info[k]["p1"], base):
        k += 1                       # subida, pairado e manobras junto da base
    if k < n and perto(info[k]["p0"], base) and info[k]["L"] >= L_TRANSITO_M:
        k += 1                       # a ida até a área
    m = n - 1
    while m >= k and info[m]["L"] < L_TRANSITO_M and perto(info[m]["p0"], pouso):
        m -= 1                       # aproximação e pouso
    if m >= k and perto(info[m]["p1"], pouso) and info[m]["L"] >= L_TRANSITO_M:
        m -= 1                       # a volta para a base
    if k > m:
        return {"aplicacao": [list(rota)], "deslocamento": [], "base": rota[0]}

    saida = {"aplicacao": [], "deslocamento": [], "base": rota[0]}
    atual, pedaco = None, []
    for j, r in enumerate(info):
        classe = "aplicacao" if k <= j <= m else "deslocamento"
        if classe != atual:
            if pedaco:
                saida[atual].append(pedaco)
            atual, pedaco = classe, [rota[r["a"]]]
        pedaco.extend(rota[r["a"] + 1: r["b"] + 1])
    if pedaco:
        saida[atual].append(pedaco)
    return saida


def trechos_aplicacao(v):
    """Linhas aplicadas do voo (o traçado inteiro, se não foi separado)."""
    linhas = v.get("rota_aplicacao")
    if linhas is None:
        linhas = [v["rota"]] if v.get("rota") else []
    return [l for l in linhas if len(l) >= 2]


def comprimento_m(linhas):
    total = 0.0
    for l in linhas:
        if len(l) < 2:
            continue
        pm = _em_metros(l)
        total += sum(math.hypot(pm[i][0] - pm[i - 1][0], pm[i][1] - pm[i - 1][1])
                     for i in range(1, len(pm)))
    return total


def agrupar_bases(voos, raio_m=30.0):
    """Pontos de decolagem, juntando os que ficam a menos de `raio_m`.

    Devolve [{"lon", "lat", "voos", "datas"}], para marcar onde ficou a base
    (o caminhão) em cada dia.
    """
    grupos = []
    for v in voos:
        b = v.get("base")
        if not b:
            continue
        for g in grupos:
            kx = 111320.0 * math.cos(math.radians(g["lat"]))
            if math.hypot((b[0] - g["lon"]) * kx,
                          (b[1] - g["lat"]) * 110540.0) <= raio_m:
                g["voos"] += 1
                g["datas"].add(v["inicio"].strftime("%d/%m/%Y"))
                break
        else:
            grupos.append({"lon": b[0], "lat": b[1], "voos": 1,
                           "datas": {v["inicio"].strftime("%d/%m/%Y")}})
    for g in grupos:
        g["datas"] = sorted(g["datas"],
                            key=lambda s: datetime.strptime(s, "%d/%m/%Y"))
    return grupos


def ler_operacoes(caminho, fuso=-3):
    """Lê o arquivo de operações do dron e devolve a lista de voos.

    Espera um GeoJSON com uma feição por voo, cada uma com o traçado e as
    propriedades que o próprio equipamento grava. Os nomes dos campos
    variam entre versões do exportador, então cada um é procurado por
    algumas grafias antes de desistir.

    A data e a hora são tratadas como horário local — é assim que o
    equipamento grava, e é assim que o operador leu o relógio.
    """
    with open(caminho, encoding="utf-8") as f:
        j = json.load(f)
    feicoes = j.get("features") if isinstance(j, dict) else None
    if not feicoes:
        raise ValueError("o arquivo não tem feições (features) de voo")

    voos, sem_hora = [], 0
    for i, f in enumerate(feicoes):
        props = f.get("properties") or {}
        pontos = _vertices(f.get("geometry") or {})
        if not pontos:
            continue

        data = _campo(props, "Data", "data", "date")
        hora = _campo(props, "Hora", "hora", "time")
        if not data or not hora:
            sem_hora += 1
            continue
        try:
            inicio = datetime.strptime(f"{str(data)[:10]} {str(hora)[:8]}",
                                       "%Y-%m-%d %H:%M:%S")
        except ValueError:
            try:
                inicio = datetime.strptime(f"{str(data)[:10]} {str(hora)[:5]}",
                                           "%Y-%m-%d %H:%M")
            except ValueError:
                sem_hora += 1
                continue
        inicio = inicio.replace(tzinfo=timezone.utc)   # local, rotulado UTC

        duracao = _num(_campo(props, "Flight Time", "flight_time",
                              "Tempo de voo")) or 0.0
        lats = [p[1] for p in pontos]
        lons = [p[0] for p in pontos]
        rota = _simplifica(pontos, TOL_ROTA)
        trechos = separar_trechos(rota)

        voos.append({
            "id": str(_campo(props, "name", "Name", "id") or f"voo {i + 1}"),
            "aeronave": str(_campo(props, "Aircraft Name", "aeronave") or "—"),
            "piloto": str(_campo(props, "Pilot Name", "piloto") or "—"),
            "modo": str(_campo(props, "Mode Selection", "modo") or "—"),
            "inicio": inicio,
            "duracao_h": duracao,
            "fim": inicio + timedelta(hours=max(duracao, 1 / 60)),
            "lat": sum(lats) / len(lats),
            "lon": sum(lons) / len(lons),
            "rota": rota,
            "rota_aplicacao": trechos["aplicacao"],
            "deslocamentos": trechos["deslocamento"],
            "base": trechos["base"],
            "altura": _num(_campo(props, "Altura (m)", "altura")),
            "espacamento": _num(_campo(props, "Espaçamento (m)", "espacamento")),
            "velocidade": _num(_campo(props, "Velocidade (Km/h)", "velocidade")),
            "area_ha": _num(_campo(props, "Area (Ha)", "area_ha")) or 0.0,
            "litros": _num(_campo(props, "Total Pulverizado (L)", "litros")),
            "taxa": _num(_campo(props, "Taxa de aplicação (L/Ha)", "taxa")),
        })

    if not voos:
        raise ValueError("nenhum voo com data e hora utilizáveis no arquivo")
    voos.sort(key=lambda v: v["inicio"])
    completar_alturas(voos)
    return voos, sem_hora


def completar_alturas(voos):
    """Dá altura aos voos que não a registraram (modo manual, M/M+).

    O equipamento só grava a altura nos voos em rota automática. Sem ela,
    o voo manual caía na altura da barra terrestre (2 m) e o vento dele
    saía 17% menor que o dos voos automáticos do mesmo dia — diferença que
    é do registro, não do tempo. Usa a mediana dos voos da mesma aeronave
    no mesmo dia; faltando, a da aeronave no arquivo todo; e marca a
    altura como estimada.
    """
    def mediana(vs):
        vs = sorted(vs)
        if not vs:
            return None
        m = len(vs) // 2
        return vs[m] if len(vs) % 2 else (vs[m - 1] + vs[m]) / 2

    por_dia, por_aeronave, todas = {}, {}, []
    for v in voos:
        if v.get("altura"):
            por_dia.setdefault((v["aeronave"], v["inicio"].date()), []).append(v["altura"])
            por_aeronave.setdefault(v["aeronave"], []).append(v["altura"])
            todas.append(v["altura"])
    for v in voos:
        if v.get("altura"):
            v["altura_origem"] = "registrada"
            continue
        estimada = (mediana(por_dia.get((v["aeronave"], v["inicio"].date()), []))
                    or mediana(por_aeronave.get(v["aeronave"], []))
                    or mediana(todas))
        if estimada:
            v["altura"] = estimada
            v["altura_origem"] = "estimada"
        else:
            v["altura_origem"] = "ausente"
    return voos


def agrupar_locais(voos, raio_km=RAIO_LOCAL_KM):
    """Junta os voos que aconteceram no mesmo lugar.

    Agrupamento simples por proximidade, sem biblioteca: para dezenas ou
    centenas de voos é instantâneo, e o critério — mesmo local se estiver
    a menos de `raio_km` do centro do grupo — é o que faz sentido aqui,
    porque o que define o grupo é compartilhar as mesmas estações.
    """
    grupos = []
    for v in voos:
        for g in grupos:
            if haversine(v["lat"], v["lon"], g["lat"], g["lon"]) <= raio_km:
                g["voos"].append(v)
                n = len(g["voos"])
                g["lat"] = sum(x["lat"] for x in g["voos"]) / n
                g["lon"] = sum(x["lon"] for x in g["voos"]) / n
                break
        else:
            grupos.append({"lat": v["lat"], "lon": v["lon"], "voos": [v]})

    for i, g in enumerate(sorted(grupos, key=lambda g: -len(g["voos"])), 1):
        g["numero"] = i
        g["nome"] = f"Local {i}"
        g["area_ha"] = sum(v["area_ha"] or 0 for v in g["voos"])
        g["ini"] = min(v["inicio"] for v in g["voos"]).date()
        g["fim"] = max(v["fim"] for v in g["voos"]).date()
        g["raio_km"] = max(haversine(v["lat"], v["lon"], g["lat"], g["lon"])
                           for v in g["voos"])
    return sorted(grupos, key=lambda g: -len(g["voos"]))


def _horas_do_voo(voo, serie):
    """Horas da série que o voo atravessa, com o peso de cada uma.

    Um voo de dez minutos cai dentro de uma hora só; um que começa às
    17:55 e dura vinte minutos pega duas, e nesse caso cada uma pesa
    proporcionalmente ao tempo que o voo passou nela.
    """
    ini, fim = voo["inicio"], voo["fim"]
    if fim <= ini:
        fim = ini + timedelta(minutes=1)
    pedacos = []
    h = ini.replace(minute=0, second=0, microsecond=0)
    while h < fim:
        prox = h + timedelta(hours=1)
        sobreposicao = (min(fim, prox) - max(ini, h)).total_seconds()
        if sobreposicao > 0 and h in serie:
            pedacos.append((serie[h], sobreposicao))
        h = prox
    total = sum(p for _, p in pedacos)
    return [(l, p / total) for l, p in pedacos] if total else []


def avaliar_voo(voo, serie, crit, sorteios=600, semente=12345):
    """Reconstrói a condição durante o voo e devolve a probabilidade.

    Por que probabilidade e não sim/não: a condição no talhão não foi
    medida, foi estimada de estações a dezenas de quilômetros. A
    ferramenta já sabe o quanto as estações discordam entre si, e essa
    discordância é justamente a incerteza da estimativa. Sorteando dentro
    dela, a pergunta "esse voo pegou condição boa?" passa a ter a resposta
    honesta: "em X% dos cenários compatíveis com o que foi medido, sim".

    Chuva e inversão não entram no sorteio: são impedimentos, não faixas.
    Se apareceram, o voo sai marcado por eles.
    """
    pedacos = _horas_do_voo(voo, serie)
    if not pedacos:
        return dict(voo, classe="sem_dado", p_apta=None, motivo="sem dado",
                    delta_t=None, vento=None, rajada=None, inversao=None)

    # o vento é levado à altura que este voo registrou, não à da barra
    altura = voo.get("altura") or crit.get("altura_vento", ALTURA_BARRA)
    fator = fator_altura_vento(altura, crit.get("z0", RUGOSIDADE))

    def media(chave, bruto=False):
        num = den = 0.0
        for l, peso in pedacos:
            v = l.get(chave)
            if v is None:
                continue
            num += v * peso
            den += peso
        return num / den if den else None

    dt = media("delta_t")
    v10 = media("vento_10m")
    if v10 is None:
        v10 = media("vento")
    r10 = media("rajada_10m")
    vento = None if v10 is None else v10 * fator
    rajada = None if r10 is None else r10 * fator
    # chuva horária é o acumulado da hora que TERMINA no rótulo: a do voo
    # das 10:05 às 10:15 está no rótulo das 11:00, não no das 10:00
    chuva = intensidade_no_intervalo(serie, voo["inicio"], voo["fim"]) or 0.0
    inversoes = [l.get("inversao") for l, _ in pedacos]
    inversao = ("alto" if "alto" in inversoes
                else "moderado" if "moderado" in inversoes else "baixo")

    direcao, constancia, *_ = media_vetorial(
        [l for l, _ in pedacos], pesos=[p for _, p in pedacos])
    saida = dict(voo, delta_t=dt, vento=vento, rajada=rajada, chuva=chuva,
                 inversao=inversao, altura_usada=altura,
                 temp=media("temp"), ur=media("ur"),
                 direcao=direcao, constancia_dir=constancia)

    if dt is None or vento is None:
        saida.update(classe="sem_dado", p_apta=None, motivo="sem dado")
        return saida

    lim_chuva = crit.get("chuva_max")
    if lim_chuva is not None and chuva > lim_chuva:
        saida.update(classe="chuva", p_apta=0.0, motivo="choveu na hora do voo")
        return saida
    if crit.get("bloquear_inversao", True) and inversao == "alto":
        saida.update(classe="inversao", p_apta=0.0,
                     motivo="risco alto de inversão térmica")
        return saida

    sd_dt, sd_v = incerteza_total(
        {"sd_dt": media("sd_dt") or 0.0, "sd_vento": media("sd_vento") or 0.0},
        crit)
    sd_dt = max(sd_dt, 0.15)      # nunca zero: sempre há incerteza
    sd_v = max(sd_v, 0.5)

    # semente fixa por voo: hash() de texto muda a cada execução do Python,
    # e o mesmo voo saía "no limite" numa rodada e "impróprio" na outra
    import zlib
    rng = np.random.default_rng(semente
                                + zlib.crc32(str(voo["id"]).encode()) % 100000)
    amostra_dt = rng.normal(dt, sd_dt, sorteios)
    amostra_v = np.maximum(0.0, rng.normal(vento, sd_v, sorteios))
    dentro = ((amostra_dt >= crit["dt_min"]) & (amostra_dt <= crit["dt_max"])
              & (amostra_v >= crit["vento_min"])
              & (amostra_v <= crit["vento_max"]))
    fora_rajada = np.zeros(sorteios, dtype=bool)
    if crit.get("rajada_max") and rajada is not None:
        fator_r = rajada / max(vento, 0.1)
        fora_rajada = (amostra_v * fator_r) > crit["rajada_max"]
        dentro &= ~fora_rajada
    p = float(dentro.mean())

    # o que mais reprovou nos sorteios, para o relatório poder dizer
    motivos = {
        "Delta T baixo": float((amostra_dt < crit["dt_min"]).mean()),
        "Delta T alto": float((amostra_dt > crit["dt_max"]).mean()),
        "vento fraco": float((amostra_v < crit["vento_min"]).mean()),
        "vento forte": float((amostra_v > crit["vento_max"]).mean()),
        "rajada forte": float(fora_rajada.mean()),
    }
    motivo = max(motivos.items(), key=lambda kv: kv[1])
    saida.update(p_apta=p, classe=classe_do_voo(p),
                 motivo="dentro do critério" if p >= 0.8 else motivo[0],
                 incerteza_dt=sd_dt, incerteza_vento=sd_v)
    if inversao == "moderado" and saida["classe"] == "apta":
        saida["classe"] = "limite"
        saida["motivo"] = "estratificação estável"
    return saida


def classe_do_voo(p):
    if p is None:
        return "sem_dado"
    for limite, nome, _ in CLASSES_VOO:
        if p >= limite:
            return nome
    return "impropria"


def resumir_voos(avaliados, por=None):
    """Agrega os voos por dia, local, piloto ou aeronave.

    `por` é o nome do campo de agrupamento; None agrupa por dia.
    """
    grupos = {}
    for v in avaliados:
        chave = (v["inicio"].strftime("%d/%m/%Y") if por is None
                 else str(v.get(por) or "—"))
        g = grupos.setdefault(chave, {"n": 0, "ha": 0.0, "classes": {},
                                      "p": []})
        g["n"] += 1
        g["ha"] += v.get("area_ha") or 0.0
        g["classes"][v["classe"]] = g["classes"].get(v["classe"], 0) + 1
        if v.get("p_apta") is not None:
            g["p"].append(v["p_apta"])

    saida = []
    for chave, g in grupos.items():
        aptos = g["classes"].get("apta", 0)
        ha_apta = sum(v.get("area_ha") or 0.0 for v in avaliados
                      if (v["inicio"].strftime("%d/%m/%Y") if por is None
                          else str(v.get(por) or "—")) == chave
                      and v["classe"] == "apta")
        saida.append({
            "chave": chave, "n": g["n"], "ha": g["ha"], "ha_apta": ha_apta,
            "aptos": aptos,
            "p_media": sum(g["p"]) / len(g["p"]) if g["p"] else None,
            "classes": g["classes"],
        })
    return sorted(saida, key=lambda x: x["chave"])


# =====================================================================
# BLOCO 12B — CHUVA DEPOIS DA APLICAÇÃO, ÁREA COM PROBLEMA E MAPAS
# =====================================================================
#
# Um voo pode ter sido feito em condição perfeita e mesmo assim falhar:
# se chove pouco depois, o produto é lavado antes de ser absorvido. Por
# isso cada voo ganha, além da condição NA HORA, a chuva acumulada nas
# horas SEGUINTES (1, 2, 6 e 24 h), em cada fonte disponível:
#
#   - cada estação com pluviômetro (medido, quando há tabela do INMET);
#   - o modelo no próprio talhão, corrigido pela calibração local.
#
# As fontes são mostradas lado a lado, sem média. Chuva de verão é
# localizada: uma pancada em Feira de Santana, a 44 km, pode não ter
# molhado o talhão, e o talhão pode ter tomado chuva que nenhuma estação
# registrou. Quando as fontes discordam, é isso que o relatório diz.
#
# A convenção de tempo importa aqui: chuva horária, tanto no INMET quanto
# no Open-Meteo, é o acumulado da hora que TERMINA no rótulo. A chuva das
# 10:00 caiu entre 9 e 10h. Somar a janela depois de um voo que acabou às
# 10:14 começa pela hora rotulada 11:00, na proporção do pedaço dela que
# ficou depois das 10:14.

JANELAS_APOS = (1, 2, 6, 24)            # horas depois do fim do voo
LIMITE_LAVAGEM_MM = 2.0
JANELA_LAVAGEM_H = 6

NOME_LAVAGEM = {"seca": "sem chuva depois",
                "leve": "chuva leve depois",
                "lavagem": "chuva que pode ter lavado",
                "sem_dado": "sem dado de chuva"}
COR_LAVAGEM = {"seca": "#c9c4bb", "leve": "#a58ad6", "lavagem": "#3c2263",
               "sem_dado": "#e8e6e2"}
ORDEM_LAVAGEM = ("seca", "leve", "lavagem", "sem_dado")

# faixas de milímetros para colorir o mapa
FAIXAS_MM = (0.2, 1.0, 2.0, 5.0)
CORES_MM = ("#d6d2cb", "#cbbce6", "#977bca", "#6a3fa0", "#2e1a4f")
ROTULOS_MM = ("menos de 0,2 mm", "0,2 a 1 mm", "1 a 2 mm", "2 a 5 mm",
              "5 mm ou mais")

MODOS_COR_MAPA = ("Condição no voo", "Chuva depois da aplicação", "Data do voo",
                  "Hora do dia", "Taxa de aplicação (L/ha)", "Modo de voo")


def chuva_no_intervalo(serie, t0, t1, chave="chuva"):
    """Chuva entre t0 e t1 (mm), com o rótulo marcando o FIM da hora.

    Devolve (mm, horas_com_dado, horas_do_intervalo). mm é None quando
    nenhuma hora do intervalo tem dado.
    """
    if t1 <= t0:
        return 0.0, 0, 0
    total, com, esperadas = 0.0, 0, 0
    h = t0.replace(minute=0, second=0, microsecond=0) + timedelta(hours=1)
    while h - timedelta(hours=1) < t1:
        sobra = (min(t1, h) - max(t0, h - timedelta(hours=1))).total_seconds() / 3600
        if sobra > 0:
            esperadas += 1
            l = serie.get(h)
            v = None if l is None else l.get(chave)
            if v is not None:
                total += v * sobra
                com += 1
        h += timedelta(hours=1)
    return (total if com else None), com, esperadas


def intensidade_no_intervalo(serie, t0, t1, chave="chuva"):
    """Maior chuva horária (mm/h) entre as horas que o intervalo toca."""
    if t1 <= t0:
        t1 = t0 + timedelta(minutes=1)
    maior = None
    h = t0.replace(minute=0, second=0, microsecond=0) + timedelta(hours=1)
    while h - timedelta(hours=1) < t1:
        l = serie.get(h)
        v = None if l is None else l.get(chave)
        if v is not None:
            maior = v if maior is None else max(maior, v)
        h += timedelta(hours=1)
    return maior


def fontes_de_chuva(series_estacoes, estacoes, serie_ponto=None):
    """{rótulo: série} das fontes de chuva de um local.

    Estação medida entra só com as horas medidas — hora que o modelo
    completou não é pluviômetro. Estação sem pluviômetro fica de fora.
    """
    fontes = {}
    por_codigo = {e["codigo"]: e for e in estacoes}
    for cod, s in (series_estacoes or {}).items():
        if cod == "PONTO":
            continue
        medida = any(l.get("medido") for l in s.values())
        util = {ts: l for ts, l in s.items()
                if not (medida and l.get("origem"))}
        if not any(l.get("chuva") is not None for l in util.values()):
            continue
        e = por_codigo.get(cod, {})
        rotulo = (f'{e.get("nome", cod)[:18]} ({e.get("distancia", 0):.0f} km'
                  f'{", medido" if medida else ", modelo"})')
        fontes[rotulo] = util
    if serie_ponto:
        fontes["modelo no talhão"] = serie_ponto
    return fontes


def anotar_chuva(voo, fontes, janela_h=JANELA_LAVAGEM_H,
                 limite_mm=LIMITE_LAVAGEM_MM):
    """Acrescenta ao voo a chuva durante e depois dele, fonte por fonte."""
    por_fonte = {}
    for rotulo, s in fontes.items():
        durante = intensidade_no_intervalo(s, voo["inicio"], voo["fim"])
        apos = {}
        for h in sorted(set(JANELAS_APOS) | {int(janela_h)}):
            mm, com, esp = chuva_no_intervalo(s, voo["fim"],
                                              voo["fim"] + timedelta(hours=h))
            apos[h] = mm if com >= max(1, esp // 2) else None
        por_fonte[rotulo] = {"durante": durante, "apos": apos}
    voo["chuva_fontes"] = por_fonte

    maximos = {}
    for h in sorted(set(JANELAS_APOS) | {int(janela_h)}):
        vs = [(d["apos"][h], r) for r, d in por_fonte.items()
              if d["apos"].get(h) is not None]
        maximos[h] = max(vs) if vs else (None, None)
    voo["chuva_apos"] = {h: v for h, (v, _) in maximos.items()}
    pior, fonte = maximos.get(int(janela_h), (None, None))
    voo["chuva_apos_janela"] = pior
    voo["chuva_apos_fonte"] = fonte
    duras = [d["durante"] for d in por_fonte.values() if d["durante"] is not None]
    voo["chuva_durante"] = max(duras) if duras else None
    if pior is None:
        voo["lavagem"] = "sem_dado"
    elif pior >= limite_mm:
        voo["lavagem"] = "lavagem"
    elif pior >= 0.2:
        voo["lavagem"] = "leve"
    else:
        voo["lavagem"] = "seca"
    # quantas fontes concordam que choveu acima do limite
    voo["lavagem_fontes"] = sum(
        1 for d in por_fonte.values()
        if (d["apos"].get(int(janela_h)) or 0) >= limite_mm)
    voo["n_fontes_chuva"] = len(por_fonte)
    return voo


def texto_chuva_voo(v, janela_h=JANELA_LAVAGEM_H):
    """'3,2 mm em 6 h em Feira de Santana (44 km, medido); 0,4 no talhão'."""
    partes = []
    for r, d in (v.get("chuva_fontes") or {}).items():
        mm = d["apos"].get(int(janela_h))
        partes.append(f"{r}: {'—' if mm is None else _fmt(mm)} mm")
    return "; ".join(partes)


def resumo_chuva_por_dia(avaliados, janela_h=JANELA_LAVAGEM_H):
    """Uma linha por dia de operação: voos, área, e a chuva durante e depois."""
    dias = {}
    for v in avaliados:
        d = dias.setdefault((v["inicio"].date(), v.get("local", "")), [])
        d.append(v)
    saida = []
    for (dia, local), vs in sorted(dias.items()):
        def pior(fn):
            valores = [fn(v) for v in vs if fn(v) is not None]
            return max(valores) if valores else None
        lav = [v for v in vs if v.get("lavagem") == "lavagem"]
        fontes = {}
        for v in vs:
            for r, dd in (v.get("chuva_fontes") or {}).items():
                mm = dd["apos"].get(int(janela_h))
                if mm is not None:
                    fontes[r] = max(fontes.get(r, 0.0), mm)
        saida.append({
            "dia": dia, "local": local, "voos": len(vs),
            "ha": sum(v.get("area_ha") or 0 for v in vs),
            "primeiro": min(v["inicio"] for v in vs),
            "ultimo": max(v["fim"] for v in vs),
            "durante": pior(lambda v: v.get("chuva_durante")),
            "apos": {h: pior(lambda v, h=h: (v.get("chuva_apos") or {}).get(h))
                     for h in JANELAS_APOS},
            "fontes": fontes,
            "voos_lavagem": len(lav),
            "ha_lavagem": sum(v.get("area_ha") or 0 for v in lav),
        })
    return saida


# ---------------------------------------------------------------------
# Área com problema: os voos que caíram nela contra o restante
# ---------------------------------------------------------------------

def ler_poligonos(caminho):
    """Todos os polígonos de um KML, KMZ, GeoJSON ou shapefile."""
    ext = os.path.splitext(caminho)[1].lower()
    if ext == ".kml":
        with open(caminho, "rb") as f:
            feicoes = ler_kml(f.read())
    elif ext == ".kmz":
        with zipfile.ZipFile(caminho) as z:
            kml = next((n for n in z.namelist() if n.lower().endswith(".kml")),
                       None)
            if not kml:
                raise RuntimeError("O .kmz não contém nenhum .kml dentro.")
            feicoes = ler_kml(z.read(kml))
    elif ext in (".json", ".geojson"):
        with open(caminho, encoding="utf-8") as f:
            feicoes = ler_geojson(f.read())
    elif ext in (".shp", ".zip"):
        feicoes = ler_shapefile(caminho)
    else:
        raise RuntimeError(f"Formato não reconhecido: {ext}")
    poligonos = [(nome, pts) for nome, pts in feicoes if len(pts) >= 3]
    if not poligonos:
        raise RuntimeError("O arquivo não tem nenhum polígono.")
    for _, pts in poligonos:
        if not all(-180 <= x <= 180 and -90 <= y <= 90 for x, y in pts):
            raise RuntimeError("As coordenadas não são latitude/longitude — "
                               "exporte em EPSG:4326 ou em KML.")
    return poligonos


def ponto_no_poligono(x, y, pts):
    """Teste do raio: quantas vezes uma semirreta cruza a borda."""
    dentro = False
    j = len(pts) - 1
    for i in range(len(pts)):
        xi, yi = pts[i]
        xj, yj = pts[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / ((yj - yi) or 1e-15) + xi:
            dentro = not dentro
        j = i
    return dentro


def fracao_dentro(linhas, poligonos):
    """Fração do comprimento aplicado que cai dentro dos polígonos.

    Aceita uma linha ([(lon, lat), ...]) ou várias ([[...], [...]]). Conta
    por comprimento, em pedaços de até 5 m, e não por vértice: uma faixa
    longa tem só dois vértices e pesaria o mesmo que uma curva curta.
    """
    if not linhas or not poligonos:
        return 0.0
    if isinstance(linhas[0][0], (int, float)):
        linhas = [linhas]
    caixas = [(min(p[0] for p in pts), max(p[0] for p in pts),
               min(p[1] for p in pts), max(p[1] for p in pts), pts)
              for _, pts in poligonos if pts]

    def dentro_de_algum(x, y):
        return any(x0 <= x <= x1 and y0 <= y <= y1
                   and ponto_no_poligono(x, y, pts)
                   for x0, x1, y0, y1, pts in caixas)

    dentro = total = 0.0
    for l in linhas:
        for (xa, ya), (xb, yb) in zip(l, l[1:]):
            kx = 111320.0 * math.cos(math.radians(ya))
            comp = math.hypot((xb - xa) * kx, (yb - ya) * 110540.0)
            if comp == 0:
                continue
            n = max(1, int(comp // 5.0))
            for i in range(n):
                t = (i + 0.5) / n
                if dentro_de_algum(xa + t * (xb - xa), ya + t * (yb - ya)):
                    dentro += comp / n
            total += comp
    if total == 0:                   # voo de um ponto só
        pts = [p for l in linhas for p in l]
        return (sum(1 for x, y in pts if dentro_de_algum(x, y)) / len(pts)
                if pts else 0.0)
    return dentro / total


def _perfil_grupo(voos, janela_h, limite_mm):
    def media(chave):
        vs = [v[chave] for v in voos if v.get(chave) is not None]
        return sum(vs) / len(vs) if vs else None
    ha = sum(v.get("area_ha") or 0 for v in voos)

    def pct(cond):
        return 100 * sum(1 for v in voos if cond(v)) / len(voos) if voos else None
    horas = [v["inicio"].hour + v["inicio"].minute / 60 for v in voos]
    chuvas = [v.get("chuva_apos_janela") for v in voos
              if v.get("chuva_apos_janela") is not None]
    return {
        "voos": len(voos), "ha": ha,
        "datas": sorted({v["inicio"].date() for v in voos}),
        "pct_apta": pct(lambda v: v.get("classe") in ("apta", "limite")),
        "delta_t": media("delta_t"), "vento": media("vento"),
        "rajada": media("rajada"),
        "pct_lavagem": pct(lambda v: v.get("lavagem") == "lavagem"),
        "chuva_media": sum(chuvas) / len(chuvas) if chuvas else None,
        "chuva_max": max(chuvas) if chuvas else None,
        "pct_manual": pct(lambda v: str(v.get("modo", "")).upper().startswith("M")),
        "taxa": media("taxa"), "altura": media("altura_usada"),
        "hora_media": sum(horas) / len(horas) if horas else None,
    }


def comparar_area_problema(avaliados, poligonos, janela_h=JANELA_LAVAGEM_H,
                           limite_mm=LIMITE_LAVAGEM_MM, minimo=0.3):
    """Perfil dos voos que passaram pela área marcada contra o restante.

    Um voo conta como "na área" quando pelo menos 30% do comprimento
    aplicado (sem a ida e a volta à base) cai dentro do polígono. A comparação põe lado a lado o tempo (Delta T, vento,
    rajada), a chuva depois da aplicação e a operação (modo manual, taxa,
    altura, hora do dia) — porque falha de qualidade nem sempre é do tempo.
    """
    for v in avaliados:
        v["fracao_area_problema"] = fracao_dentro(
            trechos_aplicacao(v) or v.get("rota"), poligonos)
        v["na_area_problema"] = v["fracao_area_problema"] >= minimo
    dentro = [v for v in avaliados if v["na_area_problema"]]
    fora = [v for v in avaliados if not v["na_area_problema"]]
    return {"dentro": _perfil_grupo(dentro, janela_h, limite_mm),
            "fora": _perfil_grupo(fora, janela_h, limite_mm),
            "voos_dentro": dentro, "janela_h": janela_h,
            "limite_mm": limite_mm}


def linhas_comparacao(c):
    """Tabela da comparação: (rótulo, na área, restante)."""
    def f(v, casas=1, suf=""):
        return "—" if v is None else _fmt(v, casas) + suf

    def hora(v):
        return "—" if v is None else f"{int(v):02d}:{int(round((v % 1) * 60)):02d}"
    d, r = c["dentro"], c["fora"]
    return [
        ("Voos", str(d["voos"]), str(r["voos"])),
        ("Área aplicada (ha)", f(d["ha"]), f(r["ha"])),
        ("Datas", ", ".join(x.strftime("%d/%m") for x in d["datas"]) or "—",
         f'{len(r["datas"])} dias'),
        ("Voos em condição apta ou no limite", f(d["pct_apta"], 0, "%"),
         f(r["pct_apta"], 0, "%")),
        ("Delta T médio (°C)", f(d["delta_t"]), f(r["delta_t"])),
        ("Vento médio na altura do voo (km/h)", f(d["vento"]), f(r["vento"])),
        ("Rajada média (km/h)", f(d["rajada"]), f(r["rajada"])),
        (f"Chuva nas {c['janela_h']} h seguintes, média (mm)",
         f(d["chuva_media"]), f(r["chuva_media"])),
        (f"Chuva nas {c['janela_h']} h seguintes, máxima (mm)",
         f(d["chuva_max"]), f(r["chuva_max"])),
        (f"Voos com chuva ≥ {_fmt(c['limite_mm'])} mm depois",
         f(d["pct_lavagem"], 0, "%"), f(r["pct_lavagem"], 0, "%")),
        ("Voos em modo manual (M/M+)", f(d["pct_manual"], 0, "%"),
         f(r["pct_manual"], 0, "%")),
        ("Taxa média (L/ha)", f(d["taxa"]), f(r["taxa"])),
        ("Altura média de voo (m)", f(d["altura"]), f(r["altura"])),
        ("Horário médio", hora(d["hora_media"]), hora(r["hora_media"])),
    ]


def texto_comparacao(c):
    """Duas ou três frases com as diferenças que saltam aos olhos."""
    d, r = c["dentro"], c["fora"]
    if not d["voos"]:
        return "Nenhum voo passou pela área marcada."
    frases = [f"Na área marcada: {d['voos']} voos, {_fmt(d['ha'])} ha, em "
              + ", ".join(x.strftime("%d/%m") for x in d["datas"]) + "."]
    difs = []
    if d["pct_lavagem"] is not None and r["pct_lavagem"] is not None \
            and d["pct_lavagem"] - r["pct_lavagem"] >= 15:
        difs.append(f"mais voos com chuva logo depois ({d['pct_lavagem']:.0f}% "
                    f"contra {r['pct_lavagem']:.0f}%)")
    if d["delta_t"] is not None and r["delta_t"] is not None \
            and abs(d["delta_t"] - r["delta_t"]) >= 1.0:
        difs.append(f"Delta T {'maior' if d['delta_t'] > r['delta_t'] else 'menor'}"
                    f" ({_fmt(d['delta_t'])} contra {_fmt(r['delta_t'])} °C)")
    if d["vento"] is not None and r["vento"] is not None \
            and abs(d["vento"] - r["vento"]) >= 2.0:
        difs.append(f"vento {'mais forte' if d['vento'] > r['vento'] else 'mais fraco'}"
                    f" ({_fmt(d['vento'])} contra {_fmt(r['vento'])} km/h)")
    if d["pct_manual"] is not None and r["pct_manual"] is not None \
            and d["pct_manual"] - r["pct_manual"] >= 20:
        difs.append(f"mais voo manual ({d['pct_manual']:.0f}% contra "
                    f"{r['pct_manual']:.0f}%)")
    if d["taxa"] is not None and r["taxa"] is not None \
            and abs(d["taxa"] - r["taxa"]) >= 2.0:
        difs.append(f"taxa {'maior' if d['taxa'] > r['taxa'] else 'menor'} "
                    f"({_fmt(d['taxa'])} contra {_fmt(r['taxa'])} L/ha)")
    if difs:
        frases.append("Em relação ao restante: " + "; ".join(difs) + ".")
    else:
        frases.append("Nenhuma diferença grande de tempo, chuva ou operação em "
                      "relação ao restante — vale olhar produto, calda, bico e "
                      "a própria lavoura.")
    return " ".join(frases)


# ---------------------------------------------------------------------
# Cores dos voos no mapa, por critério
# ---------------------------------------------------------------------

def _faixa_mm(mm):
    if mm is None:
        return None
    for i, lim in enumerate(FAIXAS_MM):
        if mm < lim:
            return i
    return len(FAIXAS_MM)


def cores_dos_voos(avaliados, modo):
    """Cor de cada voo e a legenda, para o critério escolhido.

    Devolve (lista de cores na ordem de `avaliados`, [(cor, rótulo), ...]).
    """
    import colorsys
    if modo == "Chuva depois da aplicação":
        cores = []
        for v in avaliados:
            i = _faixa_mm(v.get("chuva_apos_janela"))
            cores.append(COR_LAVAGEM["sem_dado"] if i is None else CORES_MM[i])
        usados = {_faixa_mm(v.get("chuva_apos_janela")) for v in avaliados}
        legenda = [(CORES_MM[i], ROTULOS_MM[i]) for i in range(len(CORES_MM))
                   if i in usados]
        if None in usados:
            legenda.append((COR_LAVAGEM["sem_dado"], "sem dado"))
        return cores, legenda

    if modo == "Data do voo":
        datas = sorted({v["inicio"].date() for v in avaliados})
        # vinte cores bem distintas entre si; dias vizinhos nunca se parecem
        distintas = ("#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd",
                     "#8c564b", "#e377c2", "#17becf", "#bcbd22", "#7f7f7f",
                     "#393b79", "#e6550d", "#31a354", "#756bb1", "#843c39",
                     "#3182bd", "#fd8d3c", "#74c476", "#9e9ac8", "#636363")
        paleta = {d: distintas[i % len(distintas)] for i, d in enumerate(datas)}
        return ([paleta[v["inicio"].date()] for v in avaliados],
                [(paleta[d], d.strftime("%d/%m")) for d in datas])

    if modo == "Hora do dia":
        faixas = ((0, 8, "#26509c", "antes das 8h"), (8, 10, "#5b8def", "8 às 10h"),
                  (10, 12, "#8dc26f", "10 às 12h"), (12, 14, "#e0b27a", "12 às 14h"),
                  (14, 16, "#e08a1e", "14 às 16h"), (16, 24, "#8a4f08", "depois das 16h"))

        def faixa(v):
            h = v["inicio"].hour
            return next(f for f in faixas if f[0] <= h < f[1])
        usados = {faixa(v)[3] for v in avaliados}
        return ([faixa(v)[2] for v in avaliados],
                [(f[2], f[3]) for f in faixas if f[3] in usados])

    if modo == "Taxa de aplicação (L/ha)":
        faixas = ((0, 12, "#c81010", "menos de 12"), (12, 17, "#e08a1e", "12 a 17"),
                  (17, 22, "#2e7d32", "17 a 22"), (22, 999, "#26509c", "22 ou mais"))

        def faixa(v):
            t = v.get("taxa")
            if t is None:
                return None
            return next(f for f in faixas if f[0] <= t < f[1])
        usados = {faixa(v)[3] if faixa(v) else None for v in avaliados}
        legenda = [(f[2], f[3] + " L/ha") for f in faixas if f[3] in usados]
        if None in usados:
            legenda.append(("#b9b9b9", "sem taxa"))
        return ([faixa(v)[2] if faixa(v) else "#b9b9b9" for v in avaliados],
                legenda)

    if modo == "Modo de voo":
        modos = sorted({str(v.get("modo") or "—") for v in avaliados})
        base = ["#2e7d32", "#c81010", "#26509c", "#e08a1e", "#6a3fa0"]
        paleta = {m: base[i % len(base)] for i, m in enumerate(modos)}
        return ([paleta[str(v.get("modo") or "—")] for v in avaliados],
                [(paleta[m], m) for m in modos])

    # condição no voo (padrão)
    presentes = {v["classe"] for v in avaliados}
    return ([COR_VOO.get(v["classe"], "#999") for v in avaliados],
            [(COR_VOO[k], NOME_CLASSE_VOO[k]) for k in ORDEM_CLASSE_VOO
             if k in presentes])


# ---------------------------------------------------------------------
# Mapa interativo (HTML) e GeoJSON dos voos analisados
# ---------------------------------------------------------------------

def _props_do_voo(v, janela_h):
    p = v.get("p_apta")
    ca = v.get("chuva_apos") or {}
    return {
        "voo": v["id"], "data": v["inicio"].strftime("%d/%m/%Y"),
        "inicio": v["inicio"].strftime("%H:%M"),
        "fim": v["fim"].strftime("%H:%M"),
        "duracao_min": round((v.get("duracao_h") or 0) * 60, 1),
        "local": v.get("local"), "piloto": v.get("piloto"),
        "aeronave": v.get("aeronave"), "modo": v.get("modo"),
        "area_ha": v.get("area_ha"), "litros": v.get("litros"),
        "taxa_l_ha": v.get("taxa"),
        "altura_m": v.get("altura_usada"),
        "altura_origem": v.get("altura_origem"),
        "temp_c": None if v.get("temp") is None else round(v["temp"], 1),
        "ur_pct": None if v.get("ur") is None else round(v["ur"]),
        "delta_t": None if v.get("delta_t") is None else round(v["delta_t"], 2),
        "vento_kmh": None if v.get("vento") is None else round(v["vento"], 1),
        "rajada_kmh": None if v.get("rajada") is None else round(v["rajada"], 1),
        "vento_de": None if v.get("direcao") is None else rumo(v["direcao"]),
        "dir_graus": None if v.get("direcao") is None else round(v["direcao"]),
        "deriva_para": (None if v.get("direcao") is None
                        else rumo(v["direcao"] + 180)),
        "chuva_durante_mm_h": v.get("chuva_durante"),
        **{f"chuva_apos_{h}h": (None if ca.get(h) is None else round(ca[h], 2))
           for h in JANELAS_APOS},
        "fonte_chuva_max": v.get("chuva_apos_fonte"),
        "chuva_por_fonte": texto_chuva_voo(v, janela_h),
        "lavagem": NOME_LAVAGEM.get(v.get("lavagem"), "—"),
        "confianca_pct": None if p is None else round(100 * p),
        "veredito": NOME_CLASSE_VOO.get(v.get("classe"), v.get("classe")),
        "motivo": v.get("motivo"),
        "na_area_problema": v.get("na_area_problema"),
    }


def exportar_voos_geojson(caminho, avaliados, janela_h=JANELA_LAVAGEM_H,
                          poligonos=None):
    """Voos analisados como linhas, com todos os atributos — para o QGIS.

    Cada voo sai como a linha aplicada (trecho = "aplicação"), com todos os
    atributos. A ida e a volta à base saem em feições à parte (trecho =
    "deslocamento"), para filtrar ou estilizar separado no QGIS.
    """
    def multi(linhas):
        return {"type": "MultiLineString",
                "coordinates": [[[round(x, 7), round(y, 7)] for x, y in l]
                                for l in linhas if len(l) >= 2]}

    feicoes = []
    for v in avaliados:
        if not v.get("rota"):
            continue
        desloc = [l for l in (v.get("deslocamentos") or []) if len(l) >= 2]
        props = _props_do_voo(v, janela_h)
        props["trecho"] = "aplicação"
        props["deslocamento_m"] = round(comprimento_m(desloc))
        feicoes.append({"type": "Feature",
                        "geometry": multi(trechos_aplicacao(v)),
                        "properties": props})
        if desloc:
            feicoes.append({"type": "Feature", "geometry": multi(desloc),
                            "properties": {"voo": v["id"],
                                           "data": props["data"],
                                           "inicio": props["inicio"],
                                           "trecho": "deslocamento"}})
    for nome, pts in poligonos or []:
        feicoes.append({"type": "Feature",
                        "geometry": {"type": "Polygon",
                                     "coordinates": [[list(p) for p in pts]]},
                        "properties": {"voo": "AREA_PROBLEMA", "local": nome}})
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump({"type": "FeatureCollection", "name": "voos_analisados",
                   "crs": {"type": "name", "properties": {
                       "name": "urn:ogc:def:crs:OGC:1.3:CRS84"}},
                   "features": feicoes}, f, ensure_ascii=False)
    return len(feicoes)


_HTML_MAPA = """<!DOCTYPE html>
<html lang="pt-br"><head><meta charset="utf-8">
<title>__TITULO__</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.css">
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.js"></script>
<style>
 html,body{margin:0;height:100%;font-family:Segoe UI,Arial,sans-serif}
 #mapa{position:absolute;top:0;bottom:0;left:0;right:0}
 .caixa{background:#fff;padding:8px 10px;border-radius:6px;box-shadow:0 1px 6px rgba(0,0,0,.3);font-size:12.5px;max-width:300px}
 .caixa h4{margin:0 0 6px;font-size:13px}
 .caixa select{width:100%;margin:2px 0 6px;font-size:12.5px}
 .leg i{display:inline-block;width:18px;height:5px;margin-right:6px;vertical-align:middle;border-radius:2px}
 .leg div{margin:2px 0}
 table.p{border-collapse:collapse;font-size:12px}
 table.p td{padding:1px 6px 1px 0;vertical-align:top}
 table.p td:first-child{color:#666;white-space:nowrap}
 .nota{color:#666;font-size:11px;margin-top:6px}
</style></head><body><div id="mapa"></div>
<script>
const DADOS = __DADOS__;
const mapa = L.map('mapa', {preferCanvas: true});
const sat = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
  {maxZoom: 20, attribution: 'Imagem © Esri'}).addTo(mapa);
const osm = L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',
  {maxZoom: 19, attribution: '© OpenStreetMap'});
L.control.layers({'Satélite': sat, 'Mapa': osm}, {}, {position: 'topleft'}).addTo(mapa);
L.control.scale({imperial: false}).addTo(mapa);

let modo = DADOS.modos[0], dia = 'todas', verDesloc = false;
const linhas = [], bases = [];
const campos = [['data','Data'],['inicio','Início'],['fim','Fim'],['duracao_min','Duração (min)'],
 ['area_ha','Área (ha)'],['taxa_l_ha','Taxa (L/ha)'],['modo','Modo'],['altura_m','Altura (m)'],
 ['delta_t','Delta T (°C)'],['vento_kmh','Vento (km/h)'],['rajada_kmh','Rajada (km/h)'],
 ['vento_de','Vento de'],['deriva_para','Deriva para'],['chuva_durante_mm_h','Chuva no voo (mm/h)'],
 ['chuva_apos_1h','Chuva 1 h depois (mm)'],['chuva_apos_2h','Chuva 2 h depois (mm)'],
 ['chuva_apos_6h','Chuva 6 h depois (mm)'],['chuva_apos_24h','Chuva 24 h depois (mm)'],
 ['chuva_por_fonte','Por fonte (' + DADOS.janela + ' h)'],['lavagem','Lavagem'],
 ['confianca_pct','Confiança (%)'],['veredito','Veredito'],['motivo','Motivo']];
function fmt(v){ if(v===null||v===undefined||v==='') return '—';
  if(typeof v==='number') return (Math.round(v*100)/100).toString().replace('.',','); return v; }
function popup(p){ let h='<b>Voo '+p.voo+'</b><table class="p">';
  for(const [k,r] of campos) h+='<tr><td>'+r+'</td><td>'+fmt(p[k])+'</td></tr>';
  return h+'</table>'; }
const PESO = 2.4;
for (const v of DADOS.voos) {
  const l = L.polyline(v.apl, {color: v.cores[modo], weight: PESO, opacity: .92});
  l.bindPopup(popup(v.p), {maxWidth: 360});
  l.bindTooltip('Voo ' + v.p.voo + ' · ' + v.p.data + ' ' + v.p.inicio + ' · ' + fmt(v.p.veredito), {sticky: true});
  l.on('mouseover', () => { l.setStyle({weight: 5.5}); l.bringToFront(); });
  l.on('mouseout', () => l.setStyle({weight: PESO}));
  // ida e volta à base: tracejado fino, escondido de saída
  const d = v.des.length ? L.polyline(v.des, {color: '#ffffff', weight: 1.4, opacity: .8,
                                              dashArray: '4 6', interactive: false}) : null;
  l.addTo(mapa); linhas.push({l, d, v});
}
for (const b of DADOS.bases) {
  const m = L.circleMarker([b.lat, b.lon], {radius: 6, color: '#111', weight: 2,
                                            fillColor: '#fff', fillOpacity: 1});
  m.bindTooltip('Base de decolagem · ' + b.voos + (b.voos > 1 ? ' voos' : ' voo')
                + '<br>' + b.datas.join(', '));
  m.addTo(mapa); bases.push({m, b});
}
for (const [nome, pts] of DADOS.poligonos) {
  L.polygon(pts, {color: '#ffeb3b', weight: 3, dashArray: '6 5', fill: false})
   .bindTooltip('Área com problema: ' + nome).addTo(mapa);
}
const grupo = L.featureGroup(linhas.map(x => x.l));
mapa.fitBounds(grupo.getBounds(), {padding: [20, 20]});

const caixa = L.control({position: 'topright'});
caixa.onAdd = function(){
  const d = L.DomUtil.create('div', 'caixa');
  let h = '<h4>' + DADOS.titulo + '</h4>Colorir por:<select id="modo">';
  for (const m of DADOS.modos) h += '<option>' + m + '</option>';
  h += '</select>Data:<select id="dia"><option value="todas">todas</option>';
  for (const x of DADOS.datas) h += '<option>' + x + '</option>';
  h += '</select><label style="display:block;margin:2px 0 6px"><input type="checkbox" id="desloc"> ' +
       'Mostrar ida e volta à base</label>';
  h += '<div class="leg" id="leg"></div><div class="leg" id="leg2"></div><div class="nota">' + DADOS.nota + '</div>';
  d.innerHTML = h; L.DomEvent.disableClickPropagation(d); return d; };
caixa.addTo(mapa);
function mostra(camada, sim){ if (sim) { if (!mapa.hasLayer(camada)) camada.addTo(mapa); }
                              else if (mapa.hasLayer(camada)) mapa.removeLayer(camada); }
function redesenha(){
  let n = 0;
  for (const {l, d, v} of linhas) {
    const visivel = (dia === 'todas' || v.p.data === dia);
    if (visivel) { l.setStyle({color: v.cores[modo]}); n++; }
    mostra(l, visivel);
    if (d) mostra(d, visivel && verDesloc);
  }
  for (const {m, b} of bases) mostra(m, dia === 'todas' || b.datas.includes(dia));
  let h = '';
  for (const [cor, rot] of DADOS.legendas[modo]) h += '<div><i style="background:' + cor + '"></i>' + rot + '</div>';
  document.getElementById('leg').innerHTML = h;
  document.getElementById('leg2').innerHTML =
    '<div><span style="display:inline-block;width:10px;height:10px;border:2px solid #111;border-radius:50%;background:#fff;margin:0 8px 0 3px;vertical-align:middle"></span>base de decolagem</div>' +
    (verDesloc ? '<div><i style="background:repeating-linear-gradient(90deg,#666 0 4px,transparent 4px 8px)"></i>ida e volta (sem aplicar)</div>' : '') +
    '<div style="color:#666;margin-top:3px">' + n + ' voos no mapa</div>';
}
document.getElementById('desloc').onchange = e => { verDesloc = e.target.checked; redesenha(); };
document.getElementById('modo').onchange = e => { modo = e.target.value; redesenha(); };
document.getElementById('dia').onchange = e => { dia = e.target.value; redesenha(); };
redesenha();
</script></body></html>
"""


def gerar_mapa_html(caminho, avaliados, titulo="Voos analisados",
                    janela_h=JANELA_LAVAGEM_H, limite_mm=LIMITE_LAVAGEM_MM,
                    poligonos=None):
    """Mapa interativo dos voos sobre imagem de satélite.

    Um arquivo HTML só, que abre em qualquer navegador (precisa de
    internet para as imagens de fundo). Cada voo é clicável e traz a
    condição na hora e a chuva depois; o seletor troca a cor entre
    condição, chuva depois, data, hora, taxa e modo, e o filtro de data
    isola um dia — o jeito mais rápido de achar em que dia foi aplicada
    a parte que deu problema.
    """
    com_rota = [v for v in avaliados if v.get("rota")]
    cores, legendas = {}, {}
    for m in MODOS_COR_MAPA:
        cs, leg = cores_dos_voos(com_rota, m)
        cores[m] = cs
        legendas[m] = leg
    voos = []
    for i, v in enumerate(com_rota):
        voos.append({"apl": [[[round(y, 7), round(x, 7)] for x, y in l]
                             for l in trechos_aplicacao(v)],
                     "des": [[[round(y, 7), round(x, 7)] for x, y in l]
                             for l in (v.get("deslocamentos") or [])
                             if len(l) >= 2],
                     "cores": {m: cores[m][i] for m in MODOS_COR_MAPA},
                     "p": _props_do_voo(v, janela_h)})
    dados = {
        "titulo": titulo, "modos": list(MODOS_COR_MAPA), "legendas": legendas,
        "datas": sorted({v["inicio"].strftime("%d/%m/%Y") for v in com_rota},
                        key=lambda s: datetime.strptime(s, "%d/%m/%Y")),
        "janela": int(janela_h), "voos": voos,
        "bases": [{"lat": round(b["lat"], 7), "lon": round(b["lon"], 7),
                   "voos": b["voos"], "datas": b["datas"]}
                  for b in agrupar_bases(com_rota)],
        "poligonos": [[nome, [[y, x] for x, y in pts]]
                      for nome, pts in (poligonos or [])],
        "nota": (f"Chuva depois = acumulado nas {int(janela_h)} h seguintes ao "
                 f"fim do voo, na fonte que mais choveu. Lavagem possível a "
                 f"partir de {_fmt(limite_mm)} mm. Clique num voo para os "
                 "detalhes. A ida e a volta à base são separadas pelo "
                 "traçado; o arquivo não registra quando o bico estava "
                 "aberto."),
    }
    html = (_HTML_MAPA.replace("__TITULO__", titulo)
            .replace("__DADOS__", json.dumps(dados, ensure_ascii=False)))
    with open(caminho, "w", encoding="utf-8") as f:
        f.write(html)
    return len(voos)


def desenhar_chuva_por_dia(fig, resumo_dias, janela_h=JANELA_LAVAGEM_H,
                           limite_mm=LIMITE_LAVAGEM_MM, titulo=""):
    """Barras: chuva nas horas seguintes às aplicações de cada dia, por fonte."""
    fig.clear()
    if not resumo_dias:
        _sem_dados(fig, "Analise os voos para ver a chuva depois das aplicações.")
        return
    fontes = sorted({r for d in resumo_dias for r in d["fontes"]})
    if not fontes:
        _sem_dados(fig, "Nenhuma fonte de chuva disponível para estes voos.")
        return
    ax = fig.add_subplot(111)
    n = len(fontes)
    largura = 0.8 / n
    paleta = ["#6a3fa0", "#977bca", "#26509c", "#5b8def", "#8a4f08"]
    for j, r in enumerate(fontes):
        xs = [i - 0.4 + largura * (j + 0.5) for i in range(len(resumo_dias))]
        ys = [d["fontes"].get(r, 0.0) for d in resumo_dias]
        cor = "#b0aca6" if r == "modelo no talhão" else paleta[j % len(paleta)]
        ax.bar(xs, ys, width=largura * 0.92, color=cor, label=r,
               hatch="//" if r == "modelo no talhão" else None,
               edgecolor="white" if r != "modelo no talhão" else "#777",
               linewidth=0.5)
    ax.axhline(limite_mm, color=COR_SELECIONADA, lw=1, ls="--")
    ax.annotate(f"limite de lavagem ({_fmt(limite_mm)} mm)", (len(resumo_dias) - 0.5,
                                                              limite_mm),
                xytext=(0, 3), textcoords="offset points", ha="right",
                fontsize=7, color=COR_SELECIONADA)
    ax.set_xticks(range(len(resumo_dias)))
    ax.set_xticklabels([f'{d["dia"]:%d/%m}\n{d["voos"]} voos' for d in resumo_dias],
                       fontsize=7.5)
    ax.set_ylabel(f"Chuva nas {int(janela_h)} h depois do voo (mm)", fontsize=8.5)
    ax.grid(True, axis="y", color="#e8e8e8", lw=0.7)
    ax.set_axisbelow(True)
    for lado in ("top", "right"):
        ax.spines[lado].set_visible(False)
    ax.legend(fontsize=7.5, frameon=False, loc="upper left",
              title="fonte (maior valor entre os voos do dia)", title_fontsize=7)
    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.08, ha="left")
    fig.subplots_adjust(left=0.08, right=0.98, top=0.88, bottom=0.15)


# =====================================================================
# BLOCO 13 — GRÁFICOS DOS VOOS
# =====================================================================


def _legenda_voos(ax, presentes, **kw):
    ax.legend(handles=[Patch(facecolor=COR_VOO[k], label=NOME_CLASSE_VOO[k])
                       for k in ORDEM_CLASSE_VOO if k in presentes],
              frameon=False, fontsize=7.5, handlelength=1.4,
              handletextpad=0.5, columnspacing=1.4, **kw)


def desenhar_voos_no_dia(fig, serie, crit, voos, titulo="", fontes=None,
                         janela_h=JANELA_LAVAGEM_H):
    """O meteorograma do dia com os voos marcados por cima.

    É a figura que responde de uma olhada: o voo caiu dentro da janela ou
    fora? E choveu depois? O eixo vai até a manhã seguinte, porque a chuva
    que lava o produto costuma vir à noite. No painel da chuva, cada fonte
    aparece separada — estação por estação e o modelo no talhão — e a
    faixa lilás marca as horas seguintes ao último voo do dia.
    """
    dia = voos[0]["inicio"].date() if voos else None
    if dia is not None:
        t0 = datetime(dia.year, dia.month, dia.day, tzinfo=timezone.utc)
        ultimo = max(v["fim"] for v in voos)
        t1 = min(t0 + timedelta(hours=36),
                 max(t0 + timedelta(hours=24),
                     ultimo + timedelta(hours=max(18, janela_h))))
        recorte = {t: l for t, l in serie.items() if t0 <= t <= t1}
    else:
        recorte = serie
        ultimo = None
    if not recorte:
        _sem_dados(fig, "Sem série meteorológica para este dia.")
        return

    desenhar_serie(fig, recorte, crit, titulo)
    if not fig.axes:
        return
    a_dt, a_v = fig.axes[0], (fig.axes[1] if len(fig.axes) > 1 else fig.axes[0])

    presentes = set()
    for v in voos:
        cor = COR_VOO.get(v["classe"], "#999")
        presentes.add(v["classe"])
        for ax in (a_dt, a_v):
            ax.axvspan(_limpo(v["inicio"]), _limpo(v["fim"]), color=cor,
                       alpha=0.55, lw=0, zorder=4)
        if v.get("delta_t") is not None:
            a_dt.plot([_limpo(v["inicio"] + (v["fim"] - v["inicio"]) / 2)],
                      [v["delta_t"]], marker="o", ms=5, color=cor,
                      markeredgecolor="white", markeredgewidth=1.0, zorder=6)
        if v.get("vento") is not None:
            a_v.plot([_limpo(v["inicio"] + (v["fim"] - v["inicio"]) / 2)],
                     [v["vento"]], marker="o", ms=5, color=cor,
                     markeredgecolor="white", markeredgewidth=1.0, zorder=6)

    if presentes:
        _legenda_voos(a_dt, presentes, loc="lower center",
                      bbox_to_anchor=(0.5, 1.18),
                      ncol=min(4, len(presentes)))

    a_c = next((ax for ax in fig.axes
                if ax.get_ylabel().startswith("Chuva")), None)
    if a_c is None or ultimo is None:
        return
    a_c.axvspan(_limpo(ultimo), _limpo(ultimo + timedelta(hours=janela_h)),
                color=COR_LAVAGEM["leve"], alpha=0.22, lw=0, zorder=0)
    a_c.annotate(f"{int(janela_h)} h depois do último voo",
                 (mdates.date2num(_limpo(ultimo)), 1.0),
                 xycoords=("data", "axes fraction"), xytext=(3, -9),
                 textcoords="offset points", fontsize=6.5,
                 color=COR_LAVAGEM["lavagem"])
    for v in voos:
        a_c.axvspan(_limpo(v["inicio"]), _limpo(v["fim"]),
                    color=COR_VOO.get(v["classe"], "#999"), alpha=0.45, lw=0,
                    zorder=1)
    if fontes:
        paleta = ["#6a3fa0", "#26509c", "#8a4f08", "#2e7d32"]
        topo = a_c.get_ylim()[1]
        for j, (rotulo, s) in enumerate(fontes.items()):
            ts = sorted(t for t in s if t in recorte or (
                min(recorte) <= t <= max(recorte)))
            if not ts:
                continue
            ys = [s[t].get("chuva") for t in ts]
            if not any(y for y in ys if y is not None):
                continue
            cor = "#777" if rotulo == "modelo no talhão" else paleta[j % 4]
            a_c.step([mdates.date2num(_limpo(t)) for t in ts],
                     [0 if y is None else y for y in ys], where="pre",
                     color=cor, lw=1.1,
                     ls="--" if rotulo == "modelo no talhão" else "-",
                     label=rotulo, zorder=5)
            topo = max(topo, max((y or 0) for y in ys) * 1.15)
        a_c.set_ylim(0, max(topo, 0.5))
        if a_c.get_legend_handles_labels()[0]:
            a_c.legend(fontsize=6.5, frameon=False, loc="upper right",
                       ncol=min(3, len(fontes)))


def desenhar_mapa_voos(fig, avaliados, estacoes=(), titulo="", margem=0.10,
                       colorir="Condição no voo", poligonos=None):
    """Os traçados dos voos, coloridos pelo critério escolhido.

    Serve para ver se o problema se concentrou numa parte da área, num dia
    ou num horário — o que muda a conversa de "o dia estava ruim" para "as
    faixas aplicadas no dia 14 à tarde tomaram chuva à noite". As cores
    podem ser a condição no voo, a chuva depois da aplicação, a data, a
    hora, a taxa ou o modo de voo.
    """
    fig.clear()
    if not avaliados:
        _sem_dados(fig, "Analise os voos para ver o mapa.")
        return

    ax = fig.add_subplot(111)
    ax.set_facecolor(COR_FUNDO)

    com_rota = [v for v in avaliados if v.get("rota")]
    cores, legenda = cores_dos_voos(com_rota, colorir)
    # desenha primeiro os voos "bons" e por cima os que chamam atenção, para
    # uma faixa ruim não sumir debaixo de dezenas de faixas boas
    ordem = list(range(len(com_rota)))
    if colorir == "Chuva depois da aplicação":
        ordem.sort(key=lambda i: com_rota[i].get("chuva_apos_janela") or -1)
    elif colorir == "Condição no voo":
        peso = {k: i for i, k in enumerate(("apta", "limite", "sem_dado",
                                            "impropria", "inversao", "chuva"))}
        ordem.sort(key=lambda i: peso.get(com_rota[i]["classe"], 0))
    tem_desloc = False
    if com_rota:
        # ida e volta à base: tracejado fino e claro, só para situar
        desloc = [l for v in com_rota for l in (v.get("deslocamentos") or [])
                  if len(l) >= 2]
        if desloc:
            tem_desloc = True
            ax.add_collection(LineCollection(
                desloc, colors="#8d8d8d", linewidths=0.45, alpha=0.6,
                linestyles=(0, (2, 3)), zorder=2))
        segs, cs = [], []
        for i in ordem:
            for l in trechos_aplicacao(com_rota[i]):
                segs.append(l)
                cs.append(cores[i])
        ax.add_collection(LineCollection(segs, colors=cs, linewidths=1.15,
                                         alpha=0.92, zorder=3))
        bases = agrupar_bases(com_rota)
        if bases:
            ax.scatter([b["lon"] for b in bases], [b["lat"] for b in bases],
                       s=26, marker="^", c="white", edgecolors="#1d1d1b",
                       linewidths=0.9, zorder=6)

    # O enquadramento é nos voos, nunca nas estações: elas ficam a dezenas
    # ou centenas de quilômetros, e incluí-las no limite reduziria a área
    # aplicada a um ponto. As que ficarem fora do quadro são listadas no
    # canto, com a distância — que é a informação que importa delas.
    xs = [p[0] for v in com_rota for p in v["rota"]]
    ys = [p[1] for v in com_rota for p in v["rota"]]
    for _, pts in poligonos or []:
        xs += [p[0] for p in pts]
        ys += [p[1] for p in pts]
    if xs and ys:
        dx = (max(xs) - min(xs)) or 0.02
        dy = (max(ys) - min(ys)) or 0.02
        x0, x1 = min(xs) - margem * dx, max(xs) + margem * dx
        y0, y1 = min(ys) - margem * dy, max(ys) + margem * dy
        ax.set_xlim(x0, x1)
        ax.set_ylim(y0, y1)
        lat_meio = (y0 + y1) / 2
        ax.set_aspect(1 / max(0.1, math.cos(math.radians(lat_meio))))
    else:
        x0 = x1 = y0 = y1 = 0

    for nome, pts in poligonos or []:
        xp = [p[0] for p in pts] + [pts[0][0]]
        yp = [p[1] for p in pts] + [pts[0][1]]
        ax.plot(xp, yp, color="#1d1d1b", lw=1.8, ls="--", zorder=6)
        ax.plot(xp, yp, color="#ffd400", lw=1.0, ls="--", zorder=7)
        ax.annotate(f"área com problema\n{nome}"[:60], (min(xp), max(yp)),
                    textcoords="offset points", xytext=(2, 4), fontsize=6.5,
                    color="#1d1d1b", zorder=8,
                    bbox=dict(boxstyle="round,pad=0.2", fc="#fff6bf", ec="none",
                              alpha=0.9))

    if estacoes:
        dentro = [e for e in estacoes if x0 <= e["lon"] <= x1
                  and y0 <= e["lat"] <= y1]
        if dentro:
            ax.scatter([e["lon"] for e in dentro], [e["lat"] for e in dentro],
                       s=55, c=COR_SELECIONADA, linewidths=0, zorder=5)
            for e in dentro:
                ax.annotate(f'{e["nome"][:20]}\n{e.get("distancia", 0):.0f} km',
                            (e["lon"], e["lat"]), textcoords="offset points",
                            xytext=(6, 4), fontsize=6.5, color="#444", zorder=6)
        de_fora = [e for e in estacoes if e not in dentro]
        if de_fora:
            perto = sorted(de_fora, key=lambda e: e.get("distancia") or 0)[:5]
            recado = "Estações usadas, fora do quadro:\n" + "\n".join(
                f'  {e["nome"][:22]} — {e.get("distancia", 0):.0f} km'
                for e in perto)
            ax.text(0.015, 0.015, recado, transform=ax.transAxes, fontsize=6.5,
                    color="#555", va="bottom", zorder=8,
                    bbox=dict(boxstyle="round,pad=0.4", facecolor="white",
                              edgecolor="#ddd", alpha=0.92))

    # rosa-dos-ventos mínima ao lado: de onde veio o vento durante os voos
    d_v, c_v, *_ = media_vetorial(
        [{"vento": v.get("vento"), "direcao": v.get("direcao")}
         for v in avaliados], pesos=[v.get("area_ha") or 0.01 for v in avaliados])
    if d_v is not None:
        ins = ax.inset_axes([1.03, 0.72, 0.22, 0.26])
        ins.set_xlim(-1.2, 1.2)
        ins.set_ylim(-1.6, 1.3)
        ins.set_aspect("equal")
        ins.axis("off")
        ins.add_patch(plt.Circle((0, 0), 1.0, fill=False, color="#bbb", lw=0.8))
        para = math.radians(d_v + 180)
        ins.annotate("", xy=(0.85 * math.sin(para), 0.85 * math.cos(para)),
                     xytext=(-0.85 * math.sin(para), -0.85 * math.cos(para)),
                     arrowprops=dict(arrowstyle="-|>", color=COR_AREA, lw=2.2))
        ins.text(0, 1.14, "N", ha="center", va="center", fontsize=7,
                 color="#555")
        ins.text(0, -1.40, f"vento de {rumo(d_v)}\nderiva → {rumo(d_v + 180)}",
                 ha="center", va="center", fontsize=6.5, color="#333")

    ax.set_xlabel("Longitude", fontsize=8)
    ax.set_ylabel("Latitude", fontsize=8)
    ax.tick_params(labelsize=7)
    ax.grid(True, alpha=0.25, linewidth=0.7)
    if legenda:
        extras = []
        if com_rota and any(v.get("base") for v in com_rota):
            extras.append(Line2D([], [], marker="^", ls="none", markersize=6,
                                 markerfacecolor="white",
                                 markeredgecolor="#1d1d1b",
                                 label="base de decolagem"))
        if tem_desloc:
            extras.append(Line2D([], [], color="#8d8d8d", lw=0.9, ls=(0, (2, 2)),
                                 label="ida e volta (sem aplicar)"))
        ax.legend(handles=[Patch(facecolor=c, label=r) for c, r in legenda]
                  + extras,
                  loc="upper left", bbox_to_anchor=(1.03, 0.68), frameon=False,
                  fontsize=7, handlelength=1.4, handletextpad=0.5,
                  title=colorir, title_fontsize=7.5)
    if titulo:
        ax.set_title(titulo, fontsize=9, color="#555", loc="left", pad=8)
    fig.subplots_adjust(left=0.08, right=0.78, top=0.90, bottom=0.10)


def desenhar_resumo_voos(fig, avaliados, por=None, rotulo="dia", titulo=""):
    """Barras empilhadas: hectares por veredito, em cada grupo."""
    fig.clear()
    if not avaliados:
        _sem_dados(fig, "Analise os voos para ver o resumo.")
        return

    grupos = {}
    for v in avaliados:
        chave = (v["inicio"].strftime("%d/%m") if por is None
                 else str(v.get(por) or "—"))
        d = grupos.setdefault(chave, {})
        d[v["classe"]] = d.get(v["classe"], 0.0) + (v.get("area_ha") or 0.0)

    chaves = sorted(grupos)
    ax = fig.add_subplot(111)
    fundo = np.zeros(len(chaves))
    presentes = set()
    for classe in ORDEM_CLASSE_VOO:
        alturas = np.array([grupos[k].get(classe, 0.0) for k in chaves])
        if not alturas.any():
            continue
        presentes.add(classe)
        ax.bar(range(len(chaves)), alturas, bottom=fundo, width=0.7,
               color=COR_VOO[classe], edgecolor="white", linewidth=0.8)
        fundo += alturas

    ax.set_xticks(range(len(chaves)))
    ax.set_xticklabels(chaves, fontsize=7.5,
                       rotation=45 if max(len(k) for k in chaves) > 6 else 0,
                       ha="right" if max(len(k) for k in chaves) > 6 else "center")
    ax.set_ylabel("Hectares aplicados", fontsize=9)
    ax.set_xlabel(rotulo, fontsize=9)
    ax.grid(True, axis="y", color="#e8e8e8", lw=0.7)
    ax.set_axisbelow(True)
    for lado in ("top", "right"):
        ax.spines[lado].set_visible(False)
    for i, k in enumerate(chaves):
        total = sum(grupos[k].values())
        if total:
            ax.annotate(f"{total:.0f}", (i, total), xytext=(0, 3),
                        textcoords="offset points", ha="center", fontsize=7,
                        color="#555")
    _legenda_voos(ax, presentes, loc="lower center",
                  bbox_to_anchor=(0.5, 1.01),
                  ncol=min(3, max(1, len(presentes))))
    if titulo:
        fig.suptitle(titulo, fontsize=9, color="#555", x=0.09, ha="left")
    fig.subplots_adjust(left=0.09, right=0.97, top=0.82, bottom=0.22)


# =====================================================================
# BLOCO 14 — RELATÓRIO DE VOOS EM PDF
# =====================================================================

COLUNAS_VOOS = ["Início", "Dur.", "Local", "Área (ha)", "Delta T", "Vento",
                "Vento de", "Altura", "Chuva depois", "Confiança", "Veredito"]
LARGURAS_VOOS = [0.12, 0.05, 0.07, 0.07, 0.07, 0.07, 0.08, 0.07, 0.09, 0.08, 0.19]


def _linhas_voos(voos, com_piloto=False):
    linhas = []
    for v in voos:
        p = v.get("p_apta")
        linha = [
            v["inicio"].strftime("%d/%m  %H:%M"),
            f'{(v["duracao_h"] or 0) * 60:.0f} min',
            v.get("local", "—"),
            _fmt(v.get("area_ha")),
            _fmt(v.get("delta_t")),
            _fmt(v.get("vento")),
            _rotulo_dir(v.get("direcao")),
            _fmt(v.get("altura_usada")) + " m"
            + ("*" if v.get("altura_origem") == "estimada" else ""),
            ("—" if v.get("chuva_apos_janela") is None
             else f'{_fmt(v["chuva_apos_janela"])} mm'),
            "—" if p is None else f"{100 * p:.0f}%",
            NOME_CLASSE_VOO.get(v["classe"], v["classe"]),
        ]
        if com_piloto:
            linha.insert(3, str(v.get("piloto", "—"))[:18])
        linhas.append(linha)
    return linhas


def _paginas_voos(pdf, titulo, subtitulo, voos, rodape, numero,
                  com_piloto=False, nota="", destaques=()):
    colunas = list(COLUNAS_VOOS)
    larguras = list(LARGURAS_VOOS)
    if com_piloto:
        colunas.insert(3, "Piloto")
        larguras.insert(3, 0.12)
        larguras = [x / sum(larguras) for x in larguras]

    linhas = _linhas_voos(voos, com_piloto)
    blocos = [list(range(i, min(i + LINHAS_POR_PAGINA, len(linhas))))
              for i in range(0, max(1, len(linhas)), LINHAS_POR_PAGINA)]
    for k, bloco in enumerate(blocos):
        sub = subtitulo + (f"  ·  parte {k + 1} de {len(blocos)}"
                           if len(blocos) > 1 else "")
        fig = _pagina(titulo, sub)
        caixa = [0.045, 0.10, 0.91, 0.76]
        ax = fig.add_axes(caixa)
        _tabela(ax, colunas, larguras, [linhas[i] for i in bloco],
                {i - bloco[0] for i in bloco if i in destaques})
        if nota and k == 0:
            altura = min(0.048, 0.95 / (len(bloco) + 1)) * caixa[3]
            fim = caixa[1] + caixa[3] - (len(bloco) + 1) * altura
            fig.text(0.045, max(0.06, fim - 0.035), nota, fontsize=7.5,
                     color=COR_APOIO)
        numero = _fecha(pdf, fig, rodape, numero)
    return numero


def gerar_relatorio_voos_pdf(caminho, d):
    """Relatório das operações já realizadas.

    Ordem: o que foi feito; como foi no conjunto; a chuva durante e
    depois das aplicações; onde (mapas por condição, por chuva depois e
    por data); a área com problema, se marcada; o que correu pior; e dia
    a dia, com o tempo e a chuva por trás de cada voo.
    """
    agora = datetime.now()
    rodape = (f"Análise de voos · gerado em {agora:%d/%m/%Y às %H:%M} · "
              f"tempo reconstruído de {d['fonte']} · Delta T por Stull (2011)")
    numero = 1
    secao = [0]

    def sec(titulo):
        secao[0] += 1
        return f"{secao[0]}.  {titulo}"

    voos = d["voos"]
    crit = d["crit"]
    janela_h = d.get("janela_h", JANELA_LAVAGEM_H)
    limite_mm = d.get("limite_mm", LIMITE_LAVAGEM_MM)
    poligonos = d.get("poligonos") or []

    ha_total = sum(v.get("area_ha") or 0 for v in voos)
    por_classe, por_lav = {}, {}
    for v in voos:
        por_classe.setdefault(v["classe"], {"n": 0, "ha": 0.0})
        por_classe[v["classe"]]["n"] += 1
        por_classe[v["classe"]]["ha"] += v.get("area_ha") or 0.0
        k = v.get("lavagem", "sem_dado")
        por_lav.setdefault(k, {"n": 0, "ha": 0.0})
        por_lav[k]["n"] += 1
        por_lav[k]["ha"] += v.get("area_ha") or 0.0

    with PdfPages(caminho) as pdf:
        pdf.infodict().update({
            "Title": "Análise de condições dos voos realizados",
            "Subject": f"{len(voos)} voos · {d['ini']} a {d['fim']}",
            "Creator": f"Janela de Aplicação v. {VERSAO}",
        })

        # ---- identificação e veredito geral ----
        fig = _pagina(sec("Operações analisadas"),
                      f"{len(voos)} voos  ·  {_fmt(ha_total)} ha  ·  "
                      f"{d['ini']} a {d['fim']}  ·  {len(d['locais'])} locais")
        ax = fig.add_axes([0.045, 0.60, 0.44, 0.26])
        _tabela(ax, ["Local", "Voos", "Área (ha)", "Período", "Estações"],
                [0.16, 0.13, 0.19, 0.30, 0.22],
                [[g["nome"], str(len(g["voos"])), _fmt(g["area_ha"]),
                  f'{g["ini"].strftime("%d/%m")} a {g["fim"].strftime("%d/%m")}',
                  str(len(g.get("estacoes", [])))] for g in d["locais"]],
                fonte=7.5, encher=True)

        ax2 = fig.add_axes([0.53, 0.60, 0.43, 0.26])
        _tabela(ax2, ["Condição no voo", "Voos", "Área (ha)", "% da área"],
                [0.40, 0.18, 0.21, 0.21],
                [[NOME_CLASSE_VOO[k], str(por_classe[k]["n"]),
                  _fmt(por_classe[k]["ha"]),
                  f'{100 * por_classe[k]["ha"] / max(ha_total, 0.001):.0f}%']
                 for k in ORDEM_CLASSE_VOO if k in por_classe],
                fonte=7.5, encher=True)

        ax3 = fig.add_axes([0.53, 0.40, 0.43, 0.16])
        _tabela(ax3, [f"Chuva nas {int(janela_h)} h seguintes", "Voos",
                      "Área (ha)", "% da área"],
                [0.40, 0.18, 0.21, 0.21],
                [[NOME_LAVAGEM[k], str(por_lav[k]["n"]), _fmt(por_lav[k]["ha"]),
                  f'{100 * por_lav[k]["ha"] / max(ha_total, 0.001):.0f}%']
                 for k in ORDEM_LAVAGEM if k in por_lav],
                fonte=7.5, encher=True)

        aptos = por_classe.get("apta", {"ha": 0.0})["ha"]
        texto = [
            f"Critérios aplicados:  Delta T entre {_fmt(crit['dt_min'], 0)} e "
            f"{_fmt(crit['dt_max'], 0)} °C;  vento entre "
            f"{_fmt(crit['vento_min'], 0)} e {_fmt(crit['vento_max'], 0)} km/h"
            + (f";  rajada até {_fmt(crit['rajada_max'], 0)} km/h."
               if crit.get("rajada_max") else "."),
            f"Chuva depois:  lavagem possível com {_fmt(limite_mm)} mm ou mais "
            f"nas {int(janela_h)} h seguintes ao fim do voo, na fonte que mais "
            "choveu; chuva leve a partir de 0,2 mm.",
            "Vento levado à altura de voo registrada em cada operação, pelo "
            "perfil logarítmico. Voos manuais sem altura gravada usam a "
            "mediana do dia (marcados *).",
            f"Tempo reconstruído de:  {d['fonte']}.",
            d.get("direcao_texto", ""),
            f"{_fmt(aptos)} ha de {_fmt(ha_total)} ha "
            f"({100 * aptos / max(ha_total, 0.001):.0f}%) foram aplicados em "
            "condição classificada como apta.",
            d.get("texto_area", ""),
            "",
            "A condição de cada voo foi reconstruída das estações mais "
            "próximas, não medida no talhão; a confiança é a fração dos "
            "cenários compatíveis com o que as estações mediram em que o voo "
            "atenderia ao critério — leia como probabilidade, não como "
            "sentença. Chuva é localizada: a estação a 40 km pode "
            "não ter pegado a pancada que caiu no talhão, e vice-versa — por "
            "isso as fontes aparecem separadas.",
            d.get("dispersao", ""),
        ]
        import textwrap
        corpo = "\n".join(textwrap.fill(t, 92) if t else "" for t in texto
                          if t is not None)
        fig.text(0.045, 0.555, corpo, fontsize=7.4, color=COR_TINTA, va="top",
                 linespacing=1.55)
        numero = _fecha(pdf, fig, rodape, numero)

        # ---- resumo por dia ----
        fig = plt.Figure(figsize=A4_DEITADO)
        desenhar_resumo_voos(fig, voos, None, "dia da operação")
        _cabecalho_sobre(fig, sec("Área aplicada por dia e condição"),
                         "Cada barra é um dia; a cor diz em que condição "
                         "aqueles hectares foram aplicados.", topo=0.80)
        numero = _fecha(pdf, fig, rodape, numero)

        if d.get("por"):
            fig = plt.Figure(figsize=A4_DEITADO)
            desenhar_resumo_voos(fig, voos, d["por"], d["rotulo_por"])
            _cabecalho_sobre(fig, sec(f"Área aplicada por {d['rotulo_por']}"),
                             "Mesma leitura da página anterior, agrupada de "
                             "outro jeito. Diferença entre operadores pode "
                             "ser escala de trabalho, não só decisão.",
                             topo=0.80)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- chuva durante e depois ----
        dias_chuva = resumo_chuva_por_dia(voos, janela_h)
        fig = plt.Figure(figsize=A4_DEITADO)
        desenhar_chuva_por_dia(fig, dias_chuva, janela_h, limite_mm)
        _cabecalho_sobre(fig, sec("Chuva depois das aplicações"),
                         f"Maior chuva acumulada nas {int(janela_h)} h "
                         "seguintes a um voo de cada dia, em cada fonte. "
                         "Barras acima da linha vermelha: chuva capaz de lavar "
                         "o produto antes da absorção.", topo=0.82)
        numero = _fecha(pdf, fig, rodape, numero)

        colunas = ["Dia", "Voos", "Área (ha)", "Voos de … a …",
                   "Chuva no voo (mm/h)", "1 h depois", "2 h depois",
                   "6 h depois", "24 h depois", "Voos com lavagem"]
        larguras = [0.08, 0.06, 0.08, 0.14, 0.12, 0.09, 0.09, 0.09, 0.09, 0.12]
        linhas = []
        destaque = set()
        for i, r in enumerate(dias_chuva):
            linhas.append([
                r["dia"].strftime("%d/%m"), str(r["voos"]), _fmt(r["ha"]),
                f'{r["primeiro"]:%H:%M} – {r["ultimo"]:%H:%M}',
                _fmt(r["durante"]),
                *[_fmt(r["apos"].get(h)) for h in JANELAS_APOS],
                (f'{r["voos_lavagem"]} ({_fmt(r["ha_lavagem"])} ha)'
                 if r["voos_lavagem"] else "—")])
            if r["voos_lavagem"]:
                destaque.add(i)
        fig = _pagina(sec("Chuva durante e depois, dia a dia"),
                      "Milímetros acumulados depois do fim do voo — o maior "
                      "valor entre os voos do dia e entre as fontes. Em verde, "
                      "os dias com algum voo sujeito a lavagem.")
        ax = fig.add_axes([0.045, 0.30, 0.91, 0.56])
        _tabela(ax, colunas, larguras, linhas, destaque, fonte=7.2)
        fontes_txt = sorted({f for r in dias_chuva for f in r["fontes"]})
        fig.text(0.045, 0.24, "Fontes de chuva consideradas: "
                 + ("; ".join(fontes_txt) if fontes_txt else "nenhuma")
                 + ".", fontsize=7.5, color=COR_APOIO, wrap=True)
        numero = _fecha(pdf, fig, rodape, numero)

        # ---- mapas, por local ----
        for g in d["locais"]:
            avaliados = [v for v in voos if v.get("local") == g["nome"]]
            if not avaliados:
                continue
            perto = min((e.get("distancia") or 0)
                        for e in g.get("estacoes", [{"distancia": 0}]))
            aviso = ("" if perto < 60 else
                     f"  ·  ATENÇÃO: a estação mais próxima está a "
                     f"{perto:.0f} km — a estimativa aqui é fraca")
            for modo, nome, explica in (
                    ("Condição no voo", "condição na hora do voo",
                     "cor = veredito do voo pelo Delta T, vento e rajada"),
                    ("Chuva depois da aplicação", "chuva depois da aplicação",
                     f"cor = chuva nas {int(janela_h)} h seguintes ao voo"),
                    ("Data do voo", "dia de cada faixa",
                     "cor = data da aplicação — para achar em que dia foi "
                     "feita cada parte")):
                fig = plt.Figure(figsize=A4_DEITADO)
                desenhar_mapa_voos(fig, avaliados, g.get("estacoes", ()),
                                   colorir=modo, poligonos=poligonos)
                _cabecalho_sobre(
                    fig, sec(f"{g['nome']}: {nome}"),
                    f"{len(avaliados)} voos  ·  {_fmt(g['area_ha'])} ha  ·  "
                    f"{explica}  ·  estação mais próxima a {perto:.0f} km"
                    f"{aviso}", topo=0.86)
                numero = _fecha(pdf, fig, rodape, numero)

        # ---- área com problema ----
        comp = d.get("comparacao")
        if comp:
            fig = _pagina(sec("Área com problema × restante"),
                          "Voos que passaram pela área marcada (30% ou mais do "
                          "traçado dentro dela) comparados com os demais.")
            ax = fig.add_axes([0.045, 0.30, 0.60, 0.56])
            _tabela(ax, ["", "Na área marcada", "Restante"], [0.52, 0.24, 0.24],
                    [list(l) for l in linhas_comparacao(comp)], fonte=7.5,
                    encher=True)
            import textwrap
            fig.text(0.67, 0.86, textwrap.fill(texto_comparacao(comp), 58),
                     fontsize=8, color=COR_TINTA, va="top", linespacing=1.6)
            dentro = sorted(comp["voos_dentro"], key=lambda v: v["inicio"])
            if dentro:
                lista = "\n".join(
                    f'{v["inicio"]:%d/%m %H:%M}  {_fmt(v.get("area_ha"))} ha  '
                    f'{NOME_CLASSE_VOO.get(v["classe"], "")[:18]}  · chuva '
                    f'depois {_fmt(v.get("chuva_apos_janela"))} mm'
                    for v in dentro[:16])
                fig.text(0.67, 0.52, "Voos na área marcada:\n" + lista,
                         fontsize=6.8, color=COR_APOIO, va="top",
                         family="monospace", linespacing=1.4)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- piores voos ----
        piores = sorted([v for v in voos if v.get("p_apta") is not None],
                        key=lambda v: v["p_apta"])[:LINHAS_POR_PAGINA]
        piores += [v for v in voos if v.get("p_apta") is None][:5]
        if piores:
            numero = _paginas_voos(
                pdf, sec("Voos em pior condição"),
                "Ordenados do menor para o maior grau de confiança",
                piores, rodape, numero, com_piloto=bool(d.get("com_piloto")),
                nota="São os voos a revisar primeiro. A coluna do veredito "
                     "traz o motivo dominante quando a condição não fechou.")

        molhados = sorted([v for v in voos if v.get("lavagem") in ("lavagem",
                                                                   "leve")],
                          key=lambda v: -(v.get("chuva_apos_janela") or 0))
        if molhados:
            numero = _paginas_voos(
                pdf, sec("Voos com chuva logo depois"),
                f"Ordenados pela chuva nas {int(janela_h)} h seguintes, da maior "
                "para a menor", molhados, rodape, numero,
                com_piloto=bool(d.get("com_piloto")),
                destaques={i for i, v in enumerate(molhados)
                           if v.get("lavagem") == "lavagem"},
                nota=f"Em verde, os voos com {_fmt(limite_mm)} mm ou mais — "
                     "lavagem possível.")

        # ---- dia a dia ----
        for dia in d.get("dias", []):
            do_dia = [v for v in voos if v["inicio"].date() == dia["data"]
                      and v.get("local") == dia["local"]]
            if not do_dia or not dia.get("serie"):
                continue
            fig = plt.Figure(figsize=A4_DEITADO)
            desenhar_voos_no_dia(fig, dia["serie"], crit, do_dia,
                                 fontes=dia.get("fontes"), janela_h=janela_h)
            _cabecalho_sobre(
                fig, sec(f"{dia['data'].strftime('%d/%m/%Y')} — {dia['local']}"),
                f"{len(do_dia)} voos sobre o tempo do dia e da manhã seguinte. "
                "Faixa verde = janela recomendada; barras coloridas = voos; "
                "faixa lilás no painel da chuva = horas logo depois do último "
                "voo.", topo=0.78)
            numero = _fecha(pdf, fig, rodape, numero)

        # ---- tabela completa ----
        numero = _paginas_voos(
            pdf, sec("Todos os voos"),
            f"{len(voos)} operações, em ordem cronológica",
            voos, rodape, numero, com_piloto=bool(d.get("com_piloto")))

    return numero - 1


# =====================================================================
# BLOCO 15 — ABA DE ANÁLISE DE VOOS
# =====================================================================

AGRUPAR_VOOS = ("Não agrupar", "Por piloto", "Por aeronave",
                "Por piloto e aeronave")
CAMPO_AGRUPAR = {
    "Não agrupar": (None, "dia"),
    "Por piloto": ("piloto", "piloto"),
    "Por aeronave": ("aeronave", "aeronave"),
    "Por piloto e aeronave": ("piloto_aeronave", "piloto e aeronave"),
}


class AbaVoos(ttk.Frame):
    """Cruza as operações já voadas com o tempo que fazia na hora e depois."""

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.voos = []
        self.locais = []
        self.avaliados = []
        self.dias = []
        self.crit = None
        self.caminho = None
        self.poligonos = []
        self.comparacao = None
        self.fonte_usada = ""
        self.direcao_texto = ""
        self.fila = queue.Queue()
        self._ocupado = False
        self._construir()

    def _construir(self):
        pref = ler_preferencias().get("voos", {})
        painel = ttk.LabelFrame(self, text="Operações")
        painel.pack(side="top", fill="x", padx=8, pady=(8, 4))

        l1 = ttk.Frame(painel)
        l1.pack(side="top", fill="x", padx=6, pady=(6, 2))
        ttk.Button(l1, text="Carregar arquivo de voos…", style=ESTILO_DESTAQUE,
                   command=self.carregar).pack(side="left")
        self.lbl_arquivo = ttk.Label(l1, text="  Nenhum arquivo carregado.",
                                     foreground="#666")
        self.lbl_arquivo.pack(side="left", padx=(8, 0))

        l2 = ttk.Frame(painel)
        l2.pack(side="top", fill="x", padx=6, pady=2)
        ttk.Label(l2, text="Agrupar:").pack(side="left")
        self.var_agrupar = tk.StringVar(value=AGRUPAR_VOOS[0])
        ttk.Combobox(l2, textvariable=self.var_agrupar, width=22,
                     state="readonly",
                     values=AGRUPAR_VOOS).pack(side="left", padx=(4, 12))

        ttk.Label(l2, text="Estações por local:").pack(side="left")
        self.var_n = tk.StringVar(value="4")
        ttk.Combobox(l2, textvariable=self.var_n, width=3, state="readonly",
                     values=("3", "4", "5")).pack(side="left", padx=(4, 12))

        ttk.Label(l2, text="Fuso:").pack(side="left")
        self.var_fuso = tk.StringVar(value="-3")
        ttk.Combobox(l2, textvariable=self.var_fuso, width=4, state="readonly",
                     values=("-2", "-3", "-4", "-5")).pack(side="left", padx=(4, 12))

        ttk.Label(l2, text="Fonte:").pack(side="left")
        self.var_fonte = tk.StringVar(value=FONTE_MODELO)
        ttk.Combobox(l2, textvariable=self.var_fonte, width=34,
                     state="readonly",
                     values=FONTES_VOOS).pack(side="left", padx=(4, 12))

        l2b = ttk.Frame(painel)
        l2b.pack(side="top", fill="x", padx=6, pady=2)
        ttk.Label(l2b, text="Chuva depois do voo: lavagem possível com").pack(
            side="left")
        self.var_lav_mm = tk.StringVar(value=pref.get("lav_mm", "2"))
        ttk.Entry(l2b, textvariable=self.var_lav_mm, width=5).pack(side="left",
                                                                  padx=4)
        ttk.Label(l2b, text="mm ou mais nas").pack(side="left")
        self.var_lav_h = tk.StringVar(value=pref.get("lav_h", "6"))
        ttk.Combobox(l2b, textvariable=self.var_lav_h, width=4, state="readonly",
                     values=("1", "2", "4", "6", "12", "24")).pack(side="left",
                                                                    padx=4)
        ttk.Label(l2b, text="h seguintes (use o período sem chuva da bula).   "
                            "Critérios de Delta T e vento: aba 2; chuva no "
                            "voo: aba 3.",
                  foreground="#666").pack(side="left")

        l3 = ttk.Frame(painel)
        l3.pack(side="top", fill="x", padx=6, pady=(2, 8))
        self.btn_analisar = botao_principal(l3, "Analisar voos",
                                            self.analisar, state="disabled")
        self.btn_analisar.pack(side="left")
        self.btn_pdf = ttk.Button(l3, text="Relatório de voos PDF…",
                                  style=ESTILO_DESTAQUE,
                                  state="disabled", command=self.exportar_pdf)
        self.btn_pdf.pack(side="left", padx=(10, 0))
        self.btn_csv = ttk.Button(l3, text="Exportar CSV…", state="disabled",
                                  command=self.exportar_csv)
        self.btn_csv.pack(side="left", padx=(10, 0))
        self.btn_html = ttk.Button(l3, text="Mapa interativo…", state="disabled",
                                   command=self.exportar_html)
        self.btn_html.pack(side="left", padx=(10, 0))
        self.btn_geojson = ttk.Button(l3, text="GeoJSON para o QGIS…",
                                      state="disabled",
                                      command=self.exportar_geojson)
        self.btn_geojson.pack(side="left", padx=(10, 0))
        ttk.Button(l3, text="Área com problema…",
                   command=self.carregar_area_problema).pack(side="left",
                                                             padx=(10, 0))
        self.lbl_area = ttk.Label(l3, text="", foreground="#666")
        self.lbl_area.pack(side="left", padx=(8, 0))

        quadro = ttk.LabelFrame(self, text="Resumo")
        quadro.pack(side="top", fill="x", padx=8, pady=4)
        self.lbl_resumo = ttk.Label(
            quadro, justify="left", wraplength=1040,
            text="Carregue o arquivo de operações do dron (GeoJSON com um "
                 "traçado por voo, com Data e Hora).")
        self.lbl_resumo.pack(side="top", anchor="w", padx=8, pady=8)

        saida = ttk.LabelFrame(self, text="Resultado")
        saida.pack(side="top", fill="both", expand=True, padx=8, pady=(4, 8))
        self.vistas = ttk.Notebook(saida)
        self.vistas.pack(fill="both", expand=True, padx=6, pady=6)

        aba_tab = ttk.Frame(self.vistas)
        self.vistas.add(aba_tab, text="  Voos  ")
        self.tabela = self._montar_tabela(aba_tab)

        aba_pior = ttk.Frame(self.vistas)
        self.vistas.add(aba_pior, text="  Piores  ")
        self.tabela_pior = self._montar_tabela(aba_pior)

        aba_mapa = ttk.Frame(self.vistas)
        self.vistas.add(aba_mapa, text="  Mapa  ")
        barra_m = ttk.Frame(aba_mapa)
        barra_m.pack(side="top", fill="x", padx=6, pady=(6, 0))
        ttk.Label(barra_m, text="Colorir por:").pack(side="left")
        self.var_colorir = tk.StringVar(value=MODOS_COR_MAPA[0])
        self.cb_colorir = ttk.Combobox(barra_m, textvariable=self.var_colorir,
                                       width=28, state="readonly",
                                       values=MODOS_COR_MAPA)
        self.cb_colorir.pack(side="left", padx=4)
        self.cb_colorir.bind("<<ComboboxSelected>>",
                             lambda e: self.desenhar_mapa())
        ttk.Label(barra_m, text="  Dia:").pack(side="left")
        self.var_dia_mapa = tk.StringVar(value="todos")
        self.cb_dia_mapa = ttk.Combobox(barra_m, textvariable=self.var_dia_mapa,
                                        width=12, state="readonly",
                                        values=("todos",))
        self.cb_dia_mapa.pack(side="left", padx=4)
        self.cb_dia_mapa.bind("<<ComboboxSelected>>",
                              lambda e: self.desenhar_mapa())
        ttk.Label(barra_m, foreground="#666",
                  text="   Para clicar em cada voo sobre a imagem de satélite, "
                       "use “Mapa interativo…”.").pack(side="left")
        self.fig_mapa, self.canvas_mapa = montar_figura(aba_mapa)

        aba_chuva = ttk.Frame(self.vistas)
        self.vistas.add(aba_chuva, text="  Chuva depois  ")
        self.fig_chuva, self.canvas_chuva = montar_figura(aba_chuva)

        aba_resumo = ttk.Frame(self.vistas)
        self.vistas.add(aba_resumo, text="  Resumo  ")
        self.fig_resumo, self.canvas_resumo = montar_figura(aba_resumo)

        aba_dia = ttk.Frame(self.vistas)
        self.vistas.add(aba_dia, text="  Dia a dia  ")
        barra = ttk.Frame(aba_dia)
        barra.pack(side="top", fill="x", padx=6, pady=(6, 0))
        ttk.Label(barra, text="Dia:").pack(side="left")
        self.var_dia = tk.StringVar()
        self.cb_dia = ttk.Combobox(barra, textvariable=self.var_dia, width=28,
                                   state="readonly")
        self.cb_dia.pack(side="left", padx=4)
        self.cb_dia.bind("<<ComboboxSelected>>", lambda e: self.desenhar_dia())
        self.fig_dia, self.canvas_dia = montar_figura(aba_dia)

    def _montar_tabela(self, pai):
        colunas = ("ini", "dur", "local", "piloto", "ha", "dt", "vento",
                   "dir", "alt", "chuva", "p", "veredito")
        titulos = {"ini": "Início", "dur": "Duração", "local": "Local",
                   "piloto": "Piloto", "ha": "Área (ha)", "dt": "Delta T",
                   "vento": "Vento", "dir": "Vento de", "alt": "Altura",
                   "chuva": "Chuva depois", "p": "Confiança",
                   "veredito": "Veredito"}
        larguras = {"ini": 110, "dur": 60, "local": 65, "piloto": 110,
                    "ha": 65, "dt": 65, "vento": 65, "dir": 75, "alt": 65,
                    "chuva": 90, "p": 75, "veredito": 190}
        moldura = ttk.Frame(pai)
        moldura.pack(side="top", fill="both", expand=True, padx=6, pady=6)
        tabela = ttk.Treeview(moldura, columns=colunas, show="headings")
        for c in colunas:
            tabela.heading(c, text=titulos[c])
            tabela.column(c, width=larguras[c],
                          anchor="w" if c in ("ini", "piloto", "veredito")
                          else "center")
        rol = ttk.Scrollbar(moldura, orient="vertical", command=tabela.yview)
        tabela.configure(yscrollcommand=rol.set)
        tabela.pack(side="left", fill="both", expand=True)
        rol.pack(side="right", fill="y")
        return tabela

    def _lavagem(self):
        """(janela em horas, limite em mm) lidos da tela."""
        try:
            limite = float(self.var_lav_mm.get().replace(",", "."))
            janela = int(float(self.var_lav_h.get().replace(",", ".")))
        except ValueError:
            messagebox.showerror("Parâmetro inválido",
                                 "O limite de chuva e as horas precisam ser "
                                 "números.")
            return None
        gravar_preferencias("voos", {"lav_mm": self.var_lav_mm.get(),
                                     "lav_h": self.var_lav_h.get()})
        return max(1, janela), max(0.1, limite)

    # ------------------------------------------------------------------
    def carregar(self):
        caminho = filedialog.askopenfilename(
            title="Arquivo de operações do dron",
            filetypes=[("GeoJSON", "*.geojson *.json"),
                       ("Todos os arquivos", "*.*")])
        if not caminho:
            return
        try:
            voos, sem_hora = ler_operacoes(caminho, int(self.var_fuso.get()))
        except Exception as e:
            messagebox.showerror("Não consegui ler o arquivo de voos", str(e))
            return

        self.caminho = caminho
        self.voos = voos
        self.locais = agrupar_locais(voos)
        self.avaliados = []

        ini = min(v["inicio"] for v in voos).date()
        fim = max(v["inicio"] for v in voos).date()
        ha = sum(v.get("area_ha") or 0 for v in voos)
        self.lbl_arquivo.config(
            text=f"  {os.path.basename(caminho)} — {len(voos)} voos",
            foreground="#333")
        recado = [f"{len(voos)} voos · {_fmt(ha)} ha · {ini:%d/%m/%Y} a "
                  f"{fim:%d/%m/%Y} · {len(self.locais)} locais distintos:"]
        for g in self.locais:
            recado.append(
                f"   {g['nome']}: {len(g['voos'])} voos, {_fmt(g['area_ha'])} ha, "
                f"centro {g['lat']:.4f}, {g['lon']:.4f}, raio "
                f"{g['raio_km']:.1f} km, de {g['ini']:%d/%m} a {g['fim']:%d/%m}")
        estimadas = sum(1 for v in voos if v.get("altura_origem") == "estimada")
        if estimadas:
            recado.append(f"{estimadas} voos manuais sem altura gravada receberam "
                          "a mediana dos voos do mesmo dia.")
        if sem_hora:
            recado.append(f"{sem_hora} feições ficaram de fora por não terem "
                          "data e hora utilizáveis.")
        recado.append("Clique em “Analisar voos” — cada local usa as estações "
                      "mais próximas dele.")
        self.lbl_resumo.config(text="\n".join(recado))
        self.btn_analisar.config(state="normal")
        self.app.status(f"{len(voos)} voos carregados, {len(self.locais)} locais.")

    def carregar_area_problema(self):
        """Polígono da parte que não ficou boa, para comparar com o resto."""
        caminho = filedialog.askopenfilename(
            title="Polígono da área com problema (KML, KMZ, GeoJSON ou SHP)",
            filetypes=[("Arquivos de área", "*.kml *.kmz *.geojson *.json "
                                            "*.shp *.zip"),
                       ("Todos os arquivos", "*.*")])
        if not caminho:
            return
        try:
            self.poligonos = ler_poligonos(caminho)
        except Exception as e:
            messagebox.showerror("Não consegui ler o polígono", str(e))
            return
        ha = sum(area_hectares(p) or 0 for _, p in self.poligonos)
        self.lbl_area.config(text=f"{len(self.poligonos)} polígono(s), "
                                  f"{_fmt(ha)} ha")
        if self.avaliados:
            self._comparar()
            self._mostrar(self.avaliados, self.locais, self.dias, self.crit, [])
        self.app.status("Área com problema carregada. "
                        + ("Os voos foram comparados." if self.avaliados
                           else "Analise os voos para comparar."))

    def _comparar(self):
        if not self.poligonos or not self.avaliados:
            self.comparacao = None
            return
        janela, limite = self.janela_h, self.limite_mm
        self.comparacao = comparar_area_problema(self.avaliados, self.poligonos,
                                                 janela, limite)

    # ------------------------------------------------------------------
    def analisar(self):
        if self._ocupado or not self.voos:
            return
        if not self.app.estacoes:
            messagebox.showwarning("Sem lista de estações",
                                   "A lista de estações do INMET ainda não "
                                   "carregou. Tente de novo em instantes.")
            return
        crit = self.app.aba_series.ler_criterios()
        if crit is None:
            return
        crit_prev = self.app.aba_previsao.ler_criterios()
        if crit_prev:
            crit["chuva_max"] = crit_prev.get("chuva_max", 0.2)
        lav = self._lavagem()
        if lav is None:
            return
        self.janela_h, self.limite_mm = lav

        self._ocupado = True
        self.btn_analisar.config(state="disabled", text="Analisando…")
        threading.Thread(
            target=self._trabalho,
            args=(list(self.locais), dict(crit), int(self.var_fuso.get()),
                  int(self.var_n.get()), self.var_fonte.get(),
                  dict(self.app.medidos), self.app.calibracao, lav),
            daemon=True).start()
        self.after(150, self._checar_fila)

    def _trabalho(self, locais, crit, fuso, n_estacoes, fonte=FONTE_MODELO,
                  medidos=None, calibracao=None, lavagem=None):
        """Um download por local, porque cada um tem as suas estações."""
        janela_h, limite_mm = lavagem or (JANELA_LAVAGEM_H, LIMITE_LAVAGEM_MM)
        self.janela_h, self.limite_mm = janela_h, limite_mm
        try:
            avaliados, dias, falhas = [], [], []
            fontes_usadas = set()
            for g in locais:
                self.fila.put(("andamento",
                               f"{g['nome']}: estações e série de "
                               f"{g['ini']:%d/%m} a {g['fim']:%d/%m}…"))
                prox = estacoes_proximas(self.app.estacoes, g["lat"], g["lon"],
                                         n=n_estacoes)
                # estação com tabela medida conta mesmo se não estiver entre
                # as mais próximas — medido perto vale mais que modelo
                for cod, tab in (medidos or {}).items():
                    if fonte == FONTE_MEDIDO and cod not in {e["codigo"] for e in prox}:
                        e = next((x for x in self.app.estacoes
                                  if x["codigo"] == cod), None)
                        if e and haversine(g["lat"], g["lon"], e["lat"],
                                           e["lon"]) <= 120:
                            e = dict(e, distancia=haversine(
                                g["lat"], g["lon"], e["lat"], e["lon"]))
                            prox.append(e)
                ini = (g["ini"] - timedelta(days=1)).isoformat()
                # um dia a mais no fim: a chuva de depois do último voo
                fim = (g["fim"] + timedelta(days=2)).isoformat()
                if fim > datetime.now().date().isoformat():
                    fim = datetime.now().date().isoformat()

                crit_local = dict(crit)
                try:
                    h = montar_historico(
                        prox, ini, fim, fuso, crit_local, g["lat"], g["lon"],
                        fonte, METODO_IDW, medidos, calibracao,
                        avisar=lambda t: self.fila.put(("andamento", t)),
                        recuar=True)
                except Exception as erro:
                    falhas.append(f"{g['nome']}: {erro}")
                    continue
                falhas += [f"{g['nome']}: {f}" for f in h["falhas"]]
                fontes_usadas.add(h["fonte"])
                serie = h["serie"]
                g["estacoes"] = h["usadas"]
                g["serie"] = serie
                g["crit"] = crit_local
                g["fonte"] = h["fonte"]

                # a chuva no próprio talhão, pelo modelo: é a única fonte que
                # está em cima da área; as estações ficam a dezenas de km
                ponto = None
                self.fila.put(("andamento", f"{g['nome']}: chuva no talhão…"))
                try:
                    ponto = baixar_open_meteo(g["lat"], g["lon"], ini, fim, fuso)
                    coef = combinar_coeficientes(
                        coeficientes_da_calibracao(calibracao), h["usadas"])
                    if coef:
                        aplicar_calibracao(ponto, coef)
                except Exception as erro:
                    falhas.append(f"{g['nome']}: chuva no talhão indisponível "
                                  f"({erro})")
                fontes = fontes_de_chuva(h["series"], h["usadas"], ponto)
                g["fontes_chuva"] = fontes

                for v in g["voos"]:
                    a = avaliar_voo(v, serie, crit_local)
                    a["local"] = g["nome"]
                    a["piloto_aeronave"] = f'{a["piloto"]} / {a["aeronave"]}'
                    anotar_chuva(a, fontes, janela_h, limite_mm)
                    avaliados.append(a)

                for data in sorted({v["inicio"].date() for v in g["voos"]}):
                    dias.append({"data": data, "local": g["nome"],
                                 "serie": serie, "fontes": fontes})

            if not avaliados:
                raise RuntimeError("nenhum voo pôde ser avaliado.\n\n"
                                   + "\n".join(falhas))
            avaliados.sort(key=lambda v: v["inicio"])
            dias.sort(key=lambda d: d["data"])
            self.fonte_usada = " + ".join(sorted(fontes_usadas)) or fonte
            self.fila.put(("pronto", (avaliados, locais, dias, crit, falhas)))
        except Exception as e:
            self.fila.put(("erro", str(e)))

    def _checar_fila(self):
        try:
            while True:
                tipo, carga = self.fila.get_nowait()
                if tipo == "andamento":
                    self.app.status(carga)
                elif tipo == "erro":
                    self._terminar()
                    messagebox.showerror("Falha na análise dos voos", carga)
                    return
                elif tipo == "pronto":
                    self._terminar()
                    self._mostrar(*carga)
                    return
        except queue.Empty:
            pass
        if self._ocupado:
            self.after(150, self._checar_fila)

    def _terminar(self):
        self._ocupado = False
        self.btn_analisar.config(state="normal", text="Analisar voos")

    # ------------------------------------------------------------------
    def _mostrar(self, avaliados, locais, dias, crit, falhas):
        self.avaliados, self.locais, self.dias, self.crit = (
            avaliados, locais, dias, crit)
        if not hasattr(self, "janela_h"):
            self.janela_h, self.limite_mm = JANELA_LAVAGEM_H, LIMITE_LAVAGEM_MM
        self._comparar()

        ha = sum(v.get("area_ha") or 0 for v in avaliados)
        contagem, area = {}, {}
        for v in avaliados:
            contagem[v["classe"]] = contagem.get(v["classe"], 0) + 1
            area[v["classe"]] = area.get(v["classe"], 0.0) + (v.get("area_ha") or 0)
        aptos = area.get("apta", 0.0)

        linhas = [
            f"{len(avaliados)} voos analisados · {_fmt(ha)} ha · "
            f"{_fmt(aptos)} ha ({100 * aptos / max(ha, 0.001):.0f}%) em "
            "condição apta",
            "Na hora do voo: " + " · ".join(
                f"{NOME_CLASSE_VOO[k]} {contagem[k]} voos ({_fmt(area.get(k, 0))} ha)"
                for k in ORDEM_CLASSE_VOO if k in contagem),
        ]
        lav, ha_lav = {}, {}
        for v in avaliados:
            k = v.get("lavagem", "sem_dado")
            lav[k] = lav.get(k, 0) + 1
            ha_lav[k] = ha_lav.get(k, 0.0) + (v.get("area_ha") or 0)
        linhas.append(
            f"Depois do voo (chuva nas {self.janela_h} h seguintes, lavagem a "
            f"partir de {_fmt(self.limite_mm)} mm): " + " · ".join(
                f"{NOME_LAVAGEM[k]} {lav[k]} voos ({_fmt(ha_lav[k])} ha)"
                for k in ORDEM_LAVAGEM if k in lav))
        molhados = []
        for r in resumo_chuva_por_dia(avaliados, self.janela_h):
            maior = max(r["fontes"].items(), key=lambda kv: kv[1],
                        default=(None, 0.0))
            if maior[1] >= 0.2:
                molhados.append((r["dia"], maior))
        if molhados:
            linhas.append("Dias com chuva depois das aplicações: " + "; ".join(
                f'{dia:%d/%m} até {_fmt(mm)} mm em {self.janela_h} h '
                f'({fonte})' for dia, (fonte, mm) in molhados[:6]))
        fontes = sorted({f for d in dias for f in (d.get("fontes") or {})})
        if fontes:
            linhas.append("Fontes de chuva: " + "; ".join(fontes) + ".")
        linhas.append("Fonte do tempo na hora do voo: "
                      + (self.fonte_usada or "—") + ".")
        d_v, c_v, *_ = media_vetorial(
            [{"vento": v.get("vento"), "direcao": v.get("direcao")}
             for v in avaliados], pesos=[v.get("area_ha") or 0.01
                                         for v in avaliados])
        self.direcao_texto = ""
        if d_v is not None:
            self.direcao_texto = ("Vento durante os voos (ponderado pela "
                                  "área):  " + texto_direcao(d_v, c_v) + ".")
            linhas.append(self.direcao_texto)
        if self.comparacao:
            linhas.append(texto_comparacao(self.comparacao))
        if falhas:
            linhas.append("Avisos: " + "; ".join(falhas[:3])
                          + (f" (+{len(falhas) - 3})" if len(falhas) > 3 else ""))
        self.lbl_resumo.config(text="\n".join(linhas))

        self._preencher(self.tabela, avaliados)
        piores = sorted([v for v in avaliados if v.get("p_apta") is not None],
                        key=lambda v: v["p_apta"])[:40]
        self._preencher(self.tabela_pior, piores)

        datas = sorted({v["inicio"].date() for v in avaliados})
        self.cb_dia_mapa.config(values=["todos"] + [d.strftime("%d/%m/%Y")
                                                    for d in datas])
        self.desenhar_mapa()

        desenhar_chuva_por_dia(self.fig_chuva,
                               resumo_chuva_por_dia(avaliados, self.janela_h),
                               self.janela_h, self.limite_mm,
                               f"Chuva nas {self.janela_h} h seguintes às "
                               "aplicações de cada dia")
        self.canvas_chuva.draw_idle()

        por, rotulo = CAMPO_AGRUPAR[self.var_agrupar.get()]
        desenhar_resumo_voos(self.fig_resumo, avaliados, por, rotulo,
                             f"Hectares por {rotulo} e condição")
        self.canvas_resumo.draw_idle()

        rotulos = [f'{d["data"]:%d/%m/%Y} — {d["local"]}' for d in dias]
        self.cb_dia.config(values=rotulos)
        if rotulos:
            if self.var_dia.get() not in rotulos:
                self.var_dia.set(rotulos[0])
            self.desenhar_dia()

        for b in (self.btn_pdf, self.btn_csv, self.btn_html, self.btn_geojson):
            b.config(state="normal")
        self.app.status(f"{len(avaliados)} voos analisados · "
                        f"{100 * aptos / max(ha, 0.001):.0f}% da área em "
                        "condição apta · "
                        f"{lav.get('lavagem', 0)} com chuva que pode ter lavado.")

    def desenhar_mapa(self):
        if not self.avaliados:
            return
        dia = self.var_dia_mapa.get()
        voos = [v for v in self.avaliados
                if dia in ("", "todos") or v["inicio"].strftime("%d/%m/%Y") == dia]
        titulo = (f"{len(voos)} voos" + ("" if dia in ("", "todos")
                                         else f" em {dia}"))
        desenhar_mapa_voos(self.fig_mapa, voos,
                           [e for g in self.locais for e in g.get("estacoes", [])],
                           titulo, colorir=self.var_colorir.get(),
                           poligonos=self.poligonos)
        self.canvas_mapa.draw_idle()

    def _preencher(self, tabela, voos):
        for item in tabela.get_children():
            tabela.delete(item)
        for v in voos:
            p = v.get("p_apta")
            ch = v.get("chuva_apos_janela")
            tabela.insert("", "end", values=(
                v["inicio"].strftime("%d/%m %H:%M"),
                f'{(v["duracao_h"] or 0) * 60:.0f} min',
                v.get("local", "—"),
                str(v.get("piloto", "—"))[:20],
                _fmt(v.get("area_ha")),
                _fmt(v.get("delta_t")),
                _fmt(v.get("vento")),
                _rotulo_dir(v.get("direcao")),
                _fmt(v.get("altura_usada"))
                + ("*" if v.get("altura_origem") == "estimada" else ""),
                "—" if ch is None else f"{_fmt(ch)} mm"
                + (" !" if v.get("lavagem") == "lavagem" else ""),
                "—" if p is None else f"{100 * p:.0f}%",
                f'{NOME_CLASSE_VOO.get(v["classe"], v["classe"])}'
                + (f' — {v.get("motivo")}' if v.get("motivo")
                   and v["classe"] != "apta" else ""),
            ))

    def desenhar_dia(self):
        rotulo = self.var_dia.get()
        for d in self.dias:
            if f'{d["data"]:%d/%m/%Y} — {d["local"]}' == rotulo:
                do_dia = [v for v in self.avaliados
                          if v["inicio"].date() == d["data"]
                          and v.get("local") == d["local"]]
                desenhar_voos_no_dia(self.fig_dia, d["serie"], self.crit,
                                     do_dia, rotulo, fontes=d.get("fontes"),
                                     janela_h=getattr(self, "janela_h",
                                                      JANELA_LAVAGEM_H))
                self.canvas_dia.draw_idle()
                return

    # ------------------------------------------------------------------
    def exportar_html(self):
        if not self.avaliados:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar o mapa interativo dos voos", defaultextension=".html",
            initialfile=f"mapa_voos_{datetime.now():%Y%m%d_%H%M}.html",
            filetypes=[("Página HTML", "*.html")])
        if not caminho:
            return
        try:
            n = gerar_mapa_html(caminho, self.avaliados,
                                f"{len(self.avaliados)} voos analisados",
                                self.janela_h, self.limite_mm, self.poligonos)
        except Exception as e:
            messagebox.showerror("Não consegui gerar o mapa", str(e))
            return
        try:
            import webbrowser
            webbrowser.open("file:///" + os.path.abspath(caminho).replace("\\", "/"))
        except Exception:
            pass
        self.app.status(f"Mapa interativo com {n} voos gravado em "
                        f"{os.path.basename(caminho)} (abre no navegador; as "
                        "imagens de fundo precisam de internet).")

    def exportar_geojson(self):
        if not self.avaliados:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar os voos analisados (GeoJSON)",
            defaultextension=".geojson",
            initialfile=f"voos_analisados_{datetime.now():%Y%m%d_%H%M}.geojson",
            filetypes=[("GeoJSON", "*.geojson")])
        if not caminho:
            return
        try:
            n = exportar_voos_geojson(caminho, self.avaliados, self.janela_h,
                                      self.poligonos)
        except Exception as e:
            messagebox.showerror("Não consegui salvar", str(e))
            return
        self.app.status(f"{n} feições gravadas em {os.path.basename(caminho)} — "
                        "no QGIS, estilize por 'lavagem', 'veredito' ou "
                        "'chuva_apos_6h'.")

    def exportar_csv(self):
        if not self.avaliados:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar a análise dos voos", defaultextension=".csv",
            initialfile=f"voos_{datetime.now():%Y%m%d_%H%M}.csv",
            filetypes=[("CSV", "*.csv")])
        if not caminho:
            return

        def br(v, casas=2):
            return "" if v is None else f"{v:.{casas}f}".replace(".", ",")

        try:
            with open(caminho, "w", encoding="utf-8-sig", newline="") as f:
                f.write("Voo;Data;Hora;Duracao_min;Local;Piloto;Aeronave;Modo;"
                        "Area_ha;Litros;Taxa_L_ha;Altura_voo_m;Temp_C;UR_pct;"
                        "DeltaT_C;Vento_kmh;Rajada_kmh;Chuva_mm;Inversao;"
                        "Confianca_pct;Veredito;Motivo;DirVento_graus;VentoDe;"
                        "DerivaPara;Altura_origem;Fonte;Chuva_durante_mm_h;"
                        + "".join(f"Chuva_{h}h_depois_mm;" for h in JANELAS_APOS)
                        + "Fonte_da_maior_chuva;Chuva_por_fonte;Lavagem;"
                          "Na_area_problema\n")
                for v in self.avaliados:
                    p = v.get("p_apta")
                    ca = v.get("chuva_apos") or {}
                    f.write(";".join([
                        v["id"], v["inicio"].strftime("%d/%m/%Y"),
                        v["inicio"].strftime("%H:%M:%S"),
                        br((v["duracao_h"] or 0) * 60, 1),
                        v.get("local", ""), v.get("piloto", ""),
                        v.get("aeronave", ""), v.get("modo", ""),
                        br(v.get("area_ha")), br(v.get("litros")),
                        br(v.get("taxa")), br(v.get("altura_usada")),
                        br(v.get("temp")), br(v.get("ur"), 0),
                        br(v.get("delta_t")), br(v.get("vento")),
                        br(v.get("rajada")), br(v.get("chuva")),
                        str(v.get("inversao") or ""),
                        "" if p is None else br(100 * p, 0),
                        NOME_CLASSE_VOO.get(v["classe"], v["classe"]),
                        str(v.get("motivo") or ""),
                        "" if v.get("direcao") is None
                        else f'{v["direcao"]:.0f}',
                        "" if v.get("direcao") is None else rumo(v["direcao"]),
                        "" if v.get("direcao") is None
                        else rumo(v["direcao"] + 180),
                        str(v.get("altura_origem") or ""),
                        self.fonte_usada or "",
                        br(v.get("chuva_durante")),
                        *[br(ca.get(h)) for h in JANELAS_APOS],
                        str(v.get("chuva_apos_fonte") or ""),
                        texto_chuva_voo(v, self.janela_h).replace(";", " |"),
                        NOME_LAVAGEM.get(v.get("lavagem"), ""),
                        "" if v.get("na_area_problema") is None
                        else ("sim" if v["na_area_problema"] else "não"),
                    ]) + "\n")
        except Exception as e:
            messagebox.showerror("Não consegui salvar", str(e))
            return
        self.app.status(f"Análise gravada em {os.path.basename(caminho)}.")

    def exportar_pdf(self):
        if not self.avaliados:
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar o relatório de voos", defaultextension=".pdf",
            initialfile=f"relatorio_voos_{datetime.now():%Y%m%d_%H%M}.pdf",
            filetypes=[("PDF", "*.pdf")])
        if not caminho:
            return

        por, rotulo = CAMPO_AGRUPAR[self.var_agrupar.get()]
        disp = ""
        primeiro = next((g for g in self.locais if g.get("crit")), None)
        if primeiro:
            c = primeiro["crit"]
            if c.get("margem_dt"):
                disp = (f"Incerteza de representatividade adotada: "
                        f"±{_fmt(c['margem_dt'])} °C no Delta T e "
                        f"±{_fmt(c['margem_vento'])} km/h no vento.")
        dados = {
            "voos": self.avaliados, "locais": self.locais, "dias": self.dias,
            "crit": self.crit,
            "ini": min(v["inicio"] for v in self.avaliados).strftime("%d/%m/%Y"),
            "fim": max(v["inicio"] for v in self.avaliados).strftime("%d/%m/%Y"),
            "por": por, "rotulo_por": rotulo,
            "com_piloto": por in ("piloto", "piloto_aeronave"),
            "fonte": {FONTE_MEDIDO: "estações do INMET (medido)",
                      FONTE_CORRIGIDO: "Open-Meteo corrigido pela calibração "
                                       "local"}.get(
                self.fonte_usada, "Open-Meteo (reanálise)"),
            "direcao_texto": self.direcao_texto,
            "dispersao": disp,
            "janela_h": self.janela_h, "limite_mm": self.limite_mm,
            "poligonos": self.poligonos, "comparacao": self.comparacao,
            "texto_area": (texto_comparacao(self.comparacao)
                           if self.comparacao else ""),
        }
        try:
            paginas = gerar_relatorio_voos_pdf(caminho, dados)
        except Exception as e:
            messagebox.showerror("Não consegui gerar o relatório", str(e))
            return
        messagebox.showinfo("Relatório pronto",
                            f"{paginas} páginas gravadas em:\n{caminho}")
        self.app.status(f"Relatório de voos com {paginas} páginas gravado.")


# =====================================================================
# BLOCO 16 — JANELA PRINCIPAL
# =====================================================================

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"Janela de Aplicação — estações automáticas do INMET "
                   f"— v. {VERSAO}")
        self.geometry("1100x860")
        self.minsize(900, 700)

        # estado compartilhado entre as abas
        self.estacoes = []
        self.lat = None
        self.lon = None
        self.area_ha = None
        self.origem = None
        self.proximas = []
        # tabelas medidas carregadas nesta sessão: {código: tabela}
        self.medidos = {}
        # leituras feitas no talhão (termo-higrômetro, anemômetro de mão)
        self.campo = []
        # pares medido × modelo acumulados entre sessões
        self.calibracao = carregar_calibracao()

        configurar_estilos(self)
        self._construir_status()
        self._construir_abas()
        self.after(120, self.carregar_estacoes_inicial)

    # ------------------------------------------------------------------
    def _construir_abas(self):
        self.abas = ttk.Notebook(self)
        self.abas.pack(fill="both", expand=True, padx=2, pady=2)

        self.aba_area = AbaArea(self.abas, self)
        self.abas.add(self.aba_area, text="  1. Área e estações  ")

        self.aba_series = AbaSeries(self.abas, self)
        self.abas.add(self.aba_series, text="  2. Séries e Delta T  ")

        self.aba_previsao = AbaPrevisao(self.abas, self)
        self.abas.add(self.aba_previsao, text="  3. Previsão  ")

        self.aba_relatorio = AbaRelatorio(self.abas, self)
        self.abas.add(self.aba_relatorio, text="  4. Relatório  ")

        self.aba_voos = AbaVoos(self.abas, self)
        self.abas.add(self.aba_voos, text="  5. Voos realizados  ")

        # o botão do rodapé muda de papel conforme a aba aberta
        self.abas.bind("<<NotebookTabChanged>>", self._aba_mudou)
        self._aba_mudou()

    def _construir_status(self):
        barra = ttk.Frame(self)
        barra.pack(side="bottom", fill="x")
        ttk.Separator(barra, orient="horizontal").pack(side="top", fill="x")

        self.lbl_status = ttk.Label(barra, text="Iniciando…", anchor="w")
        self.lbl_status.pack(side="left", padx=8, pady=4)

        self.btn_proxima = ttk.Button(barra, text="Próxima etapa: séries e Delta T  →",
                                      style=ESTILO_DESTAQUE,
                                      command=self.ir_para_series, state="disabled")
        self.btn_proxima.pack(side="right", padx=8, pady=3)

        self.btn_atualizar = ttk.Button(barra, text="Atualizar lista de estações",
                                        command=self.atualizar_estacoes)
        self.btn_atualizar.pack(side="right", padx=4, pady=3)

    def status(self, texto):
        self.lbl_status.config(text=texto)
        self.update_idletasks()

    # ------------------------------------------------------------------
    def carregar_estacoes_inicial(self):
        self.status("Carregando estações do INMET…")
        try:
            bruto, origem = carregar_estacoes()
            self.estacoes = normalizar(bruto)
        except Exception as e:
            messagebox.showerror(
                "Não consegui carregar as estações",
                f"{e}\n\n"
                "Verifique a conexão e clique em 'Atualizar lista de estações'.\n"
                "A lista vem de apitempo.inmet.gov.br/estacoes/T, que é pública.")
            self.status("Sem lista de estações.")
            return

        operantes = sum(1 for e in self.estacoes if e["operante"])
        self.aba_area.preencher_ufs()

        # Monta o cache de contornos na primeira execução, se os zips do IBGE
        # estiverem nesta pasta. Depois disso carrega do cache, num piscar.
        try:
            feito = construir_cache_contornos(avisar=self.status)
            if feito:
                self.aba_area._contorno_uf = carregar_contorno_ufs()
                self.aba_area._contorno_mun = {}
                self.status("Contornos preparados: " + ", ".join(feito))
        except Exception as e:
            print("Não consegui preparar os contornos do mapa:", e)

        self.aba_area.atualizar_mapa()
        fundo = "com contorno de estados e municípios" if self.aba_area._contorno_uf \
                else "sem contorno de fundo (coloque os zips do IBGE nesta pasta)"
        self.status(f"{len(self.estacoes)} estações ({operantes} operantes) do {origem}, "
                    f"{fundo}. Escolha o estado e marque sua área.")

    def atualizar_estacoes(self):
        self.status("Baixando a lista atualizada do INMET…")
        try:
            bruto, _ = carregar_estacoes(forcar_download=True)
            self.estacoes = normalizar(bruto)
        except Exception as e:
            messagebox.showerror("Falha ao atualizar", str(e))
            self.status("Continuo com a lista anterior.")
            return
        operantes = sum(1 for e in self.estacoes if e["operante"])
        self.aba_area.preencher_ufs()
        if self.lat is not None:
            self.definir_area(self.lat, self.lon, self.area_ha, self.origem)
        else:
            self.aba_area.atualizar_mapa()
        self.status(f"Lista atualizada: {len(self.estacoes)} estações, "
                    f"{operantes} operantes.")

    # ------------------------------------------------------------------
    def definir_area(self, lat, lon, area_ha=None, origem=""):
        """Registra a área e recalcula tudo que depende dela."""
        self.lat, self.lon = lat, lon
        self.area_ha = area_ha
        self.origem = origem

        n = int(self.aba_area.var_n.get())
        self.proximas = estacoes_proximas(self.estacoes, lat, lon, n=n)

        self.aba_area.var_lat.set(f"{lat:.6f}")
        self.aba_area.var_lon.set(f"{lon:.6f}")

        # o mapa acompanha a área: se ela caiu em outro estado, mostra o de lá
        if self.proximas:
            uf = self.proximas[0]["uf"]
            for rotulo, sigla in self.aba_area._uf_por_rotulo.items():
                if sigla == uf and self.aba_area.var_uf.get() != rotulo:
                    self.aba_area.var_uf.set(rotulo)
                    break

        self.aba_area.atualizar_mapa()
        self.aba_area.atualizar_tabela()

        self._aba_mudou()

        txt = f"Área em {lat:.5f}, {lon:.5f}"
        if area_ha:
            txt += f" · {area_ha:,.1f} ha".replace(",", "X").replace(".", ",").replace("X", ".")
        txt += f" · {origem} · {len(self.proximas)} estações escolhidas."
        self.status(txt)

    def _aba_mudou(self, _evento=None):
        """Mantém o botão do rodapé coerente com a aba que está aberta.

        Ele acompanha a sequência natural do trabalho: definir a área, olhar
        o histórico, olhar a previsão. Na última aba o caminho é de volta —
        não faz sentido oferecer 'próxima etapa' quando não há próxima.
        """
        if not hasattr(self, "btn_proxima") or not hasattr(self, "abas"):
            return
        try:
            aba = self.abas.index(self.abas.select())
        except tk.TclError:
            return

        tem_area = self.lat is not None
        if aba == 0:
            self.btn_proxima.config(text="Próxima etapa: séries e Delta T  →",
                                    command=self.ir_para_series,
                                    state="normal" if tem_area else "disabled")
        elif aba == 1:
            self.btn_proxima.config(text="Próxima etapa: previsão  →",
                                    command=self.ir_para_previsao,
                                    state="normal" if tem_area else "disabled")
        elif aba == 2:
            self.btn_proxima.config(text="Próxima etapa: relatório  →",
                                    command=self.ir_para_relatorio,
                                    state="normal" if tem_area else "disabled")
        elif aba == 3:
            self.btn_proxima.config(text="Analisar voos realizados  →",
                                    command=self.ir_para_voos, state="normal")
        else:
            self.btn_proxima.config(text="←  Voltar para o relatório",
                                    command=self.ir_para_relatorio,
                                    state="normal")

    def voltar_para_area(self):
        """Volta para a aba 1 sem perder nada do que já foi baixado."""
        self.abas.select(self.aba_area)

    def ir_para_series(self):
        """Leva para a aba 2 já com as estações da área."""
        self.abas.select(self.aba_series)
        if not self.aba_series.serie:
            self.aba_series.lbl_resumo.config(
                text=f"{len(self.proximas)} estações escolhidas na aba 1. "
                     "Confira o período e os critérios e clique em "
                     "“Baixar e analisar”.")

    def ir_para_previsao(self):
        """Leva para a aba 3, que olha para os próximos dias."""
        self.abas.select(self.aba_previsao)
        if not self.aba_previsao.serie:
            self.aba_previsao.lbl_resumo.config(
                text=f"{len(self.proximas)} estações escolhidas na aba 1. "
                     "Escolha quantos dias à frente e clique em "
                     "“Buscar previsão”.")

    def ir_para_relatorio(self):
        """Leva para a aba 4, que junta tudo num PDF."""
        self.abas.select(self.aba_relatorio)

    def ir_para_voos(self):
        """Leva para a aba 5, que olha as operações já realizadas."""
        self.abas.select(self.aba_voos)

    def limpar_area(self):
        self.lat = self.lon = self.area_ha = self.origem = None
        self.proximas = []
        self._aba_mudou()
        self.aba_area.atualizar_mapa()
        self.aba_area.atualizar_tabela()
        self.status("Área limpa. Clique no mapa, digite a coordenada ou "
                    "carregue o arquivo do talhão.")


# =====================================================================
# BLOCO 17 — INÍCIO DO PROGRAMA
# =====================================================================

def main():
    try:
        app = App()
    except tk.TclError as e:
        print("Não consegui abrir a janela:", e)
        print("\nNo Linux, instale o tkinter:  sudo apt install python3-tk")
        sys.exit(1)
    app.mainloop()


if __name__ == "__main__":
    main()
