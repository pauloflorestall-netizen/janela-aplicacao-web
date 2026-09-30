"""
A orquestração que no desktop ficava dentro das abas do Tkinter,
reescrita como funções simples, sem tela.

Toda a conta continua no janela_aplicacao.py. Aqui só se junta o que
cada botão fazia: ler critérios, chamar as funções, montar os textos
do resumo e gerar os arquivos para download (em bytes, sem diálogo de
"salvar como").
"""

import io
import json
import math
import os
import tempfile
import zipfile
from datetime import datetime, timedelta

import numpy as np
from matplotlib.collections import LineCollection
from matplotlib.figure import Figure

import nucleo

ja = nucleo.carregar()


# ---------------------------------------------------------------------
# Critérios
# ---------------------------------------------------------------------

class _Var:
    """Imita o tk.StringVar: só precisa do .get()."""

    def __init__(self, valor):
        self.valor = "" if valor is None else str(valor)

    def get(self):
        return self.valor


class _Campos:
    pass


def criterios(dt_min, dt_max, vento_min, vento_max, rajada, rainfast,
              altura, z0, inversao, bulbo, chuva_max=0.2, conjunto=False):
    """Monta o dicionário de critério. Levanta ValueError com o recado."""
    crit = {"dt_min": float(dt_min), "dt_max": float(dt_max),
            "vento_min": float(vento_min), "vento_max": float(vento_max)}
    if crit["dt_min"] >= crit["dt_max"]:
        raise ValueError("O Delta T mínimo tem que ser menor que o máximo.")
    if crit["vento_min"] >= crit["vento_max"]:
        raise ValueError("O vento mínimo tem que ser menor que o máximo.")

    c = _Campos()
    c.var_rajada, c.var_rainfast = _Var(rajada), _Var(rainfast)
    c.var_altura, c.var_z0 = _Var(altura), _Var(z0)
    c.var_inversao, c.var_bulbo = _Var(inversao), _Var(bulbo)
    nucleo.pegar_avisos()
    if not ja.ler_seguranca(c, crit):
        avisos = nucleo.pegar_avisos()
        raise ValueError(avisos[-1][2] if avisos else "Parâmetro inválido.")
    crit["chuva_max"] = float(chuva_max)
    if conjunto:
        crit["limiar_p"] = ja.LIMIAR_P
    return crit


# ---------------------------------------------------------------------
# Arquivos enviados pelo navegador
# ---------------------------------------------------------------------

_PASTA_UPLOAD = os.path.join(tempfile.gettempdir(), "janela_uploads")


def salvar_upload(arquivo):
    """Grava o arquivo enviado com o nome original e devolve o caminho.

    O nome importa: o programa reconhece a estação pelo código no nome
    do arquivo (A413.csv), e o tipo do talhão pela extensão.
    """
    pasta = tempfile.mkdtemp(dir=_garantir(_PASTA_UPLOAD))
    caminho = os.path.join(pasta, os.path.basename(arquivo.name))
    with open(caminho, "wb") as f:
        f.write(arquivo.getvalue())
    return caminho


def _garantir(pasta):
    os.makedirs(pasta, exist_ok=True)
    return pasta


def _para_bytes(gravar, sufixo):
    """Roda uma função que grava num caminho e devolve o conteúdo."""
    pasta = tempfile.mkdtemp()
    caminho = os.path.join(pasta, "saida" + sufixo)
    retorno = gravar(caminho)
    with open(caminho, "rb") as f:
        return f.read(), retorno


# ---------------------------------------------------------------------
# Figuras
# ---------------------------------------------------------------------

def figura_png(desenhar, largura=10, altura=5.4, dpi=110):
    """Desenha numa figura em memória e devolve o PNG."""
    fig = Figure(figsize=(largura, altura), facecolor=ja.COR_FUNDO)
    desenhar(fig)
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=dpi, facecolor=fig.get_facecolor())
    return buf.getvalue()


_CONTORNOS_MUN = {}


def municipios(uf):
    if uf not in _CONTORNOS_MUN:
        _CONTORNOS_MUN[uf] = ja.carregar_contorno_municipios(uf)
    return _CONTORNOS_MUN[uf]


def segs_uf():
    cont = ja.carregar_contorno_ufs() or {}
    return [parte for partes in cont.values() for parte in partes
            if len(parte) > 2]


def segs_mun(ufs):
    segs = []
    for sigla in ufs:
        try:
            segs += [m["p"] for m in municipios(sigla) if len(m["p"]) > 2]
        except Exception:
            pass
    return segs


def ufs_em_cena(uf, proximas):
    ufs = {uf} if uf else set()
    ufs |= {p["uf"] for p in proximas if p.get("uf")}
    return ufs


def desenhar_mapa_area(fig, estacoes, uf, proximas, lat, lon,
                       pontos_area=None):
    """O mapa da aba 1, sem a parte de clique e de mouse."""
    ax = fig.add_subplot(111)
    ax.set_facecolor(ja.COR_FUNDO)
    cena = ufs_em_cena(uf, proximas)
    s_mun, s_uf = segs_mun(cena), segs_uf()
    if s_mun:
        ax.add_collection(LineCollection(s_mun, colors=ja.COR_MUNICIPIO,
                                         linewidths=0.6, zorder=0))
    if s_uf:
        ax.add_collection(LineCollection(s_uf, colors=ja.COR_UF,
                                         linewidths=0.9, zorder=1))

    base = [e for e in estacoes if e["operante"]]
    visiveis = [e for e in base if e["uf"] == uf] if uf else base
    escolhidas = {p["codigo"] for p in proximas}
    if visiveis:
        ax.scatter([e["lon"] for e in visiveis if e["codigo"] not in escolhidas],
                   [e["lat"] for e in visiveis if e["codigo"] not in escolhidas],
                   s=22, c=ja.COR_ESTACAO, linewidths=0, alpha=0.85, zorder=2,
                   label="Estações operantes")
    if lat is not None and proximas:
        for p in proximas:
            ax.plot([lon, p["lon"]], [lat, p["lat"]], color=ja.COR_LINHA,
                    linewidth=1, linestyle="--", alpha=0.8, zorder=3)
        ax.scatter([p["lon"] for p in proximas], [p["lat"] for p in proximas],
                   s=70, c=ja.COR_SELECIONADA, linewidths=0, zorder=5,
                   label="Estações escolhidas")
        for p in proximas:
            ax.annotate(f'{p["nome"][:22]}\n{p["distancia"]:.0f} km',
                        (p["lon"], p["lat"]), textcoords="offset points",
                        xytext=(7, 5), fontsize=7.5, color="#333", zorder=6)
    if pontos_area and len(pontos_area) >= 3:
        xs = [p[0] for p in pontos_area]
        ys = [p[1] for p in pontos_area]
        ax.fill(xs, ys, color=ja.COR_AREA, alpha=0.25, zorder=4)
        ax.plot(xs + [xs[0]], ys + [ys[0]], color=ja.COR_AREA, linewidth=1.8,
                zorder=4)
    if lat is not None:
        ax.scatter([lon], [lat], s=130, marker="X", c=ja.COR_AREA,
                   edgecolors="white", linewidths=1.5, zorder=7,
                   label="Sua área")

    # enquadramento: a área e as estações, ou o estado, ou o Brasil
    if lat is not None and proximas:
        lats = [lat] + [p["lat"] for p in proximas]
        lons = [lon] + [p["lon"] for p in proximas]
    elif visiveis:
        lats = [e["lat"] for e in visiveis]
        lons = [e["lon"] for e in visiveis]
    else:
        lats, lons = [-34, 6], [-74, -34]
    fy = max(0.25, (max(lats) - min(lats)) * 0.22)
    fx = max(0.25, (max(lons) - min(lons)) * 0.22)
    ax.set_xlim(min(lons) - fx, max(lons) + fx)
    ax.set_ylim(min(lats) - fy, max(lats) + fy)

    # nome dos maiores municípios, só quando o recorte é pequeno
    x0, x1 = ax.get_xlim()
    y0, y1 = ax.get_ylim()
    if x1 - x0 <= 12:
        vis = []
        for sigla in cena:
            for m in municipios(sigla):
                bx0, by0, bx1, by1 = m["b"]
                cx, cy = (bx0 + bx1) / 2, (by0 + by1) / 2
                if x0 < cx < x1 and y0 < cy < y1:
                    vis.append(((bx1 - bx0) * (by1 - by0), cx, cy, m["n"]))
        limite = 12 if x1 - x0 > 3 else 20
        for _, cx, cy, nome in sorted(vis, reverse=True)[:limite]:
            ax.text(cx, cy, nome, fontsize=6.5, color=ja.COR_NOME_MUN,
                    ha="center", va="center", zorder=1)

    ax.set_xlabel("Longitude", fontsize=9)
    ax.set_ylabel("Latitude", fontsize=9)
    ax.grid(True, alpha=0.25, linewidth=0.7)
    ax.tick_params(labelsize=8)
    if visiveis or lat is not None:
        ax.legend(loc="upper right", fontsize=8, framealpha=0.9)
    lat_meio = np.mean(ax.get_ylim())
    ax.set_aspect(1 / max(0.1, math.cos(math.radians(lat_meio))))
    fig.tight_layout()


# ---------------------------------------------------------------------
# Tabelas
# ---------------------------------------------------------------------

def tabela_estacoes(proximas):
    pesos = ja.pesos_idw(proximas)
    return [{"Código": p["codigo"], "Estação": p["nome"], "UF": p["uf"],
             "Distância (km)": round(p["distancia"], 1),
             "Peso na série": f'{pesos.get(p["codigo"], 0) * 100:.0f}%',
             "Altitude (m)": round(p["altitude"])} for p in proximas]


def aviso_estacoes(proximas):
    if not proximas:
        return ""
    pesos = ja.pesos_idw(proximas)
    d0 = proximas[0]["distancia"]
    if d0 > 100:
        return (f"A estação mais próxima está a {d0:.0f} km. A série vai "
                "representar mal o microclima da sua área.")
    if pesos and max(pesos.values()) > 0.8:
        dom = max(pesos, key=pesos.get)
        nome = next(p["nome"] for p in proximas if p["codigo"] == dom)
        return (f"{nome} responde por {pesos[dom] * 100:.0f}% da série — na "
                "prática a análise é dela. As outras entram como conferência "
                "e cobrem as horas sem dado.")
    return ""


def tabela_janelas(janelas, com_chuva=False, com_prob=False):
    colunas = list(ja.COLUNAS_JANELAS)
    if com_chuva:
        colunas.append("Chuva (mm)")
    if com_prob:
        colunas.append("Confiança")
    return [dict(zip(colunas, linha))
            for linha in ja._linhas_janelas(janelas, com_chuva, com_prob)]


def tabela_voos(voos):
    saida = []
    for v in voos:
        p = v.get("p_apta")
        ch = v.get("chuva_apos_janela")
        saida.append({
            "Início": v["inicio"].strftime("%d/%m %H:%M"),
            "Duração": f'{(v["duracao_h"] or 0) * 60:.0f} min',
            "Local": v.get("local", "—"),
            "Piloto": str(v.get("piloto", "—"))[:20],
            "Área (ha)": ja._fmt(v.get("area_ha")),
            "Delta T": ja._fmt(v.get("delta_t")),
            "Vento": ja._fmt(v.get("vento")),
            "Vento de": ja._rotulo_dir(v.get("direcao")),
            "Altura": ja._fmt(v.get("altura_usada"))
            + ("*" if v.get("altura_origem") == "estimada" else ""),
            "Chuva depois": "—" if ch is None else f"{ja._fmt(ch)} mm"
            + (" !" if v.get("lavagem") == "lavagem" else ""),
            "Confiança": "—" if p is None else f"{100 * p:.0f}%",
            "Veredito": ja.NOME_CLASSE_VOO.get(v["classe"], v["classe"])
            + (f' — {v.get("motivo")}' if v.get("motivo")
               and v["classe"] != "apta" else ""),
        })
    return saida


# ---------------------------------------------------------------------
# Aba 2 — histórico
# ---------------------------------------------------------------------

def periodo_das_tabelas(medidos):
    inicios = [t["diag"]["inicio"] for t in medidos.values()
               if (t.get("diag") or {}).get("inicio")]
    fins = [t["diag"]["fim"] for t in medidos.values()
            if (t.get("diag") or {}).get("fim")]
    if not inicios or not fins:
        return None
    return min(inicios).date(), max(fins).date()


def resumo_historico(r, crit, lat, lon, campo=None):
    """As linhas do quadro "Resumo" da aba 2. Devolve (linhas, metodo)."""
    serie, janelas = r["serie"], r["janelas"]
    metodo = r["metodo"] if r["usadas"] or r["metodo"] == ja.METODO_PONTO \
        else ja.METODO_IDW
    if r["fonte"] == ja.FONTE_MEDIDO:
        metodo = ja.METODO_IDW
    texto, n_validas, n_aptas = ja.resumir(serie, janelas, crit, r["falhas"])
    linhas = [ja.texto_fonte(r),
              ja.linha_do_metodo(metodo, r["alt"], r["series"], serie),
              ja.texto_do_vento(crit), texto]
    aptas = [l for l in serie.values() if ja.e_apto(ja.classificar(l, crit))]
    d_apt, c_apt, *_ = ja.media_vetorial(aptas)
    if d_apt is not None:
        linhas.append("Vento nas horas aptas: "
                      + ja.texto_direcao(d_apt, c_apt) + ".")
    if r.get("verif"):
        linhas.append(ja.texto_verificacao(r["verif"]))
    if campo:
        linhas.append(ja.texto_campo(ja.comparar_campo(campo, serie, crit)))
    if r.get("calibracao"):
        linhas.append(f"Calibração local atualizada ({r['novos_dias']} dia(s) "
                      "novo(s)). Baixe o calibracao.json no menu lateral para "
                      "não perder.")
    return [t for t in linhas if t], metodo, n_validas, n_aptas


def figuras_historico(r, crit, metodo, periodo, lat, lon, campo=None):
    """PNG de cada vista da aba 2 (menos os mapas, que têm parâmetro)."""
    serie = r["serie"]
    alvo = ("série no ponto da área" if metodo == ja.METODO_PONTO
            else f"{len(r['series'])} estações interpoladas")
    rotulo = {ja.FONTE_MEDIDO: "medido",
              ja.FONTE_CORRIGIDO: "modelo corrigido",
              ja.FONTE_API: "medido (API)"}.get(r["fonte"], "modelo")
    titulo = f"{periodo} · {alvo} · {rotulo}"

    def serie_fig(fig):
        ja.desenhar_serie(fig, serie, crit, titulo)
        ja.marcar_campo_no_grafico(fig, campo, crit)

    figs = {
        "serie": figura_png(serie_fig),
        "calor": figura_png(lambda f: ja.desenhar_mapa_calor(f, serie, crit,
                                                             titulo)),
        "verif": figura_png(lambda f: ja.desenhar_verificacao(
            f, r.get("verif"), None,
            "Modelo (Open-Meteo) × medido nas estações, na área")),
    }
    if metodo == ja.METODO_PONTO:
        figs["dir"] = figura_png(lambda f: ja.desenhar_direcao(
            f, serie, crit, None, (lat, lon), f"{titulo} · direção do vento"))
    return figs


def pontos_das_estacoes(r, proximas):
    if not r or "PONTO" in (r.get("series") or {}):
        return []
    usadas = r.get("usadas") or proximas
    return ja.resumo_por_estacao(r["series"], usadas)


def figuras_mapas(r, crit, pontos, lat, lon, potencia, celulas, em_km,
                  periodo):
    area = (lat, lon) if lat is not None else None
    figs = {"mapas": figura_png(lambda f: ja.desenhar_mapas_interpolacao(
        f, pontos, area, crit, potencia, celulas, em_km, periodo),
        largura=12, altura=5.4)}
    if r and r.get("serie"):
        figs["dir"] = figura_png(lambda f: ja.desenhar_direcao(
            f, r["serie"], crit, pontos, area,
            f"{periodo} · direção do vento", potencia, em_km))
    return figs


def verificar_passadas(r, fuso, avisar=None):
    avisar = avisar or (lambda t: None)
    dias = (datetime.now().date() - min(r["obs_area"]).date()).days + 1
    rodadas, falhas = {}, []
    for i, e in enumerate(r["est_verif"]):
        avisar(f"Rodadas anteriores em {e['nome']} "
               f"({i + 1} de {len(r['est_verif'])})…")
        try:
            rodadas[e["codigo"]] = ja.baixar_rodadas_anteriores(
                e["lat"], e["lon"], dias, fuso)
        except Exception as erro:
            falhas.append(f"{e['nome']}: {erro}")
    if not rodadas:
        raise RuntimeError("nenhuma estação devolveu rodadas anteriores.\n\n"
                           + "\n".join(falhas))
    avisar("Medindo o acerto por antecedência…")
    linhas = ja.verificar_antecedencias(
        r["obs_area"], r["medidas"], rodadas, r["est_verif"], r["alt"][0],
        dict(r["crit"]), r["pares"])
    return linhas, falhas


def csv_serie(serie, crit, com_chuva):
    dados, _ = _para_bytes(
        lambda c: ja.gravar_csv(c, serie, crit, com_chuva=com_chuva), ".csv")
    return dados


def zip_qgis(pontos, lat, lon, potencia, celulas, em_km, periodo):
    pasta = tempfile.mkdtemp()
    destino = os.path.join(pasta, f"qgis_{datetime.now():%Y%m%d_%H%M}")
    area = (lat, lon) if lat is not None else None
    ja.exportar_para_qgis(destino, pontos, area, potencia, celulas, em_km,
                          periodo)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for raiz, _, arquivos in os.walk(destino):
            for nome in arquivos:
                completo = os.path.join(raiz, nome)
                z.write(completo, os.path.relpath(completo, pasta))
    return buf.getvalue()


# ---------------------------------------------------------------------
# Aba 3 — previsão
# ---------------------------------------------------------------------

def resumo_previsao(r, crit, fuso):
    serie, janelas = r["serie"], r["janelas"]
    texto, n_validas, n_aptas = ja.resumir(serie, janelas, crit, r["avisos"])
    linhas = [ja.proxima_janela(janelas, fuso), r.get("correcao"),
              ja.linha_do_conjunto(r.get("conjunto"), serie, crit),
              ja.linha_do_metodo(r["metodo"], r.get("alt"),
                                 r.get("por_estacao", {}), serie),
              ja.texto_do_vento(crit), texto]
    aptas = [l for l in serie.values() if ja.e_apto(ja.classificar(l, crit))]
    d_apt, c_apt, *_ = ja.media_vetorial(aptas)
    if d_apt is not None:
        linhas.append("Vento previsto nas horas aptas: "
                      + ja.texto_direcao(d_apt, c_apt) + ".")
    return [t for t in linhas if t], n_validas, n_aptas


def figuras_previsao(r, crit, dias, fuso, lat, lon):
    serie, conjunto = r["serie"], r.get("conjunto")
    alvo = ("no ponto da área" if r["metodo"] == ja.METODO_PONTO
            else f"{len(r.get('por_estacao', {}))} estações interpoladas")
    corr = " · corrigida" if r.get("corrigida") else ""
    titulo = f"Previsão dos próximos {dias} dias · {alvo}{corr}"

    def calor(fig):
        if conjunto:
            ja.desenhar_mapa_calor_prob(fig, serie, crit, titulo, fuso)
        else:
            ja.desenhar_mapa_calor(fig, serie, crit, titulo)

    area = (lat, lon) if lat is not None else None
    return {
        "serie": figura_png(lambda f: ja.desenhar_serie(f, serie, crit, titulo)),
        "calor": figura_png(calor),
        "dir": figura_png(lambda f: ja.desenhar_direcao(
            f, serie, crit, None, area, f"{titulo} · direção do vento")),
    }


# ---------------------------------------------------------------------
# Aba 4 — relatório padrão
# ---------------------------------------------------------------------

def relatorio_padrao(alvo, ini, fim, fuso, dias, crit, crit_prev, lat, lon,
                     par_mapa, fonte, medidos, calibracao, corrigir,
                     antecedencias, campo, area_ha, origem, pontos_area, uf,
                     avisar=None):
    """Mesma sequência do botão "Gerar relatório PDF". Devolve
    (pdf em bytes, páginas, falhas, calibração nova ou None)."""
    avisar = avisar or (lambda t: None)
    if fonte == ja.FONTE_API:
        fonte = ja.FONTE_MODELO
    h = ja.montar_historico(alvo, ini, fim, fuso, crit, lat, lon, fonte,
                            ja.METODO_IDW, medidos, calibracao, avisar=avisar,
                            recuar=True)
    serie, janelas, usadas = h["serie"], h["janelas"], h["usadas"]
    falhas = list(h["falhas"])
    alt, origem_alt = h["alt"]
    cal_nova = h.get("calibracao")
    if cal_nova:
        calibracao = cal_nova

    avisar(f"previsão de {dias} dias no ponto, com o conjunto…")
    serie_prev, janelas_prev, conjunto = {}, [], None
    correcao_texto, corrigida = "", False
    try:
        crit_prev["limiar_p"] = ja.LIMIAR_P
        p = ja.montar_previsao(usadas or alvo, dias, fuso, crit_prev,
                               ja.METODO_PONTO, lat, lon, ja.MODO_ENSEMBLE,
                               calibracao, corrigir, avisar=avisar)
        serie_prev, janelas_prev = p["serie"], p["janelas"]
        conjunto, crit_prev = p.get("conjunto"), p["crit"]
        try:
            ja.arquivar_previsao(p, lat, lon, crit_prev, fuso)
        except Exception:
            pass
        correcao_texto, corrigida = p.get("correcao", ""), p["corrigida"]
        falhas += p["avisos"]
    except Exception as e:
        falhas.append(f"previsão: {e}")

    _, n_validas, n_aptas = ja.resumir(serie, janelas, crit)
    disp_dt = [l["disp_dt"] for l in serie.values()
               if l.get("disp_dt") is not None]
    disp_v = [l["disp_vento"] for l in serie.values()
              if l.get("disp_vento") is not None]
    dispersao = ""
    if disp_dt and disp_v:
        dispersao = (f"Discordância média entre as estações:  Delta T "
                     f"{ja._fmt(sum(disp_dt) / len(disp_dt))} °C e vento "
                     f"{ja._fmt(sum(disp_v) / len(disp_v))} km/h.")
    aptas = [l for l in serie.values() if ja.e_apto(ja.classificar(l, crit))]
    d_apt, c_apt, *_ = ja.media_vetorial(aptas)
    direcao_texto = ("Vento nas horas aptas:  " + ja.texto_direcao(d_apt, c_apt)
                     + "." if d_apt is not None else "")

    avisar("montando as páginas…")
    _, _, pct_cob = ja.cobertura(serie)
    conj_txt = ""
    if conjunto:
        conj_txt = (f"Previsão por conjunto de {conjunto['membros']} rodadas "
                    f"({', '.join(conjunto['modelos'])}).")
    rotulo_fonte = {
        ja.FONTE_MEDIDO: "estações do INMET (medido) e Open-Meteo (previsão)",
        ja.FONTE_CORRIGIDO: "Open-Meteo corrigido pela calibração local",
    }.get(h["fonte"], "Open-Meteo (modelos oficiais)")
    dados = {
        "lat": lat, "lon": lon, "ini": ini, "fim": fim, "fuso": fuso,
        "conjunto": conjunto, "conjunto_texto": conj_txt,
        "cobertura": pct_cob,
        "bulbo": ("Psicrométrico, com a pressão da altitude"
                  if crit.get("usar_psicrometrico") else "Stull (2011)"),
        "area_ha": area_ha, "origem": origem or "—", "proximas": usadas,
        "medidos_codigos": set(h.get("medidas") or {}),
        "pontos_area": pontos_area,
        "segs_uf": segs_uf(), "segs_mun": segs_mun(ufs_em_cena(uf, alvo)),
        "crit": crit, "crit_previsao": crit_prev,
        "serie": serie, "janelas": janelas,
        "serie_previsao": serie_prev, "janelas_previsao": janelas_prev,
        "previsao_corrigida": corrigida, "correcao_texto": correcao_texto,
        "dias_previsao": dias,
        "proxima": ja.proxima_janela(janelas_prev, fuso),
        "pontos_mapa": ja.resumo_por_estacao(h["series"], usadas),
        "potencia": par_mapa[0], "celulas": par_mapa[1], "em_km": par_mapa[2],
        "n_validas": n_validas, "n_aptas": n_aptas,
        "metodo": f"{len(usadas)} estações interpoladas por IDW (potência "
                  f"{par_mapa[0]:g}), com correção de altitude",
        "altitude": f"{alt:.0f} m ({origem_alt})",
        "dispersao": dispersao, "direcao_texto": direcao_texto,
        "texto_fonte": ja.texto_fonte(h), "campo": campo,
        "campo_texto": (ja.texto_campo(ja.comparar_campo(campo, serie, crit))
                        if campo else ""),
        "verif": h.get("verif"), "antecedencias": antecedencias,
        "fonte": rotulo_fonte,
    }
    pdf, paginas = _para_bytes(lambda c: ja.gerar_relatorio_pdf(c, dados),
                               ".pdf")
    return pdf, paginas, falhas, cal_nova


# ---------------------------------------------------------------------
# Aba 5 — voos
# ---------------------------------------------------------------------

def descrever_voos(voos, sem_hora, locais, nome_arquivo):
    ini = min(v["inicio"] for v in voos).date()
    fim = max(v["inicio"] for v in voos).date()
    ha = sum(v.get("area_ha") or 0 for v in voos)
    recado = [f"{nome_arquivo}: {len(voos)} voos · {ja._fmt(ha)} ha · "
              f"{ini:%d/%m/%Y} a {fim:%d/%m/%Y} · {len(locais)} local(is)."]
    for g in locais:
        recado.append(
            f"{g['nome']}: {len(g['voos'])} voos, {ja._fmt(g['area_ha'])} ha, "
            f"centro {g['lat']:.4f}, {g['lon']:.4f}, raio {g['raio_km']:.1f} km, "
            f"de {g['ini']:%d/%m} a {g['fim']:%d/%m}")
    estimadas = sum(1 for v in voos if v.get("altura_origem") == "estimada")
    if estimadas:
        recado.append(f"{estimadas} voos manuais sem altura gravada receberam "
                      "a mediana dos voos do mesmo dia.")
    if sem_hora:
        recado.append(f"{sem_hora} feições ficaram de fora por não terem data "
                      "e hora utilizáveis.")
    return recado


def analisar_voos(estacoes, locais, crit, fuso, n_estacoes, fonte, medidos,
                  calibracao, janela_h, limite_mm, avisar=None):
    """Um histórico por local, cada um com as suas estações."""
    avisar = avisar or (lambda t: None)
    avaliados, dias, falhas, fontes_usadas = [], [], [], set()
    hoje = datetime.now().date().isoformat()
    for g in locais:
        avisar(f"{g['nome']}: estações e série de {g['ini']:%d/%m} a "
               f"{g['fim']:%d/%m}…")
        prox = ja.estacoes_proximas(estacoes, g["lat"], g["lon"], n=n_estacoes)
        for cod in (medidos or {}):
            if fonte == ja.FONTE_MEDIDO and cod not in {e["codigo"] for e in prox}:
                e = next((x for x in estacoes if x["codigo"] == cod), None)
                if e:
                    d = ja.haversine(g["lat"], g["lon"], e["lat"], e["lon"])
                    if d <= 120:
                        prox.append(dict(e, distancia=d))
        ini = (g["ini"] - timedelta(days=1)).isoformat()
        fim = min((g["fim"] + timedelta(days=2)).isoformat(), hoje)

        crit_local = dict(crit)
        try:
            h = ja.montar_historico(prox, ini, fim, fuso, crit_local, g["lat"],
                                    g["lon"], fonte, ja.METODO_IDW, medidos,
                                    calibracao, avisar=avisar, recuar=True)
        except Exception as erro:
            falhas.append(f"{g['nome']}: {erro}")
            continue
        falhas += [f"{g['nome']}: {f}" for f in h["falhas"]]
        fontes_usadas.add(h["fonte"])
        serie = h["serie"]
        g.update(estacoes=h["usadas"], serie=serie, crit=crit_local,
                 fonte=h["fonte"])

        ponto = None
        avisar(f"{g['nome']}: chuva no talhão…")
        try:
            ponto = ja.baixar_open_meteo(g["lat"], g["lon"], ini, fim, fuso)
            coef = ja.combinar_coeficientes(
                ja.coeficientes_da_calibracao(calibracao), h["usadas"])
            if coef:
                ja.aplicar_calibracao(ponto, coef)
        except Exception as erro:
            falhas.append(f"{g['nome']}: chuva no talhão indisponível ({erro})")
        fontes = ja.fontes_de_chuva(h["series"], h["usadas"], ponto)
        g["fontes_chuva"] = fontes

        for v in g["voos"]:
            a = ja.avaliar_voo(v, serie, crit_local)
            a["local"] = g["nome"]
            a["piloto_aeronave"] = f'{a["piloto"]} / {a["aeronave"]}'
            ja.anotar_chuva(a, fontes, janela_h, limite_mm)
            avaliados.append(a)
        for data in sorted({v["inicio"].date() for v in g["voos"]}):
            dias.append({"data": data, "local": g["nome"], "serie": serie,
                         "fontes": fontes})

    if not avaliados:
        raise RuntimeError("nenhum voo pôde ser avaliado.\n\n"
                           + "\n".join(falhas))
    avaliados.sort(key=lambda v: v["inicio"])
    dias.sort(key=lambda d: d["data"])
    fonte_usada = " + ".join(sorted(fontes_usadas)) or fonte
    return avaliados, dias, falhas, fonte_usada


def resumo_voos(avaliados, dias, janela_h, limite_mm, fonte_usada,
                comparacao, falhas):
    """As linhas do resumo da aba 5 e o texto da direção do vento."""
    ha = sum(v.get("area_ha") or 0 for v in avaliados)
    contagem, area = {}, {}
    for v in avaliados:
        contagem[v["classe"]] = contagem.get(v["classe"], 0) + 1
        area[v["classe"]] = area.get(v["classe"], 0.0) + (v.get("area_ha") or 0)
    aptos = area.get("apta", 0.0)
    linhas = [
        f"{len(avaliados)} voos analisados · {ja._fmt(ha)} ha · "
        f"{ja._fmt(aptos)} ha ({100 * aptos / max(ha, 0.001):.0f}%) em "
        "condição apta",
        "Na hora do voo: " + " · ".join(
            f"{ja.NOME_CLASSE_VOO[k]} {contagem[k]} voos "
            f"({ja._fmt(area.get(k, 0))} ha)"
            for k in ja.ORDEM_CLASSE_VOO if k in contagem),
    ]
    lav, ha_lav = {}, {}
    for v in avaliados:
        k = v.get("lavagem", "sem_dado")
        lav[k] = lav.get(k, 0) + 1
        ha_lav[k] = ha_lav.get(k, 0.0) + (v.get("area_ha") or 0)
    linhas.append(
        f"Depois do voo (chuva nas {janela_h} h seguintes, lavagem a partir "
        f"de {ja._fmt(limite_mm)} mm): " + " · ".join(
            f"{ja.NOME_LAVAGEM[k]} {lav[k]} voos ({ja._fmt(ha_lav[k])} ha)"
            for k in ja.ORDEM_LAVAGEM if k in lav))
    molhados = []
    for r in ja.resumo_chuva_por_dia(avaliados, janela_h):
        maior = max(r["fontes"].items(), key=lambda kv: kv[1],
                    default=(None, 0.0))
        if maior[1] >= 0.2:
            molhados.append((r["dia"], maior))
    if molhados:
        linhas.append("Dias com chuva depois das aplicações: " + "; ".join(
            f"{dia:%d/%m} até {ja._fmt(mm)} mm em {janela_h} h ({fonte})"
            for dia, (fonte, mm) in molhados[:6]))
    fontes = sorted({f for d in dias for f in (d.get("fontes") or {})})
    if fontes:
        linhas.append("Fontes de chuva: " + "; ".join(fontes) + ".")
    linhas.append("Fonte do tempo na hora do voo: " + (fonte_usada or "—") + ".")
    d_v, c_v, *_ = ja.media_vetorial(
        [{"vento": v.get("vento"), "direcao": v.get("direcao")}
         for v in avaliados],
        pesos=[v.get("area_ha") or 0.01 for v in avaliados])
    direcao_texto = ""
    if d_v is not None:
        direcao_texto = ("Vento durante os voos (ponderado pela área):  "
                         + ja.texto_direcao(d_v, c_v) + ".")
        linhas.append(direcao_texto)
    if comparacao:
        linhas.append(ja.texto_comparacao(comparacao))
    if falhas:
        linhas.append("Avisos: " + "; ".join(falhas[:3])
                      + (f" (+{len(falhas) - 3})" if len(falhas) > 3 else ""))
    return linhas, direcao_texto


def csv_voos(avaliados, janela_h, fonte_usada):
    def br(v, casas=2):
        return "" if v is None else f"{v:.{casas}f}".replace(".", ",")

    saida = io.StringIO()
    saida.write("Voo;Data;Hora;Duracao_min;Local;Piloto;Aeronave;Modo;"
                "Area_ha;Litros;Taxa_L_ha;Altura_voo_m;Temp_C;UR_pct;"
                "DeltaT_C;Vento_kmh;Rajada_kmh;Chuva_mm;Inversao;"
                "Confianca_pct;Veredito;Motivo;DirVento_graus;VentoDe;"
                "DerivaPara;Altura_origem;Fonte;Chuva_durante_mm_h;"
                + "".join(f"Chuva_{h}h_depois_mm;" for h in ja.JANELAS_APOS)
                + "Fonte_da_maior_chuva;Chuva_por_fonte;Lavagem;"
                  "Na_area_problema\n")
    for v in avaliados:
        p = v.get("p_apta")
        ca = v.get("chuva_apos") or {}
        d = v.get("direcao")
        saida.write(";".join([
            str(v["id"]), v["inicio"].strftime("%d/%m/%Y"),
            v["inicio"].strftime("%H:%M:%S"),
            br((v["duracao_h"] or 0) * 60, 1),
            str(v.get("local", "")), str(v.get("piloto", "")),
            str(v.get("aeronave", "")), str(v.get("modo", "")),
            br(v.get("area_ha")), br(v.get("litros")), br(v.get("taxa")),
            br(v.get("altura_usada")), br(v.get("temp")), br(v.get("ur"), 0),
            br(v.get("delta_t")), br(v.get("vento")), br(v.get("rajada")),
            br(v.get("chuva")), str(v.get("inversao") or ""),
            "" if p is None else br(100 * p, 0),
            ja.NOME_CLASSE_VOO.get(v["classe"], v["classe"]),
            str(v.get("motivo") or ""),
            "" if d is None else f"{d:.0f}",
            "" if d is None else ja.rumo(d),
            "" if d is None else ja.rumo(d + 180),
            str(v.get("altura_origem") or ""), fonte_usada or "",
            br(v.get("chuva_durante")),
            *[br(ca.get(h)) for h in ja.JANELAS_APOS],
            str(v.get("chuva_apos_fonte") or ""),
            ja.texto_chuva_voo(v, janela_h).replace(";", " |"),
            ja.NOME_LAVAGEM.get(v.get("lavagem"), ""),
            "" if v.get("na_area_problema") is None
            else ("sim" if v["na_area_problema"] else "não"),
        ]) + "\n")
    return saida.getvalue().encode("utf-8-sig")


def html_mapa_voos(avaliados, janela_h, limite_mm, poligonos):
    dados, _ = _para_bytes(lambda c: ja.gerar_mapa_html(
        c, avaliados, f"{len(avaliados)} voos analisados", janela_h,
        limite_mm, poligonos), ".html")
    return dados


def geojson_voos(avaliados, janela_h, poligonos):
    dados, _ = _para_bytes(lambda c: ja.exportar_voos_geojson(
        c, avaliados, janela_h, poligonos), ".geojson")
    return dados


def pdf_voos(avaliados, locais, dias, crit, agrupar, fonte_usada,
             direcao_texto, janela_h, limite_mm, poligonos, comparacao):
    por, rotulo = ja.CAMPO_AGRUPAR[agrupar]
    disp = ""
    primeiro = next((g for g in locais if g.get("crit")), None)
    if primeiro and primeiro["crit"].get("margem_dt"):
        c = primeiro["crit"]
        disp = (f"Incerteza de representatividade adotada: "
                f"±{ja._fmt(c['margem_dt'])} °C no Delta T e "
                f"±{ja._fmt(c['margem_vento'])} km/h no vento.")
    dados = {
        "voos": avaliados, "locais": locais, "dias": dias, "crit": crit,
        "ini": min(v["inicio"] for v in avaliados).strftime("%d/%m/%Y"),
        "fim": max(v["inicio"] for v in avaliados).strftime("%d/%m/%Y"),
        "por": por, "rotulo_por": rotulo,
        "com_piloto": por in ("piloto", "piloto_aeronave"),
        "fonte": {ja.FONTE_MEDIDO: "estações do INMET (medido)",
                  ja.FONTE_CORRIGIDO: "Open-Meteo corrigido pela calibração "
                                      "local"}.get(fonte_usada,
                                                   "Open-Meteo (reanálise)"),
        "direcao_texto": direcao_texto, "dispersao": disp,
        "janela_h": janela_h, "limite_mm": limite_mm,
        "poligonos": poligonos, "comparacao": comparacao,
        "texto_area": ja.texto_comparacao(comparacao) if comparacao else "",
    }
    pdf, paginas = _para_bytes(lambda c: ja.gerar_relatorio_voos_pdf(c, dados),
                               ".pdf")
    return pdf, paginas


def calibracao_json(cal):
    """O mesmo formato do calibracao.json que o desktop grava."""
    cal = dict(cal or {"versao": 2, "estacoes": {}})
    cal["atualizada"] = datetime.now().isoformat(timespec="minutes")
    return json.dumps(cal, ensure_ascii=False).encode("utf-8")
