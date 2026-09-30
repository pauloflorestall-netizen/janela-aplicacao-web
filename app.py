"""
Janela de Aplicação — versão web (Streamlit)
============================================

As mesmas cinco abas do programa de desktop, no navegador. Toda a conta
continua no janela_aplicacao.py: este arquivo só desenha a tela.

Para rodar no seu computador:
    pip install -r requirements.txt
    streamlit run app.py
"""

import os
from datetime import datetime, timedelta, timezone

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Janela de Aplicação · Geo Rubi",
                   page_icon="🌬️", layout="wide")

import nucleo
import servicos as sv

ja = sv.ja

# Endereço do seu hub. Preencha para aparecer o link "voltar" no topo.
URL_HUB = ""

PASTA = os.path.dirname(os.path.abspath(__file__))
PASTA_EXEMPLO = os.path.join(PASTA, "exemplo")
FUSOS = [-2, -3, -4, -5]

ss = st.session_state


# =====================================================================
# Estado inicial
# =====================================================================

def hoje(fuso=-3):
    """Data local. O servidor roda em UTC; sem isso, à noite, 'hoje'
    já seria amanhã."""
    return (datetime.now(timezone.utc) + timedelta(hours=fuso)).date()


CRITERIO_PADRAO = {"dtmin": 2.0, "dtmax": 8.0, "vmin": 3.0, "vmax": 15.0,
                   "rajada": 20.0, "rainfast": 2, "altura": 2.0, "z0": 0.03,
                   "inversao": ja.OPCOES_INVERSAO[0],
                   "bulbo": ja.OPCOES_BULBO[0], "chuva": 0.2}


def padroes():
    d = {
        # aba 1
        "lat": None, "lon": None, "area_ha": None, "origem": None,
        "pontos_area": None, "lat_txt": "", "lon_txt": "", "n_est": 4,
        "uf": None,
        # dados carregados
        "medidos": {}, "pendentes": [], "campo": [],
        "calibracao": ja.carregar_calibracao(),
        # aba 2
        "s_ini": hoje() - timedelta(days=14), "s_fim": hoje(), "s_fuso": -3,
        "s_fonte": ja.FONTE_MODELO, "s_metodo": ja.METODO_IDW, "s_token": "",
        "s_vista": "Janelas", "m_potencia": 2.0, "m_celulas": 140,
        "m_metrica": ja.METRICA_KM, "hist": None,
        # aba 3
        "p_dias": 7, "p_fuso": -3, "p_metodo": ja.METODO_PONTO,
        "p_conjunto": ja.MODO_ENSEMBLE, "p_correcao": ja.CORRECAO_SIM,
        "p_vista": "Janelas", "prev": None,
        # aba 4
        "r_ini": hoje() - timedelta(days=14), "r_fim": hoje(), "r_dias": 7,
        "r_fuso": -3, "rel": None,
        # aba 5
        "v_agrupar": ja.AGRUPAR_VOOS[0], "v_n": 4, "v_fuso": -3,
        "v_fonte": ja.FONTE_MODELO, "v_lav_mm": 2.0, "v_lav_h": 6,
        "v_vista": "Voos", "v_colorir": ja.MODOS_COR_MAPA[0],
        "v_dia_mapa": "todos", "v_dia": None, "voos": None, "voos_res": None,
        "poligonos": [], "recados": {},
    }
    for p in ("s_", "p_"):
        for k, v in CRITERIO_PADRAO.items():
            d[p + k] = v
    return d


# Reatribuir a cada rodada impede que o Streamlit apague o valor de um
# controle que ficou escondido (por exemplo, os parâmetros dos mapas).
for _k, _v in padroes().items():
    ss[_k] = ss[_k] if _k in ss else _v


def recado(aba, tipo, texto):
    ss.recados.setdefault(aba, []).append((tipo, texto))


def mostrar_recados(aba):
    for tipo, texto in ss.recados.pop(aba, []):
        getattr(st, {"erro": "error", "aviso": "warning",
                     "ok": "success"}.get(tipo, "info"))(texto)


# =====================================================================
# Estações
# =====================================================================

@st.cache_data(show_spinner="Carregando as estações do INMET…")
def estacoes():
    bruto, _ = ja.carregar_estacoes()
    return ja.normalizar(bruto)


try:
    ESTACOES = estacoes()
except Exception as e:
    ESTACOES = []
    st.error(f"Não consegui carregar a lista de estações: {e}")


def rotulos_uf():
    rot = {"Brasil inteiro": ""}
    for uf in sorted({e["uf"] for e in ESTACOES if e["uf"]}):
        n = sum(1 for e in ESTACOES if e["uf"] == uf and e["operante"])
        rot[f"{ja.UF_NOMES.get(uf, uf)} ({n} operantes)"] = uf
    return rot


UFS = rotulos_uf()
if ss.uf not in UFS:
    ss.uf = next((r for r, s in UFS.items() if s == ja.UF_INICIAL),
                 "Brasil inteiro")

ss.proximas = (ja.estacoes_proximas(ESTACOES, ss.lat, ss.lon, n=int(ss.n_est))
               if ss.lat is not None else [])
TEM_AREA = ss.lat is not None


# =====================================================================
# Ações (callbacks rodam antes de a tela ser redesenhada)
# =====================================================================

def definir_area(lat, lon, area_ha=None, origem="", pontos=None):
    ss.lat, ss.lon, ss.area_ha, ss.origem = lat, lon, area_ha, origem
    ss.pontos_area = pontos
    ss.lat_txt, ss.lon_txt = f"{lat:.6f}", f"{lon:.6f}"
    prox = ja.estacoes_proximas(ESTACOES, lat, lon, n=int(ss.n_est))
    if prox:
        ss.uf = next((r for r, s in UFS.items() if s == prox[0]["uf"]), ss.uf)


def cb_coordenada():
    try:
        lat = float(ss.lat_txt.replace(",", "."))
        lon = float(ss.lon_txt.replace(",", "."))
    except ValueError:
        recado("area", "erro", "Preencha latitude e longitude com números. "
                               "Exemplo: -12,43 e -38,642.")
        return
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        recado("area", "erro", "Coordenada fora do mundo. No Brasil, latitude "
                               "e longitude são negativas.")
        return
    definir_area(lat, lon, None, "coordenada digitada")


def cb_talhao():
    arq = ss.get("up_talhao")
    if arq is None:
        return
    try:
        nome, pts, quantas = ja.ler_area(sv.salvar_upload(arq))
    except Exception as e:
        recado("area", "erro", f"Não consegui ler o arquivo: {e}")
        return
    lat, lon = ja.centroide(pts)
    ha = ja.area_hectares(pts) if len(pts) >= 3 else None
    origem = f"arquivo {arq.name}"
    if quantas > 1:
        origem += f" ({quantas} feições, usando a primeira: {nome})"
    definir_area(lat, lon, ha, origem, pts)


def cb_limpar():
    ss.lat = ss.lon = ss.area_ha = ss.origem = ss.pontos_area = None
    ss.lat_txt = ss.lon_txt = ""


def ler_tabelas(caminhos):
    """Lê as tabelas do INMET. As sem código vão para a associação."""
    fuso = int(ss.s_fuso)
    tabelas, erros = [], []
    for c in caminhos:
        try:
            tabelas.append(ja.ler_tabela_inmet(c, fuso))
        except Exception as e:
            erros.append(f"{os.path.basename(c)}: {e}")
    if erros:
        recado("series", "aviso", "Não li: " + "; ".join(erros))
    if not tabelas:
        return
    estacoes_area = list(ss.proximas)
    por_codigo = {e["codigo"]: e for e in ESTACOES}
    for t in tabelas:
        e = por_codigo.get(t.get("codigo") or "")
        if e and e["codigo"] not in {x["codigo"] for x in estacoes_area}:
            estacoes_area.append(e)
    sugestao = ja.sugerir_associacao(tabelas, estacoes_area)
    prontas = [(t, c) for t, c in sugestao if t.get("codigo")]
    pendentes = [(t, c) for t, c in sugestao if not t.get("codigo")]
    guardar_tabelas(prontas, estacoes_area)
    if pendentes:
        if not estacoes_area:
            recado("series", "aviso",
                   "As tabelas do portal não trazem o código da estação. "
                   "Marque a área na aba 1 para eu sugerir a estação de cada "
                   "arquivo, ou ponha o código no nome (ex.: A413.csv).")
            return
        ss.pendentes = [(t, c, estacoes_area) for t, c in pendentes]


def guardar_tabelas(pares, estacoes_area):
    nomes = {e["codigo"]: e["nome"] for e in estacoes_area}
    novas = []
    for tab, cod in pares:
        if not cod:
            continue
        tab["codigo"] = cod
        tab["nome"] = tab.get("nome") or nomes.get(cod, cod)
        ss.medidos[cod] = tab
        novas.append(ja.descrever_tabela(tab))
    if not novas:
        return
    per = sv.periodo_das_tabelas(ss.medidos)
    if per and not (per[0] <= ss.s_ini <= ss.s_fim <= per[1]):
        ss.s_ini, ss.s_fim = per
        novas.append(f"O período passou para {per[0]:%d/%m/%Y} a "
                     f"{per[1]:%d/%m/%Y}, o das tabelas.")
    ss.s_fonte = ss.v_fonte = ja.FONTE_MEDIDO
    recado("series", "ok", "Tabelas carregadas — a fonte passou para "
                           "“Medido”.\n\n" + "\n\n".join(novas))


def cb_tabelas():
    arquivos = ss.get("up_tabelas") or []
    ler_tabelas([sv.salvar_upload(a) for a in arquivos])


def cb_associar():
    pares = []
    estacoes_area = []
    for i, (tab, _, est) in enumerate(ss.pendentes):
        escolha = ss.get(f"assoc_{i}")
        cod = escolha.split(" ")[0] if escolha and escolha != "Ignorar" else None
        pares.append((tab, cod))
        estacoes_area = est
    ss.pendentes = []
    guardar_tabelas(pares, estacoes_area)


def cb_campo():
    arq = ss.get("up_campo")
    if arq is None:
        return
    try:
        ss.campo = ja.ler_medicao_campo(sv.salvar_upload(arq))
        recado("series", "ok", f"{len(ss.campo)} leitura(s) de campo "
                               "carregada(s). Entram no próximo “Baixar e "
                               "analisar” e no relatório.")
    except Exception as e:
        recado("series", "erro", f"Não consegui ler a medição de campo: {e}")


def ultimos_dias(prefixo, dias):
    def cb():
        ss[prefixo + "ini"] = hoje() - timedelta(days=dias - 1)
        ss[prefixo + "fim"] = hoje()
    return cb


def ler_voos(caminho, nome):
    voos, sem_hora = ja.ler_operacoes(caminho, int(ss.v_fuso))
    locais = ja.agrupar_locais(voos)
    ss.voos = {"voos": voos, "locais": locais, "nome": nome,
               "recado": sv.descrever_voos(voos, sem_hora, locais, nome)}
    ss.voos_res = None


def cb_voos():
    arq = ss.get("up_voos")
    if arq is None:
        return
    try:
        ler_voos(sv.salvar_upload(arq), arq.name)
    except Exception as e:
        recado("voos", "erro", f"Não consegui ler o arquivo de voos: {e}")


def cb_problema():
    arq = ss.get("up_problema")
    if arq is None:
        return
    try:
        ss.poligonos = ja.ler_poligonos(sv.salvar_upload(arq))
    except Exception as e:
        recado("voos", "erro", f"Não consegui ler o polígono: {e}")
        return
    ha = sum(ja.area_hectares(p) or 0 for _, p in ss.poligonos)
    recado("voos", "ok", f"Área com problema: {len(ss.poligonos)} polígono(s), "
                         f"{ja._fmt(ha)} ha.")
    if ss.voos_res:
        atualizar_resumo_voos()


def cb_calibracao():
    arq = ss.get("up_cal")
    if arq is None:
        return
    try:
        import json
        cal = json.loads(arq.getvalue().decode("utf-8"))
        if not isinstance(cal, dict) or "estacoes" not in cal:
            raise ValueError("não parece um calibracao.json")
        ss.calibracao = cal
        recado("lateral", "ok", f"Calibração carregada: "
                                f"{len(cal['estacoes'])} estação(ões).")
    except Exception as e:
        recado("lateral", "erro", f"Arquivo inválido: {e}")


def cb_exemplo():
    """O mesmo teste do LEIA-ME, com os arquivos da pasta exemplo."""
    definir_area(-12.430, -38.642, None, "exemplo do LEIA-ME")
    ss.proximas = ja.estacoes_proximas(ESTACOES, ss.lat, ss.lon,
                                       n=int(ss.n_est))
    csvs = sorted(os.path.join(PASTA_EXEMPLO, f)
                  for f in os.listdir(PASTA_EXEMPLO) if f.endswith(".csv"))
    ler_tabelas(csvs)
    geo = [f for f in os.listdir(PASTA_EXEMPLO) if f.endswith(".geojson")]
    if geo:
        ler_voos(os.path.join(PASTA_EXEMPLO, geo[0]), geo[0])
    recado("lateral", "ok", "Exemplo carregado: área, três tabelas do INMET "
                            "e o arquivo de voos. Siga pelas abas 2 a 5.")


# =====================================================================
# Pedaços de tela usados em mais de uma aba
# =====================================================================

def controles_criterio(p, com_chuva=False):
    c = st.columns(4)
    c[0].number_input("Delta T mín (°C)", key=p + "dtmin", step=0.5,
                      format="%.1f")
    c[1].number_input("Delta T máx (°C)", key=p + "dtmax", step=0.5,
                      format="%.1f")
    c[2].number_input("Vento mín (km/h)", key=p + "vmin", step=0.5,
                      format="%.1f")
    c[3].number_input("Vento máx (km/h)", key=p + "vmax", step=0.5,
                      format="%.1f")
    c = st.columns(4)
    c[0].number_input("Rajada máx (km/h, 0 desliga)", key=p + "rajada",
                      min_value=0.0, step=1.0, format="%.0f",
                      help="Pico da hora, na altura de aplicação.")
    c[1].number_input("Sem chuva por (h após aplicar)", key=p + "rainfast",
                      min_value=0, step=1)
    c[2].number_input("Vento a (m, altura da barra)", key=p + "altura",
                      min_value=0.05, max_value=10.0, step=0.5, format="%.2f")
    c[3].number_input("Rugosidade z0 (m)", key=p + "z0", min_value=0.001,
                      max_value=0.99, step=0.01, format="%.3f",
                      help="0,005 m solo nu · 0,03 m cultura rasteira · "
                           "0,3 m cultura alta")
    c = st.columns(3)
    c[0].selectbox("Inversão térmica", ja.OPCOES_INVERSAO, key=p + "inversao")
    c[1].selectbox("Bulbo úmido", ja.OPCOES_BULBO, key=p + "bulbo")
    if com_chuva:
        c[2].number_input("Descartar chuva acima de (mm/h)", key=p + "chuva",
                          min_value=0.0, step=0.1, format="%.1f")


def ler_crit(p, chuva_max=None, conjunto=False):
    return sv.criterios(
        ss[p + "dtmin"], ss[p + "dtmax"], ss[p + "vmin"], ss[p + "vmax"],
        str(ss[p + "rajada"]), str(ss[p + "rainfast"]), str(ss[p + "altura"]),
        str(ss[p + "z0"]), ss[p + "inversao"], ss[p + "bulbo"],
        ss.p_chuva if chuva_max is None else chuva_max, conjunto)


def figura(chave, desenhar, **kw):
    """PNG guardado por chave: redesenha só quando algo muda."""
    cache = ss.setdefault("_figs", {})
    if chave not in cache:
        if len(cache) > 40:
            cache.clear()
        cache[chave] = sv.figura_png(desenhar, **kw)
    return cache[chave]


def linhas_resumo(linhas):
    st.markdown("\n\n".join(t.replace("\n", "  \n") for t in linhas))


def pedir_area():
    st.info("Defina a área na aba **1. Área e estações** primeiro.")


# =====================================================================
# Cabeçalho e barra lateral
# =====================================================================

voltar = (f'<a href="{URL_HUB}" style="color:#e84040;text-decoration:none">'
          '← Geo Rubi</a> · ' if URL_HUB else "")
st.markdown(
    f'<p style="font-family:monospace;font-size:0.75rem;letter-spacing:0.12em;'
    f'color:#e84040;margin:0">{voltar}GEO RUBI · METEOROLOGIA DE APLICAÇÃO</p>',
    unsafe_allow_html=True)
st.title("Janela de Aplicação")
st.caption("Delta T, vento e rajada com as estações automáticas do INMET e a "
           "previsão do Open-Meteo · versão " + ja.VERSAO.split(" ")[0])

with st.sidebar:
    st.subheader("Teste rápido")
    st.button("Carregar o exemplo", on_click=cb_exemplo,
              help="Área perto de Feira de Santana, três tabelas do INMET e "
                   "180 voos de dron, como no LEIA-ME.")
    mostrar_recados("lateral")

    st.subheader("Calibração local")
    n_cal = len((ss.calibracao or {}).get("estacoes", {}))
    st.caption(f"{n_cal} estação(ões) na calibração desta sessão. O site não "
               "guarda arquivos entre visitas: baixe o calibracao.json depois "
               "de carregar tabelas medidas e envie de novo na próxima vez.")
    st.download_button("Baixar calibracao.json",
                       sv.calibracao_json(ss.calibracao),
                       file_name="calibracao.json", mime="application/json")
    st.file_uploader("Enviar calibracao.json", type=["json"], key="up_cal",
                     on_change=cb_calibracao)

    st.subheader("Estações")
    st.caption(f"{len(ESTACOES)} estações na lista.")
    if st.button("Atualizar lista do INMET"):
        atualizou = False
        try:
            ja.carregar_estacoes(forcar_download=True)
            atualizou = True
        except Exception as e:
            st.error(f"O INMET não respondeu: {e}")
        if atualizou:
            st.cache_data.clear()
            st.rerun()

aba1, aba2, aba3, aba4, aba5 = st.tabs([
    "1. Área e estações", "2. Séries e Delta T", "3. Previsão",
    "4. Relatório", "5. Voos realizados"])


# =====================================================================
# ABA 1 — Área e estações
# =====================================================================

with aba1:
    mostrar_recados("area")
    st.markdown("Marque a área digitando a coordenada ou enviando o arquivo "
                "do talhão.")
    c = st.columns([2, 2, 1.4])
    c[0].text_input("Latitude", key="lat_txt", placeholder="-12,430")
    c[1].text_input("Longitude", key="lon_txt", placeholder="-38,642")
    c[2].markdown("&nbsp;")
    c[2].button("Usar coordenada", type="primary", on_click=cb_coordenada)

    c = st.columns([3, 1])
    c[0].file_uploader("Arquivo do talhão (KML, KMZ, GeoJSON ou shapefile "
                       "em .zip)", type=["kml", "kmz", "geojson", "json", "zip"],
                       key="up_talhao")
    c[1].markdown("&nbsp;")
    c[1].button("Usar arquivo", on_click=cb_talhao)

    c = st.columns([3, 1, 1])
    c[0].selectbox("Estado no mapa", list(UFS), key="uf")
    c[1].selectbox("Estações", [3, 4, 5], key="n_est")
    c[2].markdown("&nbsp;")
    c[2].button("Limpar área", on_click=cb_limpar)

    if TEM_AREA:
        txt = f"**Área:** {ss.lat:.5f}, {ss.lon:.5f}"
        if ss.area_ha:
            txt += f" · {ja._fmt(ss.area_ha)} ha"
        txt += f" · {ss.origem} · {len(ss.proximas)} estações escolhidas"
        st.markdown(txt)

    uf_sigla = UFS.get(ss.uf, "")
    png = figura(("area", ss.lat, ss.lon, uf_sigla, int(ss.n_est),
                  len(ss.pontos_area or [])),
                 lambda f: sv.desenhar_mapa_area(
                     f, ESTACOES, uf_sigla, ss.proximas, ss.lat, ss.lon,
                     ss.pontos_area), largura=9, altura=6)
    st.image(png)

    if ss.proximas:
        st.subheader("Estações mais próximas")
        st.dataframe(pd.DataFrame(sv.tabela_estacoes(ss.proximas)),
                     hide_index=True)
        aviso = sv.aviso_estacoes(ss.proximas)
        if aviso:
            st.warning(aviso)
        st.success("Próxima etapa: aba **2. Séries e Delta T**.")


# =====================================================================
# ABA 2 — Séries e Delta T
# =====================================================================

with aba2:
    mostrar_recados("series")
    if not TEM_AREA:
        pedir_area()

    c = st.columns([2, 2, 1])
    c[0].date_input("De", key="s_ini", format="DD/MM/YYYY")
    c[1].date_input("Até", key="s_fim", format="DD/MM/YYYY")
    c[2].selectbox("Fuso", FUSOS, key="s_fuso")
    c = st.columns(3)
    for i, d in enumerate((7, 15, 30)):
        c[i].button(f"Últimos {d} dias", key=f"s_atalho{d}",
                    on_click=ultimos_dias("s_", d))

    with st.expander("Critérios", expanded=False):
        controles_criterio("s_")
        st.caption("O limite de chuva por hora é o da aba 3.")

    c = st.columns(2)
    c[0].selectbox("Fonte", ja.FONTES_HISTORICO, key="s_fonte")
    c[1].selectbox("Método", (ja.METODO_IDW, ja.METODO_PONTO), key="s_metodo")
    if ss.s_fonte == ja.FONTE_API:
        st.text_input("Token INMET", key="s_token", type="password")

    with st.expander(f"Tabelas medidas do INMET ({len(ss.medidos)} "
                     "carregada(s))", expanded=not ss.medidos):
        if ss.proximas:
            st.markdown("O portal pede a verificação “não sou robô”, então o "
                        "download é manual. Gere a tabela de cada estação, "
                        "clique em Baixar CSV e salve com o código no nome "
                        "(ex.: A413.csv):")
            st.markdown("  \n".join(
                f"[{p['codigo']} · {p['nome']}]({u})" for p, u in
                zip(ss.proximas, ja.urls_tabelas_inmet(ss.proximas))))
        st.file_uploader("Tabelas horárias (CSV)", type=["csv"],
                         accept_multiple_files=True, key="up_tabelas")
        st.button("Carregar tabelas", on_click=cb_tabelas)
        for t in ss.medidos.values():
            st.caption(ja.descrever_tabela(t))
        if ss.medidos and st.button("Esquecer as tabelas"):
            ss.medidos = {}
            st.rerun()

    if ss.pendentes:
        st.warning("Estas tabelas não trazem o código da estação. Confirme a "
                   "qual estação pertence cada uma:")
        for i, (tab, sug, est) in enumerate(ss.pendentes):
            opcoes = [f'{e["codigo"]} · {e["nome"]}' for e in est] + ["Ignorar"]
            padrao = next((j for j, e in enumerate(est) if e["codigo"] == sug),
                          len(opcoes) - 1)
            st.selectbox(ja.descrever_tabela(tab), opcoes, index=padrao,
                         key=f"assoc_{i}")
        st.button("Confirmar estações", type="primary", on_click=cb_associar)

    with st.expander("Medição de campo (opcional)"):
        st.markdown("Leituras feitas no talhão (termo-higrômetro, anemômetro "
                    "de mão). Poucas bastam para dizer se a estimativa está "
                    "deslocada naquele lugar.")
        st.download_button("Baixar modelo de planilha",
                           ja.MODELO_CAMPO.encode("utf-8-sig"),
                           file_name="modelo_medicao_campo.csv",
                           mime="text/csv")
        st.file_uploader("Planilha de campo (CSV)", type=["csv", "txt"],
                         key="up_campo", on_change=cb_campo)
        if ss.campo:
            st.caption(f"{len(ss.campo)} leitura(s) carregada(s).")

    if st.button("Baixar e analisar", type="primary", disabled=not TEM_AREA):
        try:
            crit = ler_crit("s_")
            if ss.s_fim < ss.s_ini:
                raise ValueError("A data final é anterior à inicial.")
        except ValueError as e:
            st.error(str(e))
            crit = None
        if crit:
            with st.status("Baixando…", expanded=False) as s:
                try:
                    r = ja.montar_historico(
                        list(ss.proximas), ss.s_ini.isoformat(),
                        ss.s_fim.isoformat(), int(ss.s_fuso), crit, ss.lat,
                        ss.lon, ss.s_fonte, ss.s_metodo, dict(ss.medidos),
                        ss.calibracao, ss.s_token.strip() or None,
                        avisar=lambda t: s.update(label=t))
                    r["crit"], r["area"] = crit, (ss.lat, ss.lon)
                    if r.get("calibracao"):
                        ss.calibracao = r["calibracao"]
                    s.update(label="Montando os gráficos…")
                    linhas, metodo, nv, na = sv.resumo_historico(
                        r, crit, ss.lat, ss.lon, ss.campo)
                    periodo = f"{ss.s_ini:%d/%m/%Y} a {ss.s_fim:%d/%m/%Y}"
                    ss.hist = {
                        "r": r, "crit": crit, "linhas": linhas,
                        "metodo": metodo, "periodo": periodo,
                        "figs": sv.figuras_historico(r, crit, metodo, periodo,
                                                     ss.lat, ss.lon, ss.campo),
                        "csv": sv.csv_serie(r["serie"], crit, any(
                            l.get("chuva") is not None
                            for l in r["serie"].values())),
                        "id": datetime.now().timestamp(),
                        "antecedencias": None,
                    }
                    s.update(label=f"{na} horas aptas de {nv} · "
                                   f"{len(r['janelas'])} janelas",
                             state="complete")
                except Exception as e:
                    s.update(label="Falhou", state="error")
                    st.error(f"Falha ao baixar: {e}")

    h = ss.hist
    if h:
        r, crit = h["r"], h["crit"]
        st.subheader("Resumo")
        linhas_resumo(h["linhas"])
        st.download_button("Exportar série (CSV)", h["csv"],
                           file_name=f"janelas_{datetime.now():%Y%m%d_%H%M}.csv",
                           mime="text/csv")
        vista = st.radio("Ver", ["Janelas", "Gráfico", "Mapa de calor", "Mapas",
                                 "Direção do vento", "Modelo × medido"],
                         key="s_vista", horizontal=True,
                         label_visibility="collapsed")
        pontos = sv.pontos_das_estacoes(r, ss.proximas)

        def mapas():
            chave = ("mapas", h["id"], ss.m_potencia, ss.m_celulas, ss.m_metrica)
            cache = ss.setdefault("_figs", {})
            if chave not in cache:
                cache[chave] = sv.figuras_mapas(
                    r, crit, pontos, ss.lat, ss.lon, float(ss.m_potencia),
                    int(ss.m_celulas), ss.m_metrica.startswith("km"),
                    h["periodo"])
            return cache[chave]

        if vista == "Janelas":
            if r["janelas"]:
                st.dataframe(pd.DataFrame(sv.tabela_janelas(r["janelas"])),
                             hide_index=True)
            else:
                st.info("Nenhuma janela no período com os critérios atuais.")
        elif vista == "Gráfico":
            st.image(h["figs"]["serie"])
        elif vista == "Mapa de calor":
            st.image(h["figs"]["calor"])
        elif vista == "Mapas":
            c = st.columns(3)
            c[0].selectbox("Potência do IDW", [1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0],
                           key="m_potencia")
            c[1].selectbox("Células", [60, 100, 140, 200, 300], key="m_celulas")
            c[2].selectbox("Distância em", [ja.METRICA_KM, ja.METRICA_GRAU],
                           key="m_metrica")
            st.image(mapas()["mapas"])
            if len(pontos) >= 2:
                figs_mapa = mapas()
                if "zip" not in figs_mapa:
                    figs_mapa["zip"] = sv.zip_qgis(
                        pontos, ss.lat, ss.lon, float(ss.m_potencia),
                        int(ss.m_celulas), ss.m_metrica.startswith("km"),
                        h["periodo"])
                st.download_button(
                    "Exportar para o QGIS (.zip)", figs_mapa["zip"],
                    file_name=f"qgis_{datetime.now():%Y%m%d_%H%M}.zip",
                    mime="application/zip")
            else:
                st.caption("Os mapas precisam de pelo menos duas estações "
                           "(método “Interpolar estações”).")
        elif vista == "Direção do vento":
            st.image(h["figs"].get("dir") or mapas()["dir"])
        else:
            st.image(h["figs"]["verif"])
            pode = bool(r.get("verif") and r.get("obs_area"))
            st.caption("Busca o que as rodadas de 1 a 7 dias antes previam para "
                       "as horas medidas e mede o acerto de cada antecedência. "
                       "Precisa de tabelas medidas.")
            if st.button("Verificar previsões passadas", disabled=not pode):
                verificou = False
                with st.status("Buscando rodadas…") as s:
                    try:
                        linhas, falhas = sv.verificar_passadas(
                            r, int(ss.s_fuso), avisar=lambda t: s.update(label=t))
                        h["antecedencias"] = linhas
                        h["figs"]["verif"] = sv.figura_png(
                            lambda f: ja.desenhar_verificacao(
                                f, r.get("verif"), linhas,
                                "Modelo (Open-Meteo) × medido nas estações, "
                                "na área"))
                        s.update(label="Pronto", state="complete")
                        if falhas:
                            recado("series", "aviso",
                                   "Avisos: " + "; ".join(falhas))
                        verificou = True
                    except Exception as e:
                        s.update(label="Falhou", state="error")
                        st.error(str(e))
                if verificou:
                    st.rerun()


# =====================================================================
# ABA 3 — Previsão
# =====================================================================

with aba3:
    mostrar_recados("previsao")
    if not TEM_AREA:
        pedir_area()
    c = st.columns([1, 1, 2])
    c[0].selectbox("Próximos dias", [1, 2, 3, 4, 5, 6, 7], key="p_dias")
    c[1].selectbox("Fuso", FUSOS, key="p_fuso")
    c[2].selectbox("Método", (ja.METODO_PONTO, ja.METODO_IDW), key="p_metodo")
    c = st.columns(2)
    c[0].selectbox("Saída", (ja.MODO_ENSEMBLE, ja.MODO_UNICO), key="p_conjunto")
    c[1].selectbox("Correção", (ja.CORRECAO_SIM, ja.CORRECAO_NAO),
                   key="p_correcao")
    with st.expander("Critérios", expanded=False):
        controles_criterio("p_", com_chuva=True)

    if st.button("Buscar previsão", type="primary", disabled=not TEM_AREA):
        try:
            crit = ler_crit("p_", conjunto=ss.p_conjunto == ja.MODO_ENSEMBLE)
        except ValueError as e:
            st.error(str(e))
            crit = None
        if crit:
            with st.status("Buscando a previsão…", expanded=False) as s:
                try:
                    fuso = int(ss.p_fuso)
                    r = ja.montar_previsao(
                        list(ss.proximas), int(ss.p_dias), fuso, crit,
                        ss.p_metodo, ss.lat, ss.lon, ss.p_conjunto,
                        ss.calibracao, ss.p_correcao == ja.CORRECAO_SIM,
                        avisar=lambda t: s.update(label=t))
                    try:
                        ja.arquivar_previsao(r, ss.lat, ss.lon, r["crit"], fuso)
                    except Exception:
                        pass
                    s.update(label="Montando os gráficos…")
                    linhas, nv, na = sv.resumo_previsao(r, r["crit"], fuso)
                    ss.prev = {
                        "r": r, "linhas": linhas,
                        "figs": sv.figuras_previsao(r, r["crit"],
                                                    int(ss.p_dias), fuso,
                                                    ss.lat, ss.lon),
                        "csv": sv.csv_serie(r["serie"], r["crit"], True),
                    }
                    s.update(label=f"{na} horas aptas de {nv} · "
                                   f"{len(r['janelas'])} janelas",
                             state="complete")
                except Exception as e:
                    s.update(label="Falhou", state="error")
                    st.error(f"Não consegui a previsão: {e}")

    pv = ss.prev
    if pv:
        r = pv["r"]
        st.subheader("Resumo")
        linhas_resumo(pv["linhas"])
        st.caption("Previsão é estimativa: confirme no dia, principalmente o "
                   "vento.")
        st.download_button("Exportar previsão (CSV)", pv["csv"],
                           file_name=f"previsao_{datetime.now():%Y%m%d_%H%M}.csv",
                           mime="text/csv")
        vista = st.radio("Ver", ["Janelas", "Gráfico", "Mapa de calor",
                                 "Direção do vento"], key="p_vista",
                         horizontal=True, label_visibility="collapsed")
        if vista == "Janelas":
            if r["janelas"]:
                st.dataframe(pd.DataFrame(sv.tabela_janelas(
                    r["janelas"], True, bool(r.get("conjunto")))),
                    hide_index=True)
            else:
                st.info("Nenhuma janela nos próximos dias com os critérios "
                        "atuais.")
        else:
            st.image(pv["figs"][{"Gráfico": "serie", "Mapa de calor": "calor",
                                 "Direção do vento": "dir"}[vista]])


# =====================================================================
# ABA 4 — Relatório
# =====================================================================

with aba4:
    mostrar_recados("relatorio")
    if not TEM_AREA:
        pedir_area()
    st.markdown(
        "O PDF junta: localização e estações, janelas do período, "
        "meteorograma, mapa de calor, mapas de interpolação, direção do "
        "vento, conferência modelo × medido (com tabelas do INMET) e a "
        "previsão dos próximos dias.")
    st.caption("Usa os critérios da aba 2, o limite de chuva e a correção da "
               "aba 3, a fonte da aba 2 e os parâmetros da vista de mapas.")
    c = st.columns([2, 2, 1, 1])
    c[0].date_input("Histórico de", key="r_ini", format="DD/MM/YYYY")
    c[1].date_input("até", key="r_fim", format="DD/MM/YYYY")
    c[2].selectbox("Previsão (dias)", [1, 2, 3, 4, 5, 6, 7], key="r_dias")
    c[3].selectbox("Fuso", FUSOS, key="r_fuso")
    c = st.columns(2)
    c[0].button("Últimos 15 dias", key="r_15", on_click=ultimos_dias("r_", 15))
    c[1].button("Últimos 30 dias", key="r_30", on_click=ultimos_dias("r_", 30))

    if st.button("Gerar relatório PDF", type="primary", disabled=not TEM_AREA):
        try:
            crit = ler_crit("s_")
            crit_prev = ler_crit("p_", conjunto=True)
            if ss.r_fim < ss.r_ini:
                raise ValueError("A data final é anterior à inicial.")
        except ValueError as e:
            st.error(str(e))
            crit = None
        if crit:
            h = ss.hist
            antecedencias = (h["antecedencias"] if h and h["r"].get("area")
                             == (ss.lat, ss.lon) else None)
            with st.status("Gerando o relatório…", expanded=True) as s:
                try:
                    pdf, paginas, falhas, cal = sv.relatorio_padrao(
                        list(ss.proximas), ss.r_ini.isoformat(),
                        ss.r_fim.isoformat(), int(ss.r_fuso), int(ss.r_dias),
                        crit, crit_prev, ss.lat, ss.lon,
                        (float(ss.m_potencia), int(ss.m_celulas),
                         ss.m_metrica.startswith("km")),
                        ss.s_fonte, dict(ss.medidos), ss.calibracao,
                        ss.p_correcao == ja.CORRECAO_SIM, antecedencias,
                        list(ss.campo), ss.area_ha, ss.origem, ss.pontos_area,
                        UFS.get(ss.uf, ""), avisar=lambda t: s.write(t))
                    if cal:
                        ss.calibracao = cal
                    ss.rel = {"pdf": pdf, "paginas": paginas, "falhas": falhas,
                              "nome": f"relatorio_janela_"
                                      f"{datetime.now():%Y%m%d_%H%M}.pdf"}
                    s.update(label=f"Pronto: {paginas} páginas",
                             state="complete", expanded=False)
                except Exception as e:
                    s.update(label="Falhou", state="error")
                    st.error(f"Não consegui gerar o relatório: {e}")

    if ss.rel:
        st.success(f"Relatório com {ss.rel['paginas']} páginas.")
        st.download_button("Baixar relatório PDF", ss.rel["pdf"],
                           file_name=ss.rel["nome"], mime="application/pdf",
                           type="primary")
        if ss.rel["falhas"]:
            st.caption("Ficaram de fora: " + "; ".join(ss.rel["falhas"]))


# =====================================================================
# ABA 5 — Voos realizados
# =====================================================================

def atualizar_resumo_voos():
    v = ss.voos_res
    v["comparacao"] = (ja.comparar_area_problema(
        v["av"], ss.poligonos, v["janela_h"], v["limite_mm"])
        if ss.poligonos else None)
    v["linhas"], v["dtxt"] = sv.resumo_voos(
        v["av"], v["dias"], v["janela_h"], v["limite_mm"], v["fonte"],
        v["comparacao"], v["falhas"])
    v["csv"] = sv.csv_voos(v["av"], v["janela_h"], v["fonte"])
    v["geojson"] = sv.geojson_voos(v["av"], v["janela_h"], ss.poligonos)
    v["html"] = None
    v["pdf"] = None
    v["id"] = datetime.now().timestamp()


with aba5:
    mostrar_recados("voos")
    st.file_uploader("Arquivo de operações do dron (GeoJSON, um traçado por "
                     "voo, com Data e Hora)", type=["geojson", "json"],
                     key="up_voos", on_change=cb_voos)
    if ss.voos:
        st.markdown("  \n".join(ss.voos["recado"]))

    c = st.columns(4)
    c[0].selectbox("Agrupar", ja.AGRUPAR_VOOS, key="v_agrupar")
    c[1].selectbox("Estações por local", [3, 4, 5], key="v_n")
    c[2].selectbox("Fuso", FUSOS, key="v_fuso")
    c[3].selectbox("Fonte", ja.FONTES_VOOS, key="v_fonte")
    c = st.columns(2)
    c[0].number_input("Lavagem possível com (mm ou mais)", key="v_lav_mm",
                      min_value=0.1, step=0.5, format="%.1f")
    c[1].selectbox("…nas horas seguintes", [1, 2, 4, 6, 12, 24], key="v_lav_h",
                   help="Use o período sem chuva da bula.")
    st.caption("Critérios de Delta T e vento: aba 2 · chuva no voo: aba 3.")
    st.file_uploader("Área com problema (opcional: KML, KMZ, GeoJSON ou "
                     "shapefile .zip)", type=["kml", "kmz", "geojson", "json",
                                              "zip"],
                     key="up_problema", on_change=cb_problema)

    if st.button("Analisar voos", type="primary", disabled=not ss.voos):
        try:
            crit = ler_crit("s_")
        except ValueError as e:
            st.error(str(e))
            crit = None
        if crit:
            janela_h, limite_mm = int(ss.v_lav_h), max(0.1, float(ss.v_lav_mm))
            with st.status("Analisando os voos…", expanded=False) as s:
                try:
                    locais = [dict(g) for g in ss.voos["locais"]]
                    av, dias, falhas, fonte = sv.analisar_voos(
                        ESTACOES, locais, crit, int(ss.v_fuso), int(ss.v_n),
                        ss.v_fonte, dict(ss.medidos), ss.calibracao, janela_h,
                        limite_mm, avisar=lambda t: s.update(label=t))
                    ss.voos_res = {"av": av, "locais": locais, "dias": dias,
                                   "falhas": falhas, "fonte": fonte,
                                   "crit": crit, "janela_h": janela_h,
                                   "limite_mm": limite_mm}
                    atualizar_resumo_voos()
                    s.update(label=f"{len(av)} voos analisados",
                             state="complete")
                except Exception as e:
                    s.update(label="Falhou", state="error")
                    st.error(f"Falha na análise dos voos: {e}")

    v = ss.voos_res
    if v:
        st.subheader("Resumo")
        linhas_resumo(v["linhas"])
        c = st.columns(3)
        agora = f"{datetime.now():%Y%m%d_%H%M}"
        c[0].download_button("CSV", v["csv"], file_name=f"voos_{agora}.csv",
                             mime="text/csv")
        c[1].download_button("GeoJSON para o QGIS", v["geojson"],
                             file_name=f"voos_analisados_{agora}.geojson",
                             mime="application/geo+json")
        if v["pdf"] is None:
            if c[2].button("Gerar relatório de voos (PDF)"):
                with st.spinner("Montando as páginas…"):
                    try:
                        v["pdf"], v["pdf_pag"] = sv.pdf_voos(
                            v["av"], v["locais"], v["dias"], v["crit"],
                            ss.v_agrupar, v["fonte"], v["dtxt"], v["janela_h"],
                            v["limite_mm"], ss.poligonos, v["comparacao"])
                    except Exception as e:
                        st.error(f"Não consegui gerar o relatório: {e}")
                if v["pdf"] is not None:
                    st.rerun()
        else:
            c[2].download_button(f"Baixar PDF ({v['pdf_pag']} páginas)",
                                 v["pdf"], file_name=f"relatorio_voos_{agora}.pdf",
                                 mime="application/pdf", type="primary")

        vista = st.radio("Ver", ["Voos", "Piores", "Mapa", "Mapa interativo",
                                 "Chuva depois", "Resumo", "Dia a dia"],
                         key="v_vista", horizontal=True,
                         label_visibility="collapsed")
        if vista == "Voos":
            st.dataframe(pd.DataFrame(sv.tabela_voos(v["av"])),
                         hide_index=True)
        elif vista == "Piores":
            piores = sorted([x for x in v["av"] if x.get("p_apta") is not None],
                            key=lambda x: x["p_apta"])[:40]
            st.dataframe(pd.DataFrame(sv.tabela_voos(piores)),
                         hide_index=True)
        elif vista == "Mapa":
            datas = sorted({x["inicio"].date() for x in v["av"]})
            opcoes_dia = ["todos"] + [d.strftime("%d/%m/%Y") for d in datas]
            if ss.v_dia_mapa not in opcoes_dia:
                ss.v_dia_mapa = "todos"
            c = st.columns(2)
            c[0].selectbox("Colorir por", ja.MODOS_COR_MAPA, key="v_colorir")
            c[1].selectbox("Dia", opcoes_dia, key="v_dia_mapa")
            dia = ss.v_dia_mapa
            voos = [x for x in v["av"] if dia == "todos"
                    or x["inicio"].strftime("%d/%m/%Y") == dia]
            titulo = f"{len(voos)} voos" + ("" if dia == "todos" else f" em {dia}")
            st.image(figura(
                ("mapa_voos", v["id"], ss.v_colorir, dia),
                lambda f: ja.desenhar_mapa_voos(
                    f, voos, [e for g in v["locais"]
                              for e in g.get("estacoes", [])],
                    titulo, colorir=ss.v_colorir, poligonos=ss.poligonos),
                largura=10, altura=7))
        elif vista == "Mapa interativo":
            if v["html"] is None:
                v["html"] = sv.html_mapa_voos(v["av"], v["janela_h"],
                                              v["limite_mm"], ss.poligonos)
            components.html(v["html"].decode("utf-8"), height=620)
            st.download_button("Baixar mapa interativo (.html)", v["html"],
                               file_name=f"mapa_voos_{agora}.html",
                               mime="text/html")
        elif vista == "Chuva depois":
            st.image(figura(
                ("chuva", v["id"]),
                lambda f: ja.desenhar_chuva_por_dia(
                    f, ja.resumo_chuva_por_dia(v["av"], v["janela_h"]),
                    v["janela_h"], v["limite_mm"],
                    f"Chuva nas {v['janela_h']} h seguintes às aplicações de "
                    "cada dia")))
        elif vista == "Resumo":
            por, rotulo = ja.CAMPO_AGRUPAR[ss.v_agrupar]
            st.image(figura(
                ("resumo_voos", v["id"], ss.v_agrupar),
                lambda f: ja.desenhar_resumo_voos(
                    f, v["av"], por, rotulo, f"Hectares por {rotulo} e condição")))
        else:
            rotulos = [f'{d["data"]:%d/%m/%Y} — {d["local"]}' for d in v["dias"]]
            if ss.v_dia not in rotulos:
                ss.v_dia = rotulos[0] if rotulos else None
            if rotulos:
                st.selectbox("Dia", rotulos, key="v_dia")
                d = v["dias"][rotulos.index(ss.v_dia)]
                do_dia = [x for x in v["av"] if x["inicio"].date() == d["data"]
                          and x.get("local") == d["local"]]
                st.image(figura(
                    ("dia", v["id"], ss.v_dia),
                    lambda f: ja.desenhar_voos_no_dia(
                        f, d["serie"], v["crit"], do_dia, ss.v_dia,
                        fontes=d.get("fontes"), janela_h=v["janela_h"])))
