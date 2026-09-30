# Janela de Aplicação — versão web

A mesma ferramenta do desktop, no navegador. O `janela_aplicacao.py` é o
seu arquivo original, sem nenhuma mudança: o site importa as funções de
cálculo dele e troca só a janela do Tkinter por uma página.

## O que tem nesta pasta

| Arquivo | Para que serve |
|---|---|
| `app.py` | A página: as cinco abas, no navegador |
| `servicos.py` | O que os botões das abas faziam, sem a janela |
| `nucleo.py` | Importa o `janela_aplicacao.py` sem abrir janela |
| `janela_aplicacao.py` | Seu programa, igual ao do desktop |
| `estacoes_inmet.json`, `contornos/` | Estações e contornos do mapa |
| `exemplo/` | Os dados do teste do LEIA-ME (botão "Carregar o exemplo") |
| `requirements.txt` | Pacotes que o servidor instala |
| `.streamlit/config.toml` | Cores do Geo Rubi |

## Publicar (uma vez só, uns 15 minutos)

1. **GitHub.** Crie uma conta em github.com, clique em **New repository**,
   dê um nome (ex.: `janela-aplicacao-web`) e crie. Na página do
   repositório, clique em **uploading an existing file** e arraste todo o
   conteúdo desta pasta (inclusive as pastas `.streamlit`, `contornos` e
   `exemplo`). Clique em **Commit changes**.
   A pasta `.streamlit` começa com ponto e às vezes fica oculta no
   Windows: se ela não subir, crie pelo site com **Add file → Create new
   file**, nome `.streamlit/config.toml`, e cole o conteúdo.
2. **Streamlit.** Entre em share.streamlit.io com a conta do GitHub,
   clique em **Create app**, escolha o repositório, a branch `main` e o
   arquivo `app.py`. Se quiser, escolha o endereço (ex.:
   `georubi-janela`). Clique em **Deploy**. A primeira instalação leva
   alguns minutos.
3. **Hub.** Copie o endereço do app (algo como
   `https://georubi-janela.streamlit.app`) e cole no card novo do
   `georubi-hub.html`, no lugar de `https://SEU-APP.streamlit.app/`.
   Publique o hub no Netlify como você já faz.
4. **Teste.** No app, clique em **Carregar o exemplo** no menu lateral e
   siga pelas abas 2 a 5.

## Atualizar

Mudou o `janela_aplicacao.py` no PyCharm? Envie o arquivo novo para o
GitHub (mesmo botão de upload, substituindo o antigo). O site se atualiza
sozinho em um ou dois minutos.

## Rodar no seu computador

    pip install -r requirements.txt
    streamlit run app.py

Abre no navegador em http://localhost:8501. O desktop continua
funcionando igual: `python janela_aplicacao.py`.

## Diferenças em relação ao desktop

- **Área:** por coordenada ou arquivo do talhão. Não há clique no mapa.
- **Calibração:** o servidor não guarda arquivos entre visitas. Depois de
  carregar tabelas medidas, baixe o `calibracao.json` no menu lateral e
  envie de novo na próxima vez. Se você colocar um `calibracao.json` no
  GitHub, ao lado do `app.py`, ele vira o ponto de partida de todo mundo.
- **Preferências:** os critérios voltam ao padrão a cada visita.
- **Arquivos gerados** (PDF, CSV, GeoJSON, mapa interativo, pacote do
  QGIS) saem como download.

## Bom saber

- Por padrão, quem tiver o link consegue usar. Para restringir, veja as
  opções de compartilhamento nas configurações do app no Streamlit.
- App gratuito sem uso por um tempo costuma "dormir"; o primeiro acesso
  depois disso demora um pouco para acordar.
- As tabelas medidas do INMET continuam sendo baixadas à mão no portal
  (ele pede "não sou robô"); a aba 2 traz os links de cada estação.
