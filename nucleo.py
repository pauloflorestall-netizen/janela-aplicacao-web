"""
Carrega o janela_aplicacao.py (a versão de desktop) sem abrir janela.

O arquivo original fica intacto: você continua editando e rodando no
PyCharm como sempre. Aqui ele é importado só pelas funções de cálculo,
download, gráficos e PDF. A parte de janela (Tkinter) é trocada por
peças vazias, porque no servidor não existe tela.

Os avisos que o programa mostraria em caixa de mensagem
(messagebox.showerror etc.) ficam guardados em AVISOS, e o site mostra.
"""

import os
import sys
import types

import matplotlib

matplotlib.use("Agg")                        # desenha em memória, sem tela
os.environ.setdefault("JANELA_SEM_PREFERENCIAS", "1")   # site não grava preferências

AVISOS = []   # [(tipo, título, texto)] vindos de messagebox


class _Qualquer:
    """Aceita qualquer chamada ou atributo e não faz nada."""

    def __init__(self, *a, **k):
        pass

    def __call__(self, *a, **k):
        return _Qualquer()

    def __getattr__(self, nome):
        return _Qualquer()

    def __iter__(self):
        return iter(())

    def __bool__(self):
        return False


class _ModuloVazio(types.ModuleType):
    def __getattr__(self, nome):
        if nome.startswith("__"):
            raise AttributeError(nome)
        return _Qualquer


def _caixa(tipo):
    def mostrar(titulo="", texto="", *a, **k):
        AVISOS.append((tipo, str(titulo), str(texto)))
        return None
    return mostrar


def _instalar_tk_falso():
    tk = _ModuloVazio("tkinter")
    ttk = _ModuloVazio("tkinter.ttk")
    filedialog = _ModuloVazio("tkinter.filedialog")
    messagebox = _ModuloVazio("tkinter.messagebox")
    messagebox.showerror = _caixa("erro")
    messagebox.showwarning = _caixa("aviso")
    messagebox.showinfo = _caixa("info")
    messagebox.askyesno = lambda *a, **k: False
    tk.ttk, tk.filedialog, tk.messagebox = ttk, filedialog, messagebox
    tk.TclError = RuntimeError

    tkagg = _ModuloVazio("matplotlib.backends.backend_tkagg")
    tkagg.FigureCanvasTkAgg = _Qualquer
    tkagg.NavigationToolbar2Tk = _Qualquer

    sys.modules.update({
        "tkinter": tk, "tkinter.ttk": ttk, "tkinter.filedialog": filedialog,
        "tkinter.messagebox": messagebox,
        "matplotlib.backends.backend_tkagg": tkagg,
    })


def carregar():
    """Importa o programa de desktop e devolve o módulo."""
    if "janela_aplicacao" in sys.modules:
        return sys.modules["janela_aplicacao"]
    _instalar_tk_falso()
    usar_original = matplotlib.use
    matplotlib.use = lambda *a, **k: None    # o original pede TkAgg; fica o Agg
    try:
        pasta = os.path.dirname(os.path.abspath(__file__))
        if pasta not in sys.path:
            sys.path.insert(0, pasta)
        import janela_aplicacao
    finally:
        matplotlib.use = usar_original
    return janela_aplicacao


def pegar_avisos():
    """Devolve e limpa os avisos acumulados."""
    saida = list(AVISOS)
    AVISOS.clear()
    return saida
