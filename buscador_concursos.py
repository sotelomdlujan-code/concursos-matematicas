#!/usr/bin/env python3
"""
Buscador de concursos de MATEMÁTICA - CGE Entre Ríos (Concordia)

Qué hace:
  1. Lee el listado https://cge.entrerios.gov.ar/category/concordia-concursos/
  2. Abre cada publicación (el listado solo muestra el nombre de la escuela,
     la materia está adentro).
  3. Se queda solo con las que mencionan Matemática.
  4. Te muestra únicamente las NUEVAS desde la última vez que lo corriste
     (guarda el historial en concursos_vistos.json).
  5. Te avisa por consola, ventana de Windows y, si lo configurás, Telegram.

Uso:
  python buscador_concursos.py              # busca una vez
  python buscador_concursos.py --todos      # muestra todas las de matemática, no solo las nuevas
  python buscador_concursos.py --vigilar 30 # repite cada 30 minutos
  python buscador_concursos.py --paginas 3  # revisa 3 páginas del listado (default 2)

Requisitos:  pip install requests beautifulsoup4
"""

import argparse
import html
import json
import os
import re
import smtplib
import ssl
import sys
import time
import unicodedata
from email.message import EmailMessage
from pathlib import Path

import requests
from bs4 import BeautifulSoup

# ----------------------------------------------------------------------------
# CONFIGURACIÓN (editá lo que quieras)
# ----------------------------------------------------------------------------
URL_LISTADO = "https://cge.entrerios.gov.ar/category/concordia-concursos/"

# Palabras a buscar (sin tildes, en minúscula). Agregá las que quieras,
# por ejemplo "fisica" si también te interesa Física.
PALABRAS_CLAVE = [
    "matematica",
    "matematicas",
]

# Telegram (opcional). Dejá vacío para no usarlo.
# 1) Hablá con @BotFather en Telegram, creá un bot y copiá el TOKEN.
# 2) Escribile algo a tu bot y abrí https://api.telegram.org/bot<TOKEN>/getUpdates
#    para ver tu CHAT_ID.
# En GitHub se toman de los "Secrets" (ver README). En tu PC podés escribirlos acá.
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

# Avisos por GitHub Issues (automático dentro de GitHub Actions, no requiere nada).
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN", "")
GITHUB_REPO = os.environ.get("GITHUB_REPOSITORY", "")          # "usuario/repo"
GITHUB_USUARIO = os.environ.get("GITHUB_REPOSITORY_OWNER", "")  # para mencionarte

# Email (opcional). Con Gmail: usá una "contraseña de aplicación".
EMAIL_USUARIO = os.environ.get("EMAIL_USUARIO", "")   # tu cuenta que envía
EMAIL_CLAVE = os.environ.get("EMAIL_CLAVE", "")       # contraseña de aplicación
EMAIL_DESTINO = os.environ.get("EMAIL_DESTINO", "") or EMAIL_USUARIO
SMTP_SERVIDOR = os.environ.get("SMTP_SERVIDOR", "smtp.gmail.com")

MAX_MENSAJES_POR_CORRIDA = 15  # evita inundarte en la primera ejecución

CARPETA = Path(__file__).parent
ARCHIVO_HISTORIAL = CARPETA / "concursos_vistos.json"
ARCHIVO_PAGINA = CARPETA / "docs" / "index.html"
HEADERS = {"User-Agent": "Mozilla/5.0 (buscador-concursos personal)"}
PAUSA_ENTRE_PEDIDOS = 0.6  # segundos, para no sobrecargar el sitio
# ----------------------------------------------------------------------------


def normalizar(texto: str) -> str:
    """Minúsculas y sin tildes, para que 'Matemática' == 'matematica'."""
    texto = unicodedata.normalize("NFD", texto.lower())
    return "".join(c for c in texto if unicodedata.category(c) != "Mn")


PATRON = re.compile(r"\b(" + "|".join(map(re.escape, PALABRAS_CLAVE)) + r")\b")


def descargar(url: str) -> BeautifulSoup | None:
    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
        return BeautifulSoup(r.text, "html.parser")
    except requests.RequestException as e:
        print(f"  [!] No pude abrir {url}: {e}")
        return None


def obtener_publicaciones(paginas: int) -> list[tuple[str, str, str]]:
    """Devuelve [(titulo, url, fecha), ...] de las primeras N páginas."""
    resultado, vistas = [], set()
    for n in range(1, paginas + 1):
        url = URL_LISTADO if n == 1 else f"{URL_LISTADO}?paged={n}"
        soup = descargar(url)
        if soup is None:
            continue
        for h3 in soup.find_all("h3"):
            a = h3.find("a", href=True)
            if not a or a["href"] in vistas:
                continue
            if not re.search(r"/\d{4}/\d{2}/", a["href"]):
                continue
            vistas.add(a["href"])
            fecha = ""
            previo = h3.find_previous(string=re.compile(r"^\s*\d{2}/\d{2}/\d{4}\s*$"))
            if previo:
                fecha = previo.strip()
            resultado.append((a.get_text(strip=True), a["href"], fecha))
        time.sleep(PAUSA_ENTRE_PEDIDOS)
    return resultado


def analizar_publicacion(url: str) -> dict | None:
    """Abre la publicación y devuelve datos si menciona matemática."""
    soup = descargar(url)
    if soup is None:
        return None

    h1 = soup.find("h1")
    # Texto desde el título hacia abajo (evita el menú del sitio)
    if h1:
        texto = "\n".join(
            t.strip() for t in h1.find_all_next(string=True) if t.strip()
        )
    else:
        texto = soup.get_text("\n", strip=True)

    # Cortamos antes del pie de página
    texto = texto.split("Los interesados deberán presentarse")[0]

    if not PATRON.search(normalizar(texto)):
        return {"coincide": False}

    lineas = [l.strip() for l in texto.split("\n") if l.strip()]
    coincidencias = [l for l in lineas if PATRON.search(normalizar(l))]

    # Fecha/hora de la convocatoria, si aparece
    m = re.search(r"para el d[ií]a\s+(.{5,60}?20\d\d)", texto, re.IGNORECASE)
    fecha_conv = m.group(1) if m else ""

    # Horarios ("10:30 hs.")
    horarios = re.findall(r"\b\d{1,2}[:.]\d{2}\s*hs\.?", texto)

    return {
        "coincide": True,
        "convocatoria": fecha_conv,
        "horarios": sorted(set(horarios))[:4],
        "detalle": coincidencias[:6],
    }


def cargar_historial() -> dict:
    if ARCHIVO_HISTORIAL.exists():
        try:
            return json.loads(ARCHIVO_HISTORIAL.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            pass
    return {}


def guardar_historial(h: dict) -> None:
    ARCHIVO_HISTORIAL.write_text(
        json.dumps(h, ensure_ascii=False, indent=2), encoding="utf-8"
    )


def formatear(titulo, url, fecha, info) -> str:
    out = [f"📐 {titulo}"]
    if fecha:
        out.append(f"   Publicado: {fecha}")
    if info.get("convocatoria"):
        out.append(f"   Convocatoria: {info['convocatoria']}")
    if info.get("horarios"):
        out.append(f"   Horarios: {', '.join(info['horarios'])}")
    for d in info.get("detalle", []):
        out.append(f"   • {d}")
    out.append(f"   {url}")
    return "\n".join(out)


def enviar_telegram(texto: str) -> None:
    if not (TELEGRAM_TOKEN and TELEGRAM_CHAT_ID):
        return
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            data={
                "chat_id": TELEGRAM_CHAT_ID,
                "text": texto[:4000],
                "disable_web_page_preview": True,
            },
            timeout=20,
        )
    except requests.RequestException as e:
        print(f"  [!] No pude enviar a Telegram: {e}")


def crear_issue_github(titulo: str, url: str, fecha: str, info: dict) -> None:
    """Crea un Issue en el repo: GitHub te notifica por app y por email."""
    if not (GITHUB_TOKEN and GITHUB_REPO):
        return
    cuerpo = formatear(titulo, url, fecha, info)
    if GITHUB_USUARIO:
        cuerpo = f"@{GITHUB_USUARIO} hay un concurso nuevo de Matemática:\n\n" + cuerpo
    try:
        r = requests.post(
            f"https://api.github.com/repos/{GITHUB_REPO}/issues",
            headers={
                "Authorization": f"Bearer {GITHUB_TOKEN}",
                "Accept": "application/vnd.github+json",
            },
            json={"title": f"📐 {titulo}", "body": cuerpo},
            timeout=20,
        )
        if r.status_code >= 300:
            print(f"  [!] GitHub Issue falló ({r.status_code}): {r.text[:200]}")
    except requests.RequestException as e:
        print(f"  [!] No pude crear el Issue: {e}")


def enviar_email(items: list) -> None:
    if not (EMAIL_USUARIO and EMAIL_CLAVE and EMAIL_DESTINO):
        return
    msg = EmailMessage()
    msg["Subject"] = f"📐 {len(items)} concurso(s) nuevo(s) de Matemática"
    msg["From"] = EMAIL_USUARIO
    msg["To"] = EMAIL_DESTINO
    msg.set_content("\n\n".join(formatear(*x) for x in items))
    try:
        with smtplib.SMTP_SSL(SMTP_SERVIDOR, 465, context=ssl.create_default_context()) as srv:
            srv.login(EMAIL_USUARIO, EMAIL_CLAVE)
            srv.send_message(msg)
    except (smtplib.SMTPException, OSError) as e:
        print(f"  [!] No pude enviar el email: {e}")


def avisar(items: list) -> None:
    """items = [(titulo, url, fecha, info), ...]"""
    # Ventana de Windows (solo si lo corrés en tu PC)
    if sys.platform == "win32":
        try:
            import ctypes

            ctypes.windll.user32.MessageBoxW(
                0,
                f"Hay {len(items)} concurso(s) nuevo(s) de Matemática.",
                "Concursos de Matemática",
                0x40 | 0x1000,
            )
        except Exception:
            pass

    enviar_email(items)

    for x in items[:MAX_MENSAJES_POR_CORRIDA]:
        crear_issue_github(*x)
        enviar_telegram("NUEVO CONCURSO DE MATEMÁTICA\n\n" + formatear(*x))
        time.sleep(0.5)
    if len(items) > MAX_MENSAJES_POR_CORRIDA:
        enviar_telegram(
            f"... y {len(items) - MAX_MENSAJES_POR_CORRIDA} más. Mirá la página completa."
        )


def generar_pagina(historial: dict) -> None:
    """Crea docs/index.html: lista para abrir desde el celular (GitHub Pages)."""
    filas = []
    for url, d in reversed(list(historial.items())):  # más nuevos primero
        if not d.get("matematica"):
            continue
        info = d.get("info", {})
        detalle = "".join(f"<li>{html.escape(l)}</li>" for l in info.get("detalle", []))
        conv = html.escape(info.get("convocatoria", "") or "sin fecha detectada")
        hor = html.escape(", ".join(info.get("horarios", [])))
        filas.append(
            f'<article><h2><a href="{html.escape(url)}">{html.escape(d.get("titulo", ""))}</a></h2>'
            f"<p><b>Convocatoria:</b> {conv}"
            + (f" &middot; {hor}" if hor else "")
            + f"</p><ul>{detalle}</ul></article>"
        )
    actualizado = time.strftime("%d/%m/%Y %H:%M", time.gmtime(time.time() - 3 * 3600))
    cuerpo = "\n".join(filas) or "<p>Todavía no hay concursos de Matemática detectados.</p>"
    ARCHIVO_PAGINA.parent.mkdir(exist_ok=True)
    ARCHIVO_PAGINA.write_text(
        f"""<!doctype html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Concursos de Matemática - Concordia</title>
<style>
:root{{--bg:#fff;--fg:#1a1a1a;--card:#f3f4f6;--link:#0b5fff}}
@media(prefers-color-scheme:dark){{:root{{--bg:#111;--fg:#eee;--card:#1e1e1e;--link:#6ea8ff}}}}
body{{font-family:system-ui,sans-serif;background:var(--bg);color:var(--fg);max-width:720px;margin:0 auto;padding:16px}}
article{{background:var(--card);border-radius:12px;padding:12px 16px;margin:12px 0}}
h1{{font-size:1.3rem}} h2{{font-size:1.05rem;margin:0 0 6px}} a{{color:var(--link)}}
ul{{padding-left:18px;margin:6px 0}} small{{opacity:.7}}
</style></head><body>
<h1>Concursos de Matemática - Concordia</h1>
<small>Actualizado: {actualizado} (hora Argentina)</small>
{cuerpo}
</body></html>""",
        encoding="utf-8",
    )


def buscar(paginas: int, mostrar_todos: bool) -> None:
    historial = cargar_historial()  # url -> {"matematica": bool, ...}
    print(f"Revisando {paginas} página(s) del listado...")
    publicaciones = obtener_publicaciones(paginas)
    print(f"Publicaciones en el listado: {len(publicaciones)}")

    nuevos, todos = [], []
    for titulo, url, fecha in publicaciones:
        if url in historial:
            if mostrar_todos and historial[url].get("matematica"):
                todos.append((titulo, url, fecha, historial[url]["info"]))
            continue  # ya la revisé antes, no la vuelvo a abrir

        info = analizar_publicacion(url)
        time.sleep(PAUSA_ENTRE_PEDIDOS)
        if info is None:
            continue  # error de red: la reintento la próxima vez

        historial[url] = {
            "matematica": info["coincide"],
            "titulo": titulo,
            "info": info,
        }
        if info["coincide"]:
            nuevos.append((titulo, url, fecha, info))
            todos.append((titulo, url, fecha, info))

    guardar_historial(historial)
    generar_pagina(historial)

    a_mostrar = todos if mostrar_todos else nuevos
    if not a_mostrar:
        print("No hay concursos de Matemática nuevos. ✔")
        return

    titulo_bloque = "Concursos de Matemática" if mostrar_todos else "NUEVOS concursos de Matemática"
    print(f"\n=== {titulo_bloque}: {len(a_mostrar)} ===\n")
    print("\n\n".join(formatear(*x) for x in a_mostrar))
    if not mostrar_todos:
        avisar(a_mostrar)


def main() -> None:
    ap = argparse.ArgumentParser(description="Concursos de Matemática - CGE Concordia")
    ap.add_argument("--todos", action="store_true", help="mostrar todas, no solo las nuevas")
    ap.add_argument("--vigilar", type=int, metavar="MIN", help="repetir cada MIN minutos")
    ap.add_argument("--paginas", type=int, default=2, help="páginas del listado a revisar")
    args = ap.parse_args()

    if args.vigilar:
        print(f"Modo vigilancia: reviso cada {args.vigilar} min. Ctrl+C para salir.")
        while True:
            buscar(args.paginas, args.todos)
            print(f"\nPróxima revisión en {args.vigilar} min...\n")
            time.sleep(args.vigilar * 60)
    else:
        buscar(args.paginas, args.todos)
        if sys.platform == "win32" and getattr(sys, "frozen", False):
            input("\nEnter para salir...")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nListo.")
