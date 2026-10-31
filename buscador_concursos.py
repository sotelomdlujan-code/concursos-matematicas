#!/usr/bin/env python3
"""
Buscador de concursos docentes - CGE Entre Ríos (v2)

Qué hace:
  1. Lee los listados del CGE (por defecto: Concordia concursos).
  2. Abre cada publicación y entiende su estructura: fecha, hora, lugar,
     espacio curricular, horas, curso, división, turno, carácter y clases.
  3. Se queda con las de las materias que configures (config.json).
  4. Avisa de las NUEVAS: Issue de GitHub (app + email), email y/o Telegram.
     Si es una 2.ª convocatoria de un concurso ya avisado, lo agrega como
     comentario en el mismo Issue en vez de abrir otro.
  5. Recordatorios: el día anterior a la noche y el mismo día a la mañana.
  6. Cierra solos los Issues de concursos vencidos.
  7. Genera la APP en docs/ (buscador de TODAS las materias, instalable en el
     celular) y docs/calendario.ics (calendario al que podés suscribirte).
  8. Si deja de poder leer el sitio del CGE, te avisa.
  9. Avisa de publicaciones que son solo imagen/PDF (para revisarlas a mano).

Uso:
  python buscador_concursos.py              # una revisión
  python buscador_concursos.py --todos      # muestra todos los vigentes
  python buscador_concursos.py --vigilar 30 # repite cada 30 minutos

Requisitos:  pip install requests beautifulsoup4
"""

import argparse
import base64
import copy
import hashlib
import html
import json
import os
import re
import smtplib
import ssl
import sys
import time
import unicodedata
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path

import requests
from bs4 import BeautifulSoup
from bs4.element import Comment

# ----------------------------------------------------------------------------
# RUTAS Y CONFIGURACIÓN
# ----------------------------------------------------------------------------
CARPETA = Path(__file__).parent
ARCHIVO_CONFIG = CARPETA / "config.json"
ARCHIVO_HISTORIAL = CARPETA / "concursos_vistos.json"
ARCHIVO_PAGINA = CARPETA / "docs" / "index.html"
ARCHIVO_CALENDARIO = CARPETA / "docs" / "calendario.ics"

HEADERS = {"User-Agent": "Mozilla/5.0 (buscador-concursos personal)"}
PAUSA_ENTRE_PEDIDOS = 0.6
ART = timezone(timedelta(hours=-3))  # Argentina no usa horario de verano
VERSION_DATOS = 3

# Credenciales: en GitHub vienen de los "Secrets" (ver README).
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN", "")
GITHUB_REPO = os.environ.get("GITHUB_REPOSITORY", "")
GITHUB_USUARIO = os.environ.get("GITHUB_REPOSITORY_OWNER", "")
EMAIL_USUARIO = os.environ.get("EMAIL_USUARIO", "")
EMAIL_CLAVE = os.environ.get("EMAIL_CLAVE", "")
EMAIL_DESTINO = os.environ.get("EMAIL_DESTINO", "") or EMAIL_USUARIO
SMTP_SERVIDOR = os.environ.get("SMTP_SERVIDOR", "smtp.gmail.com")
# ntfy (notificaciones push al celular). El nombre del canal es como una contraseña: va como Secret.
NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "").strip()
NTFY_SERVIDOR = os.environ.get("NTFY_SERVIDOR", "https://ntfy.sh").strip().rstrip("/")
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")
MAX_TELEGRAM_POR_CORRIDA = 15

CONFIG_DEFECTO = {
    "materias": {"Matemática": ["matematica", "matematicas"]},
    "fuentes": [
        {
            "nombre": "Concordia",
            "url": "https://cge.entrerios.gov.ar/category/concordia-concursos/",
        }
    ],
    "paginas": 3,
    "filtros": {
        "escuelas_incluir": [],
        "escuelas_excluir": [],
        "turnos": [],
        "horas_minimas": 0,
    },
    "recordatorios": {"el_dia": True, "dia_antes": True},
    "ntfy": {"silencio_desde": 23, "silencio_hasta": 7, "urgente_dias": 1, "prueba": 1},
    "cerrar_issues_vencidos": True,
    "avisar_publicaciones_sin_texto": True,
    "alerta_si_falla_revisiones": 3,
}


def cargar_config() -> dict:
    cfg = copy.deepcopy(CONFIG_DEFECTO)
    if ARCHIVO_CONFIG.exists():
        try:
            usuario = json.loads(ARCHIVO_CONFIG.read_text(encoding="utf-8"))
            for k, v in usuario.items():
                if k.startswith("_"):
                    continue  # claves de comentario
                if isinstance(v, dict) and isinstance(cfg.get(k), dict) and k != "materias":
                    cfg[k].update(v)
                else:
                    cfg[k] = v
        except (json.JSONDecodeError, OSError) as e:
            print(f"[!] config.json inválido ({e}). Uso la configuración por defecto.")
    return cfg


# ----------------------------------------------------------------------------
# TEXTO Y FECHAS
# ----------------------------------------------------------------------------
DIAS = ["lunes", "martes", "miércoles", "jueves", "viernes", "sábado", "domingo"]
MESES = {
    "enero": 1, "febrero": 2, "marzo": 3, "abril": 4, "mayo": 5, "junio": 6,
    "julio": 7, "agosto": 8, "septiembre": 9, "setiembre": 9, "octubre": 10,
    "noviembre": 11, "diciembre": 12,
}


def ahora() -> datetime:
    return datetime.now(ART)


def normalizar(texto: str) -> str:
    """Minúsculas y sin tildes, para que 'Matemática' == 'matematica'."""
    texto = unicodedata.normalize("NFD", texto.lower())
    return "".join(c for c in texto if unicodedata.category(c) != "Mn")


def limpiar_linea(l: str) -> str:
    l = l.replace("\u00ad", "").replace("\u200b", "").replace("\xa0", " ")
    return re.sub(r"\s+", " ", l).strip()


def parse_dmy(s: str):
    m = re.match(r"^\s*(\d{1,2})/(\d{1,2})/(\d{4})\s*$", s or "")
    if not m:
        return None
    try:
        return date(int(m.group(3)), int(m.group(2)), int(m.group(1)))
    except ValueError:
        return None


_RE_NUM = re.compile(r"\b(\d{1,2})/(\d{1,2})/(\d{4})\b")
_RE_TXT = re.compile(
    r"\b(\d{1,2})\s*(?:º|°)?\s+de\s+(" + "|".join(MESES) + r")(?:\s+(?:de|del)\s+(\d{4}))?\b"
)


def buscar_fecha(norm: str, ref: date):
    """Primera fecha válida de una línea ya normalizada (dd/mm/aaaa o '2 de noviembre [de 2026]')."""
    hallazgos = []
    for m in _RE_NUM.finditer(norm):
        hallazgos.append((m.start(), int(m.group(3)), int(m.group(2)), int(m.group(1))))
    for m in _RE_TXT.finditer(norm):
        anio = int(m.group(3)) if m.group(3) else None
        hallazgos.append((m.start(), anio, MESES[m.group(2)], int(m.group(1))))
    for _, anio, mes, dia in sorted(hallazgos, key=lambda x: x[0]):
        try:
            if anio is None:
                d = date(ref.year, mes, dia)
                if d < ref - timedelta(days=90):
                    d = date(ref.year + 1, mes, dia)
                return d
            return date(anio, mes, dia)
        except ValueError:
            continue
    return None


def fecha_larga(iso) -> str:
    if not iso:
        return "Fecha no detectada (ver la publicación)"
    d = date.fromisoformat(iso)
    return f"{DIAS[d.weekday()]} {d.strftime('%d/%m/%Y')}"


# ----------------------------------------------------------------------------
# DESCARGA Y EXTRACCIÓN DE TEXTO
# ----------------------------------------------------------------------------
BLOQUES = {
    "p", "li", "div", "h1", "h2", "h3", "h4", "h5", "h6", "td", "th", "tr",
    "ul", "ol", "section", "article", "blockquote", "pre", "table", "header", "footer",
}


def descargar(url: str):
    descargar.ultimo_status = None
    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        descargar.ultimo_status = r.status_code
        r.raise_for_status()
        return BeautifulSoup(r.text, "html.parser")
    except requests.RequestException as e:
        print(f"  [!] No pude abrir {url}: {e}")
        return None


descargar.ultimo_status = None


def extraer_lineas(h1) -> list[str]:
    """
    Texto de la publicación como líneas reales. Une el texto en negrita/cursiva
    con el resto del párrafo (antes se cortaba en cada <strong>) y respeta los <br>.
    """
    for br in h1.find_all_next("br"):
        br.replace_with("\n")
    grupos, ultimo_bloque = [], object()
    for s in h1.find_all_next(string=True):
        if isinstance(s, Comment) or (s.parent and s.parent.name in ("script", "style", "noscript")):
            continue
        bloque = s.parent
        while bloque is not None and bloque.name not in BLOQUES:
            bloque = bloque.parent
        if bloque is not ultimo_bloque:
            grupos.append([])
            ultimo_bloque = bloque
        grupos[-1].append(str(s))
    lineas = []
    for g in grupos:
        for l in "".join(g).split("\n"):
            l = limpiar_linea(l)
            if l:
                lineas.append(l)
    return lineas


def contar_adjuntos(h1) -> int:
    """Imágenes de contenido o PDFs/documentos enlazados (ignora logos del tema)."""
    n = 0
    for tag in h1.find_all_next(["img", "a"]):
        if tag.name == "img":
            src = tag.get("src", "")
            if "wp-content/uploads" in src and "/themes/" not in src:
                n += 1
        else:
            href = (tag.get("href") or "").lower().split("?")[0]
            if href.endswith((".pdf", ".doc", ".docx", ".xls", ".xlsx", ".jpg", ".jpeg", ".png")):
                n += 1
    return n


# ----------------------------------------------------------------------------
# ANÁLISIS DE UNA PUBLICACIÓN
# ----------------------------------------------------------------------------
RE_HORA_SOLA = re.compile(r"^\W*(\d{1,2})[:.](\d{2})\s*(?:hs|horas)?\.?\W*$", re.I)
RE_ITEM = re.compile(r"^\W*(\d{1,2})\s*(?:hs|horas)\b\.?\s*(.*)$", re.I)
RE_DIA = re.compile(r"^(lunes|martes|miercoles|jueves|viernes|sabado|domingo)\b")
RE_ORDINAL = re.compile(r"\b(primer[oa]?|segund[oa]|tercer[oa]?|cuart[oa])\s+(llamado|convocatoria)\b")
RE_CURSO = re.compile(r"(\d+)\s*\.?\s*[º°]\s*a[ñn]o", re.I)
RE_DIVISION = re.compile(r"divisi[oó]n\s*[“\"']?\s*([A-Za-z0-9]+)", re.I)
RE_TURNO = re.compile(r"turno\s+([A-Za-zñáéíóúÑÁÉÍÓÚ]+)", re.I)
RE_CARACTER = re.compile(r"\b(suplente|titular|interin[oa]|provisional)\b", re.I)


def compilar_materias(cfg: dict):
    res = []
    for nombre, palabras in cfg["materias"].items():
        palabras = [normalizar(p) for p in palabras if p.strip()]
        if palabras:
            res.append((nombre, re.compile(r"\b(?:" + "|".join(map(re.escape, palabras)) + r")\b")))
    return res


def materia_de(norm: str, materias):
    for nombre, rx in materias:
        if rx.search(norm):
            return nombre
    return None


def es_encabezado(l: str) -> bool:
    letras = [c for c in l if c.isalpha()]
    return len(letras) >= 3 and all(c.isupper() for c in letras) and len(l) < 90 and not RE_ITEM.match(l)


RE_CANCEL_FUERTE = re.compile(r"\bdesconvoc\w*")
RE_CANCEL_DEBIL = re.compile(
    r"\b(?:suspend\w*|anul\w*|cancel\w*|(?:queda\w*|deja\w*)\s+sin\s+efecto|sin\s+efecto)\b"
)
RE_CONCURSO = re.compile(r"\b(?:concurso|llamado|convocatoria)\b")


def es_cancelacion(titulo: str, lineas) -> bool:
    """¿La publicación anuncia que un concurso se desconvoca/suspende/anula?"""
    t = normalizar(titulo)
    inicio = [normalizar(l) for l in lineas[:15]]  # encabezado de la publicación
    if RE_CANCEL_FUERTE.search(t) or any(RE_CANCEL_FUERTE.search(l) for l in inicio):
        return True
    return any(RE_CANCEL_DEBIL.search(x) and RE_CONCURSO.search(x) for x in [t] + inicio)


def limpiar_titulo(titulo: str) -> str:
    """Quita 'DESCONVOCA CONCURSO' del título para poder compararlo con el del concurso original."""
    t = re.sub(r"(?i)\bdesconvoca(?:toria|do)?\b(?:\s+(?:de\s+)?(?:el\s+)?concursos?)?", " ", titulo)
    return re.sub(r"\s+", " ", t).strip()


def extraer_lugar(linea: str) -> str:
    for rx in (
        r"sito en\s+(.+?),\s*(?:con|en el d[ií]a|munid)",
        r"presentarse en\s+(.+?),\s*en el d[ií]a",
        r"sito en\s+(.+?)[,.]",
    ):
        m = re.search(rx, linea, re.I)
        if m:
            return m.group(1).strip()
    return ""


def nombre_espacio(resto: str, encabezado: str, propio: bool) -> str:
    """Nombre del espacio curricular tal como figura en la publicación (para el buscador)."""
    if propio:
        n = re.split(r"\s+[–—-]\s+|\s*,\s+", resto, maxsplit=1)[0]
    else:
        n = encabezado.capitalize()
    n = n.strip(" .:-–—")
    return n[:60] or "Sin especificar"


def analizar_texto(lineas, titulo, fecha_pub, materias) -> dict:
    """
    Devuelve TODOS los espacios de la publicación ("todos", para el buscador) y, aparte,
    los que coinciden con tus materias configuradas ("items", para los avisos).
    """
    corte = next(
        (i for i, l in enumerate(lineas) if normalizar(l).startswith("los interesados deberan presentarse")),
        None,
    )
    cuerpo = lineas[:corte] if corte is not None else lineas
    lugar = extraer_lugar(lineas[corte]) if corte is not None else ""

    texto_norm = normalizar("\n".join(cuerpo))
    coincide = materia_de(texto_norm, materias) is not None

    resultado = {
        "coincide": coincide, "items": [], "todos": [], "detalle": [], "fecha_gral": None,
        "materias": [n for n, rx in materias if rx.search(texto_norm)],
        "lugar": lugar, "ordinal": "", "largo": len(" ".join(cuerpo)), "texto_corto": "",
        "cancelacion": es_cancelacion(titulo, lineas),
    }

    fecha_titulo = buscar_fecha(normalizar(titulo), fecha_pub)
    fecha_act, hora_act, encabezado, ordinal = fecha_titulo, None, "", ""
    primera_fecha, items, ultimo = None, [], None

    for l in cuerpo:
        n = normalizar(l)
        if not ordinal:
            mo = RE_ORDINAL.search(n)
            if mo:
                ordinal = f"{mo.group(1)} {mo.group(2)}"
        mi = RE_ITEM.match(l)
        if not mi:
            f = buscar_fecha(n, fecha_pub)
            if f:
                if primera_fecha is None:
                    primera_fecha = f
                if f != fecha_act:
                    hora_act = None
                fecha_act = f

        if mi:
            resto = mi.group(2)
            propio = bool(re.match(r"^[^\W\d_]", resto))  # el ítem nombra su propia materia
            cfg_nombre = materia_de(normalizar(resto), materias)
            if cfg_nombre is None and not propio:
                cfg_nombre = materia_de(normalizar(encabezado), materias)
            mc, md, mt, mk = RE_CURSO.search(resto), RE_DIVISION.search(resto), RE_TURNO.search(resto), RE_CARACTER.search(resto)
            ultimo = {
                "materia": cfg_nombre or nombre_espacio(resto, encabezado, propio),
                "buscada": cfg_nombre is not None,
                "hs": int(mi.group(1)),
                "curso": f"{mc.group(1)}.º año" if mc else "",
                "division": md.group(1) if md else "",
                "turno": mt.group(1).lower() if mt else "",
                "caracter": mk.group(1).lower() if mk else "",
                "fecha": fecha_act.isoformat() if fecha_act else None,
                "hora": hora_act,
                "clases": [],
            }
            items.append(ultimo)
        elif RE_HORA_SOLA.match(l):
            m2 = RE_HORA_SOLA.match(l)
            hora_act = f"{int(m2.group(1)):02d}:{m2.group(2)}"
            ultimo = None
        elif es_encabezado(l):
            encabezado = l
            ultimo = None
        elif ultimo is not None and (n.startswith("horario") or RE_DIA.match(n)):
            if n.rstrip(":") in ("horario", "horarios"):
                continue
            if re.match(r"horarios?:", n):
                l = l.split(":", 1)[1].strip()
            if l:
                ultimo["clases"].append(l)

    fecha_gral = primera_fecha or fecha_titulo
    resultado["fecha_gral"] = fecha_gral.isoformat() if fecha_gral else None
    resultado["ordinal"] = ordinal
    for it in items:
        if it["fecha"] is None:
            it["fecha"] = resultado["fecha_gral"]
    resultado["todos"] = items
    resultado["items"] = [i for i in items if i["buscada"]]
    if coincide and not resultado["items"]:
        resultado["detalle"] = [l for l in cuerpo if materia_de(normalizar(l), materias)][:6]
    if not items:  # publicación sin estructura: guardo un extracto para que el buscador la encuentre igual
        resultado["texto_corto"] = " ".join(l for l in cuerpo if l != titulo)[:500]
    return resultado


def analizar_soup(soup, titulo, fecha_pub, materias) -> dict:
    h1 = soup.find("h1")
    if h1:
        lineas, adjuntos = extraer_lineas(h1), contar_adjuntos(h1)
    else:
        lineas = [limpiar_linea(l) for l in soup.get_text("\n").split("\n") if limpiar_linea(l)]
        adjuntos = 0
    res = analizar_texto(lineas, titulo, fecha_pub, materias)
    res["adjuntos"] = adjuntos
    meta = soup.find("meta", attrs={"property": "article:modified_time"})
    res["modificado"] = (meta.get("content") or "") if meta else ""
    return res


def analizar_publicacion(url, titulo, fecha_pub, materias):
    soup = descargar(url)
    if soup is None:
        return None
    return analizar_soup(soup, titulo, fecha_pub, materias)


def aplicar_filtros(titulo, items, cfg):
    f, t = cfg["filtros"], normalizar(titulo)
    inc = [normalizar(x) for x in f.get("escuelas_incluir", []) if x]
    exc = [normalizar(x) for x in f.get("escuelas_excluir", []) if x]
    if inc and not any(x in t for x in inc):
        return False, items
    if any(x in t for x in exc):
        return False, items
    if not items:
        return True, items
    turnos = [normalizar(x)[:4] for x in f.get("turnos", []) if x]
    minimo = f.get("horas_minimas") or 0
    res = []
    for it in items:
        if turnos and it.get("turno") and not any(normalizar(it["turno"]).startswith(x) for x in turnos):
            continue
        if minimo and it.get("hs") and it["hs"] < minimo:
            continue
        res.append(it)
    return bool(res), res


def calcular_grupo(titulo, items, detalle) -> str:
    """Identifica 'el mismo concurso' (misma escuela y mismos espacios) para detectar 2.as convocatorias."""
    base = normalizar(re.sub(r"\s+", " ", titulo))
    if items:
        firma = sorted((i["materia"], i["curso"], i["division"], str(i["hs"]), i["turno"]) for i in items)
    else:
        firma = sorted(normalizar(d) for d in detalle)
    return hashlib.sha1((base + "|" + repr(firma)).encode("utf-8")).hexdigest()[:16]


# ----------------------------------------------------------------------------
# FORMATO DE MENSAJES
# ----------------------------------------------------------------------------
def agrupar(e: dict) -> dict:
    g = {}
    for it in e.get("items", []):
        g.setdefault((it.get("fecha"), it.get("hora")), []).append(it)
    if not g:
        for f in e.get("fechas") or [None]:
            g[(f, None)] = []
    return g


def resumen(it: dict) -> str:
    curso = it.get("curso") or ""
    if it.get("division"):
        curso = (curso + f" “{it['division']}”").strip()
    partes = [
        it.get("materia", ""),
        f"{it['hs']} hs." if it.get("hs") else "",
        curso,
        f"Turno {it['turno']}" if it.get("turno") else "",
        (it.get("caracter") or "").capitalize(),
    ]
    return " · ".join(p for p in partes if p)


def formatear(url: str, e: dict) -> str:
    L = [f"📐 {e['titulo']}"]
    if e.get("ordinal"):
        L.append(f"   🔁 {e['ordinal'].capitalize()}")
    for (f, h), its in agrupar(e).items():
        L.append(f"   🗓 {fecha_larga(f)}" + (f" · {h} hs." if h else ""))
        for it in its:
            L.append(f"      • {resumen(it)}")
            if it.get("clases"):
                L.append(f"        Clases: {' | '.join(it['clases'])}")
        if not its:
            for d in e.get("detalle", []):
                L.append(f"      • {d}")
    if e.get("lugar"):
        L.append(f"   📍 {e['lugar']}")
    L.append(f"   Publicado: {e.get('fecha_pub', '')}")
    L.append(f"   {url}")
    return "\n".join(L)


def mencion() -> str:
    return f"@{GITHUB_USUARIO} " if GITHUB_USUARIO else ""


# ----------------------------------------------------------------------------
# CANALES DE AVISO
# ----------------------------------------------------------------------------
def gh(metodo: str, ruta: str, **kw):
    if not (GITHUB_TOKEN and GITHUB_REPO):
        return None
    try:
        r = requests.request(
            metodo,
            f"https://api.github.com/repos/{GITHUB_REPO}{ruta}",
            headers={"Authorization": f"Bearer {GITHUB_TOKEN}", "Accept": "application/vnd.github+json"},
            timeout=20,
            **kw,
        )
        if r.status_code >= 300:
            print(f"  [!] GitHub {metodo} {ruta} falló ({r.status_code}): {r.text[:200]}")
            return None
        return r.json() if r.text else {}
    except requests.RequestException as e:
        print(f"  [!] Error hablando con GitHub: {e}")
        return None


def crear_issue(titulo: str, cuerpo: str):
    r = gh("POST", "/issues", json={"title": titulo, "body": cuerpo})
    return r.get("number") if r else None


def comentar(numero: int, texto: str) -> None:
    gh("POST", f"/issues/{numero}/comments", json={"body": texto})


def cerrar_issue(numero: int, motivo: str = "completed") -> None:
    gh("PATCH", f"/issues/{numero}", json={"state": "closed", "state_reason": motivo})


def enviar_email(asunto: str, cuerpo: str) -> None:
    if not (EMAIL_USUARIO and EMAIL_CLAVE and EMAIL_DESTINO):
        return
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = asunto, EMAIL_USUARIO, EMAIL_DESTINO
    msg.set_content(cuerpo)
    try:
        with smtplib.SMTP_SSL(SMTP_SERVIDOR, 465, context=ssl.create_default_context()) as srv:
            srv.login(EMAIL_USUARIO, EMAIL_CLAVE)
            srv.send_message(msg)
    except (smtplib.SMTPException, OSError) as e:
        print(f"  [!] No pude enviar el email: {e}")


def enviar_telegram(texto: str) -> None:
    if not (TELEGRAM_TOKEN and TELEGRAM_CHAT_ID):
        return
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": texto[:4000], "disable_web_page_preview": True},
            timeout=20,
        )
    except requests.RequestException as e:
        print(f"  [!] No pude enviar a Telegram: {e}")


def enviar_ntfy(titulo: str, mensaje: str, prioridad: int = 3, click: str = "", tags=None) -> bool:
    """Notificación push vía ntfy. Se publica por JSON a la raíz del servidor, así el nombre
    del canal NUNCA aparece en una URL ni en los logs (que en un repo público son visibles)."""
    if not NTFY_TOPIC:
        return False
    payload = {"topic": NTFY_TOPIC, "title": titulo[:200], "message": (mensaje or titulo)[:3500], "priority": prioridad}
    if tags:
        payload["tags"] = tags
    if click.startswith(("http://", "https://")):
        payload["click"] = click
    try:
        r = requests.post(NTFY_SERVIDOR, json=payload, timeout=20)
        if r.status_code >= 300:
            print(f"  [!] ntfy respondió {r.status_code}"
                  + (" (el nombre del canal no es válido: solo letras sin tildes, números, - y _, hasta 64 caracteres)" if r.status_code == 400 else ""))
            return False
        return True
    except requests.RequestException:
        print("  [!] No pude conectar con ntfy.")
        return False


def en_silencio(cfg: dict, ahora_dt: datetime) -> bool:
    c = cfg.get("ntfy", {})
    d, h = c.get("silencio_desde", 23), c.get("silencio_hasta", 7)
    if d == h:
        return False
    return (ahora_dt.hour >= d or ahora_dt.hour < h) if d > h else (d <= ahora_dt.hour < h)


def prioridad_ntfy(base: int, cfg: dict, ahora_dt: datetime) -> int:
    """De noche, lo que no es urgente (prioridad < 5) llega en silencio (prioridad 2)."""
    return 2 if base < 5 and en_silencio(cfg, ahora_dt) else base


def prioridad_por_fecha(e: dict, cfg: dict, ahora_dt: datetime) -> int:
    hoy = ahora_dt.date()
    futuras = [date.fromisoformat(f) for f in (e.get("fechas") or []) if f and date.fromisoformat(f) >= hoy]
    if not futuras:
        return 3
    dias = (min(futuras) - hoy).days
    u = cfg.get("ntfy", {}).get("urgente_dias", 1)
    return 5 if dias <= u else (4 if dias <= u + 2 else 3)


def texto_ntfy(url: str, e: dict):
    grupos = list(agrupar(e).items())
    cuando = ""
    if grupos and grupos[0][0][0]:
        (f, h), _ = grupos[0]
        d = date.fromisoformat(f)
        cuando = f"{DIAS[d.weekday()][:3]} {d.strftime('%d/%m')}" + (f" {h}" if h else "")
    titulo = f"📐 {e['titulo']}" + (f" · {cuando}" if cuando else "")
    L = []
    if e.get("ordinal"):
        L.append(e["ordinal"].capitalize())
    for _k, its in grupos:
        L += [resumen(i) for i in its[:4]]
    if not any(grupos[i][1] for i in range(len(grupos))):
        L += e.get("detalle", [])[:3]
    if e.get("lugar"):
        L.append("📍 " + e["lugar"])
    return titulo, "\n".join(L) or e["titulo"]


def avisar_ntfy_concurso(url: str, e: dict, cfg: dict, ahora_dt: datetime, prefijo: str = "", prioridad=None, tags=None) -> None:
    titulo, cuerpo = texto_ntfy(url, e)
    if prefijo:
        titulo = titulo.replace("📐 ", "", 1)  # el prefijo ya lleva su propio ícono
    base = prioridad if prioridad is not None else prioridad_por_fecha(e, cfg, ahora_dt)
    enviar_ntfy(prefijo + titulo, cuerpo, prioridad_ntfy(base, cfg, ahora_dt), click=url, tags=tags or ["triangular_ruler"])


def notificar_texto(asunto: str, texto: str, prioridad: int = 2, tags=None) -> None:
    enviar_email(asunto, texto)
    enviar_telegram(f"{asunto}\n\n{texto}")
    enviar_ntfy(asunto, texto, prioridad, tags=tags or ["warning"])


def ventana_windows(texto: str) -> None:
    if sys.platform != "win32":
        return
    try:
        import ctypes

        ctypes.windll.user32.MessageBoxW(0, texto[:900], "Concursos", 0x40 | 0x1000)
    except Exception:
        pass


# ----------------------------------------------------------------------------
# HISTORIAL Y SALUD
# ----------------------------------------------------------------------------
def cargar_historial() -> dict:
    vacio = {
        "version": VERSION_DATOS,
        "estado": {"fallas": 0, "alertado": False, "issue_alerta": None},
        "entradas": {},
    }
    if ARCHIVO_HISTORIAL.exists():
        try:
            d = json.loads(ARCHIVO_HISTORIAL.read_text(encoding="utf-8"))
            if isinstance(d, dict) and d.get("version") in (2, VERSION_DATOS):
                d["version"] = VERSION_DATOS  # la v2 se migra sola (completa datos sin re-avisar)
                d.setdefault("estado", vacio["estado"])
                d.setdefault("entradas", {})
                return d
            print("Historial de una versión anterior: empiezo de cero.")
        except json.JSONDecodeError:
            pass
    return vacio


def guardar_historial(d: dict) -> None:
    ARCHIVO_HISTORIAL.write_text(json.dumps(d, ensure_ascii=False, indent=1), encoding="utf-8")


def revisar_salud(estado: dict, cfg: dict, cantidad: int) -> None:
    umbral = cfg.get("alerta_si_falla_revisiones", 3)
    if cantidad == 0:
        estado["fallas"] = estado.get("fallas", 0) + 1
        print(f"[!] No encontré publicaciones ({estado['fallas']} revisiones seguidas).")
        if umbral and estado["fallas"] >= umbral and not estado.get("alertado"):
            texto = (
                f"Hace {estado['fallas']} revisiones seguidas que el buscador no encuentra ninguna "
                "publicación en el listado del CGE. Puede ser que el sitio esté caído o que haya "
                "cambiado su diseño. Revisá el listado a mano y, si es el diseño, hay que ajustar el script."
            )
            estado["issue_alerta"] = crear_issue("⚠️ El buscador no puede leer la página del CGE", mencion() + texto)
            estado["alertado"] = True
            notificar_texto("⚠️ El buscador no puede leer la página del CGE", texto, 2, ["warning"])
    else:
        if estado.get("alertado"):
            if estado.get("issue_alerta"):
                comentar(estado["issue_alerta"], mencion() + "✅ Volvió a funcionar.")
                cerrar_issue(estado["issue_alerta"])
            notificar_texto("✅ El buscador volvió a funcionar", "Ya puedo leer de nuevo el listado del CGE.", 2, ["white_check_mark"])
        estado.update(fallas=0, alertado=False, issue_alerta=None)


# ----------------------------------------------------------------------------
# LISTADOS
# ----------------------------------------------------------------------------
def obtener_publicaciones(cfg: dict) -> list:
    """[(titulo, url, fecha_publicación, fuente)], más nuevas primero."""
    resultado, vistas = [], set()
    for fuente in cfg["fuentes"]:
        for n in range(1, int(cfg.get("paginas", 2)) + 1):
            base = fuente["url"]
            url = base if n == 1 else f"{base}{'&' if '?' in base else '?'}paged={n}"
            soup = descargar(url)
            if soup is None:
                continue
            for h3 in soup.find_all("h3"):
                a = h3.find("a", href=True)
                if not a or a["href"] in vistas or not re.search(r"/\d{4}/\d{2}/", a["href"]):
                    continue
                vistas.add(a["href"])
                previo = h3.find_previous(string=re.compile(r"^\s*\d{2}/\d{2}/\d{4}\s*$"))
                resultado.append((a.get_text(strip=True), a["href"], previo.strip() if previo else "", fuente.get("nombre", "")))
            time.sleep(PAUSA_ENTRE_PEDIDOS)
    return resultado


# ----------------------------------------------------------------------------
# AVISOS, RECORDATORIOS Y CIERRE
# ----------------------------------------------------------------------------
def issue_de_grupo(entradas: dict, grupo: str, excepto: str):
    for u, e in entradas.items():
        if u != excepto and e.get("grupo") == grupo and e.get("issue") and e.get("issue_abierto") and not e.get("vencido"):
            return e["issue"]
    return None


def notificar_nuevo(entradas: dict, url: str, e: dict) -> None:
    texto = formatear(url, e)
    num = issue_de_grupo(entradas, e["grupo"], url)
    if num:
        etiqueta = e.get("ordinal") or "actualización"
        comentar(num, f"{mencion()}🔁 Nueva publicación del mismo concurso ({etiqueta}):\n\n{texto}")
        e["issue"], e["issue_abierto"] = num, True
        return
    titulo = f"📐 {e['titulo']}" + (f" ({e['ordinal']})" if e.get("ordinal") else "")
    n = crear_issue(titulo, f"{mencion()}hay un concurso nuevo:\n\n{texto}")
    if n:
        e["issue"], e["issue_abierto"] = n, True


def notificar_revisar(url: str, e: dict) -> None:
    cuerpo = (
        f"{mencion()}esta publicación no tiene texto legible (parece una imagen o un PDF), "
        f"así que no pude saber si es de tus materias. Revisala a mano:\n\n{e['titulo']}\n{url}"
    )
    n = crear_issue(f"👀 Revisar a mano: {e['titulo']}", cuerpo)
    if n:
        e["issue"], e["issue_abierto"] = n, True


def buscar_originales(entradas: dict, url_c: str) -> list:
    """Concursos ya registrados a los que se refiere un aviso de desconvocatoria (misma escuela, mismo día, mismos espacios)."""
    c = entradas[url_c]
    t = normalizar(limpiar_titulo(c["titulo"]))
    fechas_c = set(c.get("fechas") or [])
    cands = [
        (u, e) for u, e in entradas.items()
        if u != url_c and e.get("relevante") and not e.get("desconvocado") and not e.get("cancelacion")
        and normalizar(limpiar_titulo(e["titulo"])) == t
    ]
    if fechas_c:
        cands = [x for x in cands if fechas_c & set(x[1].get("fechas") or [])]
    if not cands:
        return []
    exactos = [x for x in cands if x[1].get("grupo") and x[1]["grupo"] == c.get("grupo")]
    if exactos:
        return exactos

    def claves(e):
        return {(i.get("curso"), i.get("division"), i.get("turno")) for i in e.get("items", [])}

    con_espacios = [x for x in cands if claves(x[1]) & claves(c)]
    if con_espacios:
        return con_espacios
    return cands if len(cands) == 1 else []


def _cerrar_issue_de(entradas: dict, num, motivo: str) -> None:
    cerrar_issue(num, motivo)
    for x in entradas.values():
        if x.get("issue") == num:
            x["issue_abierto"] = False


def _avisar_cambio(entradas, url, e, url_click, cfg, ahora_dt, titulo_issue, texto, prefijo, prioridad_min, tags, cerrar=False) -> None:
    """Comenta en el Issue del concurso (o abre uno) y avisa por email, Telegram y ntfy."""
    num = e.get("issue")
    if num:
        comentar(num, mencion() + texto)
    else:
        num = crear_issue(titulo_issue, mencion() + texto)
        if num:
            e["issue"], e["issue_abierto"] = num, True
    if num and cerrar:
        _cerrar_issue_de(entradas, num, "not_planned")
    enviar_email(titulo_issue, texto)
    enviar_telegram(texto)
    avisar_ntfy_concurso(url_click, e, cfg, ahora_dt, prefijo=prefijo, tags=tags,
                         prioridad=max(prioridad_por_fecha(e, cfg, ahora_dt), prioridad_min))


def alertar_desconvocatoria(entradas, url, e, url_aviso, cfg, ahora_dt, sin_original=False) -> None:
    nota = "\n(No tenía registrado el concurso original: este es el aviso del CGE.)" if sin_original else ""
    texto = f"❌ DESCONVOCADO\n\n{formatear(url, e)}{nota}\n\nAviso de desconvocatoria: {url_aviso}"
    _avisar_cambio(entradas, url, e, url_aviso, cfg, ahora_dt, f"❌ DESCONVOCADO: {e['titulo']}", texto,
                   "❌ DESCONVOCADO · ", 4, ["x"], cerrar=True)


def alertar_modificacion(entradas, url, e, cfg, ahora_dt) -> None:
    texto = f"✏️ El CGE modificó esta publicación. Datos actuales:\n\n{formatear(url, e)}"
    _avisar_cambio(entradas, url, e, url, cfg, ahora_dt, f"✏️ Modificado: {e['titulo']}", texto,
                   "✏️ MODIFICADO · ", 4, ["pencil2"])


def alertar_eliminada(entradas, url, e, cfg, ahora_dt) -> None:
    texto = ("⚠️ Esta publicación ya no existe en el CGE (la borraron o la movieron). Puede indicar una "
             "desconvocatoria o un error: verificá en el sitio.\n\n" + formatear(url, e))
    _avisar_cambio(entradas, url, e, url, cfg, ahora_dt, f"⚠️ Ya no está en el CGE: {e['titulo']}", texto,
                   "⚠️ YA NO ESTÁ EN EL CGE · ", 4, ["warning"])


def procesar_cancelacion(entradas: dict, url_c: str, cfg: dict, ahora_dt: datetime) -> None:
    """Un aviso de desconvocatoria nuevo: lo asocia al concurso original y te avisa."""
    c = entradas[url_c]
    originales = buscar_originales(entradas, url_c)
    if originales:
        c["desconvoca_a"] = originales[0][0]
        for u, o in originales:
            o["desconvocado"] = {"url": url_c, "visto": c["visto"]}
            if o.get("avisado", True) or o.get("issue"):  # si nunca te avisé de ese concurso, no hace falta
                alertar_desconvocatoria(entradas, u, o, url_c, cfg, ahora_dt)
        return
    if not c.get("cancel_coincide"):
        return  # no es de tus materias
    fechas = [date.fromisoformat(f) for f in c.get("fechas", []) if f]
    if fechas and max(fechas) < ahora_dt.date():
        return  # ya pasó: nada que avisar
    c["avisado"] = True
    alertar_desconvocatoria(entradas, url_c, c, url_c, cfg, ahora_dt, sin_original=True)


def firma_concurso(items, lugar, fechas) -> str:
    return json.dumps({"i": items, "l": lugar, "f": fechas}, sort_keys=True, ensure_ascii=False)


def revisar_cambios(entradas: dict, pubs: list, cfg: dict, materias, ahora_dt: datetime, excluir: set) -> None:
    """Vuelve a leer los concursos vigentes: detecta si los editaron (fecha, espacios, 'DESCONVOCA') o si los borraron."""
    titulos = {u: t for t, u, _f, _s in pubs}
    revisadas = 0
    for url, e in list(entradas.items()):
        if (url in excluir or not e.get("relevante") or e.get("vencido") or e.get("desconvocado")
                or e.get("cancelacion") or es_vencido(e, ahora_dt)):
            continue
        if revisadas >= 40:
            break
        revisadas += 1
        soup = descargar(url)
        estado_http = getattr(descargar, "ultimo_status", None)
        time.sleep(PAUSA_ENTRE_PEDIDOS)
        if soup is None:
            if estado_http in (404, 410) and not e.get("eliminada"):
                e["eliminada"] = True
                alertar_eliminada(entradas, url, e, cfg, ahora_dt)
            continue
        h1 = soup.find("h1")
        ref = normalizar(limpiar_titulo(e["titulo"]))[:25]
        if h1 is None or ref not in normalizar(h1.get_text()):
            continue  # no parece la publicación (página de error/mantenimiento): no saco conclusiones
        e.pop("eliminada", None)
        titulo_nuevo = titulos.get(url) or limpiar_linea(h1.get_text()) or e["titulo"]
        res = analizar_soup(soup, titulo_nuevo, parse_dmy(e.get("fecha_pub", "")) or ahora_dt.date(), materias)
        if res["cancelacion"]:
            e["desconvocado"] = {"url": url, "visto": ahora_dt.isoformat(timespec="minutes")}
            e["titulo"] = titulo_nuevo
            if e.get("avisado", True) or e.get("issue"):
                alertar_desconvocatoria(entradas, url, e, url, cfg, ahora_dt)
            continue
        ok, items = aplicar_filtros(titulo_nuevo, res["items"], cfg) if res["coincide"] else (False, [])
        todos = res["todos"]
        fechas = sorted({i["fecha"] for i in todos if i.get("fecha")}) or ([res["fecha_gral"]] if res["fecha_gral"] else [])
        firma = firma_concurso(items if ok else [], res["lugar"], fechas)
        previa = e.get("firma")
        e.update(items=items if ok else [], todos=todos, texto=res["texto_corto"], lugar=res["lugar"],
                 ordinal=res["ordinal"], fechas=fechas, detalle=res["detalle"] if ok else [],
                 titulo=titulo_nuevo, modificado=res.get("modificado", ""), firma=firma)
        if previa is not None and previa != firma:
            alertar_modificacion(entradas, url, e, cfg, ahora_dt)


def recordatorios(entradas: dict, cfg: dict, ahora_dt: datetime) -> list:
    hoy, cfg_r, enviados = ahora_dt.date(), cfg["recordatorios"], []
    for url, e in entradas.items():
        if not e.get("relevante") or e.get("vencido") or e.get("desconvocado") or e.get("eliminada"):
            continue
        visto = datetime.fromisoformat(e["visto"]).date() if e.get("visto") else None
        if visto == hoy:
            continue  # ya lo avisé hoy como nuevo
        rec = e.setdefault("recordados", [])
        for (f, h), _its in agrupar(e).items():
            if not f:
                continue
            d, tipo = date.fromisoformat(f), None
            if cfg_r.get("el_dia") and d == hoy and ahora_dt.hour >= 7:
                tipo = "dia"
                if h and ahora_dt.strftime("%H:%M") > h:
                    continue  # el concurso ya pasó
            elif cfg_r.get("dia_antes") and d == hoy + timedelta(days=1) and ahora_dt.hour >= 19:
                tipo = "antes"
            if not tipo:
                continue
            clave = f"{f}|{h}|{tipo}"
            if clave in rec:
                continue
            rec.append(clave)
            cab = "⏰ HOY" if tipo == "dia" else "📅 MAÑANA"
            texto = f"{cab} hay concurso:\n\n{formatear(url, e)}"
            if e.get("issue"):
                comentar(e["issue"], mencion() + texto)
            else:
                n = crear_issue(f"{cab}: {e['titulo']}", mencion() + texto)
                if n:
                    e["issue"], e["issue_abierto"] = n, True
            enviados.append((texto, url, tipo))
    return enviados


def es_vencido(e: dict, ahora_dt: datetime) -> bool:
    hoy = ahora_dt.date()
    fechas = [date.fromisoformat(f) for f in e.get("fechas", []) if f]
    if fechas:
        return max(fechas) < hoy
    visto = datetime.fromisoformat(e["visto"]) if e.get("visto") else ahora_dt
    return visto + timedelta(days=7 if e.get("revisar") else 14) < ahora_dt


def cerrar_vencidos(entradas: dict, cfg: dict, ahora_dt: datetime) -> None:
    for e in entradas.values():
        if e.get("vencido") or not (e.get("relevante") or e.get("revisar") or e.get("cancelacion")):
            continue
        if es_vencido(e, ahora_dt):
            e["vencido"] = True
    for e in entradas.values():
        if e.get("vencido") and e.get("issue") and e.get("issue_abierto") and cfg.get("cerrar_issues_vencidos", True):
            # Solo cierro el Issue cuando TODAS las publicaciones que lo comparten están vencidas
            comparten = [x for x in entradas.values() if x.get("issue") == e["issue"]]
            if all(x.get("vencido") for x in comparten):
                cerrar_issue(e["issue"])
                for x in comparten:
                    x["issue_abierto"] = False


# ----------------------------------------------------------------------------
# CALENDARIO (.ics) Y PÁGINA
# ----------------------------------------------------------------------------
def _ics_esc(t: str) -> str:
    return t.replace("\\", "\\\\").replace(";", "\\;").replace(",", "\\,").replace("\n", "\\n")


def _plegar(linea: str) -> str:
    data, partes, limite = linea.encode("utf-8"), [], 75
    while len(data) > limite:
        corte = limite
        while corte > 0 and (data[corte] & 0xC0) == 0x80:
            corte -= 1
        partes.append(data[:corte].decode("utf-8"))
        data, limite = data[corte:], 74
    partes.append(data.decode("utf-8"))
    return "\r\n ".join(partes)


def _sello(e: dict) -> str:
    """DTSTAMP estable (momento en que vi el concurso), así el archivo no cambia en cada revisión."""
    try:
        return datetime.fromisoformat(e["visto"]).astimezone(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    except (KeyError, ValueError):
        return "20260101T000000Z"


def generar_calendario(entradas: dict, ahora_dt: datetime) -> None:
    L = [
        "BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//Concursos CGE//ES", "CALSCALE:GREGORIAN",
        "METHOD:PUBLISH", "X-WR-CALNAME:Concursos docentes - CGE",
        "X-WR-TIMEZONE:America/Argentina/Buenos_Aires",
        "REFRESH-INTERVAL;VALUE=DURATION:PT1H", "X-PUBLISHED-TTL:PT1H",
    ]
    for url, e in entradas.items():
        if not e.get("relevante") or e.get("vencido") or e.get("desconvocado") or e.get("eliminada"):
            continue
        for (f, h), its in agrupar(e).items():
            if not f:
                continue
            d = date.fromisoformat(f)
            uid = hashlib.sha1(f"{url}|{f}|{h}".encode()).hexdigest()[:24] + "@concursos-cge"
            materias = sorted({i["materia"] for i in its}) or e.get("materias") or ["concurso"]
            desc = "\n".join(
                [resumen(i) + (f" ({' | '.join(i['clases'])})" if i.get("clases") else "") for i in its]
                + [url]
            )
            L += ["BEGIN:VEVENT", f"UID:{uid}", f"DTSTAMP:{_sello(e)}"]
            if h:
                local = datetime.combine(d, datetime.strptime(h, "%H:%M").time())
                ini, fin = local + timedelta(hours=3), local + timedelta(hours=4)  # ART -> UTC
                L += [f"DTSTART:{ini.strftime('%Y%m%dT%H%M%SZ')}", f"DTEND:{fin.strftime('%Y%m%dT%H%M%SZ')}"]
                alarmas = ["-PT1H", "-P1D"]
            else:
                L += [f"DTSTART;VALUE=DATE:{d.strftime('%Y%m%d')}", f"DTEND;VALUE=DATE:{(d + timedelta(days=1)).strftime('%Y%m%d')}"]
                alarmas = ["PT7H"]
            L.append("SUMMARY:" + _ics_esc(f"Concurso {', '.join(materias)} - {e['titulo']}"))
            L.append("DESCRIPTION:" + _ics_esc(desc))
            if e.get("lugar"):
                L.append("LOCATION:" + _ics_esc(e["lugar"]))
            L.append("URL:" + url)
            for a in alarmas:
                L += ["BEGIN:VALARM", "ACTION:DISPLAY", "DESCRIPTION:Concurso", f"TRIGGER:{a}", "END:VALARM"]
            L.append("END:VEVENT")
    L.append("END:VCALENDAR")
    contenido = ("\r\n".join(_plegar(l) for l in L) + "\r\n").encode("utf-8")
    escribir_estable(ARCHIVO_CALENDARIO, contenido, binario=True)


_RE_MARCA = re.compile(r"<!--ACT-->.*?<!--/ACT-->", re.S)


def escribir_estable(ruta: Path, contenido, binario: bool = False) -> None:
    """Escribe solo si cambió (ignorando la hora de 'actualizado'), para no llenar el repo de commits."""
    ruta.parent.mkdir(exist_ok=True)
    if ruta.exists():
        if binario:
            if ruta.read_bytes() == contenido:
                return
        else:
            if _RE_MARCA.sub("", ruta.read_text(encoding="utf-8")) == _RE_MARCA.sub("", contenido):
                return
    if binario:
        ruta.write_bytes(contenido)
    else:
        ruta.write_text(contenido, encoding="utf-8")


def datos_busqueda(entradas: dict, ahora_dt: datetime) -> list:
    """Datos compactos para el buscador de la app (todas las materias)."""
    hoy, salida = ahora_dt.date(), []
    for url, e in entradas.items():
        if e.get("desconvoca_a"):
            continue  # el aviso de baja se muestra como etiqueta del concurso original
        fechas = [f for f in (e.get("fechas") or []) if f]
        venc = bool(e.get("vencido")) or es_vencido(e, ahora_dt)
        if venc and fechas and max(fechas) < (hoy - timedelta(days=60)).isoformat():
            continue
        its = e.get("todos") or e.get("items") or []
        salida.append({
            "t": e["titulo"], "u": url, "p": e.get("fecha_pub", ""), "v": venc,
            "r": bool(e.get("revisar")), "k": bool(e.get("relevante")),
            "d": bool(e.get("desconvocado") or e.get("cancelacion")), "el": bool(e.get("eliminada")),
            "du": (e.get("desconvocado") or {}).get("url", ""),
            "o": e.get("ordinal", ""), "l": e.get("lugar", ""), "x": e.get("texto", ""), "f": fechas,
            "i": [
                {
                    "m": i["materia"], "hs": i.get("hs"), "c": i.get("curso", ""), "d": i.get("division", ""),
                    "tu": i.get("turno", ""), "ca": i.get("caracter", ""), "f": i.get("fecha"),
                    "h": i.get("hora"), "cl": i.get("clases", []), "b": bool(i.get("buscada", True)),
                }
                for i in its
            ],
        })
    return salida


PLANTILLA_APP = r"""<!doctype html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Concursos docentes - CGE</title>
<meta name="theme-color" content="#1d4ed8">
<link rel="manifest" href="manifest.webmanifest">
<link rel="icon" href="icon-192.png">
<link rel="apple-touch-icon" href="icon-192.png">
<style>
:root{--bg:#fff;--fg:#1a1a1a;--card:#f3f4f6;--link:#1d4ed8;--mut:#6b7280;--hoy:#dc2626;--man:#d97706;--bord:#d1d5db}
@media(prefers-color-scheme:dark){:root{--bg:#0f1115;--fg:#eee;--card:#1c1f26;--link:#7aa7ff;--mut:#9ca3af;--hoy:#f87171;--man:#fbbf24;--bord:#374151}}
*{box-sizing:border-box}
body{font-family:system-ui,sans-serif;background:var(--bg);color:var(--fg);max-width:720px;margin:0 auto;padding:16px;padding-top:calc(16px + env(safe-area-inset-top,0px));padding-bottom:calc(24px + env(safe-area-inset-bottom,0px))}
h1{font-size:1.35rem;margin:0 0 2px} small,.mut{color:var(--mut)} a{color:var(--link)}
.buscador{display:flex;gap:8px;margin:14px 0 8px}
#q{flex:1;min-width:0;padding:13px 14px;border-radius:12px;border:2px solid var(--link);background:var(--bg);color:var(--fg);font-size:1.05rem}
button{font:inherit;cursor:pointer}
#guardar{width:50px;border-radius:12px;border:1px solid var(--bord);background:var(--card);color:var(--fg);font-size:1.3rem}
.chips{display:flex;flex-wrap:wrap;gap:6px;margin:6px 0}
.chip{border:1px solid var(--bord);background:var(--card);color:var(--fg);border-radius:99px;padding:6px 12px;font-size:.88rem}
.chip.g{border-color:var(--link)}
.chk{display:block;margin:8px 0;color:var(--mut);font-size:.92rem}
.card{background:var(--card);border-radius:12px;padding:12px 16px;margin:10px 0}
.card.v{opacity:.6} .card h3{font-size:1.02rem;margin:0 0 6px}
.badges{margin-bottom:2px}.b{display:inline-block;font-size:.72rem;font-weight:700;padding:2px 8px;border-radius:99px;margin:0 6px 2px 0;color:#fff;background:var(--mut)}
.b.hoy,.b.des{background:var(--hoy)}.b.man{background:var(--man);color:#000}.b.mia{background:var(--link)}.b.rev{background:#7c3aed}
.card.dc{opacity:.78;border-left:4px solid var(--hoy)}.card.dc h3 a{text-decoration:line-through}
.f{margin:8px 0 0;font-weight:600} ul{padding-left:18px;margin:4px 0} li{margin:4px 0}
details summary{cursor:pointer;color:var(--mut);margin-top:6px;font-size:.9rem}
.cal,.inst{display:inline-block;margin:8px 8px 0 0;padding:9px 13px;border-radius:10px;background:var(--link);color:#fff;text-decoration:none;font-size:.9rem;border:0}
.inst[hidden]{display:none}
</style></head><body>
<h1>📐 Concursos docentes</h1>
<small>Datos actualizados: <!--ACT-->__ACT__<!--/ACT--> (hora Argentina) · revisa el CGE cada 30 min</small>
<div class="buscador">
  <input id="q" type="search" placeholder="¿Qué materia buscás? Ej: matemática" autocomplete="off" enterkeyhint="search">
  <button id="guardar" title="Guardar esta búsqueda" aria-label="Guardar esta búsqueda">☆</button>
</div>
<div id="guardadas" class="chips"></div>
<div id="sugeridas" class="chips"></div>
<label class="chk"><input type="checkbox" id="venc"> Incluir vencidos</label>
<p id="cont" class="mut"></p>
<div id="res"></div>
<p><a class="cal" href="calendario.ics">📅 Calendario</a><button id="instalar" class="inst" hidden>📲 Instalar app</button></p>
<p id="ios" class="mut" hidden>En iPhone: tocá Compartir y luego «Agregar a pantalla de inicio» para instalarla.</p>
<script>
const DATA = __DATA__;
//#LOGICA
const DIAS=["domingo","lunes","martes","miércoles","jueves","viernes","sábado"];
const norm=s=>(s||"").normalize("NFD").replace(/[\u0300-\u036f]/g,"").toLowerCase();
const iso=d=>d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0")+"-"+String(d.getDate()).padStart(2,"0");
const hoyISO=(typeof HOY_OVERRIDE!=="undefined")?HOY_OVERRIDE:iso(new Date());
const mananaISO=(function(){const p=hoyISO.split("-").map(Number);return iso(new Date(p[0],p[1]-1,p[2]+1));})();
function fechaLarga(f){
  if(!f) return "Fecha no detectada";
  const p=f.split("-").map(Number), dt=new Date(p[0],p[1]-1,p[2]);
  return DIAS[dt.getDay()]+" "+String(p[2]).padStart(2,"0")+"/"+String(p[1]).padStart(2,"0")+"/"+p[0];
}
function resumen(i){
  const p=[i.m]; if(i.hs)p.push(i.hs+" hs.");
  let c=i.c||""; if(i.d)c=(c+" “"+i.d+"”").trim(); if(c)p.push(c);
  if(i.tu)p.push("Turno "+i.tu);
  if(i.ca)p.push(i.ca.charAt(0).toUpperCase()+i.ca.slice(1));
  return p.join(" · ");
}
function textoItem(i){return norm([i.m,i.hs?i.hs+" hs":"",i.c,i.d,i.tu,i.ca,(i.cl||[]).join(" ")].join(" "));}
function esVencido(e){
  if(e.v) return true;
  const fs=(e.f||[]).filter(Boolean);
  return fs.length>0 && fs.slice().sort().pop()<hoyISO;
}
function orden(e){
  const fs=(e.f||[]).filter(Boolean).slice().sort();
  if(esVencido(e)) return [2, fs.length?-Date.parse(fs[fs.length-1]):0];
  if(!fs.length) return [1,0];
  const fut=fs.filter(function(f){return f>=hoyISO;});
  return [0, Date.parse(fut.length?fut[0]:fs[fs.length-1])];
}
function buscar(q,conVencidos){
  const tokens=norm(q).split(/\s+/).filter(Boolean), res=[];
  for(const e of DATA){
    if(esVencido(e) && !conVencidos) continue;
    const base=norm(e.t+" "+(e.l||"")+" "+(e.x||""));
    let sel=e.i;
    if(tokens.length){
      if(e.i.length){
        sel=e.i.filter(function(i){const t=textoItem(i);return tokens.every(function(k){return t.includes(k)||base.includes(k);});});
        if(!sel.length) continue;
      } else if(!tokens.every(function(k){return base.includes(k);})) continue;
    }
    res.push({e:e, sel:sel, resto:e.i.filter(function(i){return sel.indexOf(i)<0;})});
  }
  res.sort(function(a,b){const x=orden(a.e),y=orden(b.e);return (x[0]-y[0])||(x[1]-y[1])||a.e.t.localeCompare(b.e.t);});
  return res;
}
function chipsMaterias(){
  const c=new Map();
  for(const e of DATA){ if(esVencido(e)) continue; for(const i of e.i){ const k=norm(i.m); const o=c.get(k)||{n:i.m,c:0}; o.c++; c.set(k,o);} }
  return Array.from(c.values()).sort(function(a,b){return b.c-a.c;}).slice(0,14);
}
//#FIN
(function(){
"use strict";
const $=function(s){return document.querySelector(s);};
const LS={
  get:function(k,d){try{const v=localStorage.getItem(k);return v==null?d:JSON.parse(v);}catch(e){return d;}},
  set:function(k,v){try{localStorage.setItem(k,JSON.stringify(v));}catch(e){}}
};
function el(tag,cls,txt){const e=document.createElement(tag);if(cls)e.className=cls;if(txt!=null)e.textContent=txt;return e;}
let guardadas=LS.get("guardadas",[]);

function tarjeta(r){
  const e=r.e, a=el("article","card"+(esVencido(e)?" v":"")+(e.d?" dc":"")), h=el("h3"), l=el("a",null,e.t);
  if(/^https:\/\/cge\.entrerios\.gov\.ar\//.test(e.u)){l.href=e.u;}
  l.target="_blank"; l.rel="noopener"; h.appendChild(l); a.appendChild(h);
  const bs=el("div","badges"), fs=e.f||[];
  if(e.d) bs.appendChild(el("span","b des","❌ DESCONVOCADO"));
  if(e.el) bs.appendChild(el("span","b rev","⚠️ Ya no está en el CGE"));
  if(!esVencido(e)&&!e.d){ if(fs.indexOf(hoyISO)>=0) bs.appendChild(el("span","b hoy","HOY")); else if(fs.indexOf(mananaISO)>=0) bs.appendChild(el("span","b man","MAÑANA")); }
  if(esVencido(e)) bs.appendChild(el("span","b","Vencido"));
  if(e.o) bs.appendChild(el("span","b",e.o));
  if(e.k) bs.appendChild(el("span","b mia","Tu materia"));
  if(e.r) bs.appendChild(el("span","b rev","Revisar a mano"));
  a.appendChild(bs);
  const g=new Map();
  r.sel.forEach(function(i){const k=(i.f||"")+"|"+(i.h||"");if(!g.has(k))g.set(k,[]);g.get(k).push(i);});
  g.forEach(function(its,k){
    const p=k.split("|");
    a.appendChild(el("p","f","🗓 "+fechaLarga(p[0]||null)+(p[1]?" · "+p[1]+" hs.":"")));
    const ul=el("ul");
    its.forEach(function(i){
      const li=el("li",null,resumen(i));
      if(i.cl&&i.cl.length){li.appendChild(el("br"));li.appendChild(el("small",null,"Clases: "+i.cl.join(" | ")));}
      ul.appendChild(li);
    });
    a.appendChild(ul);
  });
  if(!e.i.length){
    if(fs.length) a.appendChild(el("p","f","🗓 "+fechaLarga(fs[0])));
    if(e.x) a.appendChild(el("p","mut",e.x.slice(0,220)+(e.x.length>220?"…":"")));
  }
  if(r.resto.length){
    const d=el("details"); d.appendChild(el("summary",null,"Otros espacios de esta escuela ("+r.resto.length+")"));
    const ul=el("ul"); r.resto.forEach(function(i){ul.appendChild(el("li",null,resumen(i)));}); d.appendChild(ul); a.appendChild(d);
  }
  if(e.l) a.appendChild(el("p","mut","📍 "+e.l));
  if(e.du&&/^https:\/\/cge\.entrerios\.gov\.ar\//.test(e.du)&&e.du!==e.u){const p=el("p","mut"),x=el("a",null,"Ver el aviso de desconvocatoria");x.href=e.du;x.target="_blank";x.rel="noopener";p.appendChild(x);a.appendChild(p);}
  return a;
}
function chip(txt,cls,fn){const b=el("button","chip "+(cls||""),txt);b.type="button";b.addEventListener("click",fn);return b;}
function poner(q){$("#q").value=q;render();}
function estrella(){
  const q=norm($("#q").value).trim(), esta=guardadas.some(function(x){return norm(x)===q;});
  $("#guardar").textContent=esta?"★":"☆";
}
function chips(){
  const gc=$("#guardadas"); gc.textContent="";
  guardadas.forEach(function(q){gc.appendChild(chip("⭐ "+q,"g",function(){poner(q);}));});
  const sc=$("#sugeridas"); sc.textContent="";
  chipsMaterias().forEach(function(m){sc.appendChild(chip(m.n+" ("+m.c+")","",function(){poner(m.n);}));});
}
function render(){
  const q=$("#q").value, r=buscar(q,$("#venc").checked), cont=$("#cont"), res=$("#res");
  res.textContent="";
  r.slice(0,80).forEach(function(x){res.appendChild(tarjeta(x));});
  cont.textContent=DATA.length===0?"Todavía no hay datos. El robot los carga en su primera revisión.":
    (r.length===0?"No encontré concursos para «"+q+"». Probá con otra palabra o marcá «Incluir vencidos».":
    r.length+" resultado"+(r.length===1?"":"s")+(r.length>80?" (mostrando 80)":""));
  LS.set("ultima",q); estrella();
}
$("#q").addEventListener("input",render);
$("#venc").addEventListener("change",render);
$("#guardar").addEventListener("click",function(){
  const q=$("#q").value.trim(); if(!q)return;
  const n=norm(q), i=guardadas.findIndex(function(x){return norm(x)===n;});
  if(i>=0)guardadas.splice(i,1); else guardadas.push(q);
  LS.set("guardadas",guardadas); chips(); estrella();
});
const inicial=new URLSearchParams(location.search).get("q");
$("#q").value=inicial!=null?inicial:LS.get("ultima","");
chips(); render();

let evInst=null;
window.addEventListener("beforeinstallprompt",function(e){e.preventDefault();evInst=e;$("#instalar").hidden=false;});
$("#instalar").addEventListener("click",function(){ if(!evInst)return; evInst.prompt(); evInst.userChoice.then(function(){evInst=null;$("#instalar").hidden=true;}); });
if(/iphone|ipad/i.test(navigator.userAgent)&&!navigator.standalone){$("#ios").hidden=false;}
if("serviceWorker" in navigator){navigator.serviceWorker.register("sw.js").catch(function(){});}
})();
</script></body></html>"""

MANIFEST = {
    "name": "Concursos docentes - CGE",
    "short_name": "Concursos",
    "description": "Buscador de concursos docentes del CGE Entre Ríos",
    "lang": "es",
    "start_url": "./",
    "scope": "./",
    "display": "standalone",
    "background_color": "#ffffff",
    "theme_color": "#1d4ed8",
    "icons": [
        {"src": "icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any"},
        {"src": "icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any"},
        {"src": "icon-maskable-512.png", "sizes": "512x512", "type": "image/png", "purpose": "maskable"},
    ],
}

SERVICE_WORKER = """// Service worker: guarda la app para que abra rápido y funcione sin internet.
// Con internet siempre intenta traer lo más nuevo primero.
const CACHE = 'concursos-v1';
const BASE = ['./', './index.html', './manifest.webmanifest', './icon-192.png', './icon-512.png'];
self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(BASE)).then(() => self.skipWaiting()));
});
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET' || new URL(e.request.url).origin !== location.origin) return;
  e.respondWith(
    fetch(e.request).then(r => {
      if (r.ok) { const copia = r.clone(); caches.open(CACHE).then(c => c.put(e.request, copia)); }
      return r;
    }).catch(() => caches.match(e.request).then(m => m || caches.match('./index.html')))
  );
});
"""


def generar_pagina(entradas: dict, ahora_dt: datetime) -> None:
    """Escribe la app (docs/): buscador, manifiesto, service worker e íconos."""
    datos = json.dumps(datos_busqueda(entradas, ahora_dt), ensure_ascii=False, separators=(",", ":"))
    datos = datos.replace("<", "\\u003c")  # evita que un texto del CGE cierre el <script>
    pagina = PLANTILLA_APP.replace("__ACT__", ahora_dt.strftime("%d/%m/%Y %H:%M")).replace("__DATA__", datos)
    carpeta = ARCHIVO_PAGINA.parent
    escribir_estable(ARCHIVO_PAGINA, pagina)
    escribir_estable(carpeta / "manifest.webmanifest", json.dumps(MANIFEST, ensure_ascii=False, indent=1))
    escribir_estable(carpeta / "sw.js", SERVICE_WORKER)
    for nombre, b64 in ICONOS_B64.items():
        escribir_estable(carpeta / nombre, base64.b64decode(b64), binario=True)


# ----------------------------------------------------------------------------
# PROGRAMA PRINCIPAL
# ----------------------------------------------------------------------------
def buscar(cfg: dict, mostrar_todos: bool = False) -> None:
    ahora_dt = ahora()
    datos = cargar_historial()
    entradas, estado = datos["entradas"], datos["estado"]
    materias = compilar_materias(cfg)
    if not materias:
        print("[!] config.json no tiene materias para buscar.")
        return

    print(f"Avisos de: {', '.join(cfg['materias'])} (el buscador de la app cubre todas las materias)")
    pubs = obtener_publicaciones(cfg)
    print(f"Publicaciones en el listado: {len(pubs)}")
    if NTFY_TOPIC:
        print(f"ntfy: canal configurado ({len(NTFY_TOPIC)} caracteres).")
        prueba_id = cfg.get("ntfy", {}).get("prueba", 1)
        if estado.get("ntfy_prueba") != prueba_id:
            if enviar_ntfy("✅ ntfy configurado", "Si ves este mensaje, los avisos de concursos van a llegar a tu celular.", 3, tags=["white_check_mark"]):
                estado["ntfy_prueba"] = prueba_id
                print("ntfy: el servidor aceptó el mensaje de prueba. Si no te llega al celular, revisá que el nombre "
                      "del canal sea IDÉNTICO en la app y en el Secret (el servidor acepta cualquier nombre).")
            else:
                print("ntfy: el mensaje de prueba NO se pudo enviar; lo reintento en la próxima revisión.")
    else:
        print("ntfy: NO configurado (falta el Secret NTFY_TOPIC, o el buscar.yml no lo está pasando).")
    revisar_salud(estado, cfg, len(pubs))

    nuevos, a_revisar, cancelaciones, nuevas_urls = [], [], [], set()
    for titulo, url, fpub, fuente in reversed(pubs):  # de la más vieja a la más nueva
        existente = entradas.get(url)
        if existente is not None and "todos" in existente:
            continue
        res = analizar_publicacion(url, titulo, parse_dmy(fpub) or ahora_dt.date(), materias)
        time.sleep(PAUSA_ENTRE_PEDIDOS)
        if res is None:
            continue  # error de red: la reintento en la próxima revisión
        todos = res["todos"]
        fechas = sorted({i["fecha"] for i in todos if i.get("fecha")}) or ([res["fecha_gral"]] if res["fecha_gral"] else [])

        if existente is not None:
            # Entrada de una versión anterior: completo los datos del buscador SIN volver a avisar
            existente["todos"], existente["texto"] = todos, res["texto_corto"]
            if not existente.get("fechas"):
                existente["fechas"] = fechas
            continue

        cancel = res["cancelacion"]
        ok, items = res["coincide"] and not cancel, res["items"]
        if ok:
            ok, items = aplicar_filtros(titulo, items, cfg)
        e = {
            "titulo": titulo, "fuente": fuente, "fecha_pub": fpub,
            "visto": ahora_dt.isoformat(timespec="minutes"),
            "relevante": ok, "items": items if ok else [], "todos": todos, "texto": res["texto_corto"],
            "detalle": res["detalle"] if ok else [], "fechas": fechas,
            "materias": res["materias"] if ok else [],
            "lugar": res["lugar"], "ordinal": res["ordinal"],
            "grupo": calcular_grupo(limpiar_titulo(titulo), items, res["detalle"]) if ok else "",
            "issue": None, "issue_abierto": False, "vencido": False, "recordados": [],
            "modificado": res.get("modificado", ""), "avisado": False,
            "firma": firma_concurso(items if ok else [], res["lugar"], fechas),
        }
        if cancel:
            # Aviso de desconvocatoria: NO es un concurso nuevo. Se asocia al original más abajo.
            e.update(cancelacion=True, cancel_coincide=res["coincide"], items=res["items"], materias=res["materias"],
                     grupo=calcular_grupo(limpiar_titulo(titulo), res["items"], res["detalle"]))
            cancelaciones.append(url)
        elif not res["coincide"] and cfg.get("avisar_publicaciones_sin_texto", True) and res["adjuntos"] > 0 and res["largo"] < 200:
            e["revisar"] = True
            a_revisar.append(url)
        entradas[url] = e
        nuevas_urls.add(url)
        if ok:
            nuevos.append(url)

    # 1) Desconvocatorias primero: si el concurso original llegó en esta misma corrida, no lo anuncio como nuevo
    for url in cancelaciones:
        procesar_cancelacion(entradas, url, cfg, ahora_dt)
    nuevos = [u for u in nuevos if not entradas[u].get("desconvocado")]

    # Avisos de nuevos (en orden cronológico, para que una 2.ª convocatoria caiga en el Issue de la 1.ª)
    for url in nuevos:
        previo = issue_de_grupo(entradas, entradas[url]["grupo"], url)
        notificar_nuevo(entradas, url, entradas[url])
        avisar_ntfy_concurso(url, entradas[url], cfg, ahora_dt, prefijo="🔁 " if previo else "")
        entradas[url]["avisado"] = True
    for url in a_revisar:
        notificar_revisar(url, entradas[url])
        enviar_ntfy(f"👀 Revisar a mano: {entradas[url]['titulo']}", "Publicación solo con imagen o PDF: puede ser de tus materias.",
                    prioridad_ntfy(3, cfg, ahora_dt), click=url, tags=["eyes"])
    if nuevos:
        cuerpo = "\n\n".join(formatear(u, entradas[u]) for u in nuevos)
        print(f"\n=== NUEVOS concursos: {len(nuevos)} ===\n\n{cuerpo}")
        enviar_email(f"📐 {len(nuevos)} concurso(s) nuevo(s)", cuerpo)
        for u in nuevos[:MAX_TELEGRAM_POR_CORRIDA]:
            enviar_telegram("NUEVO CONCURSO\n\n" + formatear(u, entradas[u]))
        ventana_windows(f"Hay {len(nuevos)} concurso(s) nuevo(s).")
    else:
        print("No hay concursos nuevos. ✔")
    if a_revisar:
        print(f"👀 {len(a_revisar)} publicación(es) solo con imagen/PDF para revisar a mano.")

    # 2) Releo los concursos vigentes: ¿los editaron, los desconvocaron o los borraron?
    revisar_cambios(entradas, pubs, cfg, materias, ahora_dt, nuevas_urls)

    recs = recordatorios(entradas, cfg, ahora_dt)
    if recs:
        textos = [t for t, _u, _k in recs]
        print(f"\n=== RECORDATORIOS: {len(recs)} ===\n" + "\n\n".join(textos))
        enviar_email(f"⏰ {len(recs)} recordatorio(s) de concursos", "\n\n".join(textos))
        for t in textos[:MAX_TELEGRAM_POR_CORRIDA]:
            enviar_telegram(t)
        for _t, u, tipo in recs:
            avisar_ntfy_concurso(u, entradas[u], cfg, ahora_dt, prefijo="⏰ HOY · " if tipo == "dia" else "📅 MAÑANA · ",
                                 prioridad=5 if tipo == "dia" else 4, tags=["alarm_clock"])

    cerrar_vencidos(entradas, cfg, ahora_dt)

    # Poda: borro lo vencido hace más de 90 días (solo si ya no aparece en el listado)
    actuales, limite = {u for _t, u, _f, _s in pubs}, ahora_dt - timedelta(days=90)
    for u in [
        u for u, e in entradas.items()
        if u not in actuales and not e.get("issue_abierto") and e.get("visto")
        and datetime.fromisoformat(e["visto"]) < limite and es_vencido(e, ahora_dt)
    ]:
        del entradas[u]

    guardar_historial(datos)
    generar_pagina(entradas, ahora_dt)
    generar_calendario(entradas, ahora_dt)

    if mostrar_todos:
        vig = [(u, e) for u, e in entradas.items() if e.get("relevante") and not e.get("vencido")]
        print(f"\n=== Vigentes de tus materias: {len(vig)} ===\n")
        print("\n\n".join(formatear(u, e) for u, e in vig))


def main() -> None:
    ap = argparse.ArgumentParser(description="Concursos docentes - CGE Entre Ríos")
    ap.add_argument("--todos", action="store_true", help="mostrar también todos los vigentes")
    ap.add_argument("--vigilar", type=int, metavar="MIN", help="repetir cada MIN minutos")
    ap.add_argument("--paginas", type=int, default=None, help="páginas del listado (pisa config.json)")
    args = ap.parse_args()

    def una_vez():
        cfg = cargar_config()
        if args.paginas:
            cfg["paginas"] = args.paginas
        buscar(cfg, args.todos)

    if args.vigilar:
        print(f"Modo vigilancia: reviso cada {args.vigilar} min. Ctrl+C para salir.")
        while True:
            una_vez()
            print(f"\nPróxima revisión en {args.vigilar} min...\n")
            time.sleep(args.vigilar * 60)
    else:
        una_vez()
        if sys.platform == "win32" and getattr(sys, "frozen", False):
            input("\nEnter para salir...")


# ----------------------------------------------------------------------------
# ÍCONOS DE LA APP (PNG en base64; el script los escribe en docs/ solo)
# ----------------------------------------------------------------------------
ICONOS_B64 = {
    "icon-192.png": (
        "iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAYAAABS3GwHAAATZklEQVR42u2df2xcV5XHv+fc+974x9hJNthOWyehtDhtmiag"
        "tAgEwo2WkoqSlApcLYsqlooGtCu0Au0fCFgcC4SQVkLa/Yu2UBYV/qCGbRurUbpFagIVIEgJSUPSmGbbxCaNHdLEvz3z3j1n"
        "/3hjx0nTxEnGiT1zPtKoVmqPR+Pv555z77vzLuGqoYT2nQ7NJxTdD4Tpf+5Q15r23cqglZqOvV+JVjFH7xQpOlJdB2IHKIyF"
        "CAEqQYn2MsdBJHmdVA+Rr/+dQI/0++UH0U0zsvCkw2ATYdddASC9Sq9wjulUxs6djF0b0ql/uuH+3lYW/giIP0QI71PVdxNH"
        "NUQRFAJo9p5oKMLCv/AlIBeXvnQgMFQTqCSTRPQXhfs9VF4Ull/+9am2/ukfa3/B4667BF0kC1OATmUcAE0Z3rzpcEutjz6m"
        "mnxCVTawzzcAgEoBGgqAigKQ7CVp9rqI2AJUAaiWQkxaGtAYxEQuB+IcAEDS0REifoEoenoiTbYP9tw0MNUhYDV0rkSYAwGU"
        "0AGeCn7r/a+uIXWfhaYPctTQAkkhYRyQEECkUGUQ0VWpRsa80gKqCiKBKoGdY1cHsIckIwMg/4RS+HH/UzfvnxahG1Lu1qi8"
        "oWt/wU+1Oq33HlhDPvcVQD/DUT7WZBQqxQAQQGCALPDGWWWi1P+COHYU5SHJaBGgn2pa+F7/s6v3n5uxeSRAqWUBacv9f2qO"
        "teEbAH+BXS6WZBiApgCchd6YtQxAAMhz1AgJhSIgjxRp5NsDT71ncGbervQ3XXmP3aEueyGkrZt7H8ppfg+7ui9BCrEUT4ds"
        "Fkvewm9cwrhMWWagUjwdIIWYXd2Xcprf07q596GpvGXZu5YVoF09dlG6fPNL14MXPc4+v1HTUWgoBhCz9fVG+eYLIuRiRz4P"
        "SUefgww91Ldt/bGpDF7lCqCETmXsorT1voMbQYt3s6vdKMVTqUqi2dq9hd8o41yV2KkkKsVTKbvajaDFu1vvO7gRuyhFp/KZ"
        "tmjOBVBGJwhdJCs293Yy1+4gwnVSHArW6hhXozWS4lAgwnXMtTtWbO7tRBcJOkGA8qWbdanhR7Yeu/y+3kddvPThMHkiAEq2"
        "Zm9c5XmyAKSupsmF4snH+p5p23JuRsssQPbEK+7dtwS+/vvkax+QZDgB1EZ945pZAFDKUWOk6cSTSMe+ePTZtacuRQKadfg7"
        "gRW7X14EX/ccxY13SuFkWpqpG8a1FiHl3FKvxeE/IB3fePSO24fQBcxGglm0LUroBNBFoi73GMWNd8rkyaKF35hHcwMvkyeL"
        "FDfeqS73WGlOgNlMjC9eATrUoZvC8k2vPMrxooeleDoFWfiNedkRpRwv9lIceqyv55YtU9m9/ArQrj4L/5+3utqmhyUZSiz8"
        "xvwtBOQlGUpcbdPDyzf9eSu6KaBd/eVVgOmRf9/d5Bf9r4bJFBDbzmAsgIkxB3I1XtOhj/b1rH3+QpWA3nbSC5YbN+1tSbl2"
        "LxE3qxQVsKVOY0FIIMQxqcqgl4l1r/WsGwDkvCtD5w90BwidwgnFT7Cvb9FQEAu/sYB6IdZQEPb1LQnFT6BTGB3nH+z5bVuf"
        "Px580MVL7pZkKC1tbTCMheSAk2QodfGSu5f/8eCD6KZwvs1z5wighNVbdcW9+5aAo+9KMmojv7GgLZBkVMDRd1fcu28JVm/V"
        "c5dG+ZzWh9HVJcruWxw1LIMUFOXYMm0Y1waGFJSjhmXK7lvo6hJ0nJ3nMzZ0KqMLev3mV9ocx/sh6dQOO1v1MRb0jBggBXsJ"
        "UlxzbNstvVObOc+uAAdAACmrfI1dnYcGtfAbldAHQYOyq/Os8jWANMv6WRVAGYCu/ETvLYJoDySNALHR36igKsAK9gkjee+R"
        "p9teybJNklWAdjBAGkL6efb1OSCIhd+oqCqAIOzrcyGknwdIs8xnt+4igHTZPb1NUYz9IG6CJrArvkaFFQEFRYDKiaSINcd3"
        "tJ0AlLi9HQ4AvA8f57ixGVIUC79RgUWAIEXhuLHZ+/BxAGhvh+Ndzd2a/W/9FCSodT5GRXdCEpRIPwUAu5q7s4sCKz+2f5n4"
        "+C8gykNTtQpgVG4b5Amqo5wW331k+5rjDABp5O/mqCEPSYOF36jsNigNHDXk08jfDZSuA7BSe/aBe7sVs1HxXZCCKMs8AF6/"
        "fnekKh+AFKaFMIwKhiEFqMoH1q/fHfHAsrpVxP4mCQXYxjejCkoASyiA2N80sKxuFRPzTUQ+V9r6YBhVMBcOSuRzxHwTE8k6"
        "4gjZrakNoxoEgBBHIJJ1rMq3w7JvVB0CVb6dFXpz6QQbW/40qmYioCpQ6M0MIhv+jSrVgIRJdZ2Ggh1IZ1RT8FlDAaS6ju0c"
        "XqNaZ8IgdmzhN6pZAmt7jKrGBDBMAMMwAQzDBDAME8AwTADDMAEMwwQwDBPAMEwAwzABDMMEMAwTwDBMAMMwAQzDBDAME8Aw"
        "FhS+Ys02tcuCiAmw4FAFRifEPu5cBmpzXNE3zK8oAYiANCga6x1+9I1W1NUS1I77uPQBBNld0tKg+Lf/Oo6+gQRxlL2XJsAC"
        "GP0jT9hwRz2ctUFXTF2OIZIJUYkFtWJboOExQWM9WwW4ggqQpAqp8DayYifBjrOHCXD5AkgVVFBrEoyqxgQwTADDMAEMwwQw"
        "DBPAMEwAwzABDMMEMIzKpWKvBItkj9lcCSYq/9ViUVz55hkCuMyvSwGoXPx7CJW/FbpiBSAC8rV8TT8TwIR5efAsAZjtcYi5"
        "mCp+G0lFCaAKOCaMjgv+4ZtH4S8yfHLpe7/86aXYsL4eIgq+wiF3quJ8/fsD+PP/FVBbQxcdcc8ncDFV3NAU4Xv/ugzeXfm2"
        "btFMyj2HJtH1w8FZvS5V4I2/pYh8ZW6FrsgKQJTtYnxh91j2R7vAPl7nCG8OB3T8feP0H7xc/G7/OF7cO46GeoaES6weDIwX"
        "FKtWxmXbjTn1Xpw4nWL7b0bQmJ/F6yKgriarpJW6KbRiW6DG+ovXeccEEUUclb/O5+sYi/OMfB1fci/NBMSRoqGu/D1c5AmL"
        "85yJOYvXFewjkQuT2f7hgmBOyrtI9txBLn0yqXR5PzfbSnC5r6sSsWVQwwQwDBPAMEwAwzABDMMEMAwTwDBMAMMwAQzDBDAM"
        "E8AwTADDMAEMwwQwDBPAMEwAwzABDMMEMAwTwDBMAMMwAQzDBDAME8AwTADDMAEMwwQwDBPAuLp/cPuLmwDVTBxV/j3/TQDj"
        "LUxlviamir7fvwlgXNCAfJ1DLiKIzMsDbEwAY24rwN81MupqODt4wwwwAaqNJXmH5iUeaaqWfxOgiipA6dAN5whtK2MUUwXZ"
        "bNgEmM9oOY5afcsTAve8vwHFROHchQ/eqwY/TID5GPxSex6Clu2QPCAb/VWBj3+wAfd9uAH9gwmSNPsFTNk1Ap5xZnIIlf9e"
        "e4vbPG1ZGCgkijSUf7YaR4THv96K2971N/zPzmEMvJlioiClo1gJzgGxJ9TmCMVUK3rJ1ASYr6WZCJMFxcSkIF9bvkJNlFWY"
        "mhzh6//UhC9/eileO5ZgeCxMn7PsHVBfWinq+NpRnB4J8BV67cAEmKc9UHZWsODUaEDTEo9y1gEqTQdEFXU5xm035s77fWOT"
        "lX+MpM0B5ukcwDEwNiEYOJnOnL+WtRI4zkb1mUe6Bsl6fxGgUFQTwLh2LVAxUbzyegGqgM5R/0Glya+b8eDSw1aBjGtXBTRb"
        "tXlx33gppLZmbwJUEUEU+VrGr/aM4/U3iiDYye4mQJXhPeHUSIr//NlJEAEitoXTBKimKhAUi/IOP9lxGtt/MwLvafrClWEC"
        "lLXfFinvo5zkIsK//Mcb+PWfxhB5gmi2WmMqmABXHn4AuZjADEQRTa+AXO7DuTNfl0tO7wiFRPCP3+zHD7edAlO2WjO1XSJI"
        "tmVCr/B9OLMkml2BroYPzdDyza9U7UBCBCSpYtXKHFrKfLFp36uTGBoL8K48V1C5tJtzdCLgw++pxz9/cik2rK9HHJ39ikUA"
        "xduHl876gkCl9+F8S56jE4I7P3cYw6OVeyW4qgWYkmCyoFlvTbjyvqL0HLU1DM/lbVOIMhFGxgUK4LYbc2h/bx4fXFuH296V"
        "w3Xv8PDu8hROUsXYZHbh7cjxBHtfncSv94xhT+9kRV8PqHoBpkbXcv+RZQ579Kn2amJSMVkUeEdY0uhwQ1OE5c0Rli31WNLo"
        "UBMTmAmqChEgDYokBQqJYLKQBX54TDAyFjA0KnhzJGB4LGB0XJAERewJdTWV3SWbAAtd3FLA0wAkSVbJgir0PALSjEoCyhog"
        "nr4SnO0C9a40DyKClMSpZGwz3AJGFEDIYu4Y8DlCXU1WzugiE94zX+jUf86aCEuVrDGZABWC6nSeYQukl1BF7S0wTADDMAEM"
        "wwQwDBPAMEwAwzABDMMEMAwTwDBMAMMwAQzDBDAME8AwTADDMAEMwwQwDBPAMEwAw1g4Athdh41qhcBQCSaBUY3hh0pgJdpL"
        "Lgeo2s23jepAVcjloER7Gao2DzCqVQRmAr1KxIDdS8OoougTMQj0KhPJy7YYZFQfDCJ52avyXkiSTYgNozrmv6ySQJX3sooc"
        "Vk0LIGdLQUaVCOBINS2oyGFuOT5+SCU9zC4HwFaCjIpv/4VdDirp4Zbj44f4pZfuSIj4t+AcAJgARqUj4ByI+LcvvXRHwgAg"
        "pLtKd1e1Nsio8AIAgmqWeZSWf3ySPi/JyCjYO1TFyVBGlaZfwd5JMjLqk/T5TICOJ92R7WuOQ9NfsatTqLVBRsWO/pJlPP3V"
        "ke1rjqPjScftgx2UuUE/Bzuy62FGJRsAdqRKPweA9sEOIkAJIF12T29TFGM/iJugCVDRR6MZVdn+UASonEiKWHN8R9sJQIkB"
        "UrSrP76j7YRq8hOOGghAsDfMqDACRw2kmvzk+I62E2hXD1BpI9wuCKDknP+BpGOF7MQp64WMSup9HEs6VnDO/wBQyjI/vQmI"
        "BB3gI0+vOqhh4mccNTBUbDJsVEj8RThqYA0TPzvy9KqD6AADNFMAAKuhgJIQf0fCeFraGmFVwFj4oz85kjCeCvF3AKUs6xln"
        "BOjKqsCxbbceQph8hONFVgWMyhj940WMMPnIsW23HkIHGF00netzVnqU0LmVVuz+5CL1tQcAbs5WhGynqLEgEVAEQAYpnVh9"
        "9I5fDKFrqwI0XQHOOSeYFAeUjz5Lp5ZvOvBVzi39bym+mQJkAhgLcvjnKO+lcPKrR59dewp16qZ6/7epACU61GE1tHXPoR0u"
        "arxbiqcDiJ29ocYCyn7geLELyfDz/e9ddQ8OgNBNb1nef5uLXcoAy42b9rakXLuXiJtVimqVwFgo6SeOSVUGvUyse61n3QAg"
        "fO7of4HengQd4l7rWTsAmXgQ5AlgsY1yxgIIvwIsIE+QiQdf61k7gA5x5wv/hSe33RTQrr6vZ+3zmo52uZp3eIBSe4ON+Q2l"
        "ruYdXtPRrr6etc+jXf35Wp+LtEDnzAe6KSzf9MqjHC96WIqnUxB5e6ONeTj4pxwv9lIceqyv55YtU9m90I9cvKfvhqBTua/n"
        "li2SDP+Ca5Z6qBbt3TbmWfiLXLPUSzL8i76eW7agUxndF9/aP8sdn8roBFbsfnkRfN1zFDfeKYWTKWCVwJgX6U85t9RrcfgP"
        "SMc3Hr3j9iF0leay5RGgJAFIVty7bwl8/ffJ1z4gyXACqLet08a1m/BSylFjpOnEk0jHvnj02bWnprI6qxnDJf7C6Sdefl/v"
        "oy5e+nCYPBEAJZAtkRpXNfsCkLqaJheKJx/re6Zty7kZnQ2XGFqSrB1S7numbYsUTm4lX+PIxaW7TBvG1Qi/BHIxk69xUji5"
        "te+Ztqznv8TwX0YFmH4FhE4Qukha7zu4kRD/iH3NdZIMpwCctUTG3LU8CBw1ekkn31AUP9f/zK3PoVMZXThrj88cC1CiXT12"
        "Ubp880vXgxc9zj6/UdNRaCgGEDPs4AGjTMmHipCLHfk8JB19DjL0UN+29cemMni5T3zlAZ2x1tq6ufchZv4WufrrJRkCVEwE"
        "44qDD2LH0SJoGDsmIv/ev63t8XOzd+0EmGqJsqfTlvv/1BxrwzcA/gK7XCzJMAC11si45FYHIM9RIyQUioA8UqSRbw889Z7B"
        "mXm70t9U3kC2v+Cxa0MKAK33HlhDPvcVQD/DUT7WZBQqxew4JgKbDMZbQq8QQEEcO4rykGS0CNBPNS18r//Z1fvPzVg5mIMQ"
        "KqEDPN0W3f/qGlL3WWj6IEcNLZAUEsYBCQFEClUGEVmbVI3tjSqIBKoEdo5dHcAekowMgPwTSuHH/U/dvP9MuwMpx6g/xwKU"
        "6FSeuQe7edPhlloffUw1+YSqbGCfbwAAlQI0FAAVBSDZSyqVOLu2UCmDu5xpWRQAGMRELgfKbsoMSUdHiPgFoujpiTTZPthz"
        "08B08FdDZ36McWEIMFOEnTt5Ztm64f7eVhb+CIg/RAjvU9V3E0c1RFGpCmbzGg1F2OfyFzoEcnHpS5cdTKoJVJJJIvqLwv0e"
        "Ki8Kyy//+lRb/1nt9F13yVwF/+oJMLM1at/p0HxC0f1AmLmK1Jr23cqglZqOvV+JVjFH7xQpOlJdl30SzSRYqOGHSlCivcxx"
        "EEleJ9VD5Ot/J9Aj/X75wbNWcTqedBhsIuy6K5S71Xk7/h/WzY8p47iZWAAAAABJRU5ErkJggg=="
    ),
    "icon-512.png": (
        "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAYAAAD0eNT6AAAyvUlEQVR42u3deZBc53nf+9/zvqe7Z8XGBYYIglckRRLgYlkg"
        "ZZWWACoJkWKRgBhn/EccxZYdSVlKKdm5Lt9yrBrCUlxxueIom28kRZZdXq6v4BQFELJFQzSBiHRkLpIskgABkZI5AAkCJIht"
        "tu4+533yx+kZDECAwjIz6On+fqqwDDCY5XSjn9/7vMsxYY64aWhL0OGrTFov7bJCkp/tPVcOjSxT3niThcqb1JhYolhZa3nD"
        "U7DrQ6i82VPD3c1MulkhDMoLl8y4xgDa5PXOZdGU0kmX9pq5W6haSs0fhuQ/8KxqKppPqtp7zFPzJWXVlw5sWfXaOT6YaZ1H"
        "aad09SuuLUNJMucazz6KyGwW/GGZdu4M5ZP2Z4oz32PVPz621EcP3qBQu1Vm16uo3ynZMkk3uNKiEHtrkstCVXKXK0meTn2G"
        "1DjtbQBor4oSytevmW8rSGbl65dMqZiom8IJSc9L/ppi7Qm5/0Cp/owNrHh+5E+WHH3dxx36StThq0zr1ydtlhMICABtYDho"
        "6L7yGm6x0wr+irtf7IvZ5G0xhVs9+B3uxbvc01uCxSWW9UsWJM/lXkipIfckpdyl4JL7qYfHTz1GZoFrDqDNmwEzRinmpxqf"
        "ZlIyhczMghSqMouSZZIneT6m5MUxs/B9s/ioJfteEdIzRd7z9MHt14yfHgg8lq+797m0mVERAWAei/669aFMopZmPiFX5vvf"
        "ZqnxLsneI6U7zcIqi71l+i0arRF87nIlN7m5TDLJPJz6DwIAnZ0Qyl8sSa7p10JTkGVmoSqLrS5oMSH3NCKFJyT/pofqowey"
        "a7992oBr2IN27gzatTMRBggAc/GENQ0paI18ZtG/5t59K+WVtwfP75bsHWZhtcVeSUleTMpTo+zjm7lcVhZ6ijwAnDMcuCWZ"
        "XO4mU7BQNYs9ksJUINgj+beSZdtlzcdevP+mA6eFgd0ybRHrBggAl2joK1EaOq29f829+1ZaETYE04ddvj7E3kWyIE91eTHp"
        "khXlE9dMEi17ALg0Se4uM5c8WuwxCzXJk1IxccJkO5Prqx7TjtPCwJBHaYvOth4LBIA3Hu3PSJA3b3xlcFzH7rUQfto9rQ9Z"
        "/yIpKeXjUiqKcoTvgTl6AJjzJkGSWZK7KcQYsj5JQSkfO2EWdnpK/7NPS+7fu+2qk+d6TQcB4HTT80jvzaf+aNWm77/TZT8v"
        "2T8IWW2lZEr5WFn0y6tHSx8ALmMaKLdLSWUY6JfkSnn9gOR/YfLfH9n6lr+efvd1D2evW79FAOjywr9bNtXmv/qe7y3viYs2"
        "uoqfN9k7LfaU805Fg6IPAAsgDFisRou95Vos+V+b4u9PFie2HX7gjkOSyumBM9Z0EQC6ydBX4swDJlbe+9xt5vZz8vSRUBlY"
        "7kVTXoy1FvFR9AFgwYUBU7DYbxYrSs3RQ7Lwh27+Bwfuv/Hp1vuVB7Z16TqB7itqQ1+JWjM0nfxabf5flOyfhEp/1Zuj8tQs"
        "JBlz+gCw4LNAkuQWKtEqA0rNsYbkf2TyL01PDwx70O4t1m1BoHsCwBmt/mvvfX6Duf2KLGywUFFqjkpKuaTIaB8AOrArIBVS"
        "yEJlQJ6akqcdbv7b+++/YUc5QOyuqYEuKHRTK0DLwr9q03Pvk8VflYUNZkGpedIlS63RPoUfADq8KJRdAQ+hMmjlb9MOefFb"
        "I1tvfGg6CHTBrgHr6O9tyKcL/8oP7b7Nstovm4WPliP+k0mSl2dRAgC6sClQSLJQGQyemnJPX/a8/jsHvrbm6VNBwMpaQQBY"
        "IIa+Eqfmcpbf+9zVVbdfl8InQqxVU/P41Ol8FH4AQBkETCFUFlsq6g0pfb5h/tlD9994+MyaQgBo30fxVLt/7ecrq1Zu+Odu"
        "9ush1q5OzROSp0IWKPwAgLOUkLJGhMoipaJ+2Nw/O3Jgx3/Xk59oduK0QOcEgBkJbdWmZ98nq/w7i30/6XlrVb8F5vgBAD8y"
        "BshTslCJlg3Ii/G/kTf/7cjWWx7qtG5ABxREN63bGbXrvfn1739icXNg6WfMsk9KkudjRbm4j1X9AIALqi0u92RZfyzfyv9L"
        "ZfTop3/wjTuPa93DmXatLxZ6N2BhF8YZSWzlpj0fMNX+c6j03ZQaR5Pc1Rr1AwBwkTkgJZkpVJeG1Bzf56r/6wNbVz/YCd2A"
        "hRsA1nmmXTZj1B8/Kbm8mMwly3jWAgBmMQnkFnsyyeRezOgGlLVoIX5HC3CEPBw07EG7LF+5ac8Hmv3LHgtZ/ye9mEieTyaK"
        "PwBgDsbLmeeTyYuJFLL+Tzb7lz22ctOeD2iX5Rr2IA0vuHq6sDoA5Z7McqHfh/cNy6r3MeoHAFyuboC8cd/IV2/afGaNIgDM"
        "pnUPZ9r13nzVvbtXuFe/HLKBD6TGsdZcP2f2AwDmMwN4a23AkpDy0QfNGh8duX/NwalaRQCYnatsGpZps6VyoV/1yyHrWZGa"
        "Jxj1AwAuezcgVBZlKZ886Gp89MDW1Q9q2IM2y9t9l0B7j5yHPUjm2mzp2k37PhVC39fNtCI1jhcUfwBAG4yjs9Q4XphpRQh9"
        "X792075PlTcTMi9rGB2AC9eaS7li457Bvlj7XIgDv5DqrxWSc5teAECbNQI8SeahtiymYvT3xov6p45sW32yndcFtGchXfdw"
        "pi1WrPrAEyv6LHsoxP5fSI0jucwjxR8A0H7DaQsyj6lxJA+x/xf6LHto1QeeWKEtVmjdw23ZsW6/DkBrT+XKu5+6y7KBrWZx"
        "hRdjzPcDABZKOyC32J+5Fwc9H910YPvtj7fjeQHtNZpe93BZ/D/01AdC1vegWVjh+Sjz/QCAhdQOyDwfLczCipD1PbjyQ0+V"
        "5wW0WSegfToArXS0auPujylb9AUVE/LUTBznCwBYmI2AlCxUgmKvlJ/4+Mi2NV9sp05AewSAM4q/5+OFvGCxHwBggYcAT7Lo"
        "lvXFdgsBlz8AnK34Kw9S4A5+AIAOkFzKUruFgMs7wqb4AwA6XjApD56PF8oWfWHVxt0fK9cE+GVdE3D5AgDFHwBACLhsIeDy"
        "BACKPwCAEHBZQ8D8B4AhjxR/AAAhYEYIGPI431/J/Bbd1sj/mo27PxYp/gCArnVqYWCRn/j4i5dhYeD8Fd6ptv+Hvvd+9Szb"
        "4U2KPwCAEGCVvqjJ1zaMfO2Ob8xnCJifKYBW23/lh77zdlUH/1T5ZJIXRvEHAHSvYPLClE8mVQf/dOWHvvP2+ZwOmIcC7EGy"
        "tHzDo1dX+5Y/baFyledjnPAHAIBUnhiY9QdPzVca44duO7TjXYenaucCDgBuGpatePLJniwu3mmhdpfno4UsRB5xAACmQ0Bh"
        "2UD0VH88L46vP7h27aQ2yyXzOes/zOk3tG5n1GZLMQz8bqgsusuLsZziDwDAmcPxEL0Yy0Nl0V0xDPyuNlvSup1zWi/nrgPQ"
        "Wshw7T27PxV6rvyPafK1pkwVHmUAAM7VCVAz9CyrpMlXf2n/A2s+N5eLAucmAAx51BYrrr3nexussuQvPZ/IpRQlY9EfAADn"
        "TgAuhcKy3sybx/7+/gfu2DFVUxdAAPAgyd98z1NX56H3b83C1Z4aLnFnPwAAzqOOJgtVc0+HszTx4z984PbDZb2e3UWBs1+U"
        "h2SSedNqfxiyvuVe1BPFHwCA8x6bBy/qKWR9y5tW+0PJvKyts2t2C/M6z8rW/zP3xeqSDal5gkV/AABceAaIqXkij9UlG669"
        "55n7tMWK2b5nwOwlitYcxaq7n3mfqgM7vDmZZE7xBwDgYrkVVukJaoxuGNl+60OzuR4gzNZXqDXyKzbuGUyh+nklN6lgwR8A"
        "AJekMCW3FKqfv2LjnkGtkUs+K/V1dgLAOkVtttTn6d/H6uANXowXnPQHAMAlshC8GC9idfCGPk//vjwfQLPSXb/0FHFa63/w"
        "G94cL2Si9Q8AwGxxFVbpi2qcfP9sTQVc4ij9zNZ/MWutCQAAMKPepsJncyrg0gLAkMLprf+JJGPLHwAAs8oseDGRTpsKGLq0"
        "Gn7x6WHqtL9Nz7zH4uD/ovUPAMBcNwLKqQAvTv69/Vtv/ealTAVcZHooW/9a93DmHj8nd0mJ1j8AAHMqmdzlHj+ndQ9nlzIV"
        "cHEBoNX6X7l4+SdidcnbPB9j1T8AAHPNQvB8rIjVJW9buXj5Jy5lKuAiUoObXFp191NLUtb7vCksljeMG/0AADAf3GVVd6Xj"
        "IZ+4YWT77cfKam4+tx2AIQWZuYf4mZj1L1WqO8UfAIB5awOYUt1j1r/UQ/yMzPxiugAXVriHPWiz/E0bn70phurTSkUoT/wj"
        "AAAAMK9dAEVXiKlIjdte2nbLPg3LtPn87xh4YYlhd3mnv8z1ayH2ZvKc0T8AAJejC+C5h9ibZa5fk8zLGj0XHYDWVoOVd+9e"
        "Fyr9D3k+KW72AwDA5WwEWGFZj1Jz7H0Htq/ZdSHbAs+/A7BG3soc95llUUpceAAALqsksyya6b6ZtXr2OgCtRHHNpj3rY+x/"
        "mEN/AABoly5AeThQUYy998Wtq3eebxfg/DoAa+Qa9hCSD5uCJOeCAwDQJgnAFBSSD2vYw/l2AX50B6BMEunajXvWWux93HPO"
        "+wcAoL0ygCfLeoMXE3ft37b6SQ15+FFdgHD+H9r/lYWqyq0HAACgnRKAhao8+b+SZqUD4EGSX/fhfbckz74rzyvl4j+2/gEA"
        "0E4BQAqSZc1g+Vtf+OpNz5Y1/tznArxxB2CdgmReFPk/C5WBqpQKij8AAO3GTEpFqAxUiyL/Z5J5WcMvqgNQ3l1oxd17r8hC"
        "eEYWrpI3Gf0DANCuXQCrSJ5eyVO69eD2m4+0Sr1fWAdgnaJkXgl2b6guulqpkSj+AAC0cRcgNVKoLrq6EuzeVhfgnFv2zx0A"
        "1itp2IN78TEvGn5RNw4EAADzGQLkRcPdi49p2IPWn/vUvrNX9eljf5+9yyq1bymvSya2/gEA0O5cSVlN3qy/48D2Wx4/18FA"
        "b7xAwPzjIfQEmXPuLwAAC6IJ4CmEnmDmH3/jXsHro4NJ5lcNPT1Qq2fPmVWWyxvc9Q8AgIXRAnBZ1dybh+q1/MZXttw2OlXb"
        "37gD0FowUKvHTaEyuFypwdY/AAAWTgvAlBpFqAwur9Xjppm1/Y0DQGvBgLn/LFUfAIAFGgNatXxmbT/z72e2DUwyv+6nnv6x"
        "VKntlbRIntP+BwBgQXGXZSbpRGjWb37hz297+cxpgNM7AK0WQYrxg6HSv0gpp/0PAMDCG/+bUl6ESv+iFOMHZ9b4sweA6RaB"
        "Dylxzx8AABa05GVNP63GtyLCjHaBSebXbtzzJlm2R7T/AQBYwE5NA8jz1fu3rX5p5jTAqQ7AUPl7T+ntlvXR/gcAYEErpwEs"
        "61vkKb19Zq0/PQBMv3vcaDLJxBwAAAALOgPITSazuPH1f3WqVWA3fvD71Xolfc9iz02eJpJkHP8LAMCC5clCb/Bicl+tGe54"
        "7utvaZw+BTDsQTKvV4vbFWs3ejHhFH8AABZ8CyB4MeGKtRvr1eJ2ybys+VMBYGfrV/d3h6wnyFRw0QAA6IQMoCJkPUHu755Z"
        "88vCf/XUfL+tkyfJufcvAAAdwWXyVNb4GTXfprYELN/w3f5qb22vhdo1nups/wMAoDMSgFuomaf6i42J+s2Hdrx1THILGi5H"
        "+6HWf7NCz495QfEHAKBzmHlRd4WeHwu1/pslScOysK41FxCV/3iItSi9/oYBAABgQUsh1mJU/uOStG6nQhgdfdLKfGBvlQX2"
        "/wMA0HFNALkslLVe0ujok5Y9efcDxVo9UTkkf7cXDckVWAIIAEAHcQUvGnL5u9eufaLy5N0PFCZJ12364ZIiTbxgobpI3mQN"
        "AAAAnZUAXFYxT40TMfRe98LWNx8LkpSHxnUWe/u4+Q8AAJ3ITJ67xd6+PDSuk1rnAIQ8/USIPZncWQAIAEBnNgFSiD1ZyNNP"
        "TAcAN93EAkAAADq5CVAuBHTTTdMBQAq3yQtOAAQAoGM7ADJ5UdZ8SWHN0NNVc7+6/EMCAAAAndsDKGTuV68ZeroaJo9O9sr8"
        "Bk8NyQgAAAB0aPm3stb7DZNHJ3tDo9K/Shb75AXz/wAAdDIvXBb7GpX+VcGirzCr9LkXYgsgAAAd2wIw90JmlT6LviLIwhIu"
        "CgAA3ZQFwpIgS2+3UJGcmwABANDRXMlCRbL09iDZOFcEAICuagGMB5dubh0AyPw/AAAdXvndk1y6OZh0s+j+AwDQJZJMujlI"
        "anAxAADoKo0g5/x/AAC6isszl60WpwACAND5WqcBumx1sBAG5UkcAgQAQMcnAJMnWQiDgSOAAQDoMl54YOQPAED3dQICFwEA"
        "gO5DAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAA"
        "AAAIAAAAgAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAA"
        "AAABAAAAEAAAAAABAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAA"
        "ACAAAAAAAgAAACAAAAAAAgAAAN0s4xLgkhIkERKYc+7lD4AAgLaQkjQ+mbgQwByLwVSrGhcCBABcXmbSZN21+s01/ea/WM4F"
        "AeYsZLtCMH372Qn9xpdeUW+P0QkAAQCXNwDkybWoP+idt/dxQYC55q48ucwIACAA4HKHAElFKn8AmBtFcsVgGpt0MQEAAgDa"
        "KgREFgECcyoGKVD9MQd4+QYAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAAgAAAAAAIAAAA"
        "gAAAAAAIAAAAgAAAAAAIAAAAgAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAA"
        "EAAAAAABAAAAEAAAAAABAAAAnFXGJcClcL88n9eM69quOvmxme/Hxf3UD4AAgLZ6oe/0QkwRxeV8XLJorV+59iAAoI1eCPPC"
        "dXysuAzDMGmgLyiGzqySzdw1PplkJi2ogZ9LMZgG+jp3ZnG8ntRouoKZfB4enZSkEKST44lQiNl/Hb9247M0l3Dhr/Vejk4G"
        "euf3xd4kNZPrz35zlW69vjb9AtkJisIVo+mBR07qk//hoBb3B6W0ML72YNJ4w3XzdVVt/a1VitHkrcerIx6bJMUg/ep/PaT/"
        "/xvHtXhgfh4bl8tkahausQlCAOgAoI06AEdO5PMfAApXXnRubm00XUeO5yqKoGIhBYC66/jJzu5Vn5xIevV4riJFFcnn8f+b"
        "KbJkGwQAtFMIqGTzOySx1k+dPBKauq6VzBQWUACoFFKWdfYQNYuX77FhISAIAGgrl+NFqRteCBfa6m9Xd6xWn/m4UJCx0NFU"
        "AgCAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgA"
        "AACAAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEAAAAQAAAAAAEA"
        "AAAQAAAAAAEAAAACAAAAIAAAAAACAAAAIAAAAAACAAAAIAAAAAACAAAAIAAAAAACAAAAIAAAAAACAAAAIAAAAAACAAAAIAAA"
        "AAACAAAAIAAAAAACAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAA"
        "AEAAAAAABAAAAEAAAAAABAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAHcy4BCAAAEAXBgAjCYAAAABdxMsXzMiVAAEA"
        "ALpOJZrcnQsBAgAAdFEDQJWM3j8IAADQdWqVIBdLAEAAAIBuagCop2ZiBgAEAADoMn01xv4gAABA15gq+wO9QcFOdQQAAgAA"
        "dEECWNQfFUgAIAAAQHclgMWDsdUBIAGAAAAA3dIA0NKBoErGQkAQAACgqxLAksGo3p6glNgKCAIAAHRNB2DZ4qiB3qAiOQkA"
        "BAAA6JYEMNgXdeXiqLyYcWMggAAAAJ1b/5NLMUgrrqwoL5wGAAgAANANPJUr/66/pqKicBktABAAAKALAkDr11uuq532NkAA"
        "AIBOfrFsjfhvvb5HfT1BKREBQAAAgI431fG/eVVV11xVUaPpLAQEAQAATJK8c1vjZlJKUl9P0NrVvZqoe3ksMEAAANDtOr0r"
        "7q0jAH/qnQPsAgABAACmWgDJXSlNVcsOfMGMZdl/350DuvHaqibrSTQBQAAA0LW8rP8qis7uApikIpW3Bf6XP71MJ8aSYiQB"
        "gAAAoJsbACY1cy+Pye3kF81QrgX4uZ9aqnvXL9Kh13JVMkIACAAAujgANHJXUXT499n6Xs2k//dX3qQNbx/QoSO5QihPCgQI"
        "AAC6rwPQdNWb3hXfqyQN9gf96Weu1b/46WUaHU86PpZkkrJoiuFUULjQYGEmBdN0qGC7IQgAANp4ZGxqFq7JerkKsNNjgJnk"
        "LtWqpt/+5I/p/t+6ThvuGlCRXK8ez3V8NKneONURmSro0z/s9ICQVK4vyItyKmWi4RqbSDo2mlTnzAHMgYxLAOCSeVnUGk3X"
        "2GSa/rNO3ys3FQLcpfe8tU/veWufnvlhXQ89PqrHnpnQcwfqOnK80ETdNZn7qdMDTQoyWSsIxGCKUapkpiwz1aqmgd6gwb6g"
        "5csy/fClpr6/v65qxeQcQAgCAIA2qv8ykybrrtHx1F2dDzt1SJCZdOuba7r1zeX9AiYbriPHcx09UWi87soLn/43wcppgiya"
        "skyqZqZaNai3ZuqtBdUqpkommZk+/fnD+u6+CfXUMhUFCQAEAABtJJjULFzHRrtjCuB1339rQjWl8jyEYKaequmaqyq65qrK"
        "RX3MIrnMxbHDIAAAaOuxsFKSXj3WbLUFumAO4BxBILS+76l2vZ/jiGQ7yxt2lo9H8QcBAED7ln+TUnK9/FrRlR2Ac12Tmb9e"
        "MC4i5jKscgkAzIapdQAvHW5eWtEDQAAAsJASgCtG08h0ACABAAQAAN1Q/1WJpgOHm2rmrmB0sAECAIDuCAAV08uv5nr5tbz1"
        "h1wXgAAAoLMDgKQsSkdHC31/pCGp3A4HgAAAoNNfUMzUbLq+vXdiuisAgAAAoMMld1Uy07eeHpdUHnELgAAAoNMDQJL6eoK+"
        "vXdSL7zcLM8GoAsAEAAAdL5KZnr1WK6/+N8nJUlOAgAIAAC6oQvg6qma/uyvTigvXIFpAIAAAKALAoBL/b1R39k7ob96Ykxm"
        "5U1tABAAAHS88u51//XPjshdMtEFAAgAADpekaTB/qhvfndc2755QiGUfwaAAACg03sAyVWrmj775Vd0YizJxLkAAAEAQMdL"
        "LvXVgvaN1PUbXzrc6gKQAAACAICOlxeuZYsyfemBo9ryV8eVRVNeEAIAAgCALugEuPp7g/7Nf3pZT+yZIAQABAAA3cC9vElQ"
        "I3f9080HtOfv6oQAgAAAoCu6AEnqrZqOHC/0j35tRH/7/cnpEEAMAAgAADpYkaS+XtORY4X+4f8zoge/NaosmuRlQAAwvzIu"
        "ARbqiLJI5a+dMoIskqQOv3lOUUi9taDJetJHNh/Qr/zslfq/f/bKcodA69hg48wggAAAnMtAX1AMUuygHtbUrXP7atbR++WL"
        "VN4yOMukz375FT3yvTF99hPLdfsNPa2QQBAACADAWZhJ33p6XIeP5vIkWYeEgFS4QjQ99XxdWdbZIWCqy3HF4qhHvjuuD/3y"
        "C/rFe5bqX/6jZbpqSTYdFEymwEQl6yRAAAC8NVL+5f/0slKH9sqzaOqvmbrhzJy8cC3qj8oL1+/8f6/qzx4+oZ/7qSX62Q8s"
        "0YorT708FYXLrOwKdENnwL38kReuGKyjOl0gAACXpK/WuZVg6sW/WxTJFUy6YnGmI8dzfeb3DutLDxzVPe8e1D987yL95Jo+"
        "xWinvb9cHRMIph5vl8tdClZ2PcykWqv9MTqemBLBrLNrNz5LdwlAe7wgWdnhqTddo+OFemtBd9zYo/ffNaD33dWv22/oUbVy"
        "eiVMqTxsyKy866CZJNNlvf+gT/906vfeqvZefnkyO/f0xkQ96dkXGnrku2P6y8dG9dTzk+yUAAEAQHcEgRBMKbnGJ5PqTVd/"
        "T9Cb31TVnat79Y5be/XWm3p1wzVV1apnL/VpamTdaqfY9E+n/eZHlfE3+u2Mj2nTb19oV+L4aKGXXs31w5ca2vN3dT39fF27"
        "/25S+19uanQyqZqZensCN1QGAQBAdwmhbIsXyTXZcNUb5VB4sC/q2uUV3bSqpluvr+mW62r6v1ZUtPKqihYNxMs6b55cqjeS"
        "JhuuE2NJx0cLHTtZ6PDRXIdey/XSq7lefKWpg6/mevlIrtdOFBqbSMpTOedfq5hqVVMMpuTO6B8EAABdHgZMstZ2yaJwNZqu"
        "etNVtApnX0/QssGoK5dGLV+WacUVma5cnOmKxVGLBqIGeoP6ekyVaMqilTtIWu15dyklV/LyTIaicOWFKy+kZu5q5qc+31Rx"
        "n6i7JupJY5NJYxNJoxNJ4xPl26PjSaOTSZN112Q9abLpSkVrd0Orw5FFlVsiY7nQz6zc/ZHcuXUyCAAA8IaBwKYKp6tImi7a"
        "eVGOnFNyycougln5b861RuCcc/c6fTrBW39+quXfWpA41bEIpmCnfh+t3K46tUZh5nqAblv0ifbBLgAAC1byM6q2yhF1NSuL"
        "ssymC7233u98a62d7U/s9X/nZ6SHM4PDdGBIp3+dAAEAAGaR+8xMMJsFl+KNzsLxEgAAEAAAAAABAAAAEAAAAAABAAAAEAAA"
        "AAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAAAABAAAAEAAAACAAAAAAAgAAACAAAAAAAgAA"
        "ACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAAAAAgAAACAAAABAAAAAAAQAAABAAAAA"
        "AAQAAABAAAAAAAQAAABAAAAAAAQAAABAAAAAAAQAAABAAAAAAAQAAABAAAAAAAQAAABAAAAAAAQAAABAAAAAgAAAAAC6LQC4"
        "cxkAAOgm7kEWjQsBAEAXsWjBUzopC6ITAABA54/8ZUGe0slg8j0WqpKLAAAAQEfXf7mFqky+J8jEFAAAAN3Eyt5/lSsBAEBX"
        "qQaX9rIbEACAbhHk0t5g0l6zIIk1AAAAdDg3CzJpb5C8j+sBAEBX5YC+IA+PeWpKxjwAAAAdzRQ8NSUPjwV5OsYVAQCgmxoA"
        "6Vjwwg66N8fNojgMCACAjq36bhbl3hz3wg6GanNsRF6McyQwAAAdzqLJi/Fqc2wk9CztmZDb85wGCABAJzcAylMA5fZ8z9Ke"
        "ibB7y20NNzssi+VfAwCAzowAFuVmh3dvua3RWvmfnpZFyQgAAAB0JCsDgJSellpHAJprnzxJzn0BAADo1PG/PJU1X1ImSSkL"
        "31ExmavcCgAAADquA2AhFZN5ysJ3pjsAWaq+4MXEuCwztgICANBxw3+XZebFxHiWqi+UAWB4OFx54MiYZM+xEwAAgE6s/60d"
        "ALLnrjxwZEzDwyGs3X5PfPLJO5sme8RiVTIlrhQAAB3ElCxWZbJHnnzyzuba7ffEMDCw1svmgH+XhYAAAHRkB8Dkqaz1kgYG"
        "1nrYtb4c8RfK/jYV9ULipkAAAHSYkIp6USj7W0natV4paHM555/qY3uVJl+2WGMhIAAAnTP8d4s1U5p8OdXH9kqSNsuDZK4h"
        "j4d2vHVMrsct1iRnHQAAAJ1R/5Vatf3xQzveOqYhj5J52e4/PDXv77tkgRMBAQDoFCaXhbLGz6j5ZQBorQOQ2SMpn0xycSAQ"
        "AACd0QGIKZ9MMntkZs0vA8BmS5JbrRGfUlF/zmKvSc40AAAAC7v6J4u9pqL+XK0Rn5Lcypo/c8X/kMJzX7+pLulRi1VJrAMA"
        "AGCBS62a/uhzX7+prqFTdf91W/7ci20u5zwAAAAWfANA5nK5F9vO/KtTAWBLOeK3EB7zfPyEQhbZDggAwIKt/q6QRc/HT1gI"
        "j82s9Wd0AMw17GH/ttUvKTUfCbGP7YAAACzc0X8KsU9KzUf2b1v9koZbW/9fHwAk7Zx627YoMAMAAMCCFqys6afV+LMFgF0q"
        "JCkUxddTc4xpAAAAFubw3xWymJpjJ0JRfH1mjT97AGhNA7zw57e9rNR8NGRMAwAAsPDqv1LI+qTUfPSFP7/t5TPb/2cJAKda"
        "BG72xwz9AQBYqBmgrOUza/sbB4BWi6BeK7am5slDClWmAQAAWDil3xWqMTVPHqrXiq0za/sbB4DWzYFe2XLbqLk/ELI+Sa//"
        "hwAAoC0VIeuTuT/wypbbRqdu/nMeAWBmhrAvpDSZ5Ba4ngAALIQGgIWUJpO7feGN3u3ce/2GyzsFXvvtPd+ybOBOz8eSzLhJ"
        "EAAAbVv8vbCsP3g++sT+t61+hyRNnf1//h2AnQrabMksftFi1cQdggEAaPcEIItVM4tf1GZLZ1v896MDwC4Vklsz+f2pceKw"
        "QjWwGBAAgPYd/itUQ2qcONxMfr/kdrbFfz86AMhc6xQPbr/lVffmH4XKoInFgAAAtKsiVAbNvflHB7ff8qrW6ayL/84jAEja"
        "pSS5xZj9j9QcbUiBLYEAALTj6F8hpuZoI8bsf7RG/294kN+PWN1vSUMKL3z15j1e1P8kVAZN7pwMCABAe9X/FCqD5kX9T174"
        "6s17NKQg2aUEgFNJwIL9N08NScZdggAAaCtmnhqyYP9Nb7TDb+a/OK+Pe2pL4EOhsmh9ap4s2BIIAEBbjP6LUBmMqXli5/63"
        "rX6fpHNu/bvwDsBumTZbSsE2l/cGogkAAECbjP7lSkrBNmuzJe0+vyJ9fgFgixUa9vDi1tU7vTm6M1QGo9zZEQAAQBuM/r05"
        "uvPFrat3atiDtth51efzP+K3lSjcdZ97XlzIPwUAAHMhyD0v3HXfzFo9uwFgixUa8nhg+5pdysf/OFQHozzRBQAA4LKM/lMR"
        "qoNR+fgfH9i+ZpeGPJ7v6P/CAoAkrZFLbrnpN1Mxkcsy41wAAADmvfq7LLNUTOS56Tclt7JGX0jv4EJsLs8FeGnb6r0qJj8f"
        "KgOBcwEAAJj3+p9CZSComPz8S9tW79VQef+eC/kQF7Gc300urbr7qSUp633eFBbLG8b5AAAAzNfov+qudDzkEzeMbL/9WFnN"
        "bQ47AGp9gp9RGPnaHUflzU+HSj9dAAAA5nX03x/kzU+PfO2Oo/oZhQst/hfZAWh1AYZl2rkzrFy84m9C7H2b52NJFtgaAADA"
        "nBX/lCzrD6mY+PaB4wd/UuvXJ22WX0wAuMiCba7dMu16b25WfKrs/gcWAwIAMKeCy0xmxae06715ue3PLqr+XvyIvbUtcP/W"
        "W7/pzZO/G2pL2BYIAMDcjf6LUFsSvXnyd/dvvfWbF7rt73VD+Uv8akzDsiu+82x/r7LvhJBd78Wky4ypAAAAZq34e7LYYynl"
        "P5hQ/hNHfuKWsYtt/V96B6DMD67dsiPbVp8MqfEJhWiX8sUAAIBz1NsQLaTGJ45sW33yUlr/sxQAVE4FrPNsZPutDzEVAADA"
        "bI/+T7X+R7bf+pDWeXYprf/pSDFLX90ZUwGVG7wYZ1cAAACXVvyTxb6QUvP52Wr9z14HoMwRZ0wFmEuRqQAAAC5JdAXz2Wz9"
        "z3IA0BlTAaO/EWpLouQ5Dx4AABc1/M/L1v/ob8xm63966D7rX29rW8LKjXv/MlYGNqTG8UIWIg8kAADnW/tTEaqLY9Ec3XFg"
        "281//1K3/M1tB2C6E1DeMbDi9Y+kfPyQxVqQOCoYAIDzrf4WayHl44cqXv+I5FbW1tk1B4v0yjsG/vCBOw4pTXxEoWJSSNw2"
        "GACAH1n8XQpJoWJKEx/54QN3HNKQgmSzPpCem1X6rfUA+x+4Y4c3R38p1JZmcmM9AAAAb1j/LQ+1pZk3R39p/wN37Jjtef+5"
        "DwCStMtyrXs42//Ams8V9df+INSWVlgUCADAOat/HmpLK0X9tT/Y/8Caz2ndw5l2zd3g2eb4mzENy1Y8+WRPFhfvtFC7y/NR"
        "FgUCAHBauUyFZQPRU/3xvDi+/uDatZOztd//MgUASfIgWVq+4dGrq33Ln7ZQuYpbBwMAMF38k2X9wVPzlcb4odsO7XjX4ana"
        "OZefdh6KsCUNeTy0412HPT95t5SOWKhKzs4AAEC3F39PFqqS0hHPT959aMe7DmvI41wX/3nqALSs80y7LF/1oe+9Xz3Ldnhz"
        "vJDyIAXjGQAA6D7JpSxZpS9q8rUNI1+74xtTtXI+Pvv8teF3Wa51no187Y5vFM0TH7esL0pZKi8AAABdWPyzvlg0T3x8vov/"
        "/AaAqRAw5PHFbWu+qJwQAADo7uKv/MTHX9y25osa8jifxV+azymAmaamAzbu/piyRV/wnOkAAED3Ff+RbWu+ON8j/8vTAZjZ"
        "CVjn2QidAAAAxf+ynJFz+bbiEQIAABT/y3ZA3uXdi08IAABQ/C+L9phzP9uaAC9MZhwWBABYuNyTLHq7Ff/2CQBnCQEqJuSp"
        "yYmBAIAFWvxTslAJir1qt+IvXe4pgJlaNw8a2bbmi6l+9IOycNSy/iBPBc8iAMACK/6FZf1BFo6m+tEPlsX/4bYp/u3VATij"
        "E7Dy7qfusmxgq1lc4cVYLlnGMwoAsACqf26xP3MvDno+uunA9tsfb6eRf/t1AM7oBBzYfvvjNnFkraf646G6LCtvJczaQABA"
        "2xZ+SZ6H6rLMU/1xmziytiz+D7dd8W/PDsCUIY/aYsUVG/cM9sXa50Ic+IVUf62QnMWBAIA2q/2eJPNQWxZTMfp740X9U0e2"
        "rT45Vcva8Utu75P3hj1oc3lHpGs37fuUhdp/lOfyol7IQuQZBwC4/MU/FRZrUZbJU/2X9m+96XNn1jACwMVdWdOwTJstrdy0"
        "5wOm6pdD1rMiNU+wLgAAcLlrVB4qi7KUTx50NT56YOvqB8vCL5esreetF0Ar3VybLWndw9mBrasftFBfm4qJB0N1aSYplW0X"
        "AADms+57kpRCdWmWiokHLdTXHti6+kGtezgrR/3W9ovWFtbNd2bMpaz68L5hWfU+yeXFJN0AAMC8jfot9mSSSd64b+SrN20+"
        "s0YtBAtrMd0WK6ThoGEPI1+9aXNKEx/05PvKboDTDQAAzPGo31OoLs08+b6UJj448tWbNmvYgzQcFlLxX3gdgJlaeyqvf/8T"
        "i5sDSz9jFj9JNwAAMNejfvfiv1RGj376B9+483g77u/v/AAgSUNfidryM4UklQsEa/85VPpuSo2jSe7iGGEAwKXV/ZRkplBd"
        "GlJzfJ+r/q8PbF394Jk1iABweR4d07qdUbveO6MbkH2yzGtjRXlmgBnPYgDABdQWl3uyrD+Wb+UzRv0PZ9q1vlgIC/06PAC8"
        "vhuwatOz75NV/p3Fvp/0fFSemkWrG0AQAAC8YeVv3cQnWjYgL8b/Rt78tyNbb3moE0b9nRkAproBQyoXYqz9fGXVyg3/3M1+"
        "PcTa1al5QvLEAUIAgHOUkLJGhMoipaJ+2Nw/O3Jgx3/Xk59oliv8lRb6qL+DA8DruwHL733u6qrbr0vhEyHWqql53OVKMiMI"
        "AAAk90KmECqLLRX1hpQ+3zD/7KH7bzzcaaP+zg8AU9/bkE9vy1j5od23WVb7ZbPwUQsVpebJJMkJAgDQxYVfslAZDJ6ack9f"
        "9rz+Owe+tubpsvB71BYra0VHFsnOf4RPTQtIWrXpuffJ4q/KwgazoNQ86ZKl1g2GWCMAAB1eFFr7+UOoDFpra/8OefFbI1tv"
        "fOhU4e+sdn+XBoCWYQ/aLZsKAtfe+/wGc/sVWdhQdgRGJaVcUmTXAAB03nBfUiGFLFQG5Kkpedrh5r+9//4bdkwX/jXydr6B"
        "DwHgUgx9JWrN0PQDvGrT99/psl+U7J+ESn/Vm61dAxK3HQaAhV/3kyS3UIlWGVBqjjUk/yOTf2lk61v++tQAcYt14jw/AeBc"
        "QWDL0HSLZ+W9z91mbj8nTx8JlYHlXjTlxVhrwaA4SwAAFtJov/XabbHfLFaUmqOHZOEP3fwPDtx/49Ot9zMNbQndVvgJAFPO"
        "mBq4+p7vLe+Jiza6ip832Tst9siLCXnRKFpXjDAAAO1a9CVZrEaLvfJiUi7/a1P8/cnixLbDD9xxqBwAdlernwBwPkFg586g"
        "Xe+dPtO5NT3w85L9g5DVVkqmlI9JqSAMAEAbFX2FGEPWL8mV8voByf/C5L8/3eaXpHUPZ1q/PnV74ScAnPsJ1do1cGoF6M0b"
        "Xxkc17F7LYSfdk/rQ9a/SEpK+XgZBsxc7oE1AwAw5zU/ySzJ3cqi3ycpKOVjJ8zCTk/pf/Zpyf17t1118lyv6SAA/GhDX4nS"
        "kGbe4vGae/ettCJsCKYPu3x9iL2LZEGe6vJi0iUr5G4yMy202y0DQPtJcneZueTRYo9ZqEmelIqJEybbmVxf9Zh2vHj/TQdO"
        "vX57lLaoW+f3CQCz3RU4Y87omnv3rZRX3h48v1uyd5iF1RZ7y+drMSlPjalTB10ukzlTBgDwBsN7uSWZvBxIKViomsUeSaFc"
        "j+Vpj+TfSpZtlzUfO63oT6/pYrRPAJgTw0Hr1ofXzSMNeVyZ73+bpca7JHuPlO40C6ss9kpm8qIhTw3Jc5crucnNZZKpDAYS"
        "4QBAVxT5clyVJNf0a6EpyDKzUJXFapkFyoI/IoUnJP+mh+qjB7Jrvz2zK3tq/dbOJG1mbp8AMI9hYOi+8hrOfEJKWnH3i30x"
        "m7wtpnCrB7/DvXiXe3pLsLjEsn7JguR5eRJlapRbVVPuUvDp/yCysvsw/WixxgBA29f3GUXY/NQpumZSMoXMzIIUquVJ7JZJ"
        "nuT5mJIXx8zC983io5bse0VIzxR5z9MHt18zftrnGPLyCPct9zlFnwDQDs9607BMO3cGXf2Kn23eadU/PrbURw/eoFC7VWbX"
        "q6jfKdkySTe40qIQe2uSy0L11OLWGf+Xyg4Cz3UA7VpRQvn6NfPt1mYpTw1JplRM1E3hhKTnJX9NsfaE3H+gVH/GBlY8P/In"
        "S46+7uMOfSXq8FVWdl7ltPcJAO0fCIa2BB2+yqT10i4rdI4bSqwcGlmmvPEmC5U3qTGxRLGy1vKGp2DXh1B5s6eGu5uZdLNC"
        "GJQXznQBgHYa9suiKaWTLu01c7dQtZSaPwzJf+BZ1VQ0n1S195in5kvKqi8d2LLqtXPWpXUepZ0qB1NDzOfPkf8DCIFuj8wx"
        "rQMAAAAASUVORK5CYII="
    ),
    "icon-maskable-512.png": (
        "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAYAAAD0eNT6AAAPbklEQVR42u3dS4wk90HH8d+/qrvntQ8/5Nhxso5AdkyEIltW"
        "LhwSLJ9QDiZIlhASEpGCD7kg35CCDKfABQmJAxESByMQByRQFETIDYiREFKIEjDCJJZjsn7EXu96X7MzPd1Vfw7V+7CxAhPv"
        "7kxPfz5Sz8zuSDM1NT31/9a/qqvKqSdfrAEAVkpjFQCAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAABAAAIAAAAAEA"
        "AAgAAEAAAAACAAAQAACAAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAA"
        "AQAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAABAAAIAAAAAEAAAgA"
        "AEAAAAACAAAQAACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAABAAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAA"
        "CAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAEABWAQAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAA"
        "EAAAgAAAAAQAACAAAAABAAAIAAAQAACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAABAAAIAAAAAEAAAgAAEAAAAAC"
        "AAAQAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAABAAAAAAgAAEAAA"
        "gAAAAAQAACAAAAABAAAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQ"
        "AACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAAAWAVAIAAAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAg"
        "AAAAAQAACAAAYJ9GVgFLV62ylUOg1uEBAgBug74mV670VgQHbjIuGbclGgABALdQKcnerOaBe8f5/d+4L+1iw1usGm53hPY1"
        "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"
        "BAAAIAAAAAEAAAgAAEAAAAACAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAA"
        "AAAEAAAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAAAQAACAAAAABAAA"
        "IAAAAAEAAAgAAEAAAAACAAAQAACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAAAQAACAAAQAAAAAIAABAAAIAAAAAE"
        "AAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAAEAAAgAAA"
        "AAQAACAAAAABAAAIAABAAAAAAgAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACAAAAABAAAIAAAAAEAAAgAAEAAAAACAAAQAACA"
        "AAAABAAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAQAAAAAIAABAAAIAAAAAEAAAgAAAAAQAACAAAEAAAgAAAAAQA"
        "ACAAAAABAAAIAABAAAAAAgAAEAAAgAAAAAQAACAAAAABAAAIAABAAAAAAgAAEAAAgAAAAAEAAAgAAEAAAAACAAAQAACAAAAA"
        "BAAAIAAAAAEAAAgAAEAAAAACAAAQAADAfv0PlyW2hbsyGFgAAAAASUVORK5CYII="
    ),
}


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nListo.")
