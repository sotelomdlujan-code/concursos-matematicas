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
  7. Genera docs/index.html (página para el celular) y docs/calendario.ics
     (calendario al que podés suscribirte).
  8. Si deja de poder leer el sitio del CGE, te avisa.
  9. Avisa de publicaciones que son solo imagen/PDF (para revisarlas a mano).

Uso:
  python buscador_concursos.py              # una revisión
  python buscador_concursos.py --todos      # muestra todos los vigentes
  python buscador_concursos.py --vigilar 30 # repite cada 30 minutos

Requisitos:  pip install requests beautifulsoup4
"""

import argparse
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
VERSION_DATOS = 2

# Credenciales: en GitHub vienen de los "Secrets" (ver README).
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN", "")
GITHUB_REPO = os.environ.get("GITHUB_REPOSITORY", "")
GITHUB_USUARIO = os.environ.get("GITHUB_REPOSITORY_OWNER", "")
EMAIL_USUARIO = os.environ.get("EMAIL_USUARIO", "")
EMAIL_CLAVE = os.environ.get("EMAIL_CLAVE", "")
EMAIL_DESTINO = os.environ.get("EMAIL_DESTINO", "") or EMAIL_USUARIO
SMTP_SERVIDOR = os.environ.get("SMTP_SERVIDOR", "smtp.gmail.com")
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
    "paginas": 2,
    "filtros": {
        "escuelas_incluir": [],
        "escuelas_excluir": [],
        "turnos": [],
        "horas_minimas": 0,
    },
    "recordatorios": {"el_dia": True, "dia_antes": True},
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
    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
        return BeautifulSoup(r.text, "html.parser")
    except requests.RequestException as e:
        print(f"  [!] No pude abrir {url}: {e}")
        return None


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


def analizar_texto(lineas, titulo, fecha_pub, materias) -> dict:
    corte = next(
        (i for i, l in enumerate(lineas) if normalizar(l).startswith("los interesados deberan presentarse")),
        None,
    )
    cuerpo = lineas[:corte] if corte is not None else lineas
    lugar = ""
    if corte is not None:
        m = re.search(r"presentarse en\s+(.+?),\s*en el d[ií]a", lineas[corte], re.I)
        if m:
            lugar = m.group(1).strip()

    texto_norm = normalizar("\n".join(cuerpo))
    coincide = materia_de(texto_norm, materias) is not None

    resultado = {
        "coincide": coincide, "items": [], "detalle": [], "fecha_gral": None,
        "materias": [n for n, rx in materias if rx.search(texto_norm)],
        "lugar": lugar, "ordinal": "", "largo": len(" ".join(cuerpo)),
    }
    if not coincide:
        return resultado

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
            nombre = materia_de(normalizar(resto), materias)
            if nombre is None and not propio:
                nombre = materia_de(normalizar(encabezado), materias)
            if nombre is None:
                ultimo = None
                continue
            mc, md, mt, mk = RE_CURSO.search(resto), RE_DIVISION.search(resto), RE_TURNO.search(resto), RE_CARACTER.search(resto)
            ultimo = {
                "materia": nombre,
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
        elif ultimo is not None and (n.startswith("horarios") or RE_DIA.match(n)):
            if n.rstrip(":") == "horarios":
                continue
            if n.startswith("horarios:"):
                l = l.split(":", 1)[1].strip()
            if l:
                ultimo["clases"].append(l)

    fecha_gral = primera_fecha or fecha_titulo
    resultado["fecha_gral"] = fecha_gral.isoformat() if fecha_gral else None
    resultado["ordinal"] = ordinal
    for it in items:
        if it["fecha"] is None:
            it["fecha"] = resultado["fecha_gral"]
    resultado["items"] = items
    if not items:
        resultado["detalle"] = [l for l in cuerpo if materia_de(normalizar(l), materias)][:6]
    return resultado


def analizar_publicacion(url, titulo, fecha_pub, materias):
    soup = descargar(url)
    if soup is None:
        return None
    h1 = soup.find("h1")
    if h1:
        lineas, adjuntos = extraer_lineas(h1), contar_adjuntos(h1)
    else:
        lineas = [limpiar_linea(l) for l in soup.get_text("\n").split("\n") if limpiar_linea(l)]
        adjuntos = 0
    res = analizar_texto(lineas, titulo, fecha_pub, materias)
    res["adjuntos"] = adjuntos
    return res


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


def cerrar_issue(numero: int) -> None:
    gh("PATCH", f"/issues/{numero}", json={"state": "closed", "state_reason": "completed"})


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


def notificar_texto(asunto: str, texto: str) -> None:
    enviar_email(asunto, texto)
    enviar_telegram(f"{asunto}\n\n{texto}")


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
            if isinstance(d, dict) and d.get("version") == VERSION_DATOS:
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
            notificar_texto("⚠️ El buscador no puede leer la página del CGE", texto)
    else:
        if estado.get("alertado"):
            if estado.get("issue_alerta"):
                comentar(estado["issue_alerta"], mencion() + "✅ Volvió a funcionar.")
                cerrar_issue(estado["issue_alerta"])
            notificar_texto("✅ El buscador volvió a funcionar", "Ya puedo leer de nuevo el listado del CGE.")
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


def recordatorios(entradas: dict, cfg: dict, ahora_dt: datetime) -> list:
    hoy, cfg_r, enviados = ahora_dt.date(), cfg["recordatorios"], []
    for url, e in entradas.items():
        if not e.get("relevante") or e.get("vencido"):
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
            enviados.append(texto)
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
        if e.get("vencido") or not (e.get("relevante") or e.get("revisar")):
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


def generar_calendario(entradas: dict, ahora_dt: datetime) -> None:
    sello = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    L = [
        "BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//Concursos CGE//ES", "CALSCALE:GREGORIAN",
        "METHOD:PUBLISH", "X-WR-CALNAME:Concursos docentes - CGE",
        "X-WR-TIMEZONE:America/Argentina/Buenos_Aires",
        "REFRESH-INTERVAL;VALUE=DURATION:PT1H", "X-PUBLISHED-TTL:PT1H",
    ]
    for url, e in entradas.items():
        if not e.get("relevante") or e.get("vencido"):
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
            L += ["BEGIN:VEVENT", f"UID:{uid}", f"DTSTAMP:{sello}"]
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
    ARCHIVO_CALENDARIO.parent.mkdir(exist_ok=True)
    with open(ARCHIVO_CALENDARIO, "w", encoding="utf-8", newline="") as fh:
        fh.write("\r\n".join(_plegar(l) for l in L) + "\r\n")


PLANTILLA_PAGINA = """<!doctype html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Concursos docentes - CGE</title>
<style>
:root{--bg:#fff;--fg:#1a1a1a;--card:#f3f4f6;--link:#0b5fff;--mut:#6b7280;--hoy:#dc2626;--man:#d97706;--ok:#047857}
@media(prefers-color-scheme:dark){:root{--bg:#111;--fg:#eee;--card:#1e1e1e;--link:#6ea8ff;--mut:#9ca3af;--hoy:#f87171;--man:#fbbf24;--ok:#34d399}}
body{font-family:system-ui,sans-serif;background:var(--bg);color:var(--fg);max-width:720px;margin:0 auto;padding:16px}
h1{font-size:1.3rem;margin:.2em 0} h2.s{font-size:1rem;margin:22px 0 4px;color:var(--mut);text-transform:uppercase;letter-spacing:.04em}
article{background:var(--card);border-radius:12px;padding:12px 16px;margin:10px 0}
article h3{font-size:1.02rem;margin:0 0 6px} a{color:var(--link)} ul{padding-left:18px;margin:4px 0} li{margin:3px 0}
.f{margin:8px 0 0;font-weight:600} .b{display:inline-block;font-size:.72rem;font-weight:700;padding:2px 8px;border-radius:99px;margin-right:6px;color:#fff;background:var(--mut)}
.hoy{background:var(--hoy)} .man{background:var(--man);color:#000} small,.mut{color:var(--mut)}
input{width:100%;box-sizing:border-box;padding:10px 12px;border-radius:10px;border:1px solid var(--mut);background:var(--bg);color:var(--fg);font-size:1rem;margin:10px 0}
.cal{display:inline-block;margin:6px 0;padding:8px 12px;border-radius:10px;background:var(--link);color:#fff;text-decoration:none;font-size:.9rem}
details summary{cursor:pointer;color:var(--mut);margin:18px 0 4px} article.v{opacity:.6}
</style></head><body>
<h1>Concursos docentes - CGE</h1>
<small>Actualizado: __ACT__ (hora Argentina) · __RESUMEN__</small><br>
<a class="cal" href="calendario.ics">📅 Suscribirme al calendario</a>
<input id="q" type="search" placeholder="Buscar escuela, materia, turno...">
__CUERPO__
<script>
const norm=s=>s.normalize("NFD").replace(/[\\u0300-\\u036f]/g,"").toLowerCase();
document.getElementById("q").addEventListener("input",e=>{const q=norm(e.target.value);
document.querySelectorAll("article").forEach(a=>{a.style.display=norm(a.dataset.t).includes(q)?"":"none"});});
</script></body></html>"""


def _tarjeta(url: str, e: dict, hoy: date, vencida=False) -> str:
    esc = html.escape
    g, badges, partes = agrupar(e), "", []
    fechas = [date.fromisoformat(f) for (f, _h) in g if f]
    if hoy in fechas:
        badges += '<span class="b hoy">HOY</span>'
    elif hoy + timedelta(days=1) in fechas:
        badges += '<span class="b man">MAÑANA</span>'
    if e.get("ordinal"):
        badges += f'<span class="b">{esc(e["ordinal"])}</span>'
    busq = [e["titulo"], e.get("lugar", "")]
    for (f, h), its in g.items():
        cab = fecha_larga(f) + (f" · {h} hs." if h else "")
        lis = ""
        for i in its:
            busq.append(resumen(i))
            lis += f"<li>{esc(resumen(i))}"
            if i.get("clases"):
                lis += f"<br><small>Clases: {esc(' | '.join(i['clases']))}</small>"
            lis += "</li>"
        if not its:
            lis = "".join(f"<li>{esc(d)}</li>" for d in e.get("detalle", []))
        partes.append(f'<p class="f">🗓 {esc(cab)}</p><ul>{lis}</ul>')
    lugar = f'<p class="mut">📍 {esc(e["lugar"])}</p>' if e.get("lugar") else ""
    return (
        f'<article class="{"v" if vencida else ""}" data-t="{esc(normalizar(" ".join(busq)))}">'
        f'<h3><a href="{esc(url)}">{esc(e["titulo"])}</a></h3>{badges}{"".join(partes)}{lugar}</article>'
    )


def generar_pagina(entradas: dict, ahora_dt: datetime) -> None:
    hoy = ahora_dt.date()

    def clave(item):
        fs = [f for (f, _h) in agrupar(item[1]) if f]
        return min(fs) if fs else "9999"

    vigentes = sorted(((u, e) for u, e in entradas.items() if e.get("relevante") and not e.get("vencido")), key=clave)
    vencidos = sorted(((u, e) for u, e in entradas.items() if e.get("relevante") and e.get("vencido")), key=clave, reverse=True)
    revisar = [(u, e) for u, e in entradas.items() if e.get("revisar") and not e.get("vencido")]
    con_fecha = [x for x in vigentes if clave(x) != "9999"]
    sin_fecha = [x for x in vigentes if clave(x) == "9999"]

    cuerpo = ""
    if con_fecha:
        cuerpo += '<h2 class="s">Próximos</h2>' + "".join(_tarjeta(u, e, hoy) for u, e in con_fecha)
    else:
        cuerpo += '<p class="mut">No hay concursos próximos detectados.</p>'
    if sin_fecha:
        cuerpo += '<h2 class="s">Sin fecha detectada</h2>' + "".join(_tarjeta(u, e, hoy) for u, e in sin_fecha)
    if revisar:
        cuerpo += '<h2 class="s">👀 Revisar a mano (imagen/PDF)</h2>' + "".join(
            f'<article data-t="{html.escape(normalizar(e["titulo"]))}"><h3><a href="{html.escape(u)}">{html.escape(e["titulo"])}</a></h3></article>'
            for u, e in revisar
        )
    if vencidos:
        cuerpo += f'<details><summary>Vencidos ({len(vencidos)})</summary>' + "".join(_tarjeta(u, e, hoy, True) for u, e in vencidos[:60]) + "</details>"

    ARCHIVO_PAGINA.parent.mkdir(exist_ok=True)
    pagina = (
        PLANTILLA_PAGINA.replace("__ACT__", ahora_dt.strftime("%d/%m/%Y %H:%M"))
        .replace("__RESUMEN__", f"{len(vigentes)} vigente(s)")
        .replace("__CUERPO__", cuerpo)
    )
    ARCHIVO_PAGINA.write_text(pagina, encoding="utf-8")


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

    print(f"Buscando: {', '.join(cfg['materias'])}")
    pubs = obtener_publicaciones(cfg)
    print(f"Publicaciones en el listado: {len(pubs)}")
    revisar_salud(estado, cfg, len(pubs))

    nuevos, a_revisar = [], []
    for titulo, url, fpub, fuente in reversed(pubs):  # de la más vieja a la más nueva
        if url in entradas:
            continue
        res = analizar_publicacion(url, titulo, parse_dmy(fpub) or ahora_dt.date(), materias)
        time.sleep(PAUSA_ENTRE_PEDIDOS)
        if res is None:
            continue  # error de red: la reintento en la próxima revisión
        ok, items = res["coincide"], res["items"]
        if ok:
            ok, items = aplicar_filtros(titulo, items, cfg)
        fechas = sorted({i["fecha"] for i in items if i.get("fecha")}) or ([res["fecha_gral"]] if (ok and res["fecha_gral"]) else [])
        e = {
            "titulo": titulo, "fuente": fuente, "fecha_pub": fpub,
            "visto": ahora_dt.isoformat(timespec="minutes"),
            "relevante": ok, "items": items if ok else [],
            "detalle": res["detalle"] if ok else [], "fechas": fechas if ok else [],
            "materias": res["materias"] if ok else [],
            "lugar": res["lugar"] if ok else "", "ordinal": res["ordinal"] if ok else "",
            "grupo": calcular_grupo(titulo, items, res["detalle"]) if ok else "",
            "issue": None, "issue_abierto": False, "vencido": False, "recordados": [],
        }
        if not res["coincide"] and cfg.get("avisar_publicaciones_sin_texto", True) and res["adjuntos"] > 0 and res["largo"] < 200:
            e["revisar"] = True
            a_revisar.append(url)
        entradas[url] = e
        if ok:
            nuevos.append(url)

    # Avisos de nuevos (en orden cronológico, para que una 2.ª convocatoria caiga en el Issue de la 1.ª)
    for url in nuevos:
        notificar_nuevo(entradas, url, entradas[url])
    for url in a_revisar:
        notificar_revisar(url, entradas[url])
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

    recs = recordatorios(entradas, cfg, ahora_dt)
    if recs:
        print(f"\n=== RECORDATORIOS: {len(recs)} ===\n" + "\n\n".join(recs))
        enviar_email(f"⏰ {len(recs)} recordatorio(s) de concursos", "\n\n".join(recs))
        for t in recs[:MAX_TELEGRAM_POR_CORRIDA]:
            enviar_telegram(t)

    cerrar_vencidos(entradas, cfg, ahora_dt)
    guardar_historial(datos)
    generar_pagina(entradas, ahora_dt)
    generar_calendario(entradas, ahora_dt)

    if mostrar_todos:
        vig = [(u, e) for u, e in entradas.items() if e.get("relevante") and not e.get("vencido")]
        print(f"\n=== Vigentes: {len(vig)} ===\n")
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


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nListo.")
