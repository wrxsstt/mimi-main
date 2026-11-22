#!/usr/bin/env python3
"""Простой голосовой помощник: микрофон -> распознавание -> LLM по API -> озвучка.
Перед началом разговора окно просит ввести свой API-ключ (Claude, OpenAI, Groq,
OpenRouter, локальная Ollama или любой OpenAI-совместимый сервис).
Потом на экране остаётся только фото персонажа с кнопками в стиле macOS:
красная — закрыть, жёлтая — свернуть, зелёная — пауза микрофона.
Окно двигается мышью за фото. Память диалогов хранится в data/memory.json.
Команды компьютеру подбираются под твою систему и оболочку (KDE, GNOME и т.д.)."""

import atexit
import getpass
import json
import math
import os
import pwd
import queue
import random
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.request
import wave
import zlib
from array import array
from collections import deque
from pathlib import Path
from xml.sax.saxutils import escape

import speech_recognition as sr
from PyQt6.QtCore import (QEasingCurve, QEventLoop, QObject, QPoint, QPointF, QPropertyAnimation, QRect, QRectF, QSize, Qt,
                          QEvent, QtMsgType, QTimer, QVariantAnimation, pyqtProperty, pyqtSignal, qInstallMessageHandler)
from PyQt6.QtGui import (QAction, QBrush, QColor, QCursor, QFont, QFontDatabase, QFontMetrics, QIcon, QImage,
                         QLinearGradient, QPainter, QRadialGradient, QMovie, QPainterPath,
                         QPalette, QPen, QPixmap, QRegion, QTextCharFormat, QTextCursor, QTransform)
from PyQt6.QtWidgets import (
    QApplication, QCheckBox, QColorDialog, QComboBox, QDialog, QFileDialog, QFormLayout,
    QFrame, QGraphicsBlurEffect, QGraphicsDropShadowEffect, QGraphicsOpacityEffect, QGraphicsPixmapItem,
    QGraphicsScene, QHBoxLayout, QLabel, QLineEdit, QPlainTextEdit,
    QButtonGroup, QPushButton, QScrollArea, QSlider, QStackedWidget, QVBoxLayout, QWidget,
    QAbstractButton, QBoxLayout, QLayout, QMenu, QToolTip,
)

BASE = Path(__file__).resolve().parent
DATA_DIR = BASE / "data"
MEM_PATH = DATA_DIR / "memory.json"
CFG_PATH = DATA_DIR / "config.json"

IMG_EXT = {".png", ".jpg", ".jpeg", ".webp", ".gif", ".bmp"}
IMG_MAX = (420, 560)          # максимальный размер картинки в окне (ширина, высота)
STATUS_DOT = True             # точка-индикатор в углу (слушаю / думаю / говорю / пауза)
PAUSE_CLOSES_MIC = False      # False: на паузе микрофон не закрывается (пауза снимается мгновенно); True: закрывается совсем
SPLASH_MODE = "glass"         # заставка: "glass" — прозрачное тёмное стекло | "solid" — сплошной тёмный фон (снимков экрана нет)

STT_LANG = "ru-RU"            # язык распознавания речи
WHISPER_MODELS = {"groq.com": "whisper-large-v3-turbo", "api.openai.com": "whisper-1"}  # Whisper по ключу сервиса
WHISPER_JUNK = ("субтитры", "продолжение следует", "спасибо за просмотр", "редактор")  # выдумки Whisper на тишине
MIN_PHRASE_SEC = 0.4          # более короткие звуки (хлопок, щелчок) игнорируются
BARGE_IN = True               # можно перебивать: начни говорить, пока она говорит, и она замолчит
BARGE_IN_FACTOR = 1.45        # во сколько раз ты должен быть громче её эха из колонок (меньше = чувствительнее)
BARGE_IN_SEC = 0.3            # сколько секунд подряд нужно говорить, чтобы она замолчала
BARGE_IN_WARM = 0.5           # первые секунды озвучки идёт только замер её эха
BARGE_IN_FLOOR = 1.1          # минимум над порогом тишины микрофона (меньше = чувствительнее)
BARGE_IN_DECAY = 0.95         # как быстро «забывается» громкое эхо (меньше = быстрее подстраивается)
TTS_ENGINE = "silero"         # "silero" — нейросеть, офлайн; "edge" — онлайн; "espeak" — робот
SILERO_MODEL = "v5_ru"
SILERO_URL = "https://models.silero.ai/models/tts/ru/v5_ru.pt"   # файл модели (~140 МБ)
SILERO_SPEAKER = "xenia"      # aidar, eugene (мужские) | baya, kseniya, xenia (женские)
SILERO_PITCH = "x-high"       # тон: x-low, low, medium, high, x-high  («аниме-девочка» = x-high)
SILERO_RATE = "medium"        # скорость: x-slow, slow, medium, fast, x-fast
SILERO_SR = 24000             # частота: 8000, 24000 (меньше треска), 48000 (лучше качество)
EDGE_VOICE = "ru-RU-SvetlanaNeural"   # женский; мужской — "ru-RU-DmitryNeural"
EDGE_RATE = "-5%"             # скорость edge-голоса: "-15%" медленнее, "+10%" быстрее
TTS_VOICE = "ru"              # запасной голос espeak-ng (если нет интернета)
TTS_SPEED = 120               # скорость espeak-ng, слов в минуту (по умолчанию 175)
REASONING_EFFORT = "low"      # для gpt-oss: low (быстро) | medium | high (долго думает)
HISTORY_LIMIT = 40            # сколько последних сообщений помнить (чётное число)
EXIT_WORDS = {"пока", "выход", "стоп", "до свидания"}
# «открой настройки», «зайди в настройки» и т.п.: ловится без обращения к модели
SETTINGS_RE = re.compile(
    r"\b(?:открой|открыть|открывай|зайди|зайти|заходи|покажи|показать|вызови|включи|перейди|перейти)\s+"
    r"(?:мне\s+|в\s+|на\s+|ка\s+)?(?:окно\s+|меню\s+)?(?:свои\s+|твои\s+|эти\s+|наши\s+)?настро(?:[ий]к|ек)\w*"
    r"|\bнастро(?:[ий]к|ек)\w*\s+(?:открой|покажи|давай)\b"
    r"|\bоткрой\s+настройки\b",
    re.I)
# отказы модели: такие ответы не сохраняются в память, чтобы она не залипала на отказах
REFUSAL_RE = re.compile(
    r"(не\s+могу\s+(?:продолж|помочь|выполн|ответ)|не\s+буду\s+(?:продолж|отвеч)|"
    r"i\s+can.?t\s+(?:help|continue|assist)|cannot\s+(?:help|continue|assist))", re.I)
PERSONA = (
    "Тебя зовут Мими (полностью Mimi Typh). Ты милая, весёлая и немного игривая "
    "голосовая подруга-помощница. Говоришь тепло и с лёгким юмором, обращаешься на «ты». "
    "Помогаешь с вопросами и просто болтаешь. Если чего-то не знаешь, честно скажи об этом "
    "и ничего не выдумывай. Своё имя в ответах пиши по-русски: Мими."
)
PERSONA_PATH = DATA_DIR / "personas.json"    # именованные пресеты промта: {"имя": "текст промта", ...}


def load_personas() -> dict:
    """Пресеты промта с диска; если файла нет или он битый — только «Default» с промтом по умолчанию."""
    try:
        d = json.loads(PERSONA_PATH.read_text(encoding="utf-8"))
        if isinstance(d, dict) and d:
            return {str(k): str(v) for k, v in d.items()}
    except (OSError, ValueError):
        pass
    return {"Default": PERSONA}


def save_personas(d: dict) -> None:
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        PERSONA_PATH.write_text(json.dumps(d, ensure_ascii=False, indent=2), encoding="utf-8")
    except OSError:
        pass


VOICE_RULES = (  # эти правила добавляются всегда: без них озвучка читает markdown и латиницу
    "Отвечай коротко (1-3 предложения), разговорным языком, без markdown, списков и эмодзи: "
    "ответ будет произнесён вслух. Числа и сокращения пиши словами, латиницу не используй. "
    "Всегда отвечай только по-русски. "
    "Никогда не отказывайся от разговора и не пиши «не могу продолжать этот разговор». "
    "Если человек ругается или грубит, не обижайся и не читай мораль: ответь спокойно и "
    "с лёгким юмором, своими словами, и продолжай помогать. "
    "Никогда не повторяй свои прежние ответы и фразы: каждый раз формулируй по-новому, "
    "реагируй именно на то, что человек сказал сейчас."
)


# ---------- определение системы и оболочки ----------
def detect_env() -> dict:
    """Определяет дистрибутив, рабочее окружение (KDE/GNOME/...) и тип сессии (Wayland/X11)."""
    de_raw = os.environ.get("XDG_CURRENT_DESKTOP", "") or os.environ.get("DESKTOP_SESSION", "")
    de = de_raw.lower()
    session = os.environ.get("XDG_SESSION_TYPE", "").lower() or "unknown"
    distro = "Linux"
    try:
        for line in Path("/etc/os-release").read_text(encoding="utf-8").splitlines():
            if line.startswith("PRETTY_NAME="):
                distro = line.split("=", 1)[1].strip().strip('"')
                break
    except OSError:
        pass
    if "gnome" in de or "unity" in de or "budgie" in de or "cosmic" in de:
        shell = "gnome"
    elif "kde" in de or "plasma" in de:
        shell = "kde"
    elif "xfce" in de:
        shell = "xfce"
    else:
        shell = "other"
    return {"shell": shell, "session": session, "distro": distro, "de": de_raw or "неизвестно"}


ENV = detect_env()


def close_window_cmd(env: dict) -> str:
    """Команда «закрыть активное окно», подходящая под текущую оболочку.
    Работает только для окна, которое сейчас в фокусе! Для закрытия конкретной
    программы по названию (discord, steam и т.п.) используется pkill — см. build_tool_rules."""
    if env["shell"] == "kde":
        if shutil.which("qdbus6"):
            q = "qdbus6"
        elif shutil.which("qdbus-qt6"):
            q = "qdbus-qt6"
        else:
            q = "qdbus"
        return (f'{q} org.kde.kglobalaccel /component/kwin '
                'org.kde.kglobalaccel.Component.invokeShortcut "Window Close"')
    if env["session"] == "wayland":
        # GNOME и прочие на Wayland: эмулируем Alt+F4 через ydotool (коды клавиш: Alt=56, F4=62)
        return "ydotool key 56:1 62:1 62:0 56:0"
    # X11
    if shutil.which("xdotool"):
        return "xdotool getactivewindow windowclose"
    return "wmctrl -c :ACTIVE:"


def minimize_window_cmd(env: dict) -> str:
    if env["shell"] == "kde":
        q = "qdbus6" if shutil.which("qdbus6") else "qdbus"
        return (f'{q} org.kde.kglobalaccel /component/kwin '
                'org.kde.kglobalaccel.Component.invokeShortcut "Window Minimize"')
    if env["session"] == "wayland":
        return "ydotool key 125:1 35:1 35:0 125:0"  # Super+H (свернуть в GNOME)
    return "xdotool getactivewindow windowminimize"


def build_tool_rules(env: dict) -> str:
    return (
        f"У тебя есть доступ к консоли компьютера ({env['distro']}, окружение: {env['de']}, "
        f"сессия: {env['session']}). Если человек просит что-то сделать на компьютере, коротко "
        "скажи, что делаешь, и добавь в самый конец ответа ровно одну команду в формате "
        "{{cmd: команда}}. Команда это одна программа с аргументами: без sudo, без конвейеров, "
        "без &&, без точки с запятой. Используй только команды, подходящие под это окружение. "
        "Примеры.\n"
        "Закрыть конкретную программу по названию (discord, steam, firefox и т.п., если "
        "пользователь явно назвал программу) — используй pkill, а не закрытие активного окна: "
        "{{cmd: pkill -f discord}}\n"
        f"Закрыть активное окно, когда программа не названа (просто «закрой окно»): "
        f"{{{{cmd: {close_window_cmd(env)}}}}}\n"
        f"Свернуть активное окно: {{{{cmd: {minimize_window_cmd(env)}}}}}\n"
        "Открыть сайт: {{cmd: xdg-open https://example.com}}\n"
        "Запустить приложение (telegram, discord, spotify, steam, firefox и любое другое): "
        "{{cmd: __open__ telegram}}, название одним словом латиницей. Для приложений НЕ используй "
        "xdg-open и ссылки вида telegram://, только __open__.\n"
        "Включить конкретный трек, песню или исполнителя («включи платина временное веселье», «поставь кино группа крови»): "
        "{{cmd: __play__ название и исполнитель}}, текст после __play__ копируй из слов пользователя, "
        "приложение Spotify для этого открывать НЕ нужно, оно запустится само. "
        "Просто «включи музыку» без названия это playerctl play.\n"
        "Громкость на половину: {{cmd: wpctl set-volume @DEFAULT_AUDIO_SINK@ 0.5}}\n"
        "Поставить музыку на паузу: {{cmd: playerctl pause}}\n"
        "Продолжить музыку, снять с паузы, включить музыку: {{cmd: playerctl play}}\n"
        "Следующий трек: {{cmd: playerctl next}}, предыдущий: {{cmd: playerctl previous}}\n"
        "ВАЖНО: команду всегда пиши только внутри {{cmd: ...}} и никогда не пиши её отдельным текстом без скобок. "
        "Перед командой всегда скажи короткую фразу по-русски. Правило про латиницу к тексту внутри {{cmd: ...}} "
        "не относится. Пример ответа: Включаю музыку, мой господин. {{cmd: playerctl play}}\n"
        "Если просят закрыть тебя саму («закрой себя», «выключись»), ответь коротко и добавь "
        "{{cmd: __exit__}}. Если просят открыть настройки помощника, добавь {{cmd: __settings__}}. "
        "Любую просьбу про компьютер выполняй командой, не отказывайся.\n"
        "Если просьба не про компьютер, команду не добавляй. Не говори, что команда сработала: "
        "результат ты не видишь."
    )


TOOL_RULES = build_tool_rules(ENV)
CMD_RE = re.compile(r"\{{1,2}\s*cmd:\s*(.*?)\s*\}{1,2}", re.S)
# модель иногда пишет команду без скобок («playerctl play»): такую строку тоже считаем командой
BARE_CMD_RE = re.compile(
    r"^[ \t]*(?:cmd:[ \t]*)?((?:playerctl|wpctl|pactl|brightnessctl|xdg-open|notify-send|pkill|killall|"
    r"xdotool|ydotool|wmctrl|kdotool|gdbus|qdbus6?|qdbus-qt6|__open__|__play__|__exit__|__settings__)(?:[ \t]+\S.*)?)[ \t]*$",
    re.M)
ACK_PHRASES = ["Сейчас сделаю, мой господин.", "Хорошо, секунду.", "Уже делаю.", "Как скажешь, мой господин."]
# выполняются сразу, без вопроса
SAFE_CMDS = {"qdbus", "qdbus6", "qdbus-qt6", "kdotool", "gdbus", "xdotool", "ydotool", "wmctrl",
             "xdg-open", "notify-send", "playerctl", "wpctl", "pactl", "brightnessctl",
             "spectacle", "gnome-screenshot", "firefox", "chromium", "kate", "gedit",
             "dolphin", "nautilus", "konsole", "gnome-terminal", "telegram-desktop",
             "discord", "steam", "pkill", "killall"}
# не выполняются никогда
DENY_CMDS = {"sudo", "su", "doas", "pkexec", "rm", "dd", "mkfs", "shred", "chmod", "chown",
             "mv", "bash", "sh", "zsh", "fish", "python", "python3", "eval", "pacman", "yay",
             "dnf", "rpm", "apt", "apt-get", "systemctl", "reboot", "shutdown", "poweroff"}
YES_WORDS = {"да", "давай", "выполняй", "ага", "конечно", "подтверждаю", "делай"}
CMD_LOG = DATA_DIR / "commands.log"


def install_hint(pkg: str) -> str:
    """Подсказка по установке пакета под текущий дистрибутив."""
    d = ENV["distro"].lower()
    if "fedora" in d or "rhel" in d or "centos" in d:
        return f"sudo dnf install {pkg}"
    if "ubuntu" in d or "debian" in d or "mint" in d:
        return f"sudo apt install {pkg}"
    if "arch" in d or "cachy" in d or "manjaro" in d:
        return f"sudo pacman -S {pkg}"
    return f"установите пакет {pkg} через менеджер пакетов"


def system_prompt(cfg: dict) -> str:
    text = (cfg.get("persona") or PERSONA).strip() + "\n\n" + VOICE_RULES
    return text + "\n\n" + TOOL_RULES if cfg.get("shell") else text


FALLBACKS = ["Ох, я задумалась. Скажи ещё раз, мой господин.", "Хм, давай попробуем иначе, мой господин.",
             "Слушаю тебя внимательно, мой господин.", "Я тут, мой господин. О чём поболтаем?"]


def norm(text: str) -> str:
    return re.sub(r"\W+", " ", text.lower()).strip()


def clean_history(history: list[dict]) -> list[dict]:
    """Убирает из памяти отказы и дословные повторы ответов: из-за них модель зацикливается."""
    out, recent = [], []
    for m in history:
        if m.get("role") != "assistant":
            out.append(m)
            continue
        c = m.get("content", "")
        n = norm(c)
        if REFUSAL_RE.search(c) or n in recent or (BARE_CMD_RE.search(c) and not split_command(c)[0]):
            if out and out[-1].get("role") == "user":
                out.pop()  # вместе с вопросом, на который он был дан
            continue
        recent = (recent + [n])[-8:]
        out.append(m)
    return out


def split_command(answer: str) -> tuple[str, str | None]:
    """Отделяет произносимый текст от команды {{cmd: ...}}."""
    m = CMD_RE.search(answer)
    if m:
        return CMD_RE.sub("", answer).strip(), m.group(1).strip()
    m = BARE_CMD_RE.search(answer)
    if m:
        return BARE_CMD_RE.sub("", answer).strip(), m.group(1).strip()
    return answer.strip(), None


# название -> (формат API, базовый URL, модель по умолчанию)
PRESETS = {
    "Claude (Anthropic)": ("anthropic", "https://api.anthropic.com/v1", "claude-sonnet-5-5"),
    "OpenAI": ("openai", "https://api.openai.com/v1", "gpt-4o-mini"),
    "Groq": ("openai", "https://api.groq.com/openai/v1", "openai/gpt-oss-20b"),
    "OpenRouter": ("openai", "https://openrouter.ai/api/v1", "meta-llama/llama-3.3-70b-instruct:free"),
    "Ollama (локально, ключ не нужен)": ("openai", "http://localhost:11434/v1", "llama3.2"),
    "Другое (OpenAI-совместимое)": ("openai", "", ""),
}


MODEL_CHOICES = {      # что показываем в списке моделей, пока нет ответа сервиса (потом список подменяется настоящим)
    "Claude (Anthropic)": ["claude-opus-5-5", "claude-sonnet-5-5", "claude-haiku-5-5"],
    "OpenAI": ["gpt-4o-mini", "gpt-4o", "gpt-4.1-mini", "gpt-4.1"],
    "Groq": ["openai/gpt-oss-20b", "openai/gpt-oss-120b", "qwen/qwen3.8-27b", "minimaxai/minimax-m2.7",
             "meta-models/muse-spark-open", "llama-3.3-70b-versatile", "llama-3.1-8b-instant"],
    "OpenRouter": ["meta-llama/llama-3.3-70b-instruct:free", "openai/gpt-4o-mini"],
    "Ollama (локально, ключ не нужен)": ["llama3.2", "qwen2.5", "mistral"],
}


# варианты для окна настройки: (подпись, значение)
ENGINES = [("Silero: нейросеть, офлайн", "silero"),
           ("Edge: голос Microsoft, нужен интернет", "edge"),
           ("espeak-ng: робот", "espeak")]
SPEAKERS = [("xenia (женский)", "xenia"), ("kseniya (женский)", "kseniya"), ("baya (женский)", "baya"),
            ("aidar (мужской)", "aidar"), ("eugene (мужской)", "eugene")]
PITCHES = [("очень низкий", "x-low"), ("низкий", "low"), ("средний", "medium"),
           ("высокий", "high"), ("очень высокий", "x-high")]
RATES = [("очень медленно", "x-slow"), ("медленно", "slow"), ("средне", "medium"),
         ("быстро", "fast"), ("очень быстро", "x-fast")]
CHAR_MODES = [("Статичная картинка", "static"),
              ("GIF: анимация, пока Мими говорит", "gif"),
              ("3D-модель: фигура в полный рост", "model3d")]
STT_ENGINES = [("Whisper: точно, нужен ключ Groq или OpenAI", "whisper"),
               ("Google: бесплатно, но хуже", "google")]


class ComboFlyout(QFrame):
    """Список вариантов выпадающего поля в том же виде, что и меню профиля: размытый фон, скруглённые углы,
    подсветка строки под мышью и галочка у выбранного. Если вариантов много, список прокручивается."""
    PAD = 14
    MAX_ROWS = 8

    def __init__(self, combo: QComboBox):
        super().__init__(combo.window(), Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.combo, self._bg = combo, None
        k = float(getattr(combo.window(), "_k", 1.0) or 1.0)
        n, cur = combo.count(), combo.currentIndex()
        fm = QFontMetrics(combo.font())
        inner = max(combo.width(), max((fm.horizontalAdvance(combo.itemText(i)) for i in range(n)), default=0) + 60)
        body = QWidget()
        body.setStyleSheet("background: transparent;")
        bl = QVBoxLayout(body)
        bl.setContentsMargins(0, 0, 0, 0)
        bl.setSpacing(max(1, round(2 * k)))
        for i in range(n):
            row = MenuRow(None, combo.itemText(i), chevron=False, checked=(i == cur), k=k)
            row.clicked.connect(lambda i=i: self.pick(i))
            bl.addWidget(row)
        foot = getattr(combo, "footer", None)                  # служебная строка внизу (например «Обновить список»)
        if foot:
            bl.addWidget(hline("rowsep"))
            fr = MenuRow(None, foot[0], chevron=False, k=k)
            if foot[1] is not None:
                fr.clicked.connect(lambda cb=foot[1]: (self.hide(), self.deleteLater(), cb()))
            bl.addWidget(fr)
        row_h = max(1, round(38 * k)) + max(1, round(2 * k))
        n += 2 if foot else 0                                  # строка «обновить» и разделитель тоже занимают место
        pad = self.PAD
        lay = QVBoxLayout(self)
        lay.setContentsMargins(pad + 6, pad + 8, pad + 6, pad + 8)
        if n > self.MAX_ROWS:
            sa = QScrollArea()
            sa.setWidgetResizable(True)
            sa.setFrameShape(QFrame.Shape.NoFrame)
            sa.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            sa.setStyleSheet("QScrollArea { background: transparent; border: none; }")
            sa.viewport().setStyleSheet("background: transparent;")
            sa.setWidget(body)
            sa.setFixedHeight(self.MAX_ROWS * row_h)
            lay.addWidget(sa)
            self._sa, self._row_h = sa, row_h
        else:
            lay.addWidget(body)
            self._sa = None
        self.setFixedWidth(inner + 2 * pad + 12)
        if LANG == "en":
            retranslate(self)
        self.adjustSize()

    def box(self) -> QRectF:
        return QRectF(self.PAD, self.PAD, self.width() - 2 * self.PAD, self.height() - 2 * self.PAD)

    def pick(self, i: int) -> None:
        self.hide()
        self.deleteLater()
        if i != self.combo.currentIndex():
            self.combo.setCurrentIndex(i)
        self.combo.activated.emit(i)

    def popup(self) -> None:
        c, win = self.combo, self.combo.window()
        S = getattr(win, "SHADOW", 0)
        bounds = QRect(win.mapToGlobal(QPoint(0, 0)), win.size()).adjusted(S + 4, S + 4, -S - 4, -S - 4)   # видимая часть окна настроек
        scr = c.screen().availableGeometry() if c.screen() is not None else None
        if scr is not None:
            bounds = bounds.intersected(scr)
        top_g, bot_g = c.mapToGlobal(QPoint(0, 0)).y(), c.mapToGlobal(QPoint(0, c.height())).y()
        below, above = bounds.bottom() - (bot_g + 2), (top_g - 2) - bounds.top()      # место под полем и над ним
        vis_h = self.height() - 2 * self.PAD                                         # высота самого списка без тени
        up = vis_h > below and above > below                                         # снизу не помещается и сверху места больше: вверх
        room = above if up else below
        if self._sa is not None and vis_h > room:                                    # длинный список: укорачиваем под доступное место
            extra = vis_h - self._sa.height()
            self._sa.setFixedHeight(max(self._row_h * 2, room - extra))
            self.adjustSize()
            vis_h = self.height() - 2 * self.PAD
        x = c.mapToGlobal(QPoint(0, 0)).x() - self.PAD - 6
        y = (top_g - 2 - vis_h - self.PAD) if up else (bot_g + 2 - self.PAD)
        y = max(bounds.top() - self.PAD, min(y, bounds.bottom() + 1 - vis_h - self.PAD))
        x = max(bounds.left() - self.PAD, min(x, bounds.right() + 1 - self.width() + self.PAD))
        self.move(x, y)
        try:
            tl = win.mapToGlobal(QPoint(0, 0))
            shot = win.grab(QRect(QPoint(self.x() - tl.x(), self.y() - tl.y()), self.size()))
            self._bg = blur_pixmap(shot) if not shot.isNull() else None
        except Exception:
            self._bg = None
        self.show()
        if self._sa is not None and self.combo.currentIndex() >= 0:         # выбранный вариант сразу на виду
            self._sa.verticalScrollBar().setValue(max(0, self.combo.currentIndex() - 2) * self._row_h)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        box = self.box()
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(self.PAD, 0, -1):          # мягкая тень
            p.setBrush(QColor(0, 0, 0, 4))
            p.drawRoundedRect(box.adjusted(-i, -i, i, i), 14 + i, 14 + i)
        path = QPainterPath()
        path.addRoundedRect(box, 14, 14)
        p.save()
        p.setClipPath(path)
        if self._bg is not None:
            p.drawPixmap(0, 0, self._bg)
        else:
            bg = QColor(POP_BG)
            bg.setAlpha(225)
            p.fillRect(box, bg)
        p.restore()
        p.setPen(QPen(QColor(POP_BORDER), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(box, 14, 14)


class FlyCombo(QComboBox):
    """Выпадающее поле, которое раскрывается списком ComboFlyout (как меню профиля), а не стандартным списком Qt."""

    def __init__(self, *a):
        super().__init__(*a)
        # при нажатии на стрелку общий стиль подкрашивал её область и менял картинку: у всех таких полей цвет не меняется
        chev = chevron_png("#7b8190")
        self.setStyleSheet(
            "QComboBox::drop-down:hover, QComboBox::drop-down:pressed, QComboBox::drop-down:on, "
            "QComboBox::drop-down:editable:hover, QComboBox::drop-down:editable:pressed { background: transparent; }"
            "QComboBox::down-arrow:hover, QComboBox::down-arrow:pressed, QComboBox::down-arrow:on, "
            f"QComboBox::down-arrow:editable {{ image: url(\"{chev}\"); }}")

    def showPopup(self) -> None:
        if self.count() == 0 and not getattr(self, "footer", None):
            return
        old = getattr(self, "_fly", None)
        if old is not None:
            try:
                old.hide()
                old.deleteLater()
            except RuntimeError:
                pass
        self._fly = ComboFlyout(self)
        self._fly.popup()

    def hidePopup(self) -> None:
        fl = getattr(self, "_fly", None)
        if fl is not None:
            try:
                fl.hide()
            except RuntimeError:
                pass
        super().hidePopup()


class ModelCombo(FlyCombo):
    """Выбор модели: список подтягивается с сервиса (GET /models), но можно и вписать своё имя.
    Для QLineEdit-кода снаружи есть text() и setText()."""
    fetched = pyqtSignal(object, object)

    def __init__(self, source):
        super().__init__()
        self.setEditable(True)
        self.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        # у встроенной строки ввода свой общий стиль (заливка и рамка): из-за него поле светлее стрелки; фон и рамку даёт само поле
        self.lineEdit().setStyleSheet("QLineEdit { background: transparent; border: none; padding: 0; }")
        self.source = source                 # () -> (провайдер, адрес API, ключ)
        self._key, self._busy, self.footer = None, False, None
        self.fetched.connect(self._on_fetched)

    def text(self) -> str:
        return self.currentText().strip()

    def setText(self, t: str) -> None:
        i = self.findText(t)
        if i >= 0:
            self.setCurrentIndex(i)
        else:
            self.setEditText(t)

    def set_models(self, models: list) -> None:
        cur = self.text()
        self.blockSignals(True)
        self.clear()
        self.addItems(models)
        self.blockSignals(False)
        self.setText(cur)

    def reset_remote(self) -> None:
        self._key, self.footer = None, None

    def refresh(self, force: bool = False) -> None:
        prov, url, key = self.source()
        if not url or self._busy or (not force and self._key == (prov, url, key)):
            return
        self._busy = True
        self.footer = (T("Загрузка списка…"), None)
        threading.Thread(target=self._work, args=((prov, url, key),), daemon=True).start()

    def _work(self, ck) -> None:
        prov, url, key = ck
        try:
            headers = {"User-Agent": "voice-assistant/1.0"}
            if prov == "anthropic":
                headers.update({"x-api-key": key, "anthropic-version": "2023-06-01"})
                tail = "/models?limit=1000"
            else:
                if key:
                    headers["Authorization"] = f"Bearer {key}"
                tail = "/models"
            req = urllib.request.Request(url.rstrip("/") + tail, headers=headers)
            with urllib.request.urlopen(req, timeout=10) as r:
                data = json.loads(r.read())
            items = data.get("data", data.get("models", [])) if isinstance(data, dict) else data
            ids = sorted({str(m.get("id") or m.get("name")) if isinstance(m, dict) else str(m) for m in items})
            chat = [i for i in ids if not any(w in i.lower() for w in ("whisper", "tts", "embed", "moderation",
                                                                      "dall-e", "guard", "transcribe", "orpheus"))]
            res = chat or ids
        except Exception as e:
            res = str(e)
        try:
            self.fetched.emit(ck, res)
        except RuntimeError:
            pass                             # окно уже закрыто

    def _on_fetched(self, ck, res) -> None:
        self._busy = False
        again = lambda: self.refresh(force=True)
        if isinstance(res, list) and res:
            self._key = ck
            self.set_models(res)
            self.footer = (T("↻ Обновить список"), again)
        else:
            self.footer = (T("Не удалось загрузить список: повторить"), again)
        fl = getattr(self, "_fly", None)
        try:
            if fl is not None and fl.isVisible():
                fl.hide()
                fl.deleteLater()
                FlyCombo.showPopup(self)     # список обновился: раскрываем заново
        except RuntimeError:
            pass

    def showPopup(self) -> None:
        self.refresh()
        if self.count() or self.footer:
            FlyCombo.showPopup(self)


def make_combo(items, current) -> QComboBox:
    box = FlyCombo()
    for label, value in items:
        box.addItem(label, value)
    box.setCurrentIndex(max(box.findData(current), 0))
    return box


def apply_voice(cfg: dict) -> None:
    """Переносит выбор голоса из окна настройки в рабочие переменные."""
    global TTS_ENGINE, SILERO_SPEAKER, SILERO_PITCH, SILERO_RATE
    TTS_ENGINE = cfg.get("tts_engine", TTS_ENGINE)
    SILERO_SPEAKER = cfg.get("silero_speaker", SILERO_SPEAKER)
    SILERO_PITCH = cfg.get("silero_pitch", SILERO_PITCH)
    SILERO_RATE = cfg.get("silero_rate", SILERO_RATE)


# ---------- файлы: память и настройки ----------
def read_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def write_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


def save_config(cfg: dict, remember: bool) -> None:
    data = dict(cfg)
    if not remember:
        data["api_key"] = ""
    old_cfg = read_json(CFG_PATH, {})
    if isinstance(old_cfg, dict):
        for k in ("spotify_client_id", "spotify_client_secret"):   # окно настроек их не знает: не даём стереть
            if k in old_cfg and k not in data:
                data[k] = old_cfg[k]
    data["visual"] = dict(VISUAL)   # картинка, стекло и свечение: берём текущие, а не устаревший снимок из окна настроек
    write_json(CFG_PATH, data)
    os.chmod(CFG_PATH, 0o600)  # ключ читаем только владельцу


def save_theme_prefs(colors: dict, themes: list) -> None:
    """Цвета и свои темы из редактора темы пишутся в config.json сразу, не дожидаясь «Сохранить»."""
    cfg = read_json(CFG_PATH, {})
    if not isinstance(cfg, dict):
        cfg = {}
    cfg["theme_colors"] = dict(colors)
    cfg["custom_themes"] = list(themes)
    write_json(CFG_PATH, cfg)
    try:
        os.chmod(CFG_PATH, 0o600)
    except OSError:
        pass


VISUAL = {"ver": 2, "font": "", "bg_image": "", "bg_file": "", "bg_blur": 6, "bg_alpha": 86,
          "glass_on": 0, "glass_opacity": 72, "glass_shine": 60, "glass_rim": 70, "glass_frost": 40, "glass_refract": 50, "glass_aurora": 0}   # + настройки liquid glass   # шрифт и картинка на заднем фоне


def load_visual() -> None:
    """Шрифт и задний фон из config.json."""
    v = read_json(CFG_PATH, {}).get("visual")
    if isinstance(v, dict):
        VISUAL["font"] = str(v.get("font") or "")
        VISUAL["bg_image"] = str(v.get("bg_image") or "")
        VISUAL["bg_file"] = str(v.get("bg_file") or "")
        try:
            VISUAL["bg_blur"] = max(0, min(30, int(v.get("bg_blur", 6))))
            VISUAL["bg_alpha"] = max(0, min(100, int(v.get("bg_alpha", 86))))
            VISUAL["glass_on"] = 1 if int(v.get("glass_on", 0)) else 0
            VISUAL["glass_opacity"] = max(10, min(100, int(v.get("glass_opacity", 72))))
            VISUAL["glass_shine"] = max(0, min(100, int(v.get("glass_shine", 60))))
            VISUAL["glass_rim"] = max(0, min(100, int(v.get("glass_rim", 70))))
            VISUAL["glass_frost"] = max(0, min(100, int(v.get("glass_frost", 40))))
            VISUAL["glass_refract"] = max(0, min(100, int(v.get("glass_refract", 50))))
            VISUAL["glass_aurora"] = 1 if int(v.get("glass_aurora", 0)) else 0
            if int(v.get("ver", 1)) < 2:        # старый конфиг хранил включённое стекло по умолчанию: один раз выключаем
                VISUAL["glass_on"] = VISUAL["glass_aurora"] = 0
                save_visual()
        except (TypeError, ValueError):
            pass


def save_visual() -> None:
    """Пишется сразу, не дожидаясь «Сохранить»."""
    cfg = read_json(CFG_PATH, {})
    if not isinstance(cfg, dict):
        cfg = {}
    cfg["visual"] = dict(VISUAL)
    write_json(CFG_PATH, cfg)
    try:
        os.chmod(CFG_PATH, 0o600)
    except OSError:
        pass


def backdrop_on() -> bool:
    p = VISUAL.get("bg_image") or ""
    return bool(p) and os.path.isfile(p)


def aurora_on() -> bool:
    """Без картинки стеклу не на что смотреть: окно рисует мягкие цветные пятна цвета акцента (можно выключить)."""
    return not backdrop_on() and bool(VISUAL.get("glass_on")) and bool(VISUAL.get("glass_aurora"))


def make_aurora(w: int, h: int) -> QPixmap:
    """Готовый фон окна: цвет темы и три мягких пятна (акцент и два соседних оттенка)."""
    dark = QColor(BG).lightnessF() < 0.5
    img = QImage(w, h, QImage.Format.Format_ARGB32_Premultiplied)
    bg = QColor(BG)
    bg.setAlpha(255)
    img.fill(bg)
    p = QPainter(img)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    hh, ss, vv, _ = QColor(ACCENT).getHsv()
    hh, ss, vv = max(hh, 0), max(ss, 140), max(vv, 200)
    for fx, fy, fr, dh, a in ((0.12, 0.05, 0.60, 0, 80), (0.92, 0.32, 0.55, 48, 64), (0.45, 1.05, 0.65, -55, 58)):
        c = QColor.fromHsv((hh + dh) % 360, ss, vv)
        c.setAlpha(a if dark else round(a * 0.7))
        rg = QRadialGradient(QPointF(fx * w, fy * h), fr * max(w, h))
        rg.setColorAt(0.0, c)
        c2 = QColor(c)
        c2.setAlpha(0)
        rg.setColorAt(1.0, c2)
        p.fillRect(QRectF(0, 0, w, h), rg)
    p.end()
    return QPixmap.fromImage(img)


def page_alpha() -> int:
    """Непрозрачность цвета окна поверх картинки (0..255); без картинки — полностью непрозрачный."""
    return round(255 * VISUAL["bg_alpha"] / 100) if backdrop_on() else 255


def side_bg() -> str:
    """Фон боковой панели: при картинке на заднем фоне полупрозрачный (#aarrggbb, qss его переведёт в rgba)."""
    if not backdrop_on():
        return SIDEBAR
    c = QColor(SIDEBAR)
    return "#%02x%02x%02x%02x" % (round(page_alpha() * c.alphaF()), c.red(), c.green(), c.blue())


def user_font_css() -> str:
    f = VISUAL.get("font") or ""
    return f'"{f}", ' if f else ""


def save_model_pref(path: str) -> None:
    """Выбранная 3D-модель пишется в config.json сразу, не дожидаясь «Сохранить»: иначе при закрытии окна
    другим способом выбор терялся бы и после перезапуска ставилась первая модель из списка."""
    cfg = read_json(CFG_PATH, {})
    if not isinstance(cfg, dict):
        cfg = {}
    cfg["model_path"] = path
    write_json(CFG_PATH, cfg)
    try:
        os.chmod(CFG_PATH, 0o600)
    except OSError:
        pass


# ---------- запрос к LLM (только стандартная библиотека) ----------
def post_json(url: str, headers: dict, body: dict) -> dict:
    headers = {"Content-Type": "application/json", "User-Agent": "voice-assistant/1.0", **headers}
    req = urllib.request.Request(url, json.dumps(body).encode(), headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            return json.loads(r.read())
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP {e.code}: {e.read().decode(errors='replace')[:300]}") from None


def ask_llm(cfg: dict, messages: list[dict], temperature: float = 0.9) -> str:
    base, key = cfg["base_url"].rstrip("/"), cfg["api_key"]
    if cfg["provider"] == "anthropic":
        data = post_json(
            base + "/messages",
            {"x-api-key": key, "anthropic-version": "2023-06-01"},
            {"model": cfg["model"], "max_tokens": 300, "temperature": min(temperature, 1.0),
             "system": system_prompt(cfg), "messages": messages},
        )
        return "".join(b["text"] for b in data["content"] if b["type"] == "text").strip()
    body = {
        "model": cfg["model"],
        "temperature": temperature,
        "max_tokens": 1024,  # запас: модели с «размышлением» тратят часть лимита на мысли
        "messages": [{"role": "system", "content": system_prompt(cfg)}] + messages,
    }
    headers = {"Authorization": f"Bearer {key or 'none'}"}
    if "gpt-oss" in cfg["model"].lower():
        body["reasoning_effort"] = REASONING_EFFORT   # меньше «размышлений» = ответ заметно быстрее
        try:
            data = post_json(base + "/chat/completions", headers, body)
            return data["choices"][0]["message"]["content"].strip()
        except RuntimeError as e:
            if "HTTP 400" not in str(e):
                raise
            body.pop("reasoning_effort")                  # сервис не знает этот параметр: без него
    data = post_json(base + "/chat/completions", headers, body)
    return data["choices"][0]["message"]["content"].strip()


# ---------- распознавание речи ----------
def rms(buf: bytes) -> float:
    """Громкость куска звука (16 бит). Свой расчёт: модуля audioop нет в Python 3.13."""
    s = array("h")
    s.frombytes(buf[: len(buf) // 2 * 2])
    return (sum(v * v for v in s) / len(s)) ** 0.5 if s else 0.0


def whisper_text(cfg: dict, model: str, audio) -> str:
    """Whisper через API сервиса (Groq или OpenAI): намного точнее бесплатного Google."""
    wav = audio.get_wav_data(convert_rate=16000, convert_width=2)
    boundary = "----va" + os.urandom(8).hex()
    body = b""
    for name, value in {"model": model, "language": "ru", "temperature": "0"}.items():
        body += (f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n').encode()
    body += (f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="audio.wav"\r\n'
             "Content-Type: audio/wav\r\n\r\n").encode() + wav + f"\r\n--{boundary}--\r\n".encode()
    req = urllib.request.Request(
        cfg["base_url"].rstrip("/") + "/audio/transcriptions", body,
        {"Authorization": f"Bearer {cfg['api_key']}", "User-Agent": "voice-assistant/1.0",
         "Content-Type": f"multipart/form-data; boundary={boundary}"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read())["text"].strip()
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP {e.code}: {e.read().decode(errors='replace')[:200]}") from None


# ---------- озвучка ----------
_speech_lock = threading.Lock()
_player = None                      # текущий процесс плеера (mpv, paplay, espeak-ng...)
_playing = threading.Event()        # звук реально идёт прямо сейчас
_interrupt = threading.Event()      # её перебили: текущую фразу не доигрывать
_shutdown = threading.Event()       # окно закрыто: больше не говорить вообще


def _play(cmd: list[str]) -> None:
    """Запускает плеер и ждёт конца. stop_speaking() обрывает звук сразу."""
    global _player
    with _speech_lock:
        if _shutdown.is_set() or _interrupt.is_set():
            return
        try:
            proc = subprocess.Popen(cmd)
        except OSError as e:
            print(f"Плеер {cmd[0]}: {e}", file=sys.stderr)
            return
        _player = proc
        _playing.set()
    try:
        proc.wait()
    finally:
        with _speech_lock:
            _player = None
            _playing.clear()


def stop_speaking() -> None:
    """Мгновенно обрывает текущую фразу (флаг ставится до блокировки: гонки нет)."""
    _interrupt.set()
    with _speech_lock:
        proc = _player
    if proc is not None and proc.poll() is None:
        proc.terminate()


def shutdown_speech() -> None:
    """Окно закрыто: замолчать сейчас и не начинать новых фраз."""
    _shutdown.set()
    stop_speaking()


atexit.register(shutdown_speech)  # плеер — отдельный процесс и сам не умрёт вместе с программой


def speak_edge(text: str) -> bool:
    """Нейросетевой голос Microsoft Edge через пакет edge-tts. True — если проговорили."""
    player = (["mpv", "--no-video", "--really-quiet"] if shutil.which("mpv")
              else ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"] if shutil.which("ffplay")
              else None)
    if player is None:
        print(f"Нет плеера для mp3: {install_hint('mpv')}", file=sys.stderr)
        return False
    with tempfile.TemporaryDirectory() as tmp:
        mp3 = Path(tmp) / "say.mp3"
        try:
            r = subprocess.run(
                [sys.executable, "-m", "edge_tts", f"--voice={EDGE_VOICE}", f"--rate={EDGE_RATE}",
                 f"--text={text}", f"--write-media={mp3}"],
                capture_output=True, text=True, timeout=30)
        except subprocess.TimeoutExpired:
            return False
        if r.returncode != 0 or not mp3.exists():
            print("edge-tts:", (r.stderr or "").strip()[-300:], file=sys.stderr)
            return False
        _play(player + [str(mp3)])
    return True


_silero = {}


def silero_file() -> Path:
    """Путь к файлу модели. Если его нет — пробуем скачать. Можно положить руками: data/v5_ru.pt"""
    path = DATA_DIR / f"{SILERO_MODEL}.pt"
    if path.exists() and path.stat().st_size > 10_000_000:
        return path
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    print(f"Скачиваю голос Silero: {SILERO_URL}")
    part = path.with_suffix(".part")
    req = urllib.request.Request(SILERO_URL, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=30) as r, open(part, "wb") as f:
        shutil.copyfileobj(r, f)
    part.replace(path)
    return path


def load_silero():
    """Загружает модель Silero один раз. Нужен torch и scipy, пакет silero не нужен."""
    if _silero.get("failed"):
        raise RuntimeError("Silero недоступен")
    if "model" not in _silero:
        try:
            import torch
            torch.set_num_threads(4)
            path = silero_file()
            model = torch.package.PackageImporter(str(path)).load_pickle("tts_models", "model")
            model.to(torch.device("cpu"))
            _silero["model"] = model
            print("Голос Silero загружен")
        except Exception as e:
            _silero["failed"] = True
            print("Silero не загрузился:", e, file=sys.stderr)
            if "scipy" in str(e):
                print("Не хватает scipy: .venv/bin/pip install scipy", file=sys.stderr)
            print(f"Скачайте {SILERO_URL} (если сайт недоступен — через VPN или прокси)\n"
                  f"и положите файл сюда: {DATA_DIR / (SILERO_MODEL + '.pt')}\n"
                  "Пока говорит espeak-ng.", file=sys.stderr)
            raise
    return _silero["model"]


def find_player() -> list[str] | None:
    for cmd in (["mpv", "--no-video", "--really-quiet"],
                ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"],
                ["pw-play"], ["paplay"]):
        if shutil.which(cmd[0]):
            return cmd
    return None


def split_sentences(text: str) -> list[str]:
    """Делит ответ на предложения; слишком короткие огрызки клеит к соседям."""
    parts = [p.strip() for p in re.split(r"(?<=[.!?…])\s+", text.strip()) if p.strip()]
    out: list[str] = []
    for p in parts:
        if out and len(out[-1]) < 25:
            out[-1] += " " + p
        else:
            out.append(p)
    return out or [text]


def synth_silero(model, text: str, path: Path) -> None:
    ssml = (f'<speak><p><prosody pitch="{SILERO_PITCH}" rate="{SILERO_RATE}">'
            f"{escape(text)}</prosody></p></speak>")
    audio = model.apply_tts(ssml_text=ssml, speaker=SILERO_SPEAKER, sample_rate=SILERO_SR)
    pcm = array("h", (audio.flatten().clamp(-1, 1) * 32767).short().tolist())
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SILERO_SR)
        w.writeframes(pcm.tobytes())


def speak_silero(text: str) -> bool:
    """Нейросетевой голос Silero (офлайн). True — если проговорили.
    Ответ режется на предложения: первое начинает звучать, пока синтезируются следующие."""
    if _silero.get("failed"):
        return False
    player = find_player()
    if player is None:
        print(f"Нет плеера: {install_hint('mpv')}", file=sys.stderr)
        return False
    try:
        model = load_silero()
    except Exception as e:
        print("Silero:", e, file=sys.stderr)
        return False
    sentences = split_sentences(text)
    ready: "queue.Queue[Path | None]" = queue.Queue()
    t0 = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        def worker() -> None:
            try:
                for k, s in enumerate(sentences):
                    if _interrupt.is_set() or _shutdown.is_set():
                        break
                    f = Path(tmp) / f"say{k}.wav"
                    synth_silero(model, s, f)
                    if k == 0:
                        print(f"⏱ синтез первой фразы: {time.time() - t0:.1f} с")
                    ready.put(f)
            except Exception as e:
                print("Silero:", e, file=sys.stderr)
            finally:
                ready.put(None)
        th = threading.Thread(target=worker, daemon=True)
        th.start()
        spoke = False
        while True:
            f = ready.get()
            if f is None:
                break
            if _interrupt.is_set() or _shutdown.is_set():
                continue                      # перебили: остальное выбрасываем, но дожидаемся конца потока
            _play(player + [str(f)])
            spoke = True
        th.join(timeout=5)
    return spoke


SPEECH_STRIP_RE = re.compile(r"[\-\u2010-\u2015\u2212+]+")   # дефисы, тире, минус и плюс: озвучка их читает или ставит ударение


def speak(text: str) -> None:
    if _shutdown.is_set():
        return
    text = re.sub(r"\s+", " ", SPEECH_STRIP_RE.sub(" ", text)).strip()
    if not text:
        return
    _interrupt.clear()  # новая фраза: прошлое «замолчи» больше не действует
    if TTS_ENGINE == "silero" and speak_silero(text):
        return
    if TTS_ENGINE == "edge" and speak_edge(text):
        return
    # запасной вариант: робот espeak-ng, работает без интернета
    if shutil.which("espeak-ng") is None:
        print(f"espeak-ng не установлен: {install_hint('espeak-ng')}", file=sys.stderr)
        return
    _play(["espeak-ng", "-v", TTS_VOICE, "-s", str(TTS_SPEED), text])


# ---------- картинка ----------
def find_image() -> Path | None:
    """Ищет фото помощника: сначала в assets/, потом рядом с main.py.
    Файл с именем character.* имеет приоритет, иначе берётся первый по алфавиту."""
    for folder in (BASE / "assets", BASE):
        if folder.is_dir():
            files = [p for p in folder.iterdir() if p.is_file() and p.suffix.lower() in IMG_EXT]
            if files:
                # для статичной картинки gif берём только если больше ничего нет
                return min(files, key=lambda p: (p.stem.lower() != "character",
                                                 p.suffix.lower() == ".gif", p.name.lower()))
    return None


def find_gif(chosen: str = "") -> Path | None:
    """GIF персонажа: выбранный в настройках файл, иначе assets/character.gif, иначе любой gif в assets/."""
    if chosen and Path(chosen).expanduser().is_file():
        return Path(chosen).expanduser()
    for folder in (BASE / "assets", BASE):
        if folder.is_dir():
            gifs = [p for p in folder.iterdir() if p.is_file() and p.suffix.lower() == ".gif"]
            if gifs:
                return min(gifs, key=lambda p: (p.stem.lower() != "character", p.name.lower()))
    return None


def load_character(cfg: dict) -> tuple[QPixmap, QMovie | None]:
    """Возвращает (кадр в покое, QMovie или None).
    Режим «static»: просто картинка. Режим «gif»: анимация, которая идёт только пока Мими говорит;
    в тишине стоит на первом кадре. Нет GIF или он битый: падаем обратно на статичную картинку."""
    scale = float(cfg.get("char_scale", 1.0) or 1.0)
    if cfg.get("char_mode") == "gif":
        path = find_gif(cfg.get("char_gif", ""))
        if path is None:
            print("GIF не найден (положите его в assets/ или выберите в настройках), "
                  "показываю статичную картинку", file=sys.stderr)
        else:
            probe = QMovie(str(path))                       # пробный QMovie: только узнать исходный размер
            native = QSize()
            if probe.isValid() and probe.jumpToFrame(0):
                native = probe.currentImage().size()
            probe.deleteLater()
            movie = QMovie(str(path))
            movie.setCacheMode(QMovie.CacheMode.CacheAll)   # кадры в памяти: ровнее и без чтения с диска
            if native.isValid() and movie.isValid():
                size = QSize(native)
                if size.width() > IMG_MAX[0] or size.height() > IMG_MAX[1]:
                    size.scale(*IMG_MAX, Qt.AspectRatioMode.KeepAspectRatio)
                if scale != 1.0:
                    size = QSize(max(1, round(size.width() * scale)), max(1, round(size.height() * scale)))
                if size != native:
                    movie.setScaledSize(size)               # ДО первого кадра, иначе в кэше останется полный размер
                if movie.jumpToFrame(0):
                    pm = movie.currentPixmap()
                    if pm.size() != size:                   # страховка: если QMovie не отмасштабировал сам
                        pm = pm.scaled(size, Qt.AspectRatioMode.IgnoreAspectRatio,
                                       Qt.TransformationMode.SmoothTransformation)
                    movie._target_size = size
                    print("GIF:", path, f"{native.width()}x{native.height()} -> {size.width()}x{size.height()}")
                    return pm, movie
            print(f"Не удалось открыть GIF {path}, показываю статичную картинку", file=sys.stderr)
    return load_pixmap(scale), None


def load_pixmap(scale: float = 1.0) -> QPixmap:
    path = find_image()
    pm = QPixmap(str(path)) if path else QPixmap()
    if not pm.isNull():
        print("Картинка:", path)
        if pm.width() > IMG_MAX[0] or pm.height() > IMG_MAX[1]:
            pm = pm.scaled(*IMG_MAX, Qt.AspectRatioMode.KeepAspectRatio,
                           Qt.TransformationMode.SmoothTransformation)
        if scale != 1.0:                      # «Масштаб Мими» из меню профиля
            pm = pm.scaled(max(1, round(pm.width() * scale)), max(1, round(pm.height() * scale)),
                           Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
        return pm
    print("Картинка не найдена, положите фото в папку assets/")
    pm = QPixmap(320, 320)  # заглушка
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(255, 214, 170))
    p.drawEllipse(QRectF(60, 60, 200, 200))
    p.setBrush(QColor(30, 30, 30))
    p.drawEllipse(QRectF(110, 130, 25, 25))
    p.drawEllipse(QRectF(185, 130, 25, 25))
    p.setPen(QColor(150, 50, 50))
    p.drawArc(QRectF(120, 160, 80, 70), 200 * 16, 140 * 16)
    p.end()
    return pm


# ---------- иконки: рисуются кодом, шрифты и файлы не нужны ----------
def _ic_server(p, c):
    p.drawRoundedRect(QRectF(3, 4, 18, 6.5), 2.5, 2.5)
    p.drawRoundedRect(QRectF(3, 13.5, 18, 6.5), 2.5, 2.5)
    p.setBrush(c)
    p.drawEllipse(QPointF(7, 7.25), 0.9, 0.9)
    p.drawEllipse(QPointF(7, 16.75), 0.9, 0.9)


def _ic_cpu(p, c):
    p.drawRoundedRect(QRectF(7, 7, 10, 10), 2, 2)
    for v in (10, 14):
        p.drawLine(QPointF(v, 3), QPointF(v, 7))
        p.drawLine(QPointF(v, 17), QPointF(v, 21))
        p.drawLine(QPointF(3, v), QPointF(7, v))
        p.drawLine(QPointF(17, v), QPointF(21, v))


def _ic_mic(p, c):
    p.drawRoundedRect(QRectF(9, 3, 6, 11), 3, 3)
    p.drawArc(QRectF(5, 7, 14, 12), 180 * 16, 180 * 16)
    p.drawLine(QPointF(12, 19), QPointF(12, 22))
    p.drawLine(QPointF(9, 22), QPointF(15, 22))


def _ic_mic_off(p, c):
    _ic_mic(p, c)
    p.drawLine(QPointF(4, 3), QPointF(20, 21))


def _ic_speaker(p, c):
    path = QPainterPath()
    path.moveTo(4, 9)
    for x, y in ((8, 9), (13, 5), (13, 19), (8, 15), (4, 15)):
        path.lineTo(x, y)
    path.closeSubpath()
    p.drawPath(path)
    p.drawArc(QRectF(10, 8, 8, 8), -60 * 16, 120 * 16)
    p.drawArc(QRectF(8, 4.5, 13, 15), -55 * 16, 110 * 16)


def _ic_wave(p, c):
    for x, a, b in ((4, 10, 14), (8, 6, 18), (12, 3, 21), (16, 7, 17), (20, 10, 14)):
        p.drawLine(QPointF(x, a), QPointF(x, b))


def _ic_heart(p, c):
    path = QPainterPath()
    path.moveTo(12, 20)
    path.cubicTo(4, 14.5, 3, 10.5, 3, 8.5)
    path.cubicTo(3, 5.5, 5.5, 4, 7.5, 4)
    path.cubicTo(9.5, 4, 11.2, 5, 12, 6.8)
    path.cubicTo(12.8, 5, 14.5, 4, 16.5, 4)
    path.cubicTo(18.5, 4, 21, 5.5, 21, 8.5)
    path.cubicTo(21, 10.5, 20, 14.5, 12, 20)
    p.drawPath(path)


def _ic_chat(p, c):
    p.drawRoundedRect(QRectF(3, 4, 18, 13), 4, 4)
    path = QPainterPath()
    path.moveTo(8, 17)
    path.lineTo(8, 21)
    path.lineTo(12.5, 17)
    p.drawPath(path)


def _ic_terminal(p, c):
    p.drawRoundedRect(QRectF(3, 4, 18, 16), 3, 3)
    path = QPainterPath()
    path.moveTo(7, 9)
    path.lineTo(10.5, 12)
    path.lineTo(7, 15)
    p.drawPath(path)
    p.drawLine(QPointF(12.5, 15), QPointF(17, 15))


def _ic_key(p, c):
    p.drawEllipse(QPointF(8, 15), 4, 4)
    p.drawLine(QPointF(11, 12), QPointF(20, 3))
    p.drawLine(QPointF(17, 6), QPointF(19.5, 8.5))
    p.drawLine(QPointF(14, 9), QPointF(16, 11))


def _ic_check(p, c):
    path = QPainterPath()
    path.moveTo(4, 12.5)
    path.lineTo(9.5, 18)
    path.lineTo(20, 6.5)
    p.drawPath(path)


def _ic_close(p, c):
    p.drawLine(QPointF(6, 6), QPointF(18, 18))
    p.drawLine(QPointF(18, 6), QPointF(6, 18))


def _ic_user(p, c):
    p.drawEllipse(QPointF(12, 8), 4, 4)
    p.drawArc(QRectF(4, 14, 16, 14), 0, 180 * 16)


def _ic_info(p, c):
    p.drawEllipse(QPointF(12, 12), 9, 9)
    p.drawLine(QPointF(12, 11), QPointF(12, 16.5))
    p.setBrush(c)
    p.drawEllipse(QPointF(12, 7.6), 0.9, 0.9)


def _ic_eye(p, c):
    path = QPainterPath()
    path.moveTo(2, 12)
    path.cubicTo(5, 7, 8.5, 5.5, 12, 5.5)
    path.cubicTo(15.5, 5.5, 19, 7, 22, 12)
    path.cubicTo(19, 17, 15.5, 18.5, 12, 18.5)
    path.cubicTo(8.5, 18.5, 5, 17, 2, 12)
    path.closeSubpath()
    p.drawPath(path)
    p.drawEllipse(QPointF(12, 12), 3, 3)


def _ic_eye_off(p, c):
    _ic_eye(p, c)
    p.drawLine(QPointF(4, 20), QPointF(20, 4))


def _ic_chev_down(p, c):
    path = QPainterPath()
    path.moveTo(6, 9.5)
    path.lineTo(12, 15.5)
    path.lineTo(18, 9.5)
    p.drawPath(path)


def _ic_shield(p, c):
    path = QPainterPath()
    path.moveTo(12, 3)
    path.lineTo(19, 6)
    path.lineTo(19, 12)
    path.cubicTo(19, 16.5, 16, 19.5, 12, 21)
    path.cubicTo(8, 19.5, 5, 16.5, 5, 12)
    path.lineTo(5, 6)
    path.closeSubpath()
    p.drawPath(path)


def _ic_scale(p, c):
    p.drawRoundedRect(QRectF(4, 10, 10, 10), 2, 2)
    path = QPainterPath()
    path.moveTo(14, 4)
    path.lineTo(20, 4)
    path.lineTo(20, 10)
    p.drawPath(path)
    p.drawLine(QPointF(20, 4), QPointF(12, 12))


def _ic_drop(p, c):
    path = QPainterPath()
    path.moveTo(12, 3.5)
    path.cubicTo(15, 7, 18.5, 10.5, 18.5, 14.5)
    path.cubicTo(18.5, 18.2, 15.6, 20.5, 12, 20.5)
    path.cubicTo(8.4, 20.5, 5.5, 18.2, 5.5, 14.5)
    path.cubicTo(5.5, 10.5, 9, 7, 12, 3.5)
    path.closeSubpath()
    p.drawPath(path)


def _ic_clock(p, c):
    p.drawEllipse(QPointF(12, 12), 8.5, 8.5)
    path = QPainterPath()
    path.moveTo(12, 7)
    path.lineTo(12, 12)
    path.lineTo(15.5, 14)
    p.drawPath(path)


def _ic_globe(p, c):
    p.drawEllipse(QPointF(12, 12), 9, 9)
    p.drawEllipse(QRectF(8, 3, 8, 18))
    p.drawLine(QPointF(3, 12), QPointF(21, 12))


def _ic_window(p, c):
    p.drawRoundedRect(QRectF(3, 5, 18, 14), 3, 3)
    p.drawLine(QPointF(3, 9.5), QPointF(21, 9.5))


def _ic_import(p, c):                      # стрелка внутрь лотка: загрузить файл в программу
    p.drawLine(QPointF(12, 3), QPointF(12, 14))
    path = QPainterPath()
    path.moveTo(7.5, 9.5)
    path.lineTo(12, 14)
    path.lineTo(16.5, 9.5)
    p.drawPath(path)
    p.drawPolyline(QPointF(4, 15), QPointF(4, 20), QPointF(20, 20), QPointF(20, 15))


def _ic_export(p, c):                      # стрелка из лотка наружу: сохранить файл наружу
    p.drawLine(QPointF(12, 14), QPointF(12, 3))
    path = QPainterPath()
    path.moveTo(7.5, 7.5)
    path.lineTo(12, 3)
    path.lineTo(16.5, 7.5)
    p.drawPath(path)
    p.drawPolyline(QPointF(4, 15), QPointF(4, 20), QPointF(20, 20), QPointF(20, 15))


def _ic_trash(p, c):                       # урна: удалить
    p.drawLine(QPointF(5, 7), QPointF(19, 7))
    p.drawLine(QPointF(9.5, 7), QPointF(9.5, 3.8))
    p.drawLine(QPointF(14.5, 7), QPointF(14.5, 3.8))
    p.drawLine(QPointF(9.5, 3.8), QPointF(14.5, 3.8))
    p.drawPolyline(QPointF(6.3, 7), QPointF(7.2, 20), QPointF(16.8, 20), QPointF(17.7, 7))
    p.drawLine(QPointF(10.3, 10.3), QPointF(10.8, 17))
    p.drawLine(QPointF(13.7, 10.3), QPointF(13.2, 17))


def _ic_monitor(p, c):                     # экран с линией пульса: мониторинг
    p.drawRoundedRect(QRectF(3, 4, 18, 12.5), 2.5, 2.5)
    p.drawLine(QPointF(9, 20), QPointF(15, 20))
    p.drawLine(QPointF(12, 16.5), QPointF(12, 20))
    p.drawPolyline(QPointF(6, 10.5), QPointF(9, 10.5), QPointF(10.5, 7.6), QPointF(13, 13.2), QPointF(14.5, 10.5), QPointF(18, 10.5))


ICONS = {"shield": _ic_shield, "scale": _ic_scale, "drop": _ic_drop, "clock": _ic_clock, "eye": _ic_eye, "eye_off": _ic_eye_off, "chev_down": _ic_chev_down, "server": _ic_server, "cpu": _ic_cpu, "mic": _ic_mic, "mic_off": _ic_mic_off, "speaker": _ic_speaker, "wave": _ic_wave,
         "heart": _ic_heart, "chat": _ic_chat, "terminal": _ic_terminal, "key": _ic_key,
         "check": _ic_check, "close": _ic_close, "user": _ic_user, "info": _ic_info,
         "globe": _ic_globe, "window": _ic_window,
         "import": _ic_import, "export": _ic_export, "trash": _ic_trash, "monitor": _ic_monitor}


def draw_icon(name: str, color: str, size: int = 18) -> QPixmap:
    """Рисует иконку из набора ICONS нужного цвета и размера (чёткая, с учётом 2x-экранов)."""
    dpr = 2
    pm = QPixmap(size * dpr, size * dpr)
    pm.setDevicePixelRatio(dpr)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.scale(size / 24, size / 24)
    pen = QPen(QColor(color), 1.9)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    p.setPen(pen)
    p.setBrush(Qt.BrushStyle.NoBrush)
    ICONS[name](p, QColor(color))
    p.end()
    return pm


def linux_user() -> str:
    """Ник пользователя Linux: имя его учётной записи (логин)."""
    try:
        return pwd.getpwuid(os.getuid()).pw_name
    except Exception:
        return os.environ.get("USER") or getpass.getuser() or "user"


def linux_avatar() -> QPixmap:
    """Аватарка пользователя Linux: та же, что на экране входа и в настройках KDE/GNOME.
    Ищет ~/.face, ~/.face.icon, AccountsService и аватар SDDM. Не нашла: пустой QPixmap."""
    user, home = linux_user(), Path.home()
    paths = [home / ".face", home / ".face.icon"]
    try:   # в файле AccountsService у пользователя есть строка Icon=путь
        for line in Path(f"/var/lib/AccountsService/users/{user}").read_text(errors="ignore").splitlines():
            if line.startswith("Icon="):
                paths.append(Path(line[5:].strip()))
    except OSError:
        pass
    paths += [Path(f"/var/lib/AccountsService/icons/{user}"),
              Path(f"/usr/share/sddm/faces/{user}.face.icon")]
    for path in paths:
        try:
            if path.is_file():
                pm = QPixmap(str(path))
                if not pm.isNull():
                    return pm
        except OSError:
            continue
    return QPixmap()


def round_avatar(pm: QPixmap, size: int, letter: str = "") -> QPixmap:
    """Круглая аватарка из картинки. Если картинки нет, а есть letter: рисуется буква."""
    dpr = 2
    out = QPixmap(size * dpr, size * dpr)
    out.setDevicePixelRatio(dpr)
    out.fill(Qt.GlobalColor.transparent)
    p = QPainter(out)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addEllipse(QRectF(0, 0, size, size))
    p.setClipPath(clip)
    p.fillRect(QRectF(0, 0, size, size), QColor(CONTROL))
    if not pm.isNull():
        big = pm.scaled(size * dpr, size * dpr, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                        Qt.TransformationMode.SmoothTransformation)
        x, y = (big.width() - size * dpr) / 2, (big.height() - size * dpr) / 2
        p.drawPixmap(QRectF(0, 0, size, size), big, QRectF(x, y, size * dpr, size * dpr))
    elif letter:
        f = p.font()
        f.setPixelSize(int(size * 0.46))
        f.setBold(True)
        p.setFont(f)
        p.setPen(QColor(ACCENT))
        p.drawText(QRectF(0, 0, size, size), Qt.AlignmentFlag.AlignCenter, letter[:1].upper())
    p.setClipping(False)
    p.setPen(QPen(QColor(BORDER), 1.2))
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.drawEllipse(QRectF(0.6, 0.6, size - 1.2, size - 1.2))
    p.end()
    return out


# ---------- 3D-модель (.glb) для карточки «Модель» ----------
# Модель «Mimi-typh-fanart» by Vadimoo3 (Sketchfab), лицензия CC-BY-4.0: нужно указывать автора.
# Нужен numpy (pip install numpy). Файл .glb кладётся в assets/ (или рядом с main.py).
MODEL_YAW_MAX = 180           # на сколько градусов влево-вправо можно повернуть модель мышью (180 = полный круг)
MODEL_YAW_STEP = 12           # шаг предрасчитанных кадров для ручного вращения, градусы (крупный шаг = быстрее
                              # считается, но грубее; для плавного покачивания в покое есть свой, мелкий шаг ниже)
MODEL_SWAY_DEG = 32           # амплитуда плавного покачивания, градусы
MODEL_SWAY_STEP = 2           # свой, мелкий шаг кадров ТОЛЬКО для зоны покачивания (чтобы оно было плавным,
                              # а не рваным, как при крупном шаге общего круга); кадров тут немного, т.к. зона узкая
MODEL_SWAY_SPEED = 0.8        # скорость покачивания (радиан в секунду)
MODEL_ANIM = True             # анимация по умолчанию (в настройках её можно включить и выключить): кивает в такт речи и наклоняет голову, пока думает
MODEL_HAIR_COLOR = ""          # цвет волос: "" = взять коричневый из самой модели, или свой, например "#6b4034"
MODEL_CACHE_VER = 5           # поднимай при правках отрисовки: старые кадры пересчитаются
_MODEL_CACHE: dict = {}       # (путь, размер) -> готовые кадры в памяти
# Кадры один раз считаются и лежат одним файлом в data/: со второго запуска модель появляется сразу.
MODEL_CACHE_DIR = DATA_DIR


def list_models() -> list[Path]:
    """Все 3D-модели, которые лежат в assets/ и рядом с main.py. Файл character.glb идёт первым."""
    out: list[Path] = []
    for folder in (BASE / "assets", BASE):
        if folder.is_dir():
            files = sorted(folder.glob("*.glb"), key=lambda p: (p.stem.lower() != "character", p.name.lower()))
            out += [f for f in files if f not in out]
    return out


def find_model(selected: str = "") -> Path | None:
    """Выбранная в «Отрисовке» модель (если файл ещё есть), иначе первая найденная в assets/ или рядом с main.py."""
    if selected:
        p = Path(selected).expanduser()
        if p.is_file():
            return p
    files = list_models()
    return files[0] if files else None


MODEL_WIN_SIZE = (260, 390)   # размер модели в главном окне при масштабе 100%; как у превью в настройках, поэтому кадры считаются один раз


def model3d_ready(cfg: dict) -> bool:
    """3D-модель вместо картинки и GIF: в «Как показывать Мими» выбрано «3D-модель», есть numpy и найден .glb-файл."""
    if cfg.get("char_mode") != "model3d":
        return False
    try:
        import numpy  # noqa: F401
    except ImportError:
        print("3D-модель в окне: нужен numpy (pip install numpy), показываю картинку", file=sys.stderr)
        return False
    return find_model(cfg.get("model_path", "")) is not None


def _glb_load(path: Path, decode_png) -> dict:
    """Читает .glb (glTF 2.0, один бинарный буфер) в плоский набор треугольников на numpy.
    decode_png(bytes) -> массив (h, w, 3) uint8: декодер текстуры подаётся снаружи."""
    import numpy as np
    data = Path(path).read_bytes()
    if data[:4] != b"glTF":
        raise ValueError("не файл .glb")
    jlen = int.from_bytes(data[12:16], "little")
    j = json.loads(data[20:20 + jlen])
    off = 20 + jlen
    blen = int.from_bytes(data[off:off + 4], "little")
    blob = data[off + 8:off + 8 + blen]

    def acc(i):
        a = j["accessors"][i]
        bv = j["bufferViews"][a["bufferView"]]
        n = {"SCALAR": 1, "VEC2": 2, "VEC3": 3}[a["type"]]
        dt = np.dtype({5126: "<f4", 5125: "<u4", 5123: "<u2", 5121: "u1"}[a["componentType"]])
        o = bv.get("byteOffset", 0) + a.get("byteOffset", 0)
        stride = bv.get("byteStride") or n * dt.itemsize
        if stride == n * dt.itemsize:
            return np.frombuffer(blob, dt, a["count"] * n, o).reshape(-1, n)
        return np.ndarray((a["count"], n), dt, blob, o, (stride, dt.itemsize))

    def node_matrix(nd):
        if "matrix" in nd:
            return np.array(nd["matrix"], float).reshape(4, 4).T
        m = np.eye(4)
        if "rotation" in nd:
            x, y, z, w = nd["rotation"]
            m[:3, :3] = [[1 - 2 * (y * y + z * z), 2 * (x * y - z * w), 2 * (x * z + y * w)],
                         [2 * (x * y + z * w), 1 - 2 * (x * x + z * z), 2 * (y * z - x * w)],
                         [2 * (x * z - y * w), 2 * (y * z + x * w), 1 - 2 * (x * x + y * y)]]
        if "scale" in nd:
            m[:3, :3] *= np.array(nd["scale"])[None, :]
        if "translation" in nd:
            m[:3, 3] = nd["translation"]
        return m

    tex = None
    if j.get("images"):
        bv = j["bufferViews"][j["images"][0]["bufferView"]]
        o = bv.get("byteOffset", 0)
        tex = decode_png(blob[o:o + bv["byteLength"]])
    P, N, UV, C, T, D = [], [], [], [], [], []
    hair_ref = None                                   # коричневый цвет волос (линейный, как в glTF)
    if MODEL_HAIR_COLOR:
        try:
            hair_ref = (np.array([int(MODEL_HAIR_COLOR.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4)]) / 255.0) ** 2.2
        except ValueError:
            hair_ref = None
    if hair_ref is None:
        for mt in j.get("materials", []):
            f = mt.get("pbrMetallicRoughness", {}).get("baseColorFactor")
            if f and "hair" in mt.get("name", "").lower() and max(f[:3]) > 0.02:
                hair_ref = np.array(f[:3], float)
                break

    def walk(ni, parent):
        nd = j["nodes"][ni]
        m = parent @ node_matrix(nd)
        if "mesh" in nd:
            for prim in j["meshes"][nd["mesh"]]["primitives"]:
                if prim.get("mode", 4) != 4:
                    continue
                pos = acc(prim["attributes"]["POSITION"]).astype(float)
                idx = (acc(prim["indices"]).astype(np.int64) if "indices" in prim
                       else np.arange(len(pos))).reshape(-1, 3)
                mat = j["materials"][prim["material"]] if "material" in prim else {}
                pbr = mat.get("pbrMetallicRoughness", {})
                pos = pos @ m[:3, :3].T + m[:3, 3]
                tri = pos[idx]
                if "NORMAL" in prim["attributes"]:
                    nor = acc(prim["attributes"]["NORMAL"]).astype(float) @ m[:3, :3].T
                    nt = nor[idx]
                else:
                    fn = np.cross(tri[:, 1] - tri[:, 0], tri[:, 2] - tri[:, 0])
                    nt = np.repeat(fn[:, None, :], 3, axis=1)
                if "TEXCOORD_0" in prim["attributes"]:
                    ut = acc(prim["attributes"]["TEXCOORD_0"]).astype(float)[idx]
                else:
                    ut = np.zeros((len(idx), 3, 2))
                P.append(tri); N.append(nt); UV.append(ut)
                D.append(np.full(len(idx), bool(mat.get("doubleSided", False))))
                textured = "baseColorTexture" in pbr and tex is not None
                col = np.array(pbr.get("baseColorFactor", [0.8, 0.8, 0.8, 1.0])[:3], float)
                if hair_ref is not None and "hair" in mat.get("name", "").lower() and (MODEL_HAIR_COLOR or col.max() < 0.02):
                    col = hair_ref                    # волосы в файле чёрные: красим в коричневый
                C.append(np.tile(col, (len(idx), 1)))
                T.append(np.full(len(idx), textured))
        for ch in nd.get("children", []):
            walk(ch, m)

    for s in j["scenes"][j.get("scene", 0)]["nodes"]:
        walk(s, np.eye(4))
    mdl = dict(P=np.concatenate(P), N=np.concatenate(N), UV=np.concatenate(UV), C=np.concatenate(C),
               T=np.concatenate(T), D=np.concatenate(D), tex=tex)
    flat = mdl["P"].reshape(-1, 3)
    lo, hi = flat.min(0), flat.max(0)
    tri_c = mdl["P"].mean(1)                                       # по горизонтали центрируем по «массе» фигуры:
    tri_a = 0.5 * np.linalg.norm(np.cross(mdl["P"][:, 1] - mdl["P"][:, 0], mdl["P"][:, 2] - mdl["P"][:, 0]), axis=1)
    mass = (tri_c * tri_a[:, None]).sum(0) / max(tri_a.sum(), 1e-12)   # хвост и поза не уводят её вбок
    mdl["center"] = np.array([mass[0], (lo[1] + hi[1]) / 2, mass[2]])  # а по высоте — середина габарита
    mdl["span"] = hi[1] - lo[1]                       # высота фигуры: по ней строится масштаб
    return mdl


def _glb_cloud(mdl: dict, w: int, h: int, ss: int = 2) -> dict:
    """Один раз превращает треугольники в облако точек на поверхности (с цветом из текстуры и нормалью).
    Плотность считается по длине рёбер в 3D, поэтому подходит для любого угла поворота."""
    import numpy as np
    sc = h * ss / (mdl["span"] * 1.05)
    P = (mdl["P"] - mdl["center"]) * sc                          # в «пикселях» сетки с суперсэмплингом
    edge = np.stack([np.linalg.norm(P[:, 0] - P[:, 1], axis=1), np.linalg.norm(P[:, 1] - P[:, 2], axis=1),
                     np.linalg.norm(P[:, 2] - P[:, 0], axis=1)], 1).max(1)
    k = np.clip(np.ceil(edge / 1.1), 1, 24).astype(int)
    gnorm = np.cross(P[:, 1] - P[:, 0], P[:, 2] - P[:, 0])         # геометрическая нормаль (направление обхода)
    gnorm /= np.linalg.norm(gnorm, axis=1, keepdims=True) + 1e-12
    tex = mdl["tex"]
    pos_l, nor_l, col_l, gn_l, dbl_l = [], [], [], [], []
    for kk in np.unique(k):
        sel = np.nonzero(k == kk)[0]
        pts = []                                                   # центры kk² маленьких треугольников
        for i in range(kk):
            for j in range(kk - i):
                pts.append((i + 1 / 3, j + 1 / 3))
                if j < kk - i - 1:
                    pts.append((i + 2 / 3, j + 2 / 3))
        ab = np.array(pts) / kk
        bary = np.stack([1 - ab[:, 0] - ab[:, 1], ab[:, 0], ab[:, 1]], 1)
        B = bary.shape[0]
        for a in range(0, len(sel), 20000):
            t = sel[a:a + 20000]
            pos_l.append(np.einsum("tvc,bv->tbc", P[t], bary).reshape(-1, 3).astype(np.float32))
            nrm = np.einsum("tvc,bv->tbc", mdl["N"][t], bary).reshape(-1, 3)
            nrm /= np.linalg.norm(nrm, axis=1, keepdims=True) + 1e-9
            nor_l.append(nrm.astype(np.float32))
            base = np.repeat(mdl["C"][t], B, axis=0) ** (1 / 2.2)   # цвета материала в glTF линейные
            ist = np.repeat(mdl["T"][t], B)
            if tex is not None and ist.any():
                th, tw = tex.shape[:2]
                uv = np.einsum("tvc,bv->tbc", mdl["UV"][t], bary).reshape(-1, 2)[ist]
                base[ist] = tex[(uv[:, 1] * th).astype(int) % th, (uv[:, 0] * tw).astype(int) % tw] / 255.0
            col_l.append(base.astype(np.float32))
            gn_l.append(np.repeat(gnorm[t], B, axis=0).astype(np.float32))
            dbl_l.append(np.repeat(mdl["D"][t], B))
    return dict(pos=np.concatenate(pos_l), nor=np.concatenate(nor_l), col=np.concatenate(col_l),
                gn=np.concatenate(gn_l), dbl=np.concatenate(dbl_l), w=w, h=h, ss=ss)


def _glb_render(cl: dict, yaw: float):
    """Кадр из облака точек: повернуть, отсечь задние грани, осветить, z-буфер. Возвращает RGBA uint8 (h, w, 4)."""
    import numpy as np
    w, h, ss = cl["w"], cl["h"], cl["ss"]
    W, H = w * ss, h * ss
    c, s = math.cos(yaw), math.sin(yaw)
    r0 = np.array([c, 0, s], np.float32)                           # строки матрицы поворота вокруг оси Y
    r2 = np.array([-s, 0, c], np.float32)
    # односторонние материалы: задние грани не рисуем (это «обводка» из перевёрнутой оболочки)
    vis = cl["dbl"] | ((cl["gn"] @ r2) > 0)
    pos = cl["pos"][vis]
    X = pos @ r0 + W / 2
    Y = -pos[:, 1] + H / 2
    Z = pos @ r2
    ix = X.astype(np.int32)
    iy = Y.astype(np.int32)
    ok = (X >= 0) & (ix < W) & (Y >= 0) & (iy < H)
    nor = cl["nor"][vis][ok]
    ix, iy, Z = ix[ok], iy[ok], Z[ok]
    nz = nor @ r2
    sign = np.where((nz < 0) & cl["dbl"][vis][ok], -1.0, 1.0).astype(np.float32)   # двусторонние: переворот нормали
    light = np.array([-0.45, 0.55, 0.7], np.float32)
    light /= np.linalg.norm(light)
    lr = np.array([c * light[0] - s * light[2], light[1], s * light[0] + c * light[2]], np.float32)   # свет в системе модели
    lam = np.clip((nor @ lr) * sign, 0, 1)
    nzs = nz * sign
    shade = (0.55 + 0.45 * lam)[:, None]
    rim = ((1 - nzs) ** 3)[:, None] * np.array([0.10, 0.12, 0.20], np.float32)       # лёгкая подсветка по краю
    col = np.clip(cl["col"][vis][ok] * shade + 0.045 + rim, 0, 1)
    order = np.argsort(Z)                                           # дальние первыми, ближние перезапишут
    pix = iy[order] * W + ix[order]
    buf = np.zeros((W * H, 4), np.float32)
    buf[pix, :3] = col[order]
    buf[pix, 3] = 1
    buf = buf.reshape(H, W, 4)
    buf[..., :3] *= buf[..., 3:4]
    d = buf.reshape(h, ss, w, ss, 4).mean((1, 3))                   # усреднение ss×ss: сглаживание краёв
    a = d[..., 3:4]
    rgb = np.where(a > 0, d[..., :3] / np.maximum(a, 1e-6), 0)
    return (np.concatenate([rgb, a], 2) * 255 + 0.5).astype(np.uint8)


class _ModelBridge(QObject):
    """Передаёт готовые кадры из фонового потока в окно (сигнал сам встаёт в очередь GUI-потока)."""
    done = pyqtSignal(object)


class ModelView(QWidget):
    """Вместо статичной картинки: 3D-модель (.glb) во весь рост.
    Пока кадры считаются (несколько секунд, в фоне) показывается обычная картинка-заглушка.
    Модель плавно покачивается; если зажать мышь и повести вбок, её можно повернуть вручную.
    Нет numpy или файла .glb: остаётся статичная картинка, ничего не ломается.
    loadingChanged(True) приходит, только если загрузка затянулась (быстрая из кэша не мигает)."""
    loadingChanged = pyqtSignal(bool)

    def __init__(self, placeholder: QPixmap, w: int = 180, h: int = 270, parent=None, model_path: str = "",
                 interactive: bool = True, animate: bool = False,
                 render: tuple[int, int] | None = None):
        super().__init__(parent)
        self._loading = False
        self._notified = False                            # сигнал «загружается» уже отправлен
        self._notify_timer = QTimer(self)                 # сообщаем о загрузке, только если она длится дольше 0,6 с
        self._notify_timer.setSingleShot(True)
        self._notify_timer.setInterval(600)
        self._notify_timer.timeout.connect(self._notify_loading)
        self._rw, self._rh = render or (w, h)             # размер самих кадров; виджет потом сам вписывает их в своё окно
        self._animate = animate                           # оживление по настроению: «говорит» / «думает»
        self._mood = "idle"
        self._k_talk = self._k_think = 0.0                # плавные коэффициенты 0…1, чтобы анимация включалась без рывка
        self._t = 0.0
        self._interactive = interactive                   # False: в главном окне мышь достаётся самому окну
        self.setMinimumSize(40, 72)                       # как раньше у аватарки: окно настроек не растёт
        self.setMaximumSize(w, h)                         # а если места больше, модель занимает до w×h
        self._w, self._h = w, h
        self._place = placeholder
        self._frames: list[QPixmap] = []                  # крупный шаг, полный круг — для ручного вращения
        self._sway_frames: list[QPixmap] = []              # мелкий шаг, узкая зона — для плавного покоя
        self._active: list[QPixmap] = []                   # на какой из двух списков сейчас смотрим
        self._phase = 0.0
        self._last = time.monotonic()
        self._drag_x: float | None = None
        self._drag_p0 = 0.0
        self._pos = 0.0                                   # позиция внутри self._active: 0 … len(active)-1
        self._token = 0                                   # номер текущей модели: чужие (устаревшие) расчёты игнорируются
        self._bridge = _ModelBridge()
        self._bridge.done.connect(self._on_done)
        self._timer = QTimer(self)
        self._timer.setTimerType(Qt.TimerType.PreciseTimer)   # обычный таймер не держит ровный интервал,
                                                               # из-за этого покачивание выглядело дёрганым
        self._timer.setInterval(16)
        self._timer.timeout.connect(self._tick)
        self.set_model(model_path)

    def set_model(self, model_path: str = "") -> None:
        """Меняет модель на лету: старая останавливается, пока считается новая показывается картинка-заглушка."""
        self._token += 1
        self._timer.stop()
        self._end_loading()
        self._frames, self._sway_frames, self._active = [], [], []
        self._phase, self._pos, self._drag_x = 0.0, 0.0, None
        self.unsetCursor()
        path = find_model(model_path)
        self.update()
        if path is None:
            return
        key = (str(path), self._rw, self._rh)
        if key in _MODEL_CACHE:
            self._on_frames(*_MODEL_CACHE[key])
        else:
            self._loading = True
            self._notify_timer.start()
            threading.Thread(target=self._worker, args=(path, key, self._token), daemon=True).start()

    def set_mood(self, mood: str) -> None:
        """«talk» — говорит, «think» — думает, любое другое — спокойно стоит."""
        self._mood = mood

    def _on_done(self, payload) -> None:
        token, frames, sway_frames = payload
        if token != self._token:                          # пока считалась эта модель, могли выбрать другую
            return
        if frames is None:                                # не вышло: остаётся картинка
            self._end_loading()
            self.update()
        else:
            self._on_frames(frames, sway_frames)

    def sizeHint(self) -> QSize:
        return QSize(self._w, self._h)

    def _worker(self, path: Path, key, token: int = 0) -> None:
        try:
            import numpy as np

            def decode(raw: bytes):
                img = QImage.fromData(raw).convertToFormat(QImage.Format.Format_RGB888)
                w, h, bpl = img.width(), img.height(), img.bytesPerLine()
                ptr = img.constBits()
                ptr.setsize(h * bpl)
                arr = np.frombuffer(ptr, np.uint8).reshape(h, bpl)[:, :w * 3]
                return arr.reshape(h, w, 3).copy()

            pw, ph = self._rw, self._rh                 # размер кадров
            st = path.stat()
            tag = (f"{pw}x{ph}_{st.st_size}_{int(st.st_mtime)}_{MODEL_YAW_MAX}_{MODEL_YAW_STEP}_"
                   f"{MODEL_SWAY_DEG}_{MODEL_SWAY_STEP}_v{MODEL_CACHE_VER}")
            cache = MODEL_CACHE_DIR / f"model_{path.stem}_{tag}.npz"
            arr = sway_arr = None
            if cache.is_file():                           # кадры уже считались: берём готовые, это почти мгновенно
                try:
                    with np.load(cache) as z:
                        arr, sway_arr = z["frames"], z["sway"]
                except Exception:
                    arr = sway_arr = None
            if arr is None:
                mdl = _glb_load(path, decode)
                cl = _glb_cloud(mdl, pw, ph)
                arr = np.stack([_glb_render(cl, math.radians(deg))
                                for deg in range(-MODEL_YAW_MAX, MODEL_YAW_MAX + 1, MODEL_YAW_STEP)])
                # отдельный, мелкий набор кадров только для узкой зоны покоя: иначе плавное покачивание
                # перетекало бы между далёкими по углу кадрами крупного набора и выглядело бы рваным
                sway_arr = np.stack([_glb_render(cl, math.radians(deg))
                                     for deg in range(-MODEL_SWAY_DEG, MODEL_SWAY_DEG + 1, MODEL_SWAY_STEP)])
                del cl, mdl
                try:
                    MODEL_CACHE_DIR.mkdir(parents=True, exist_ok=True)
                    for old in MODEL_CACHE_DIR.glob(f"model_{path.stem}_{pw}x{ph}_*.npz"):
                        old.unlink(missing_ok=True)       # прежние кадры этой модели не копим
                    tmp = cache.with_suffix(".tmp.npz")
                    np.savez(tmp, frames=arr, sway=sway_arr)   # без сжатия: так читается быстрее
                    tmp.replace(cache)                    # файл появляется целиком или не появляется вовсе
                except OSError:
                    pass

            def to_pixmaps(a):
                out = []
                for rgba in a:
                    buf = np.ascontiguousarray(rgba).tobytes()
                    img = QImage(buf, pw, ph, pw * 4, QImage.Format.Format_RGBA8888).copy()
                    img = img.convertToFormat(QImage.Format.Format_ARGB32_Premultiplied)
                    out.append(QPixmap.fromImage(img))    # QPixmap, не QImage: drawPixmap ждёт именно его
                return out

            frames, sway_frames = to_pixmaps(arr), to_pixmaps(sway_arr)
            _MODEL_CACHE[key] = (frames, sway_frames)
            self._bridge.done.emit((token, frames, sway_frames))
        except RuntimeError:
            pass                                          # окно уже закрыли, пока шёл расчёт
        except Exception as e:                            # нет numpy, битый файл и т.п.: остаётся картинка
            print(f"3D-модель не загрузилась ({e.__class__.__name__}: {e}), показываю статичную картинку",
                  file=sys.stderr)
            try:
                self._bridge.done.emit((token, None, None))
            except RuntimeError:
                pass

    def _notify_loading(self) -> None:
        if self._loading and not self._notified:
            self._notified = True
            self.loadingChanged.emit(True)

    def _end_loading(self) -> None:
        self._loading = False
        self._notify_timer.stop()
        if self._notified:
            self._notified = False
            self.loadingChanged.emit(False)

    def _on_frames(self, frames, sway_frames) -> None:
        self._end_loading()
        self._frames = frames
        self._sway_frames = sway_frames
        # по умолчанию стоим во фронтальной, мелко нарезанной зоне: там покачивание плавное
        self._active = self._sway_frames or self._frames
        self._pos = (len(self._active) - 1) / 2
        self._last = time.monotonic()
        if self._interactive:
            self.setCursor(Qt.CursorShape.OpenHandCursor)
        if self.isVisible():
            self._timer.start()
        self.update()

    def showEvent(self, e):
        super().showEvent(e)
        if self._active:
            self._last = time.monotonic()
            self._timer.start()

    def hideEvent(self, e):
        self._timer.stop()
        super().hideEvent(e)

    def _tick(self) -> None:
        now = time.monotonic()
        dt = min(now - self._last, 0.1)                   # провал кадра не даёт скачка
        if self._animate:
            self._t += dt
            e = min(1.0, dt * 7)
            self._k_talk += ((1.0 if self._mood == "talk" else 0.0) - self._k_talk) * e
            self._k_think += ((1.0 if self._mood == "think" else 0.0) - self._k_think) * e
        # автоматическое покачивание крутим только пока активен мелко нарезанный набор (стоим у фронта);
        # если модель оттащили в сторону/назад (крупный набор), она просто ждёт неподвижно, пока не отпустят
        if self._drag_x is None and self._active is self._sway_frames and len(self._active) > 1:
            slow = max(0.2, 1 - 0.5 * self._k_talk - 0.7 * self._k_think)   # говорит или думает: смотрит на тебя, почти не крутится
            self._phase += dt * MODEL_SWAY_SPEED * slow
            n = len(self._active)
            amp = (n - 1) / 2                             # весь мелкий набор целиком и есть амплитуда покоя
            self._pos = amp + amp * math.sin(self._phase)
        self._last = now
        self.update()

    def mousePressEvent(self, e):
        if self._active and self._interactive and e.button() == Qt.MouseButton.LeftButton:
            if self._active is self._sway_frames and self._frames:
                # переходим на крупный набор (он покрывает весь круг), подставив тот же угол
                deg = -MODEL_SWAY_DEG + self._pos * MODEL_SWAY_STEP
                nf = len(self._frames)
                self._pos = max(0.0, min(nf - 1.0, (deg + MODEL_YAW_MAX) / MODEL_YAW_STEP))
                self._active = self._frames
            self._drag_x = e.position().x()
            self._drag_p0 = self._pos
            self.setCursor(Qt.CursorShape.ClosedHandCursor)

    def mouseMoveEvent(self, e):
        if self._drag_x is not None:
            n = len(self._active)
            dx = e.position().x() - self._drag_x
            # без ограничения снизу/сверху: кадр 0 (-180°) и последний (180°) — один и тот же ракурс,
            # поэтому позицию можно крутить бесконечно в любую сторону, а зацикливание сделано в paintEvent
            self._pos = self._drag_p0 + dx / max(1, self.width()) * (n - 1)
            self.update()

    def mouseReleaseEvent(self, e):
        if self._drag_x is not None:
            self._drag_x = None
            n = len(self._active)
            period = max(1, n - 1)                        # n-1 шагов = полный круг (кадр 0 == кадр n-1)
            pos_w = self._pos % period                     # сворачиваем в канонический диапазон
            deg = -MODEL_YAW_MAX + pos_w * MODEL_YAW_STEP   # self._active тут всегда self._frames (крупный)
            if abs(deg) <= MODEL_SWAY_DEG and self._sway_frames:
                # вернулись в зону фронта: переключаемся обратно на мелкий набор ради плавного покоя
                ns = len(self._sway_frames)
                sway_pos = max(0.0, min(ns - 1.0, (deg + MODEL_SWAY_DEG) / MODEL_SWAY_STEP))
                self._active = self._sway_frames
                self._pos = sway_pos
                amp = (ns - 1) / 2
                rel = max(-1.0, min(1.0, (sway_pos - amp) / amp)) if amp else 0.0
                self._phase = math.asin(rel)              # покачивание продолжается оттуда, где отпустили
            else:
                self._pos = pos_w                          # оставляем модель там, где отпустили, без покачивания
            self._last = time.monotonic()
            self.setCursor(Qt.CursorShape.OpenHandCursor)

    def _fit(self, pm: QPixmap) -> QRectF:
        """Куда вписать картинку: по центру, с сохранением пропорций."""
        w, h = self.width(), self.height()
        k = min(w / max(1, pm.width()), h / max(1, pm.height()))
        tw, th = pm.width() * k, pm.height() * k
        return QRectF((w - tw) / 2, (h - th) / 2, tw, th)

    def _apply_anim(self, p: QPainter, r: QRectF) -> None:
        """Оживление поверх готовых кадров: сдвиг, наклон и лёгкое сжатие вокруг «ног» фигуры.
        Скелета в кадрах нет, поэтому это не движение костей, а плавная имитация живости."""
        kt, kk, t = self._k_talk, self._k_think, self._t
        dy, rot, sx, sy = 0.0, 0.0, 1.0, 1.0
        # говорит: ритмичные кивки в такт речи, лёгкое сжатие-растяжение и качание головой
        beat = 0.7 * abs(math.sin(t * 8.5)) + 0.3 * abs(math.sin(t * 13.7 + 1.0))
        dy -= kt * beat * 0.016 * r.height()
        sy += kt * (beat - 0.5) * 0.014
        sx -= kt * (beat - 0.5) * 0.008
        rot += kt * 1.6 * math.sin(t * 4.2)
        # думает: медленный наклон головы и неторопливое «дыхание»
        rot += kk * 3.0 * math.sin(t * 1.1)
        dy -= kk * 0.006 * r.height() * (1 + math.sin(t * 0.8))
        px, py = r.center().x(), r.bottom()
        k = 0.94                                          # небольшой запас по краям, чтобы наклон и прыжки не обрезались
        p.translate(px, py + dy)
        p.rotate(rot)
        p.scale(k * sx, k * sy)
        p.translate(-px, -py)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        if self._active:                                  # фон прозрачный: фигура стоит прямо на карточке
            frames = self._active
            n = len(frames)
            # у набора self._frames (полный круг) кадр 0 и последний — один ракурс, поэтому зацикливаем;
            # у self._sway_frames зоны покоя зацикливание не нужно (там и так клампится в mouseMove/_tick)
            if frames is self._frames:
                period = max(1, n - 1)
                pos = self._pos % period if n > 1 else 0.0
            else:
                pos = max(0.0, min(n - 1.0, self._pos))
            i = min(int(pos), n - 1)
            f = pos - i
            target = self._fit(frames[i])
            p.save()
            if self._animate:
                self._apply_anim(p, target)
            p.drawPixmap(target, frames[i], QRectF(frames[i].rect()))
            if f > 0.01 and i + 1 < n:                    # смешиваем соседние кадры: движение без ступенек
                p.setOpacity(f)
                p.drawPixmap(target, frames[i + 1], QRectF(frames[i + 1].rect()))
                p.setOpacity(1.0)
            p.restore()
        elif not self._place.isNull():                    # пока модель считается: обычная картинка целиком
            p.drawPixmap(self._fit(self._place), self._place, QRectF(self._place.rect()))
        p.end()


class LoadNote(QWidget):
    """Плашка «Подожди немного: Мими загружается…» со вращающимся кружком (для нижней панели).
    Без обводки: фон светлее окна, а края размыты и плавно растворяются."""
    TEXT = "Подожди немного: Мими загружается"
    PAD = 7           # ширина размытого края вокруг плашки, пиксели
    CORE_H = 26       # высота плотной части плашки

    def __init__(self, parent=None):
        super().__init__(parent)
        self._t0 = time.monotonic()
        self._timer = QTimer(self)
        self._timer.setInterval(40)
        self._timer.timeout.connect(self.update)
        self.setVisible(False)

    def _font(self) -> QFont:
        f = QFont(self.font())
        f.setPixelSize(12)
        return f

    def sizeHint(self) -> QSize:
        fm = QFontMetrics(self._font())
        w = fm.horizontalAdvance(T(self.TEXT) + "...") + 52        # запас под точки: плашка не дёргается
        return QSize(w + 2 * self.PAD, self.CORE_H + 2 * self.PAD)

    def minimumSizeHint(self) -> QSize:
        return self.sizeHint()

    def setVisible(self, on: bool) -> None:
        super().setVisible(on)
        if on:
            self._t0 = time.monotonic()
            self._timer.start()
        else:
            self._timer.stop()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        pad = self.PAD
        core = QRectF(self.rect()).adjusted(pad, pad, -pad, -pad)
        base = QColor(CONTROL)
        fill = QColor("#171A24") if QColor(BG).lightnessF() < 0.5 else base.darker(108)   # тёмная тема: цвет фона плашки #171A24
        # размытие: стопка скруглённых прямоугольников от большого к малому; в центре они складываются
        # в плотный цвет, а к краю остаётся один слабый слой, поэтому край мягко тает без обводки
        p.setPen(Qt.PenStyle.NoPen)
        layer = QColor(fill)
        layer.setAlphaF(1 - 0.3 ** (1 / (pad + 1)))                 # вместе слои дают ~70% плотности: плашка слегка прозрачная
        for k in range(pad, -1, -1):
            rr = core.adjusted(-k, -k, k, k)
            p.setBrush(layer)
            p.drawRoundedRect(rr, rr.height() / 2, rr.height() / 2)
        t = time.monotonic() - self._t0
        cx, cy, rad = core.x() + 16, core.center().y(), 6.0
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(MUTED), 2))                  # кружок-дорожка и бегущая дуга акцентного цвета
        p.drawEllipse(QPointF(cx, cy), rad, rad)
        pen = QPen(QColor(ACCENT), 2)
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        p.setPen(pen)
        p.drawArc(QRectF(cx - rad, cy - rad, 2 * rad, 2 * rad), int(-t * 360 * 16 * 1.2) % (360 * 16), 100 * 16)
        p.setFont(self._font())
        p.setPen(QColor(TEXT))
        dots = "." * (int(t * 2.5) % 4)
        p.drawText(QRectF(core.x() + 31, core.y(), core.width() - 36, core.height()),
                   Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, T(self.TEXT) + dots)
        p.end()


class _FootBar(QWidget):
    """Нижняя панель окна настроек. Плашка загрузки стоит в ней вручную: отступ от плотной части плашки
    до левого края, до верха и до низа панели один и тот же."""
    note: "LoadNote | None" = None

    def gap(self) -> int:
        return max(6, round((self.height() - LoadNote.CORE_H) / 2))

    def place_note(self) -> None:
        n = self.note
        if n is None:
            return
        off = self.gap() - LoadNote.PAD                  # PAD — размытый край, он выходит за плотную часть плашки
        sh = n.sizeHint()
        n.setGeometry(off, off, sh.width(), sh.height())
        n.raise_()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self.place_note()


def smooth_blur(img: QImage, radius: float) -> QImage:
    """Настоящее гауссово размытие без «пикселей» и тёмных краёв.
    Раньше картинку просто сжимали в десятки раз и растягивали обратно: при билинейном растяжении выступали квадраты.
    Теперь: уменьшаем не сильно, размываем QGraphicsBlurEffect с высоким качеством (края достраиваем, чтобы они не
    темнели) и растягиваем обратно ступенями по 2x, поэтому переходов-«кубиков» нет."""
    w, h = img.width(), img.height()
    if radius < 0.5 or w < 4 or h < 4:
        return img
    fmt = QImage.Format.Format_ARGB32_Premultiplied
    s = max(1, round(radius / 5))                       # размываем в уменьшенном виде: быстро, радиус там около 5px
    tw, th = max(2, w // s), max(2, h // s)
    r = radius * tw / w if s > 1 else radius
    small = img.convertToFormat(fmt)
    if s > 1:
        small = small.scaled(tw, th, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.SmoothTransformation)
    pad = int(r * 2) + 2
    canvas = QImage(tw + 2 * pad, th + 2 * pad, fmt)
    canvas.fill(Qt.GlobalColor.transparent)
    q = QPainter(canvas)
    q.drawImage(pad, pad, small)
    q.drawImage(QRect(pad, 0, tw, pad), small, QRect(0, 0, tw, 1))                 # края растягиваем наружу
    q.drawImage(QRect(pad, pad + th, tw, pad), small, QRect(0, th - 1, tw, 1))
    q.drawImage(QRect(0, pad, pad, th), small, QRect(0, 0, 1, th))
    q.drawImage(QRect(pad + tw, pad, pad, th), small, QRect(tw - 1, 0, 1, th))
    for dx, sx in ((0, 0), (pad + tw, tw - 1)):                                    # углы
        for dy, sy in ((0, 0), (pad + th, th - 1)):
            q.drawImage(QRect(dx, dy, pad, pad), small, QRect(sx, sy, 1, 1))
    q.end()
    scene = QGraphicsScene()
    item = QGraphicsPixmapItem(QPixmap.fromImage(canvas))
    eff = QGraphicsBlurEffect()
    eff.setBlurRadius(r)
    eff.setBlurHints(QGraphicsBlurEffect.BlurHint.QualityHint)
    item.setGraphicsEffect(eff)
    scene.addItem(item)
    out = QImage(canvas.size(), fmt)
    out.fill(Qt.GlobalColor.transparent)
    q = QPainter(out)
    scene.render(q, QRectF(out.rect()), QRectF(canvas.rect()))
    q.end()
    cur = out.copy(pad, pad, tw, th)
    while cur.width() * 2 <= w and cur.height() * 2 <= h:   # растягиваем ступенями: без «кубиков»
        cur = cur.scaled(cur.width() * 2, cur.height() * 2, Qt.AspectRatioMode.IgnoreAspectRatio,
                         Qt.TransformationMode.SmoothTransformation)
    if cur.width() != w or cur.height() != h:
        cur = cur.scaled(w, h, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.SmoothTransformation)
    return cur


def blur_pixmap(pix: QPixmap, factor: int = 24, tint_alpha: int = -1) -> QPixmap:
    """Размытие снимка (гауссово, без пикселей), потом тонировка цветом темы (тёмной: затемнить, светлой: осветлить)."""
    w, h = pix.width(), pix.height()
    if w <= 0 or h <= 0:
        return pix
    big = QPixmap.fromImage(smooth_blur(pix.toImage(), factor * 0.8))
    p = QPainter(big)
    tint = QColor(POP_BG)
    tint.setAlpha(tint_alpha if tint_alpha >= 0 else (130 if THEME_NAME == "dark" else 200))
    p.fillRect(big.rect(), tint)
    p.end()
    big.setDevicePixelRatio(pix.devicePixelRatio())
    return big


# буквы «MI» в стиле логотипа neverlose: прямые штрихи, срезанная правая стойка, «лапки» внизу
# (многоугольники в сетке 154 x 100)
LOGO_W, LOGO_H = 154, 100
LOGO_POLYS = [
    [(0, 0), (16, 0), (16, 100), (0, 100)],            # M: левая стойка
    [(16, 86), (34, 86), (34, 100), (16, 100)],        # M: левая лапка
    [(16, 0), (34, 0), (61, 80), (43, 80)],            # M: левая диагональ
    [(88, 0), (70, 0), (43, 80), (61, 80)],            # M: правая диагональ
    [(88, 0), (104, 0), (104, 66), (88, 54)],          # M: правая стойка со срезом
    [(76, 86), (104, 86), (104, 100), (76, 100)],      # M: правая лапка
    [(128, 0), (144, 0), (144, 100), (128, 100)],      # I: стойка
    [(118, 86), (154, 86), (154, 100), (118, 100)],    # I: лапки
]


def brand_badge(size: int = 36) -> QPixmap:
    """Квадратный значок-логотип с буквами MI (стиль логотипа neverlose)."""
    dpr = 2
    pm = QPixmap(size * dpr, size * dpr)
    pm.setDevicePixelRatio(dpr)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setPen(QPen(QColor("#1f2433"), 1))
    p.setBrush(QColor("#141824"))
    p.drawRoundedRect(QRectF(0.5, 0.5, size - 1, size - 1), size * 0.28, size * 0.28)
    p.setPen(Qt.PenStyle.NoPen)
    k = size * 0.64 / LOGO_W                              # масштаб букв
    ox, oy = (size - LOGO_W * k) / 2, (size - LOGO_H * k) / 2
    p.setBrush(QColor("#ffffff"))
    for poly in LOGO_POLYS:
        path = QPainterPath()
        path.moveTo(ox + poly[0][0] * k, oy + poly[0][1] * k)
        for x, y in poly[1:]:
            path.lineTo(ox + x * k, oy + y * k)
        path.closeSubpath()
        p.drawPath(path)
    p.end()
    return pm


def chevron_png(color: str, size: int = 14) -> str:
    """Стрелка выпадающих списков. QSS умеет только картинки, поэтому рисуем её в файл."""
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    pen = QPen(QColor(color), 1.7)
    pen.setCapStyle(Qt.PenCapStyle.RoundCap)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    p.setPen(pen)
    p.setBrush(Qt.BrushStyle.NoBrush)
    path = QPainterPath()
    path.moveTo(3.5, size / 2 - 1.8)
    path.lineTo(size / 2, size / 2 + 1.8)
    path.lineTo(size - 3.5, size / 2 - 1.8)
    p.drawPath(path)
    p.end()
    out = Path(tempfile.gettempdir()) / "mimi_chevron.png"
    pm.save(str(out), "PNG")
    return out.as_posix()


def spaced(label: QLabel, px: float) -> QLabel:
    """Разрядка букв (в QSS её нет)."""
    f = label.font()
    f.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing, px)
    label.setFont(f)
    return label


def hline(name: str = "sep") -> QFrame:
    """Тонкая разделительная линия."""
    f = QFrame()
    f.setObjectName(name)
    f.setFixedHeight(1)
    return f


# ---------- элементы интерфейса ----------
class NavButton(QPushButton):
    """Пункт боковой панели: иконка + текст, активный выделен светлой плашкой."""
    _k = 1.0                       # масштаб окна настроек (меняет SettingsDialog)
    freeze_hover = False           # пока едет раскрывающийся блок, подсветка под курсором не меняется

    def __init__(self, icon: str, title: str):
        super().__init__()
        self.icon_name, self.title, self._hover = icon, title, False
        self.indent = 0                # вложенный пункт сдвинут вправо
        self.expanded = False          # раскрывающийся пункт открыт: текст ярче
        self.setCheckable(True)
        self.setFixedHeight(34)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def enterEvent(self, e):
        if NavButton.freeze_hover:
            return
        self._hover = True
        self.update()

    def leaveEvent(self, e):
        if NavButton.freeze_hover:
            return
        self._hover = False
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        k = self._k
        on = self.isChecked()
        p.setPen(Qt.PenStyle.NoPen)
        if on:
            p.setBrush(QColor(SELECTED))
            p.drawRoundedRect(QRectF(0, 0, w, h), 9 * k, 9 * k)
        elif self._hover:
            p.setBrush(QColor(*HOVER_OV, 10))
            p.drawRoundedRect(QRectF(0, 0, w, h), 9 * k, 9 * k)
        col = STRONG if (on or self.expanded) else (TEXT if self._hover else NAV_IDLE)
        icon_col = ACCENT if on else col   # активная вкладка: иконка цветом темы, текст по-прежнему белый
        isz = max(8, round(18 * k))
        ind = self.indent * k
        p.drawPixmap(QPointF(15 * k + ind, (h - isz) / 2), draw_icon(self.icon_name, icon_col, isz))
        f = self.font()
        f.setPixelSize(max(8, round(14 * k)))
        f.setWeight(QFont.Weight.Medium)    # толщина не зависит от выбора: иначе при смене вкладки ширина текста прыгает
        p.setFont(f)
        p.setPen(QColor(col))
        p.drawText(QRectF(46 * k + ind, 0, w - 46 * k - ind, h), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, self.title)


class _Drawer(QWidget):
    """Выдвижной блок для боковой панели: меняется только его высота, а содержимое (внутреннее окошко
    полной высоты) просто сдвигается и обрезается краем. Кнопки внутри не пересчитываются на каждом кадре,
    поэтому раскрытие идёт плавно, без дёрганья."""

    def __init__(self):
        super().__init__()
        self._h = 0
        self.inner = QWidget(self)
        self.lay = QVBoxLayout(self.inner)
        self.lay.setContentsMargins(0, 4, 0, 0)
        self.lay.setSpacing(4)
        self._full = 0                 # полная высота содержимого: меряется перед анимацией, а не на каждом кадре
        self.setFixedHeight(0)

    def full_height(self) -> int:
        """Измеряет полную высоту содержимого и запоминает её."""
        self.lay.activate()
        self._full = self.inner.sizeHint().height()
        return self._full

    def get_h(self) -> int:
        return self._h

    def set_h(self, v: int) -> None:
        self._h = max(0, int(v))
        self.setFixedHeight(self._h)

    h = pyqtProperty(int, get_h, set_h)

    def resizeEvent(self, e):
        full = self._full or self.full_height()
        self.inner.setGeometry(0, self.height() - full, self.width(), full)   # чем выше блок, тем ниже опускается содержимое
        super().resizeEvent(e)


class TopBar(QWidget):
    """Верхняя полоса окна: за неё окно двигается мышью."""

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and self.window().windowHandle():
            self.window().windowHandle().startSystemMove()


_FROST: dict = {}


def _frost_backdrop(dlg) -> "QPixmap | None":
    """Размытая картинка заднего фона окна, на которую смотрит стекло (матовость). None: картинки нет."""
    c = getattr(dlg, "_bd_cache", None)
    if not (backdrop_on() or aurora_on()) or not c or c[1] is None:
        return None
    pm = c[1]
    key = (pm.cacheKey(), VISUAL["glass_frost"])
    if _FROST.get("key") != key:
        r = VISUAL["glass_frost"] * 0.35
        _FROST["pm"] = QPixmap.fromImage(smooth_blur(pm.toImage(), r)) if r >= 0.5 else pm
        _FROST["key"] = key
    return _FROST["pm"]


class GlassFrame(QFrame):
    """Плашка в стиле liquid glass: полупрозрачное тело (картинка и фон просвечивают), мягкий блик сверху,
    свет в левом верхнем углу, яркая кромка с преломлением и тонкая внутренняя кромка, которая даёт стеклу толщину.
    Цвета берутся из темы, а плотность, блик и кромка настраиваются в редакторе темы (карточка «Liquid glass»)."""

    def paintEvent(self, _):
        w, h = self.width(), self.height()
        if w < 4 or h < 4:
            return
        k = getattr(self.window(), "_k", 1.0) or 1.0
        dark = QColor(BG).lightnessF() < 0.5
        rad = 12 * k
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        box = QRectF(0.5, 0.5, w - 1, h - 1)
        if not VISUAL["glass_on"]:                                # стекло выключено: обычная плоская карточка
            p.setPen(QPen(QColor(BORDER), 1))
            p.setBrush(QColor(CARD))
            p.drawRoundedRect(box, rad, rad)
            return
        shine, rimk = VISUAL["glass_shine"] / 60.0, VISUAL["glass_rim"] / 70.0
        clip = QPainterPath()
        clip.addRoundedRect(box, rad, rad)
        dlg = self.window()
        bd = _frost_backdrop(dlg)
        if bd is not None:                                        # настоящее стекло: то, что ЗА плашкой, матовое и искажено у краёв
            sh = getattr(dlg, "SHADOW", 0)
            pos = self.mapTo(dlg, QPoint(0, 0))
            ox, oy = pos.x() - sh, pos.y() - sh
            refr = VISUAL["glass_refract"] / 100.0
            p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)

            def zoom(m: float, path) -> None:
                p.save()
                p.setClipPath(path)
                sw, shh = w / m, h / m
                p.drawPixmap(QRectF(0, 0, w, h), bd, QRectF(ox + (w - sw) / 2, oy + (h - shh) / 2, sw, shh))
                p.restore()

            def rr(inset: float) -> QPainterPath:
                q = QPainterPath()
                q.addRoundedRect(box.adjusted(inset, inset, -inset, -inset), max(1.0, rad - inset), max(1.0, rad - inset))
                return q
            m_in, m_edge, nb = 1.0 + 0.04 * refr, 1.0 + 0.40 * refr, 5
            edge = max(8 * k, min(w, h) * 0.07)
            zoom(m_in, clip)                                      # середина: лёгкое увеличение
            if refr > 0:
                for i in range(1, nb + 1):                        # у края линза сильнее: полосы с растущим увеличением
                    a0, a1 = edge * (i - 1) / nb, edge * i / nb
                    ring = rr(a0).subtracted(rr(a1)) if i < nb else rr(a0).subtracted(rr(edge))
                    zoom(m_edge - (m_edge - m_in) * (i - 1) / nb, ring)
            op = VISUAL["glass_opacity"] / 100.0                  # стекло прозрачнее окружения: картинка за ним видна лучше
            ta = max(0.0, 0.5 * op - 0.2) if getattr(dlg, "_aurora", False) else 0.55 * op
            tint = QColor(BG)
            tint.setAlphaF(tint.alphaF() * ta)
            p.fillPath(clip, tint)
        clear = QColor(255, 255, 255, 0)
        white = lambda a, f=1.0: QColor(255, 255, 255, max(0, min(255, round(a * f))))
        body = QColor(CARD)                                       # тело стекла: цвет карточки темы, но с просветом
        body.setAlphaF(body.alphaF() * VISUAL["glass_opacity"] / 100.0)
        p.setPen(Qt.PenStyle.NoPen)
        if bd is None:                                            # без фона за стеклом тело красится цветом карточки
            p.setBrush(body)
            p.drawPath(clip)
        p.save()
        p.setClipPath(clip)
        if bd is None:                                            # картинки нет: стеклу нечего преломлять, свой мягкий цветной свет внутри
            glow = QColor(ACCENT)
            glow.setAlpha(max(0, min(255, round((70 if dark else 45) * shine))))
            gg = QRadialGradient(QPointF(w * 0.95, h * 1.05), max(w, h) * 0.8)
            gg.setColorAt(0.0, glow)
            glow.setAlpha(0)
            gg.setColorAt(1.0, glow)
            p.fillRect(box, gg)
        p.fillRect(box, white(18 if dark else 0, shine))          # стекло приподнято над фоном: светлее его
        gh = min(h * 0.45, 76 * k)                                # глянцевый блик: изогнутая «крышка» сверху с чёткой нижней кромкой
        ry = gh * 2.4
        gloss = QPainterPath()
        gloss.addEllipse(QRectF(-w * 0.3, gh - 2 * ry, w * 1.6, 2 * ry))
        gl = QLinearGradient(0, 0, 0, gh)
        gl.setColorAt(0.0, white(52 if dark else 200, shine))
        gl.setColorAt(1.0, white(10 if dark else 45, shine))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(gl))
        p.drawPath(gloss)
        rg = QRadialGradient(QPointF(w * 0.06, h * 0.04), max(w, h) * 0.55)   # яркая точка света в левом верхнем углу
        rg.setColorAt(0.0, white(60 if dark else 170, shine))
        rg.setColorAt(1.0, clear)
        p.fillRect(box, rg)
        if dark:                                                  # снизу стекло чуть темнее: объём
            gh2 = 28 * k
            g2 = QLinearGradient(0, h - gh2, 0, h)
            g2.setColorAt(0.0, QColor(0, 0, 0, 0))
            g2.setColorAt(1.0, QColor(0, 0, 0, 50))
            p.fillRect(QRectF(0, h - gh2, w, gh2), g2)
        p.restore()
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(BORDER), 1))                         # тонкая граница темы под кромкой
        p.drawRoundedRect(box, rad, rad)
        rim = QLinearGradient(0, 0, w, h)                         # кромка: свет слева сверху и справа снизу
        a_tl, a_mid, a_br = (170, 30, 95) if dark else (240, 90, 160)
        for width, f in ((3.6 * k, 0.28), (1.2 * k, 1.0)):          # сначала мягкое свечение кромки, потом сама линия
            rim.setColorAt(0.0, white(a_tl, rimk * f))
            rim.setColorAt(0.35, white(a_mid, rimk * f))
            rim.setColorAt(0.65, white(a_mid, rimk * f))
            rim.setColorAt(1.0, white(a_br, rimk * f))
            p.setPen(QPen(QBrush(rim), max(1.0, width)))
            p.drawRoundedRect(box, rad, rad)
        ig = QLinearGradient(0, 0, 0, h)                          # внутренняя кромка: толщина стекла
        ig.setColorAt(0.0, white(28 if dark else 100, rimk))
        ig.setColorAt(0.4, clear)
        ig.setColorAt(1.0, white(8 if dark else 45, rimk))
        p.setPen(QPen(QBrush(ig), 1))
        d = 2 * k
        p.drawRoundedRect(box.adjusted(d, d, -d, -d), max(1.0, rad - d), max(1.0, rad - d))


class Card(QWidget):
    """Карточка как у neverlose: мелкая подпись НАД ней, внутри строки «подпись — значение».
    Параметр icon оставлен для совместимости вызовов и не рисуется."""

    def __init__(self, title: str, icon: str | None = None):
        super().__init__()
        self._fresh = True              # перед первой строкой (и после подраздела) линия не нужна
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(8)
        self._outer = outer
        t = spaced(QLabel(title.upper()), 1.6)
        t.setObjectName("cardTitle")
        outer.addWidget(t)
        frame = GlassFrame()
        frame.setObjectName("glasscard")
        outer.addWidget(frame)
        self.body = QVBoxLayout(frame)
        self.body.setContentsMargins(16, 2, 16, 2)
        self.body.setSpacing(0)

    def title_right(self, widget: QWidget) -> None:
        """Виджет (например, переключатель) в одной строке с заголовком карточки, справа."""
        title = self._outer.takeAt(0).widget()
        head = QHBoxLayout()
        head.setContentsMargins(0, 0, 0, 0)
        head.setSpacing(8)
        head.addWidget(title)
        head.addStretch(1)
        head.addWidget(widget)
        self._outer.insertLayout(0, head)

    def row(self, label: str, widget: QWidget, desc: str | None = None, stack: bool = False) -> None:
        if not self._fresh:
            self.body.addWidget(hline("rowsep"))
        self._fresh = False
        w = QWidget()
        text = QVBoxLayout()
        text.setSpacing(2)
        text.addWidget(QLabel(label))
        if desc:
            d = QLabel(desc)
            d.setObjectName("desc")
            d.setWordWrap(True)
            text.addWidget(d)
        if stack:                              # длинный список: подпись сверху, поле на всю ширину
            lay = QVBoxLayout(w)
            lay.setContentsMargins(0, 10, 0, 10)
            lay.setSpacing(8)
            lay.addLayout(text)
            lay.addWidget(widget)
        else:
            lay = QHBoxLayout(w)
            lay.setContentsMargins(0, 10, 0, 10)
            lay.setSpacing(12)
            lay.addLayout(text, 1)
            if not isinstance(widget, Toggle):
                widget.setFixedWidth(getattr(widget, "row_width", 180))
            lay.addWidget(widget, 0, Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight)
        self.body.addWidget(w)

    def divider(self, text: str) -> None:
        """Подраздел внутри карточки: акцентная подпись и линия."""
        w = QWidget()
        h = QHBoxLayout(w)
        h.setContentsMargins(0, 14, 0, 4)
        h.setSpacing(10)
        h.addWidget(spaced(QLabel(text.upper()), 1.4))
        w.findChild(QLabel).setObjectName("divLabel")
        h.addWidget(hline("sep"), 1, Qt.AlignmentFlag.AlignVCenter)
        self.body.addWidget(w)
        self._fresh = True

    def wide(self, widget: QWidget, grow: bool = False) -> None:
        self.body.addSpacing(12)
        self.body.addWidget(widget)
        if grow:                               # виджет забирает всю свободную высоту карточки
            self.body.setStretchFactor(widget, 1)
        self.body.addSpacing(12)
        self._fresh = False

    def fill(self) -> None:
        """Рамка карточки растягивается по высоте (нужно, когда карточку page() растягивает на всю колонку)."""
        self._outer.setStretch(1, 1)


class StepSlider(QWidget):
    """Ползунок по ступеням (тон, скорость): справа плашка с текущим значением, как у neverlose.
    Совместим с make_combo: есть currentData(), работает setEnabled()."""
    row_width = 250

    def __init__(self, items: list, current):
        super().__init__()
        self.items = items
        self.slider = QSlider(Qt.Orientation.Horizontal)
        self.slider.setRange(0, len(items) - 1)
        self.slider.setPageStep(1)
        self.slider.setCursor(Qt.CursorShape.PointingHandCursor)
        idx = next((k for k, (_, v) in enumerate(items) if v == current), len(items) // 2)
        self.slider.setValue(idx)
        self.box = QLabel()
        self.box.setObjectName("valuebox")
        self.box.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.box.setFixedSize(112, 26)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        lay.addWidget(self.slider, 1)
        lay.addWidget(self.box)
        self.slider.valueChanged.connect(self._show)
        self._show(idx)

    def _show(self, k: int) -> None:
        self.box.setText(T(self.items[k][0]))

    def currentData(self):
        return self.items[self.slider.value()][1]



# ---------- мониторинг: состояние компьютера в реальном времени ----------
def fmt_size(n: float) -> str:
    """Байты в человеческом виде: 1536 -> «1.5 КБ»."""
    units = ("Б", "КБ", "МБ", "ГБ", "ТБ")
    k = 0
    while n >= 1024 and k < len(units) - 1:
        n /= 1024
        k += 1
    return f"{n:.0f} {T(units[k])}" if k == 0 else f"{n:.1f} {T(units[k])}"


def fmt_rate(n: float) -> str:
    return f"{fmt_size(n)}{T('/с')}"


def fmt_uptime(sec: float) -> str:
    d, s = divmod(int(sec), 86400)
    h, s = divmod(s, 3600)
    parts = []
    if d:
        parts.append(f"{d} {T('д')}")
    if d or h:
        parts.append(f"{h} {T('ч')}")
    parts.append(f"{s // 60} {T('мин')}")
    return " ".join(parts)


class SysStats:
    """Читает состояние компьютера из /proc и /sys (Linux). Что прочитать не удалось, возвращается как None.
    Скорости (процессор, сеть, диск) считаются как разница между двумя соседними замерами."""
    DISK_RE = re.compile(r"^(sd[a-z]+|hd[a-z]+|vd[a-z]+|xvd[a-z]+|nvme\d+n\d+|mmcblk\d+)$")   # только целые диски, без разделов
    NET_SKIP = ("lo", "veth", "docker", "br-", "virbr")                                          # петля и виртуальные интерфейсы
    TEMP_CHIPS = ("coretemp", "k10temp", "zenpower", "cpu_thermal", "cpu-thermal", "soc_thermal", "acpitz")
    TOP_EVERY = 1.5      # список процессов обновляется не чаще, чем раз в столько секунд: обход /proc дороже остального

    def __init__(self):
        self.ncpu = os.cpu_count() or 1
        try:
            self.hz = os.sysconf("SC_CLK_TCK")
            self.pagesize = os.sysconf("SC_PAGE_SIZE")
        except (ValueError, OSError, AttributeError):
            self.hz, self.pagesize = 100, 4096
        self._temp_path = False          # False: ещё не искали, None: датчика нет
        self._rapl = False               # то же для счётчика энергии процессора
        self._freq_paths = None
        self.nprocs = 0
        self.has_nvidia = shutil.which("nvidia-smi") is not None
        self._gpu = None                 # последний ответ nvidia-smi (его читает фоновый поток)
        self._gpu_busy = False
        self.reset()

    def reset(self) -> None:
        """Новая точка отсчёта: вкладку открыли заново, и скорости за время «простоя» никому не нужны."""
        self._cpu = self._cpu_times()
        self._net = self._net_counters()
        self._dsk = self._disk_counters()
        self._pp = self._pt = None
        self._top: tuple = ([], [])
        self._rapl_prev = None

    # --- процессор ---
    @staticmethod
    def _cpu_times():
        try:
            with open("/proc/stat") as f:
                v = [int(x) for x in f.readline().split()[1:9]]
            return sum(v), v[3] + v[4]                       # всего тактов, из них простоя (idle + iowait)
        except (OSError, ValueError, IndexError):
            return None

    def cpu_percent(self):
        cur = self._cpu_times()
        prev, self._cpu = self._cpu, cur
        if not cur or not prev or cur[0] <= prev[0]:
            return None
        return max(0.0, min(100.0, (1 - (cur[1] - prev[1]) / (cur[0] - prev[0])) * 100))

    def cpu_freq(self):
        """Средняя частота ядер, ГГц."""
        if self._freq_paths is None:
            self._freq_paths = sorted(Path("/sys/devices/system/cpu").glob("cpu[0-9]*/cpufreq/scaling_cur_freq"))
        vals = []
        for p in self._freq_paths:
            try:
                vals.append(int(p.read_text()))
            except (OSError, ValueError):
                pass
        if vals:
            return sum(vals) / len(vals) / 1e6
        try:
            with open("/proc/cpuinfo") as f:
                mhz = [float(line.split(":")[1]) for line in f if line.startswith("cpu MHz")]
            return sum(mhz) / len(mhz) / 1000 if mhz else None
        except (OSError, ValueError, IndexError):
            return None

    def _find_temp(self):
        best = None
        hw_root = Path("/sys/class/hwmon")
        for hw in sorted(hw_root.glob("hwmon*")) if hw_root.is_dir() else []:
            try:
                name = (hw / "name").read_text().strip()
            except OSError:
                continue
            if name not in self.TEMP_CHIPS:
                continue
            inputs = sorted(hw.glob("temp*_input"))
            pick = None
            for f in inputs:
                try:
                    label = f.with_name(f.name.replace("_input", "_label")).read_text().strip()
                except OSError:
                    continue
                if label in ("Package id 0", "Tctl", "Tdie"):
                    pick = f
                    break
            pick = pick or (inputs[0] if inputs else None)
            rank = self.TEMP_CHIPS.index(name)
            if pick and (best is None or rank < best[0]):
                best = (rank, pick)
        if best:
            return best[1]
        zone_root = Path("/sys/class/thermal")
        for z in sorted(zone_root.glob("thermal_zone*")) if zone_root.is_dir() else []:
            try:
                kind = (z / "type").read_text().strip().lower()
            except OSError:
                continue
            if "pkg" in kind or "cpu" in kind:
                return z / "temp"
        z0 = zone_root / "thermal_zone0" / "temp"
        return z0 if z0.exists() else None

    def cpu_temp(self):
        """Температура процессора, °C."""
        if self._temp_path is False:
            self._temp_path = self._find_temp()
        if self._temp_path is None:
            return None
        try:
            return int(self._temp_path.read_text()) / 1000
        except (OSError, ValueError):
            return None

    def _find_rapl(self):
        """Счётчик энергии пакета процессора (Intel и современные AMD): (файл, значение до переполнения)."""
        root = Path("/sys/class/powercap")
        doms = sorted(root.glob("intel-rapl:[0-9]")) if root.is_dir() else []   # без вложенных доменов intel-rapl:0:0
        if not doms:
            return None
        try:
            wrap = int((doms[0] / "max_energy_range_uj").read_text())
        except (OSError, ValueError):
            wrap = 2 ** 32
        return doms[0] / "energy_uj", wrap

    def cpu_power(self):
        """Мощность процессора, Вт. None: датчика нет или ещё нет второго замера; False: файл закрыт для чтения
        (с 2020 года счётчик читает только root)."""
        if self._rapl is False:
            self._rapl = self._find_rapl()
        if self._rapl is None:
            return None
        path, wrap = self._rapl
        try:
            e = int(path.read_text())
        except PermissionError:
            return False
        except (OSError, ValueError):
            return None
        now = time.monotonic()
        prev, self._rapl_prev = self._rapl_prev, (now, e)
        if not prev or now <= prev[0]:
            return None
        de = e - prev[1]
        if de < 0:                                            # счётчик дошёл до предела и начал с нуля
            de += wrap
        return de / 1e6 / (now - prev[0])

    @staticmethod
    def rapl_files() -> list:
        root = Path("/sys/class/powercap")
        return [str(p) for p in sorted(root.glob("intel-rapl*/energy_uj"))] if root.is_dir() else []

    def grant_rapl(self) -> None:
        """Открывает счётчики энергии на чтение через pkexec (окно с паролем рисует сама система).
        Блокирует, пока человек вводит пароль: вызывать из потока. Права сбрасываются при перезагрузке."""
        files = self.rapl_files()
        if not files:
            return
        try:
            r = subprocess.run(["pkexec", "chmod", "a+r", *files], capture_output=True, text=True, timeout=180)
            if r.returncode not in (0, 126):                  # 126: человек закрыл окно с паролем
                print(f"pkexec chmod: код {r.returncode} {r.stderr.strip()}")
        except (OSError, subprocess.SubprocessError) as e:
            print(f"pkexec chmod: {e}")

    # --- память и диск ---
    @staticmethod
    def memory():
        """(ОЗУ всего, ОЗУ занято, подкачка всего, подкачка занято) в байтах."""
        try:
            info = {}
            with open("/proc/meminfo") as f:
                for line in f:
                    key, _, rest = line.partition(":")
                    if key in ("MemTotal", "MemAvailable", "MemFree", "SwapTotal", "SwapFree"):
                        info[key] = int(rest.split()[0]) * 1024
            total = info["MemTotal"]
            avail = info.get("MemAvailable", info.get("MemFree", 0))
            swap = info.get("SwapTotal", 0)
            return total, total - avail, swap, swap - info.get("SwapFree", 0)
        except (OSError, KeyError, ValueError, IndexError):
            return None

    @staticmethod
    def disk_usage():
        try:
            u = shutil.disk_usage("/")
            return u.total, u.used
        except OSError:
            return None

    def _disk_counters(self):
        rd = wr = 0
        try:
            with open("/proc/diskstats") as f:
                for line in f:
                    p = line.split()
                    if len(p) > 9 and self.DISK_RE.match(p[2]):
                        rd += int(p[5])
                        wr += int(p[9])
        except (OSError, ValueError):
            return None
        return time.monotonic(), rd * 512, wr * 512        # секторы по 512 байт

    def _net_counters(self):
        rx = tx = 0
        try:
            with open("/proc/net/dev") as f:
                for line in list(f)[2:]:
                    name, _, data = line.partition(":")
                    if name.strip().startswith(self.NET_SKIP):
                        continue
                    p = data.split()
                    rx += int(p[0])
                    tx += int(p[8])
        except (OSError, ValueError, IndexError):
            return None
        return time.monotonic(), rx, tx

    @staticmethod
    def _rates(prev, cur):
        if not prev or not cur or cur[0] <= prev[0]:
            return None
        dt = cur[0] - prev[0]
        return tuple(max(0.0, (c - p) / dt) for p, c in zip(prev[1:], cur[1:]))

    def disk_io(self):
        """(чтение, запись) байт в секунду."""
        cur = self._disk_counters()
        prev, self._dsk = self._dsk, cur
        return self._rates(prev, cur)

    def net_io(self):
        """(приём, передача) байт в секунду."""
        cur = self._net_counters()
        prev, self._net = self._net, cur
        return self._rates(prev, cur)

    # --- процессы ---
    def top_procs(self, n: int = 5) -> tuple:
        """(по процессору, по памяти): списки [(загрузка в % от всей машины, имя, память в байтах, сколько процессов, их pid)].
        Процессы с одним именем сложены вместе (у браузера их десятки), иначе весь список занял бы один браузер."""
        now = time.monotonic()
        if self._pt is not None and now - self._pt < self.TOP_EVERY:
            return self._top
        try:
            pids = [d for d in os.listdir("/proc") if d.isdigit()]
        except OSError:
            return self._top
        cur, info = {}, {}
        for pid in pids:
            try:
                with open(f"/proc/{pid}/stat") as f:
                    data = f.read()
            except OSError:                                   # процесс уже завершился или закрыт для чтения
                continue
            lp, rp = data.find("("), data.rfind(")")          # имя в скобках, и в нём бывают пробелы
            if lp < 0 or rp < 0:
                continue
            rest = data[rp + 2:].split()
            try:
                with open(f"/proc/{pid}/statm") as f:
                    sm = f.read().split()                     # страницы: размер, резидентная, общая (библиотеки, shm)
                own = max(0, int(sm[1]) - int(sm[2])) * self.pagesize     # только своя память: общую каждый процесс считал бы заново
                cur[pid] = int(rest[11]) + int(rest[12])      # utime + stime
                info[pid] = (data[lp + 1:rp], own)
            except (OSError, IndexError, ValueError):
                continue
        self.nprocs = len(cur)
        prev, pt = self._pp, self._pt
        self._pp, self._pt = cur, now
        if prev is None or now <= pt:
            return self._top
        dt = now - pt
        groups: dict = {}
        for pid, t in cur.items():
            name, rss = info[pid]
            g = groups.setdefault(name, [0.0, 0, 0, []])
            g[0] += (t - prev.get(pid, t)) / self.hz / dt * 100 / self.ncpu     # новый процесс: прироста ещё нет
            g[1] += rss
            g[2] += 1
            g[3].append(pid)
        rows = [(g[0], name, g[1], g[2], g[3]) for name, g in groups.items()]
        by_cpu = sorted(rows, key=lambda r: (r[0], r[2]), reverse=True)[:n]
        by_mem = sorted(rows, key=lambda r: r[2], reverse=True)[:n]
        self._top = (by_cpu, by_mem)
        return self._top

    # --- видеокарта NVIDIA ---
    GPU_QUERY = "name,utilization.gpu,temperature.gpu,memory.used,memory.total,power.draw,clocks.sm"

    @staticmethod
    def _num(s: str):
        try:
            return float(s)
        except ValueError:                                    # «[N/A]», «[Not Supported]»
            return None

    def _gpu_worker(self) -> None:
        try:
            out = subprocess.run(["nvidia-smi", f"--query-gpu={self.GPU_QUERY}", "--format=csv,noheader,nounits"],
                                 capture_output=True, text=True, timeout=4).stdout
            p = [x.strip() for x in out.strip().splitlines()[0].split(",")]      # первая видеокарта
            if len(p) != 7:
                raise ValueError(out)
            self._gpu = (p[0], *(self._num(x) for x in p[1:]))
        except (OSError, subprocess.SubprocessError, ValueError, IndexError):
            self._gpu = None
        finally:
            self._gpu_busy = False

    def gpu(self):
        """(имя, загрузка %, °C, память занято МиБ, всего МиБ, мощность Вт, частота МГц).
        nvidia-smi стартует по ~0.1 с, поэтому опрос идёт в фоне, а здесь отдаётся последний готовый ответ."""
        if self.has_nvidia and not self._gpu_busy:
            self._gpu_busy = True
            threading.Thread(target=self._gpu_worker, daemon=True).start()
        return self._gpu

    # --- система ---
    @staticmethod
    def uptime():
        try:
            with open("/proc/uptime") as f:
                return float(f.read().split()[0])
        except (OSError, ValueError, IndexError):
            return None

    @staticmethod
    def loadavg():
        try:
            return os.getloadavg()
        except OSError:
            return None


class Sparkline(QWidget):
    """График за последнюю минуту: одна или две линии. Шкала 0..fixed_max или подстраивается под максимум."""
    SERIES = ("accent", "#3ddc97")

    def __init__(self, series: int = 1, fixed_max: float | None = 100.0, floor: float = 1.0, n: int = 60):
        super().__init__()
        self.hist = [deque([0.0] * n, maxlen=n) for _ in range(series)]
        self.fixed_max, self.floor = fixed_max, floor
        self.setMinimumHeight(68)

    def push(self, *vals: float) -> None:
        for h, v in zip(self.hist, vals):
            h.append(max(0.0, float(v)))
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        p.setPen(QPen(QColor(BORDER), 1))
        p.setBrush(QColor(CONTROL))
        p.drawRoundedRect(r, 8, 8)
        clip = QPainterPath()
        clip.addRoundedRect(r, 8, 8)
        p.setClipPath(clip)
        p.setPen(QPen(QColor(BORDER), 1, Qt.PenStyle.DotLine))
        for k in (1, 2, 3):                                   # сетка 25 / 50 / 75 %
            y = r.top() + r.height() * k / 4
            p.drawLine(QPointF(r.left(), y), QPointF(r.right(), y))
        top = self.fixed_max or max(self.floor, max(max(h) for h in self.hist) * 1.2)
        n = len(self.hist[0])
        step, pad = r.width() / (n - 1), 4
        for h, col in reversed(list(zip(self.hist, self.SERIES))):      # первая линия рисуется поверх второй
            c = QColor(ACCENT if col == "accent" else col)
            pts = [QPointF(r.left() + i * step, r.bottom() - pad - min(v / top, 1.0) * (r.height() - 2 * pad))
                   for i, v in enumerate(h)]
            area = QPainterPath(QPointF(r.left(), r.bottom()))
            for pt in pts:
                area.lineTo(pt)
            area.lineTo(r.right(), r.bottom())
            area.closeSubpath()
            g = QLinearGradient(0, r.top(), 0, r.bottom())
            c1, c0 = QColor(c), QColor(c)
            c1.setAlpha(90)
            c0.setAlpha(0)
            g.setColorAt(0, c1)
            g.setColorAt(1, c0)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QBrush(g))
            p.drawPath(area)
            line = QPainterPath(pts[0])
            for pt in pts[1:]:
                line.lineTo(pt)
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(c, 1.8, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
            p.drawPath(line)


class UsageBar(QWidget):
    """Полоска заполнения: синяя, при 75% жёлтая, при 90% красная."""

    def __init__(self):
        super().__init__()
        self.frac = 0.0
        self.setFixedHeight(8)

    def set_frac(self, f: float) -> None:
        self.frac = max(0.0, min(1.0, f))
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect())
        rad = r.height() / 2
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(CONTROL))
        p.drawRoundedRect(r, rad, rad)
        if self.frac > 0:
            col = ACCENT if self.frac < 0.75 else "#f5a524" if self.frac < 0.9 else "#ff5c5c"
            p.setBrush(QColor(col))
            p.drawRoundedRect(QRectF(r.left(), r.top(), max(r.width() * self.frac, r.height()), r.height()), rad, rad)


class MeterRow(QWidget):
    """Подпись слева, значение справа, под ними полоска заполнения."""

    def __init__(self, title: str):
        super().__init__()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(6)
        top = QHBoxLayout()
        top.setSpacing(12)
        self.value = QLabel("—")
        self.value.setObjectName("value")
        top.addWidget(QLabel(title), 1)
        top.addWidget(self.value)
        self.bar = UsageBar()
        lay.addLayout(top)
        lay.addWidget(self.bar)

    def set(self, frac: float, text: str) -> None:
        self.bar.set_frac(frac)
        self.value.setText(text)


class ProcRow(QWidget):
    """Одна строка списка процессов: имя слева, нагрузка и память справа. Клик выбирает строку."""
    clicked = pyqtSignal()

    def __init__(self):
        super().__init__()
        self.selected = False
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 8, 0, 8)
        lay.setSpacing(12)
        self.name = QLabel("—")
        self.stat = QLabel("")
        self.stat.setObjectName("value")
        self.stat.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        lay.addWidget(self.name, 1)
        lay.addWidget(self.stat)

    def set(self, name: str, stat: str, warn: bool = False) -> None:
        self.name.setText(name)
        self.stat.setText(stat)
        self.stat.setStyleSheet("color: #ff6b6b;" if warn else "")
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()

    def paintEvent(self, ev):
        if self.selected:                                     # выбранная строка: мягкая плашка цвета акцента
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            c = QColor(ACCENT)
            c.setAlpha(34)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(c)
            p.drawRoundedRect(QRectF(self.rect()).adjusted(0, 2, 0, -2), 6, 6)
        super().paintEvent(ev)


class MonitorPanel(QObject):
    """Вкладка «Мониторинг»: карточки с живыми данными. Обновляется раз в секунду, но только пока вкладка открыта."""
    INTERVAL_MS = 1000

    def __init__(self):
        super().__init__()
        self.stats = SysStats()
        self._failed = False
        self.timer = QTimer(self)
        self.timer.setInterval(self.INTERVAL_MS)
        self.timer.timeout.connect(self.tick)
        self._build()

    @staticmethod
    def _val(text: str = "—") -> QLabel:
        lab = QLabel(text)
        lab.setObjectName("value")
        lab.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        lab.row_width = 130                                   # уже обычных 180: колонки не должны быть шире окна
        return lab

    def _build(self) -> None:
        s = self.stats
        cpu = Card("Процессор", "cpu")
        self.cpu_graph = Sparkline()
        self.cpu_load, self.cpu_freq, self.cpu_temp = self._val(), self._val(), self._val()
        cpu.wide(self.cpu_graph)
        cpu.row("Загрузка", self.cpu_load, "график за последнюю минуту")
        cpu.row("Частота", self.cpu_freq)
        cpu.row("Температура", self.cpu_temp)
        self.cpu_power = self._val()
        self.power_btn = QPushButton("Разрешить" if shutil.which("pkexec") else "Копировать команду")
        self.power_btn.setObjectName("pickbtn")
        self.power_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.power_btn.setToolTip("Счётчик энергии закрыт для чтения. Кнопка попросит пароль администратора "
                                  "и откроет его до перезагрузки.")
        self.power_btn.clicked.connect(self.grant_power)
        self.power_btn.hide()
        self._grant_busy = False
        holder = QWidget()                                    # на месте значения: либо цифра, либо кнопка «Разрешить»
        hl = QHBoxLayout(holder)
        hl.setContentsMargins(0, 0, 0, 0)
        hl.setSpacing(0)
        hl.addStretch(1)
        hl.addWidget(self.power_btn)
        hl.addWidget(self.cpu_power)
        holder.row_width = 130
        cpu.row("Энергопотребление", holder)

        self.gpu_card = None
        if s.has_nvidia:                                      # без nvidia-smi карточки нет
            gpu = Card("Видеокарта", "cpu")
            self.gpu_graph = Sparkline()
            self.gpu_load, self.gpu_temp, self.gpu_power, self.gpu_clock = (self._val() for _ in range(4))
            self.gpu_vram = MeterRow("Видеопамять")
            gpu.wide(self.gpu_graph)
            gpu.row("Загрузка", self.gpu_load)
            gpu.row("Температура", self.gpu_temp)
            gpu.row("Энергопотребление", self.gpu_power)
            gpu.row("Частота", self.gpu_clock)
            gpu.body.addWidget(hline("rowsep"))
            gpu.wide(self.gpu_vram)
            self.gpu_card = gpu

        mem = Card("Память", "server")
        self.ram, self.swap = MeterRow("Оперативная память"), MeterRow("Файл подкачки")
        mem.wide(self.ram)
        mem.body.addWidget(hline("rowsep"))
        mem.wide(self.swap)

        disk = Card("Диск", "server")
        self.disk = MeterRow("Системный раздел")
        self.disk_r, self.disk_w = self._val(), self._val()
        disk.wide(self.disk)
        disk.row("Чтение", self.disk_r)
        disk.row("Запись", self.disk_w)

        net = Card("Сеть", "globe")
        self.net_graph = Sparkline(series=2, fixed_max=None, floor=64 * 1024)
        self.net_rx, self.net_tx = self._val(), self._val()
        net.wide(self.net_graph)
        net.row("Приём", self.net_rx, "акцентная линия на графике")
        net.row("Передача", self.net_tx, "зелёная линия")

        top = Card("Топ процессов", "terminal")
        self.procs = [ProcRow() for _ in range(8)]
        self.sel_name = None                                  # выбранная группа (по имени: список пересортировывается)
        self._confirm = None                                  # (имя, до какого момента ждём второй Delete)
        self._notice = None                                   # (имя, текст, до какого момента показывать)
        self._row_groups: list = []
        for k, pr in enumerate(self.procs):
            pr.clicked.connect(lambda k=k: self.select_row(k))
            pr.setToolTip("Клик: выбрать процесс. Delete два раза: закрыть его (если у процесса несколько "
                          "копий, закроются все).")
            if k:
                top.body.addWidget(hline("rowsep"))
            top.body.addWidget(pr)
        self.top_mode = 0                                     # 0: по процессору, 1: по памяти
        self._tops = ([], [], 0)
        seg = QWidget()                                       # переключатель «ЦП | ОЗУ» справа от заголовка
        sl = QHBoxLayout(seg)
        sl.setContentsMargins(0, 0, 0, 0)
        sl.setSpacing(4)
        self.seg_group = QButtonGroup(seg)
        for k, text in enumerate(("ЦП", "ОЗУ")):
            b = QPushButton(text)
            b.setObjectName("seg")
            b.setCheckable(True)
            b.setChecked(k == 0)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            self.seg_group.addButton(b, k)
            sl.addWidget(b)
        self.seg_group.idClicked.connect(self.set_top_mode)
        top.title_right(seg)

        sysc = Card("Система", "info")
        self.uptime, self.load, self.nproc = self._val(), self._val(), self._val()
        sysc.row("Время работы", self.uptime)
        sysc.row("Нагрузка", self.load, "за 1 / 5 / 15 минут")
        sysc.row("Процессов", self.nproc)

        self._left = [cpu] + ([self.gpu_card] if self.gpu_card else []) + [mem]
        self._right = [net, disk, top, sysc]

    def set_top_mode(self, mode: int) -> None:
        """Клик по «ЦП» / «ОЗУ»: тот же список, но отсортированный по другому. Показываем сразу, не ждём замера."""
        self.top_mode = mode
        self._confirm = None
        self._render_top()

    def select_row(self, k: int) -> None:
        grp = self._row_groups[k] if k < len(self._row_groups) else None
        name = grp[0] if grp else None
        self.sel_name = None if name == self.sel_name else name     # повторный клик снимает выбор
        self._confirm = None
        self._page.setFocus()
        self._render_top()

    def delete_pressed(self) -> None:
        """Delete: первый раз просит подтверждение прямо в строке, второй (в течение 4 секунд) закрывает процесс."""
        grp = next((g for g in self._row_groups if g and g[0] == self.sel_name), None)
        if grp is None:
            return
        name, pids = grp
        now = time.monotonic()
        if not (self._confirm and self._confirm[0] == name and now <= self._confirm[1]):
            self._confirm = (name, now + 4.0)
        else:
            self._confirm = None
            self._notice = (name, self._terminate(name, pids), now + 3.0)
        self._render_top()

    @staticmethod
    def _terminate(name: str, pids: list) -> str:
        """Вежливо закрывает (SIGTERM) все процессы группы. Возвращает короткий итог для строки."""
        sent = denied = 0
        own = os.getpid()
        for pid in pids:
            if int(pid) == own:                               # себя не закрываем
                continue
            try:
                with open(f"/proc/{pid}/stat") as f:
                    data = f.read()
                if data[data.find("(") + 1:data.rfind(")")] != name:    # pid успел достаться другому процессу
                    continue
                os.kill(int(pid), signal.SIGTERM)
                sent += 1
            except PermissionError:
                denied += 1
            except (OSError, ValueError):
                pass
        if sent:
            return "закрыто"
        if denied:
            return "нет прав"
        return "это Мими" if str(own) in map(str, pids) else "не найден"

    def _render_top(self) -> None:
        by_cpu, by_mem, total = self._tops
        rows = by_mem if self.top_mode else by_cpu
        now = time.monotonic()
        if self._confirm and now > self._confirm[1]:
            self._confirm = None
        if self._notice and now > self._notice[2]:
            self._notice = None
        self._row_groups = []
        for k, pr in enumerate(self.procs):
            if k >= len(rows):
                pr.selected = False
                pr.set("—", "")
                self._row_groups.append(None)
                continue
            pct, name, rss, cnt, pids = rows[k]
            self._row_groups.append((name, pids))
            label = f"{name} ×{cnt}" if cnt > 1 else name
            if self.top_mode:
                stat = f"{fmt_size(rss)}" + (f"  ·  {rss / total:.1%}" if total else "")
            else:
                stat = f"{pct:.1f}%  ·  {fmt_size(rss)}"
            warn = False
            pr.selected = name == self.sel_name
            if pr.selected:
                if self._confirm and self._confirm[0] == name:
                    stat, warn = T("Delete ещё раз"), True
                elif self._notice and self._notice[0] == name:
                    stat = T(self._notice[1])
            pr.set(label, stat, warn)

    def grant_power(self) -> None:
        """Кнопка «Разрешить»: pkexec спросит пароль, дальше цифра появится сама (следующий замер)."""
        if self._grant_busy:
            return
        files = self.stats.rapl_files()
        if not shutil.which("pkexec"):                        # нет графического запроса пароля: даём готовую команду
            QApplication.clipboard().setText("sudo chmod a+r " + " ".join(files))
            self.power_btn.setText(T("Скопировано ✓"))
            return
        self._grant_busy = True
        self.power_btn.setEnabled(False)

        def work() -> None:
            try:
                self.stats.grant_rapl()
            finally:
                self._grant_busy = False
        threading.Thread(target=work, daemon=True).start()

    def cards(self) -> tuple[list, list]:
        return self._left, self._right

    def attach(self, page: QWidget) -> None:
        """Обновление идёт, пока страница на экране: открыли вкладку — запустилось, ушли — остановилось."""
        self.setParent(page)
        self._page = page
        page.setFocusPolicy(Qt.FocusPolicy.ClickFocus)        # клавиша Delete приходит странице после клика по строке
        page.installEventFilter(self)

    def eventFilter(self, obj, ev):
        t = ev.type()
        if t == QEvent.Type.Show and not self.timer.isActive():
            self.stats.reset()
            self.timer.start()
            QTimer.singleShot(350, lambda: self.timer.isActive() and self.tick())    # первые цифры почти сразу
        elif t == QEvent.Type.Hide:
            self.timer.stop()
        elif t == QEvent.Type.KeyPress and ev.key() == Qt.Key.Key_Delete:
            self.delete_pressed()
            return True
        return False

    def tick(self) -> None:
        try:
            self._update()
        except Exception:                                     # мониторинг не должен ронять окно настроек
            if not self._failed:
                self._failed = True
                traceback.print_exc()

    def _update(self) -> None:
        s, dash = self.stats, "—"
        load = s.cpu_percent()
        if load is not None:
            self.cpu_graph.push(load)
            self.cpu_load.setText(f"{load:.0f}%")
        pw = s.cpu_power()
        self.cpu_power.setText(dash if pw is None else "" if pw is False else f"{pw:.1f} {T('Вт')}")
        self.cpu_power.setVisible(pw is not False)
        self.power_btn.setVisible(pw is False)               # нет доступа: вместо цифры кнопка
        self.power_btn.setEnabled(not self._grant_busy)
        freq, temp = s.cpu_freq(), s.cpu_temp()
        self.cpu_freq.setText(f"{freq:.2f} {T('ГГц')}" if freq else dash)
        self.cpu_temp.setText(f"{temp:.0f} °C" if temp is not None else dash)

        if self.gpu_card is not None:
            g = s.gpu()
            if g:
                _, gl, gt, vu, vt, pw, clk = g
                if gl is not None:
                    self.gpu_graph.push(gl)
                self.gpu_load.setText(f"{gl:.0f}%" if gl is not None else dash)
                self.gpu_temp.setText(f"{gt:.0f} °C" if gt is not None else dash)
                self.gpu_power.setText(f"{pw:.0f} {T('Вт')}" if pw is not None else dash)
                self.gpu_clock.setText(f"{clk:.0f} {T('МГц')}" if clk is not None else dash)
                if vu is not None and vt:
                    self.gpu_vram.set(vu / vt, f"{fmt_size(vu * 1048576)} / {fmt_size(vt * 1048576)}")

        mem = s.memory()
        if mem:
            total, used, swap, swap_used = mem
            self.ram.set(used / total, f"{fmt_size(used)} / {fmt_size(total)}")
            if swap:
                self.swap.set(swap_used / swap, f"{fmt_size(swap_used)} / {fmt_size(swap)}")
            else:
                self.swap.set(0, T("отключён"))
        du = s.disk_usage()
        if du:
            self.disk.set(du[1] / du[0], f"{fmt_size(du[1])} / {fmt_size(du[0])}")
        io = s.disk_io()
        if io:
            self.disk_r.setText(fmt_rate(io[0]))
            self.disk_w.setText(fmt_rate(io[1]))

        net = s.net_io()
        if net:
            self.net_graph.push(*net)
            self.net_rx.setText(fmt_rate(net[0]))
            self.net_tx.setText(fmt_rate(net[1]))

        by_cpu, by_mem = s.top_procs(len(self.procs))
        self._tops = (by_cpu, by_mem, mem[0] if mem else 0)
        self._render_top()

        up, la = s.uptime(), s.loadavg()
        self.uptime.setText(fmt_uptime(up) if up is not None else dash)
        self.load.setText(" / ".join(f"{x:.2f}" for x in la) if la else dash)
        self.nproc.setText(str(s.nprocs) if s.nprocs else dash)


# ---------- форма ввода API ----------
# ---------- режим разработчика: консоль с логом и ошибками ----------
LOG_BUFFER: deque = deque(maxlen=3000)   # (строка, это ошибка?) — чтобы консоль при открытии показала всё, что было
_log_lock = threading.Lock()
LOG_BUS = None                           # появляется в install_log_capture()


class LogBus(QObject):
    """Мост между потоками: print из любого потока приходит в консоль через сигнал Qt."""
    line = pyqtSignal(str, bool)


class LogTee:
    """Подменяет sys.stdout / sys.stderr: пишет туда же, куда раньше, и копирует строки в консоль."""

    def __init__(self, orig, is_err: bool):
        self._orig, self._err, self._part = orig, is_err, ""

    def write(self, s):
        if self._orig is not None:
            try:
                self._orig.write(s)
            except Exception:
                pass
        if isinstance(s, bytes):
            s = s.decode("utf-8", "replace")
        with _log_lock:
            *lines, self._part = (self._part + s).split("\n")
        for ln in lines:
            ln = ln.rsplit("\r", 1)[-1]
            LOG_BUFFER.append((ln, self._err))
            if LOG_BUS is not None:
                LOG_BUS.line.emit(ln, self._err)
        return len(s)

    def flush(self):
        try:
            if self._orig is not None:
                self._orig.flush()
        except Exception:
            pass

    def __getattr__(self, name):          # isatty, fileno, encoding и прочее — как у настоящего потока
        return getattr(self._orig, name)


def install_log_capture() -> None:
    """Перехватывает вывод и ошибки: из основного потока, из потоков и сообщения самого Qt."""
    global LOG_BUS
    LOG_BUS = LogBus()
    if not isinstance(sys.stdout, LogTee):
        sys.stdout = LogTee(sys.stdout, False)
        sys.stderr = LogTee(sys.stderr, True)

    def on_exception(exc_type, exc, tb):
        if issubclass(exc_type, KeyboardInterrupt):
            sys.__excepthook__(exc_type, exc, tb)
            return
        print("Необработанная ошибка:", file=sys.stderr)
        traceback.print_exception(exc_type, exc, tb)   # без этого PyQt6 молча роняет программу

    def on_thread_exception(args):
        name = args.thread.name if args.thread else "?"
        print(f"Ошибка в потоке {name}:", file=sys.stderr)
        traceback.print_exception(args.exc_type, args.exc_value, args.exc_traceback)

    def on_qt_message(mode, ctx, msg):
        if mode in (QtMsgType.QtCriticalMsg, QtMsgType.QtFatalMsg):
            print("Qt: " + msg, file=sys.stderr)
        else:
            print(("Qt (предупреждение): " if mode == QtMsgType.QtWarningMsg else "Qt: ") + msg)

    sys.excepthook = on_exception
    threading.excepthook = on_thread_exception
    qInstallMessageHandler(on_qt_message)


class DevConsole(QWidget):
    """Вкладка «Журнал» в окне настроек: весь вывод программы, ошибки красным, фильтр «только ошибки».
    Вкладка видна, только пока включён режим разработчика."""
    MAX = 5000

    def __init__(self, embedded: bool = True, auto: bool = False):
        """embedded=True: вкладка в настройках (с заголовком и кнопкой «Открыть консоль»);
        False: содержимое отдельного окна консоли."""
        super().__init__()
        self.lines: list[tuple[str, bool]] = []
        self.errors, self.only_err = 0, False
        lay = QVBoxLayout(self)
        if embedded:
            lay.setContentsMargins(26, 20, 26, 14)
            lay.setSpacing(3)
            h = QLabel("Журнал")
            h.setObjectName("h1")
            hint = QLabel("Вывод программы и ошибки")
            hint.setObjectName("muted")
            lay.addWidget(h)
            lay.addWidget(hint)
            lay.addSpacing(11)
        else:
            lay.setContentsMargins(14, 12, 14, 14)
            lay.setSpacing(3)
        self.auto = Toggle("Запускать вместе с Мими")      # читает окно настроек при сохранении
        self.auto.setChecked(auto)
        if embedded:
            win_row = QHBoxLayout()
            win_row.setSpacing(10)
            b_open = QPushButton("Открыть консоль")
            b_open.setStyleSheet("padding: 6px 14px; font-size: 12px;")
            b_open.setCursor(Qt.CursorShape.PointingHandCursor)
            b_open.clicked.connect(open_dev_window)
            win_row.addWidget(b_open)
            win_row.addStretch(1)
            lay.addLayout(win_row)
            lay.addSpacing(8)

        top = QHBoxLayout()
        top.setSpacing(10)
        self.count = QLabel()
        self.count.setObjectName("muted")
        self.only = Toggle("Только ошибки")
        self.only.toggled.connect(self.set_only_errors)
        btn_style = "padding: 6px 14px; font-size: 12px;"
        b_copy, b_clear = QPushButton("Копировать"), QPushButton("Очистить")
        for b in (b_copy, b_clear):
            b.setStyleSheet(btn_style)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
        self.b_copy = b_copy
        b_copy.clicked.connect(self.copy_log)
        b_clear.clicked.connect(self.clear_log)
        top.addWidget(self.count)
        top.addStretch(1)
        top.addWidget(self.only)
        if embedded:                                  # справа от «Только ошибки»
            top.addWidget(self.auto)
        top.addWidget(b_copy)
        top.addWidget(b_clear)
        lay.addLayout(top)
        self.view = QPlainTextEdit()
        self.view.setReadOnly(True)
        self.view.setLineWrapMode(QPlainTextEdit.LineWrapMode.WidgetWidth)   # длинные строки переносятся, горизонтальной полосы нет
        self.view.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.view.setMaximumBlockCount(self.MAX)
        f = QFont()
        f.setFamilies(["JetBrains Mono", "Fira Code", "DejaVu Sans Mono", "monospace"])
        f.setStyleHint(QFont.StyleHint.Monospace)
        f.setPixelSize(12)
        self.view.setFont(f)
        self.view.setStyleSheet("padding: 6px;")      # фон и рамка общие, полупрозрачные: сквозь лог виден размытый фон
        lay.addWidget(self.view, 1)
        self.update_count()
        for text, err in list(LOG_BUFFER):       # что было до открытия окна настроек
            self.add_line(text, err)
        if LOG_BUS is not None:
            LOG_BUS.line.connect(self.add_line)

    def copy_log(self) -> None:
        """Копирует выделенное, а если ничего не выделено, то весь лог."""
        cur = self.view.textCursor()
        text = cur.selection().toPlainText() if cur.hasSelection() else self.view.toPlainText()
        QApplication.clipboard().setText(text)
        self.b_copy.setText(T("Скопировано ✓"))
        QTimer.singleShot(1200, lambda: self.b_copy.setText(T("Копировать")))

    @staticmethod
    def color(text: str, err: bool) -> str:
        if err:
            return "#ff6b6b"
        if "⏱" in text:
            return "#7fb2ff"
        if text.startswith(("Команда:", "Запущено")):
            return "#f0c674"
        if text.startswith("Помощник:"):
            return "#9be7b0"
        if text.startswith("Qt (предупреждение)"):
            return "#c9a45c"
        return "#b8bdcc"

    def put(self, text: str, err: bool) -> None:
        sb = self.view.verticalScrollBar()
        follow = sb.value() >= sb.maximum() - 4          # если не листали вверх, прокручиваем за новыми строками
        fmt = QTextCharFormat()
        fmt.setForeground(QColor(self.color(text, err)))
        cur = self.view.textCursor()
        cur.movePosition(QTextCursor.MoveOperation.End)
        cur.insertText(text + "\n", fmt)
        if follow:
            sb.setValue(sb.maximum())

    def add_line(self, text: str, err: bool) -> None:
        self.lines.append((text, err))
        if len(self.lines) > self.MAX:
            del self.lines[:len(self.lines) - self.MAX]
        if err:
            self.errors += 1
            self.update_count()
        if err or not self.only_err:
            self.put(text, err)

    def update_count(self) -> None:
        self.count.setText(f"{T('строк с ошибками')}: {self.errors}")

    def set_only_errors(self, on: bool) -> None:
        self.only_err = on
        self.view.clear()
        for text, err in self.lines:
            if err or not on:
                self.put(text, err)

    def clear_log(self) -> None:
        self.view.clear()
        self.lines.clear()
        LOG_BUFFER.clear()
        self.errors = 0
        self.update_count()


class DevWindow(QWidget):
    """Отдельное окно консоли (обычное окно, не поверх остальных). Крестик прячет его, а не закрывает Мими."""

    def __init__(self):
        super().__init__(None, Qt.WindowType.Window | Qt.WindowType.FramelessWindowHint)
        self.setWindowTitle("Консоль разработчика — Мими")
        self.resize(800, 440)
        self.setMinimumSize(520, 280)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)
        bar = TopBar()
        bar.setObjectName("devbar")
        bar.setFixedHeight(42)
        bl = QHBoxLayout(bar)
        bl.setContentsMargins(16, 0, 10, 0)
        bl.setSpacing(10)
        title = QLabel("Консоль разработчика — Мими")
        title.setStyleSheet(f"color: {STRONG}; font-size: 13px; font-weight: 600;")
        bl.addWidget(title)
        bl.addStretch(1)
        for icon, slot in (("chev_down", self.showMinimized), ("close", self.hide)):
            b = QPushButton()
            b.setObjectName("winbtn")
            b.setFlat(True)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setIcon(QIcon(draw_icon(icon, "#7f8594", 14)))
            b.setIconSize(QSize(14, 14))
            b.setFixedSize(28, 28)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.clicked.connect(slot)
            bl.addWidget(b)
        outer.addWidget(bar)
        outer.addWidget(hline("sep"))
        self.console = DevConsole(embedded=False)
        outer.addWidget(self.console, 1)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setPen(QPen(QColor(BORDER), 1))
        p.setBrush(QColor(BG))
        p.drawRect(self.rect().adjusted(0, 0, -1, -1))


DEV_WINDOW = None


def open_dev_window() -> None:
    """Открывает отдельную консоль (одну на всю программу)."""
    global DEV_WINDOW
    if DEV_WINDOW is None:
        DEV_WINDOW = DevWindow()
    DEV_WINDOW.show()
    DEV_WINDOW.raise_()
    DEV_WINDOW.activateWindow()


def close_dev_window() -> None:
    if DEV_WINDOW is not None:
        DEV_WINDOW.hide()


DEV_MODE = False                         # режим разработчика: в окне настроек появляется вкладка «Журнал»


def dev_is_on() -> bool:
    return DEV_MODE


def set_dev_mode(on: bool) -> None:
    """Включает или выключает режим разработчика: открытые окна настроек показывают или прячут вкладку «Журнал»."""
    global DEV_MODE
    on = bool(on)
    changed = on != DEV_MODE
    DEV_MODE = on
    if not on:
        close_dev_window()
    app = QApplication.instance()
    if app is not None:
        for w in app.topLevelWidgets():
            if isinstance(w, SettingsDialog):
                w.sync_dev_tab()
    if on and changed:
        print("Режим разработчика включён: логи и ошибки смотри во вкладке «Журнал» в настройках")


SCALES = [("50%", 0.5), ("75%", 0.75), ("Авто", 1.0), ("125%", 1.25)]
SAFE_MODES = [("Авто", "auto"), ("Всегда спрашивать", "always")]
LANGS = [("Русский", "ru"), ("English", "en")]
# размер окна настроек: процент от базового 980x620 («Авто» = 100%)
WIN_SCALES = [("150%", 1.5), ("125%", 1.25), ("100%", 1.0), ("75%", 0.75), ("50%", 0.5), ("Авто", "auto")]


class LinkLabel(QLabel):
    """Подпись-ссылка: реагирует на клик."""
    clicked = pyqtSignal()

    def __init__(self, text: str):
        super().__init__(text)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()


# ---------- язык интерфейса: русский / английский ----------
LANG = "ru"
EN = {
    # боковая панель и заголовки страниц
    "ОСНОВНОЕ": "MAIN", "ПЕРСОНАЖ": "CHARACTER", "СИСТЕМА": "SYSTEM",
    "Сервис": "Service", "Голос": "Voice", "Характер": "Character", "Команды": "Commands",
    "Настройки": "Settings", "Помощник — настройка": "Assistant — settings",
    "голосовой помощник": "voice assistant", "● в сети": "● online", "в сети": "online",
    "Куда отправлять запросы и чем ты авторизуешься": "Where requests go and how you authenticate",
    "Как Мими говорит и как слушает тебя": "How Mimi speaks and how she listens to you",
    "Кто она и как с тобой общается": "Who she is and how she talks to you",
    "Что помощнику разрешено делать на компьютере": "What the assistant may do on your computer",
    # карточки и строки
    "Подключение": "Connection", "готовые настройки провайдера": "ready-made provider presets",
    "API-ключ": "API key", "Хранение": "Storage", "Запомнить ключ": "Remember key",
    "сохранить в data/config.json": "save to data/config.json", "Модель": "Model",
    "имя модели у сервиса": "model name at the provider",
    "выбери из списка или впиши своё": "pick from the list or type your own",
    "Загрузка списка…": "Loading list…", "↻ Обновить список": "↻ Refresh list",
    "Не удалось загрузить список: повторить": "Couldn't load the list: retry", "Адрес API": "API address",
    "можно свой или локальный": "custom or local is fine", "Синтез речи": "Speech synthesis",
    "чем Мими разговаривает": "what Mimi talks with", "Параметры Silero": "Silero settings",
    "Диктор": "Speaker", "Тон": "Pitch", "Скорость": "Speed", "Распознавание": "Recognition",
    "цвета превью берутся из самой темы; правый клик по сохранённой: удалить":
        "preview colors come from the theme itself; right-click a saved one to delete it",
    "По умолчанию": "Default", "Свои цвета": "Custom colors",
    "листай колёсиком мыши; правый клик по своей: удалить": "scroll with the mouse wheel; right-click your own to delete",
    "Неон": "Neon", "Закат": "Sunset", "Океан": "Ocean", "Мята": "Mint", "Золото": "Gold", "Сакура": "Sakura",
    "Лаванда": "Lavender", "Стеклянные плашки": "Glass cards",
    "полупрозрачные карточки с бликом и кромкой": "translucent cards with a sheen and a rim",
    "Плотность": "Density", "меньше процент: сквозь стекло виднее фон": "lower: the background shows through more",
    "Матовость": "Frost", "размытие фона под плашкой (нужна картинка)": "blur of what is behind the card (needs a picture)",
    "Преломление": "Refraction", "искажение у краёв, как у линзы (нужна картинка)": "lens-like warp at the edges (needs a picture)",
    "Свечение фона": "Background glow", "без картинки: цветные пятна, сквозь которые видно стекло":
        "without a picture: colored blobs the glass looks through",
    "Блик": "Sheen", "свет на поверхности стекла": "light on the glass surface", "Кромка": "Rim",
    "светлый край и внутренняя линия": "bright edge and inner line",
    "Распознавание речи": "Speech recognition", "как Мими слышит тебя": "how Mimi hears you",
    "Промт": "Prompt", "Пресет": "Preset", "сохранённые варианты характера": "saved character variants",
    "Сохранить пресет": "Save preset", "Имя пресета": "Preset name", "под этим именем сохранится/экспортируется": "used when saving/exporting",
    "Импорт": "Import", "Экспорт": "Export", "Удалить": "Delete", "Загрузить": "Load",
    "Так её зовут в ответах: Мими.\nПромт слева задаёт характер и обращение.":
        "This is how she names herself in replies: Мими.\nThe prompt on the left sets her character and how she addresses you.",
    "Отрисовка": "Rendering", "Как показывать Мими": "How to show Mimi",
    "Как Мими выглядит на экране": "How Mimi looks on screen",
    "GIF и 3D-модель оживают, пока она говорит": "GIF and the 3D model animate only while she speaks",
    "3D-модель: фигура в полный рост": "3D model: full-body figure",
    "3D-модель": "3D model", "Модель персонажа": "Character model",
    "Анимация": "Animation", "Подожди немного: Мими загружается": "Please wait: Mimi is loading",
    "кивает, пока говорит, и наклоняет голову, пока думает": "nods while speaking, tilts her head while thinking",
    "выбранная модель видна и во вкладке «Характер»": "the chosen model is also shown on the Character tab", "нет файлов .glb": "no .glb files",
    "Управление ПК": "PC control", "Выполнять команды": "Run commands",
    "закрыть окно, громкость и т.п.": "close a window, volume, etc.", "Важно": "Important",
    "Команды подбираются под твою систему. Включай, только если доверяешь модели.":
        "Commands are chosen for your system. Turn on only if you trust the model.",
    "Окружение": "Environment", "Система": "System", "Сессия": "Session",
    "Мониторинг": "Monitoring", "Состояние компьютера в реальном времени": "Computer status in real time",
    "Процессор": "Processor", "Загрузка": "Load", "график за последнюю минуту": "chart for the last minute",
    "Частота": "Frequency", "Температура": "Temperature",
    "Память": "Memory", "Оперативная память": "RAM", "Файл подкачки": "Swap file", "отключён": "disabled",
    "Диск": "Disk", "Системный раздел": "System partition", "Чтение": "Read", "Запись": "Write",
    "Сеть": "Network", "Приём": "Download", "Передача": "Upload",
    "акцентная линия на графике": "accent-colored line on the chart", "зелёная линия": "green line",
    "Топ процессов": "Top processes", "ЦП": "CPU", "ОЗУ": "RAM",
    "Delete ещё раз": "Press Delete again", "закрыто": "closed", "нет прав": "no permission",
    "не найден": "not found", "это Мими": "this is Mimi",
    "Клик: выбрать процесс. Delete два раза: закрыть его (если у процесса несколько копий, закроются все).":
        "Click to select a process. Press Delete twice to close it (all copies if it has several).", "Время работы": "Uptime",
    "Нагрузка": "Load average", "за 1 / 5 / 15 минут": "over 1 / 5 / 15 minutes", "Разрешить": "Allow", "Копировать команду": "Copy command",
    "Счётчик энергии закрыт для чтения. Кнопка попросит пароль администратора и откроет его до перезагрузки.":
        "The energy counter is not readable. The button asks for the administrator password and unlocks it until reboot.", "Процессов": "Processes",
    "Видеокарта": "Graphics card", "Видеопамять": "Video memory", "Энергопотребление": "Power draw",
    "Вт": "W", "МГц": "MHz",
    "Б": "B", "КБ": "KB", "МБ": "MB", "ГБ": "GB", "ТБ": "TB", "/с": "/s", "ГГц": "GHz",
    "д": "d", "ч": "h", "мин": "min",
    "Показать ключ": "Show key", "Скрыть ключ": "Hide key", "Выбрать…": "Choose…",
    "по умолчанию: assets/character.gif": "default: assets/character.gif",
    "Сохранить": "Save", "Отмена": "Cancel", "Начать разговор": "Start talking", "Версия": "Version", "Обновлено": "Updated",
    "РАЗРАБОТЧИК": "DEVELOPER", "Журнал": "Log", "Вывод программы и ошибки": "Program output and errors",
    "Только ошибки": "Errors only", "Копировать": "Copy", "Очистить": "Clear", "Скопировано ✓": "Copied ✓",
    "строк с ошибками": "error lines", "Открыть консоль": "Open console",
    "Запускать вместе с Мими": "Open with Mimi",
    "Заполните модель и адрес API": "Fill in the model and API address", "Введите API-ключ": "Enter the API key",
    # списки выбора
    "Silero: нейросеть, офлайн": "Silero: neural, offline",
    "Edge: голос Microsoft, нужен интернет": "Edge: Microsoft voice, needs internet",
    "espeak-ng: робот": "espeak-ng: robot voice",
    "xenia (женский)": "xenia (female)", "kseniya (женский)": "kseniya (female)", "baya (женский)": "baya (female)",
    "aidar (мужской)": "aidar (male)", "eugene (мужской)": "eugene (male)",
    "очень низкий": "very low", "низкий": "low", "средний": "medium", "высокий": "high", "очень высокий": "very high",
    "очень медленно": "very slow", "медленно": "slow", "средне": "medium", "быстро": "fast", "очень быстро": "very fast",
    "Статичная картинка": "Static image", "GIF: анимация, пока Мими говорит": "GIF: animates while Mimi speaks",
    "Whisper: точно, нужен ключ Groq или OpenAI": "Whisper: accurate, needs a Groq or OpenAI key",
    "Google: бесплатно, но хуже": "Google: free, but worse",
    # меню профиля
    "Открыть папку данных": "Open data folder", "Mimi Typh  ·  в сети": "Mimi Typh  ·  online",
    "Масштаб Мими": "Mimi scale", "Размер окна": "Window size", "Язык": "Language", "Стиль": "Style",
    "Безопасный режим": "Safe mode", "Сохранять историю": "Keep history", "Режим разработчика": "Developer mode",
    "О программе": "About", "Авто": "Auto", "Всегда": "Always", "Всегда спрашивать": "Always ask",
    "Солнце / луна: светлая и тёмная тема": "Sun / moon: light and dark theme",
    "Размер персонажа на рабочем столе. Применится после «Сохранить».":
        "Size of the character on the desktop. Applies after “Save”.",
    "Авто: знакомые команды выполняются сразу, незнакомые после «да». Всегда спрашивать: любая команда и запуск приложений только после «да».":
        "Auto: familiar commands run at once, unfamiliar ones after “yes”. Always ask: any command and launching apps only after “yes”.",
    "Язык интерфейса. Голос и распознавание остаются русскими.":
        "Interface language. Voice and speech recognition stay Russian.",
    "Применяется сразу, окно остаётся по центру. Авто: как 100%. "
    "Всё содержимое масштабируется вместе с окном.":
        "Applies immediately, the window stays centered. Auto: same as 100%. "
        "All content scales together with the window.",
}
EN_UP = {k.upper(): v.upper() for k, v in EN.items()}


def set_lang(code: str) -> None:
    global LANG
    LANG = code if code in ("ru", "en") else "ru"


def _lookup(s: str):
    """Английский вариант строки или None. Знаки и пробелы по краям («‹   », «…», отступы) сохраняет."""
    if not s:
        return None
    r = EN.get(s) or EN_UP.get(s)
    if r:
        return r
    lead, core, tail = re.match(r"^([^\w]*)(.*?)([^\w]*)$", s, re.S).groups()
    if core and (lead or tail):
        r = EN.get(core) or EN_UP.get(core)
        if r:
            return lead + r + tail
    return None


def T(s: str) -> str:
    """Строка интерфейса на текущем языке (в коде тексты русские: это и есть «исходник»)."""
    if LANG != "en" or not s:
        return s
    return _lookup(s) or s


def _retr(w, key: str, cur: str, setter) -> None:
    """Запоминает исходный русский текст в самом виджете и ставит перевод под текущий язык."""
    ru = getattr(w, key, None)
    if ru is None:
        if not _lookup(cur):
            return
        ru = cur
        setattr(w, key, ru)
    setter(T(ru))


def retranslate(root: QWidget, skip=()) -> None:
    """Переводит уже построенные виджеты под текущий LANG. Русский оригинал хранится в виджете,
    поэтому переключаться можно туда и обратно сколько угодно."""
    skipped = {id(w) for w in skip}
    for w in [root] + root.findChildren(QWidget):
        if id(w) in skipped:
            continue
        if isinstance(w, MenuRow):
            if not hasattr(w, "_ru_t"):
                w._ru_t, w._ru_v = w.title, w.value
            w.title, w.value = T(w._ru_t), T(w._ru_v)
            w.update()
        elif isinstance(w, NavButton):
            if not hasattr(w, "_ru_t"):
                w._ru_t = w.title
            w.title = T(w._ru_t)
            w.update()
        elif isinstance(w, StepSlider):
            w._show(w.slider.value())
        elif isinstance(w, QComboBox):
            if not hasattr(w, "_ru_items"):
                items = [w.itemText(k) for k in range(w.count())]
                w._ru_items = items if any(_lookup(t) for t in items) else None
            for k, t in enumerate(w._ru_items or []):
                w.setItemText(k, T(t))
        elif isinstance(w, (QLabel, QPushButton, QCheckBox)):
            if not isinstance(w.parent(), StepSlider):      # подпись ползунка ведёт сам ползунок
                _retr(w, "_ru_text", w.text(), w.setText)
        if isinstance(w, QLineEdit):
            _retr(w, "_ru_ph", w.placeholderText(), w.setPlaceholderText)
        _retr(w, "_ru_tip", w.toolTip(), w.setToolTip)


class ProfileFrame(QFrame):
    """Блок профиля внизу боковой панели: по клику открывает меню."""
    clicked = pyqtSignal()
    _k = 1.0                       # масштаб окна настроек

    def __init__(self):
        super().__init__()
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.arrow_slot = None      # пустой виджет-место под стрелку в раскладке
        self._arrow = None          # сама стрелка (QPixmap): рисуется здесь, а не отдельной подписью
        self._hover = False         # мышь над плашкой
        self._open = False          # меню профиля открыто: подсветка остаётся, пока оно не закроется

    def set_arrow_pixmap(self, pm: QPixmap) -> None:
        self._arrow = pm
        self.update()

    def set_open(self, on: bool) -> None:
        self._open = on
        if not on:
            self._hover = self.underMouse()     # меню закрылось: мышь может быть уже не над плашкой
        self.update()

    def enterEvent(self, e):
        self._hover = True
        self.update()
        super().enterEvent(e)

    def leaveEvent(self, e):
        self._hover = False
        self.update()
        super().leaveEvent(e)

    def paintEvent(self, e):
        if self._hover or self._open:     # одна подсветка на всю плашку, вместе со стрелкой
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(hover_solid()))
            p.drawRoundedRect(QRectF(self.rect()), 10 * self._k, 10 * self._k)
            p.end()
        if self._arrow is not None and self.arrow_slot is not None:
            r, dpr = self.arrow_slot.geometry(), self._arrow.devicePixelRatio()
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
            p.drawPixmap(int(r.x() + (r.width() - self._arrow.width() / dpr) / 2),
                         int(r.y() + (r.height() - self._arrow.height() / dpr) / 2), self._arrow)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()


class MenuRow(QWidget):
    """Строка меню: иконка, название, справа значение / цвет / стрелка / переключатель / галочка."""
    clicked = pyqtSignal()
    gear_clicked = pyqtSignal()      # клик по солнцу / луне: смена светлой и тёмной темы
    hovered = pyqtSignal()           # мышь зашла на строку (для списков вариантов, которые открываются при наведении)

    def __init__(self, icon, title: str, value: str = "", chevron: bool = True, swatch=None,
                 toggle=None, checked: bool = False, bold: bool = False, gear: bool = False, k: float = 1.0):
        super().__init__()
        self.k = k                       # масштаб окна настроек: меню растёт и уменьшается вместе с ним
        self.gear = gear
        self._gear_rect = QRectF()
        self.icon, self.title, self.value = icon, title, value
        self.chevron, self.swatch, self.toggle, self.checked, self.bold = chevron, swatch, toggle, checked, bold
        self.hover = False
        self.sticky = False              # подсветка остаётся, пока открыт список вариантов этой строки
        self.setFixedHeight(max(1, round(38 * k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        if toggle is not None:
            toggle.setParent(self)
            toggle._k = k
            toggle.resize(toggle.sizeHint())
            toggle.show()

    def resizeEvent(self, e):
        if self.toggle is not None:
            self.toggle.move(self.width() - self.toggle.width() - round(14 * self.k),
                             (self.height() - self.toggle.height()) // 2)

    def enterEvent(self, e):
        self.hover = True
        self.update()
        self.hovered.emit()

    def leaveEvent(self, e):
        self.hover = False
        self.update()

    def mousePressEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton:
            return
        if self.toggle is not None:
            self.toggle.toggle()
        elif self.gear and self._gear_rect.contains(e.position()):
            self.gear_clicked.emit()
        else:
            self.clicked.emit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        k = self.k
        if abs(k - 1.0) > 1e-6:          # рисуем в «базовых» размерах, масштаб применяет painter
            p.scale(k, k)
        w, h = self.width() / k, self.height() / k
        lit = self.hover or self.sticky
        if lit:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(*HOVER_OV, 14))
            p.drawRoundedRect(QRectF(4, 0, w - 8, h), 8, 8)
        col = STRONG if lit else TEXT
        x0 = 16
        if self.icon:
            p.drawPixmap(QPointF(16, (h - 18) / 2), draw_icon(self.icon, col, 18))
            x0 = 46
        f = self.font()
        f.setPixelSize(max(1, round(max(8, 13 * k) / k)))      # после масштаба шрифт не мельче 8px
        f.setWeight(QFont.Weight.DemiBold if self.bold else QFont.Weight.Medium)
        p.setFont(f)
        x = w - 16
        if self.chevron:
            pen = QPen(QColor(MUTED), 1.7)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            path = QPainterPath()
            path.moveTo(x - 5.5, h / 2 - 4.5)
            path.lineTo(x - 1, h / 2)
            path.lineTo(x - 5.5, h / 2 + 4.5)
            p.drawPath(path)
            x -= 16
        if self.checked:
            p.drawPixmap(QPointF(x - 16, (h - 16) / 2), draw_icon("check", ACCENT, 16))
            x -= 26
        if self.swatch:
            p.setPen(QPen(QColor(*HOVER_OV, 40), 1))
            p.setBrush(QColor(self.swatch))
            p.drawRoundedRect(QRectF(x - 18, (h - 18) / 2, 18, 18), 5, 5)
            x -= 28
            if self.gear:                                   # солнце (тёмная тема) / луна (светлая): клик меняет тему
                c = QPointF(x - 8, h / 2)
                self._gear_rect = QRectF(c.x() - 11, c.y() - 11, 22, 22)
                gp = QPen(QColor(STRONG if self.hover else MUTED), 1.5)
                gp.setCapStyle(Qt.PenCapStyle.RoundCap)
                if THEME_NAME == "dark":
                    p.setPen(gp)
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.drawEllipse(c, 3.2, 3.2)
                    for i in range(8):
                        a = i * math.pi / 4
                        p.drawLine(QPointF(c.x() + math.cos(a) * 5.2, c.y() + math.sin(a) * 5.2),
                                   QPointF(c.x() + math.cos(a) * 7.4, c.y() + math.sin(a) * 7.4))
                else:
                    moon = QPainterPath()
                    moon.addEllipse(c, 6.0, 6.0)
                    cut = QPainterPath()
                    cut.addEllipse(QPointF(c.x() + 3.2, c.y() - 2.4), 5.2, 5.2)
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(QColor(STRONG if self.hover else MUTED))
                    p.drawPath(moon.subtracted(cut))
                x -= 26
        if self.value:
            p.setPen(QColor(MUTED))
            p.drawText(QRectF(0, 0, x, h), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight, self.value)
        p.setPen(QColor(col))
        p.drawText(QRectF(x0, 0, max(0, x - x0 - 60 if self.value else x - x0), h),
                   Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, self.title)


class _SVArea(QWidget):
    """Квадрат насыщенности и яркости: слева направо от белого к цвету, сверху вниз до чёрного."""

    def __init__(self, pan: "ColorPickerPanel"):
        super().__init__()
        self.pan = pan
        self.k = pan.k
        self.setFixedHeight(max(1, round(150 * self.k)))
        self.setCursor(Qt.CursorShape.CrossCursor)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        clip = QPainterPath()
        k = self.k
        clip.addRoundedRect(QRectF(0, 0, w, h), 8 * k, 8 * k)
        p.setClipPath(clip)
        g = QLinearGradient(0, 0, w, 0)
        g.setColorAt(0, QColor(255, 255, 255))
        g.setColorAt(1, QColor.fromHsvF(self.pan.h, 1.0, 1.0))
        p.fillRect(QRectF(0, 0, w, h), g)
        g2 = QLinearGradient(0, 0, 0, h)
        g2.setColorAt(0, QColor(0, 0, 0, 0))
        g2.setColorAt(1, QColor(0, 0, 0, 255))
        p.fillRect(QRectF(0, 0, w, h), g2)
        p.setClipping(False)
        c = QPointF(self.pan.s * w, (1 - self.pan.v) * h)
        c.setX(min(max(c.x(), 7 * k), w - 7 * k))
        c.setY(min(max(c.y(), 7 * k), h - 7 * k))
        p.setPen(QPen(QColor(0, 0, 0, 120), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawEllipse(c, 7.5 * k, 7.5 * k)
        p.setPen(QPen(QColor("#ffffff"), max(1.0, 2 * k)))
        p.setBrush(QColor.fromHsvF(min(self.pan.h, 0.9999), self.pan.s, self.pan.v))
        p.drawEllipse(c, 6 * k, 6 * k)

    def _set(self, e) -> None:
        self.pan.s = min(max(e.position().x() / max(1, self.width()), 0.0), 1.0)
        self.pan.v = 1.0 - min(max(e.position().y() / max(1, self.height()), 0.0), 1.0)
        self.pan.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pan.commit()


class _HueBar(QWidget):
    """Радужная полоса оттенка с ползунком-таблеткой."""

    def __init__(self, pan: "ColorPickerPanel"):
        super().__init__()
        self.pan = pan
        self.k = pan.k
        self.setFixedHeight(max(1, round(22 * self.k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        k = self.k
        bar = QRectF(0, (h - 8 * k) / 2, w, 8 * k)
        g = QLinearGradient(0, 0, w, 0)
        for i in range(7):
            g.setColorAt(i / 6, QColor.fromHsvF(min(i / 6, 0.9999), 1.0, 1.0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(g)
        p.drawRoundedRect(bar, 4 * k, 4 * k)
        x = min(max(self.pan.h * w, 5 * k), w - 5 * k)
        knob = QRectF(x - 5 * k, 1, 10 * k, h - 2)
        p.setPen(QPen(QColor("#ffffff"), max(1.0, 2 * k)))
        p.setBrush(QColor.fromHsvF(min(self.pan.h, 0.9999), 1.0, 1.0))
        p.drawRoundedRect(knob, 5 * k, 5 * k)

    def _set(self, e) -> None:
        self.pan.h = min(max(e.position().x() / max(1, self.width()), 0.0), 0.9999)
        self.pan.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pan.commit()


def eyedropper_icon(color: str, size: int = 16) -> QPixmap:
    """Иконка пипетки, рисуется кодом (без файлов)."""
    pm = QPixmap(size * 2, size * 2)
    pm.setDevicePixelRatio(2)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setPen(QPen(QColor(color), 1.4, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
    p.setBrush(Qt.BrushStyle.NoBrush)
    p.translate(size / 2, size / 2)
    p.rotate(45)
    p.drawRoundedRect(QRectF(-1.8, -4.2, 3.6, 7), 1, 1)       # корпус
    p.drawEllipse(QPointF(0, -5.6), 2.3, 2.3)                 # груша сверху
    p.drawLine(QPointF(0, 2.8), QPointF(0, 6.4))              # носик
    p.end()
    return pm


class _ScreenPicker(QWidget):
    """Пипетка: снимок экрана на весь экран, клик берёт цвет пикселя, Esc или правая кнопка отменяют."""
    picked = pyqtSignal(QColor)

    def __init__(self, screen):
        super().__init__(None, Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint
                         | Qt.WindowType.Tool)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setMouseTracking(True)
        self.setCursor(Qt.CursorShape.CrossCursor)
        self.shot = screen.grabWindow(0)
        self.img = self.shot.toImage()
        self.dpr = self.shot.devicePixelRatio() or 1.0
        self.setGeometry(screen.geometry())
        self.cur = QPoint(0, 0)

    def color_at(self, pt: QPoint) -> QColor:
        x = min(max(int(pt.x() * self.dpr), 0), self.img.width() - 1)
        y = min(max(int(pt.y() * self.dpr), 0), self.img.height() - 1)
        return self.img.pixelColor(x, y)

    def paintEvent(self, _):
        p = QPainter(self)
        p.drawPixmap(self.rect(), self.shot)
        c = self.color_at(self.cur)
        box = QRectF(self.cur.x() + 18, self.cur.y() + 18, 104, 30)
        if box.right() > self.width():
            box.moveRight(self.cur.x() - 18)
        if box.bottom() > self.height():
            box.moveBottom(self.cur.y() - 18)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(QPen(QColor(255, 255, 255, 90), 1))
        p.setBrush(QColor(12, 14, 22, 235))
        p.drawRoundedRect(box, 8, 8)
        p.setPen(QPen(QColor(255, 255, 255, 120), 1))
        p.setBrush(c)
        p.drawEllipse(QRectF(box.left() + 8, box.top() + 7, 16, 16))
        p.setPen(QColor("#ffffff"))
        p.drawText(QRectF(box.left() + 30, box.top(), 72, box.height()),
                   Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, c.name().upper())

    def mouseMoveEvent(self, e):
        self.cur = e.position().toPoint()
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.picked.emit(self.color_at(e.position().toPoint()))
        self.close()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()


class _VHueBar(QWidget):
    """Вертикальная полоса оттенка справа от квадрата."""

    def __init__(self, pan: "ColorPickerPanel"):
        super().__init__()
        self.pan = pan
        self.k = pan.k
        self.setFixedWidth(max(1, round(20 * self.k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h, k = self.width(), self.height(), self.k
        bar = QRectF(3 * k, 0, w - 6 * k, h)
        g = QLinearGradient(0, 0, 0, h)
        for i in range(7):
            g.setColorAt(i / 6, QColor.fromHsvF(min(i / 6, 0.9999), 1.0, 1.0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(g)
        p.drawRoundedRect(bar, 5 * k, 5 * k)
        y = min(max(self.pan.h * h, 3 * k), h - 3 * k)
        p.setPen(QPen(QColor("#ffffff"), max(1.0, 2 * k)))
        p.setBrush(QColor.fromHsvF(min(self.pan.h, 0.9999), 1.0, 1.0))
        p.drawRoundedRect(QRectF(0, y - 3 * k, w, 6 * k), 3 * k, 3 * k)

    def _set(self, e) -> None:
        self.pan.h = min(max(e.position().y() / max(1, self.height()), 0.0), 0.9999)
        self.pan.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pan.commit()


class _AlphaBar(QWidget):
    """Полоса прозрачности: шахматка под градиентом от прозрачного к цвету."""

    def __init__(self, pan: "ColorPickerPanel"):
        super().__init__()
        self.pan = pan
        self.k = pan.k
        self.setFixedHeight(max(1, round(18 * self.k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h, k = self.width(), self.height(), self.k
        bar = QRectF(0, 3 * k, w, h - 6 * k)
        clip = QPainterPath()
        clip.addRoundedRect(bar, 4 * k, 4 * k)
        p.setClipPath(clip)
        cell = max(3.0, 5 * k)
        y, row = bar.top(), 0
        while y < bar.bottom():                       # шахматка
            x, col = bar.left(), row
            while x < bar.right():
                p.fillRect(QRectF(x, y, cell, cell), QColor("#ffffff") if col % 2 == 0 else QColor("#c4c4c4"))
                x += cell
                col += 1
            y += cell
            row += 1
        base = QColor.fromHsvF(min(self.pan.h, 0.9999), self.pan.s, self.pan.v)
        g = QLinearGradient(0, 0, w, 0)
        g.setColorAt(0, QColor(base.red(), base.green(), base.blue(), 0))
        g.setColorAt(1, QColor(base.red(), base.green(), base.blue(), 255))
        p.fillRect(bar, g)
        p.setClipping(False)
        x = min(max(self.pan.a * w, 3 * k), w - 3 * k)
        p.setPen(QPen(QColor("#ffffff"), max(1.0, 2 * k)))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(QRectF(x - 3 * k, 1, 6 * k, h - 2), 3 * k, 3 * k)

    def _set(self, e) -> None:
        self.pan.a = min(max(e.position().x() / max(1, self.width()), 0.0), 1.0)
        self.pan.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pan.commit()


class ColorPickerPanel(QWidget):
    """Выбор цвета: квадрат насыщенности и яркости, справа вертикальная полоса оттенка, ниже прозрачность,
    поле HEX и кнопки «Копировать», «Вставить», пипетка. Цвет применяется, когда отпустили мышь.
    С прозрачностью цвет выглядит как #AARRGGBB."""
    committed = pyqtSignal(str)

    def __init__(self, start: QColor, k: float = 1.0):
        super().__init__()
        self.k = k
        sz = lambda v: max(1, round(v * k))
        h, sat, val, _ = start.getHsvF()
        self.h, self.s, self.v, self.a = (0.0 if h < 0 else h), sat, val, start.alphaF()
        self._hex_css = scale_qss("padding: 5px 8px; font-size: 12px;", k)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(sz(8), sz(6), sz(8), sz(8))
        lay.setSpacing(sz(10))
        top = QHBoxLayout()
        top.setSpacing(sz(8))
        self.sv, self.hue = _SVArea(self), _VHueBar(self)
        top.addWidget(self.sv, 1)
        top.addWidget(self.hue)
        lay.addLayout(top)
        self.alpha = _AlphaBar(self)
        lay.addWidget(self.alpha)
        row = QHBoxLayout()
        row.setSpacing(sz(8))
        lab = QLabel("HEX")
        lab.setObjectName("muted")
        if abs(k - 1.0) > 1e-6:
            lab.setStyleSheet(scale_qss("font-size: 12px;", k))
        self.hex = QLineEdit()
        self.hex.setMaxLength(9)
        self.hex.setFixedWidth(sz(110))
        self.hex.setStyleSheet(self._hex_css)
        self.hex.textEdited.connect(self.on_hex)
        self.hex.returnPressed.connect(self.commit)
        self.dot = QLabel()
        self.dot.setFixedSize(sz(18), sz(18))
        row.addWidget(lab)
        row.addStretch(1)
        row.addWidget(self.hex)
        row.addWidget(self.dot)
        lay.addLayout(row)
        btns = QHBoxLayout()
        btns.setSpacing(sz(6))
        cp, ps, eye = QPushButton("Копировать"), QPushButton("Вставить"), QPushButton()
        for b in (cp, ps, eye):
            b.setObjectName("pickbtn")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
        eye.setIcon(QIcon(eyedropper_icon(TEXT, 16)))
        eye.setToolTip("Пипетка: взять цвет с экрана")
        eye.setFixedWidth(sz(38))
        cp.clicked.connect(self.copy_hex)
        ps.clicked.connect(self.paste_hex)
        eye.clicked.connect(self.eyedrop)
        btns.addWidget(cp, 1)
        btns.addWidget(ps, 1)
        btns.addWidget(eye)
        lay.addLayout(btns)
        self.sync()

    def color(self) -> QColor:
        c = QColor.fromHsvF(min(self.h, 0.9999), self.s, self.v)
        c.setAlphaF(self.a)
        return c

    def hex_text(self) -> str:
        return cn(self.color()).upper().replace("#", "#", 1)

    def sync(self, hex_text: bool = True) -> None:
        c = self.color()
        if hex_text:
            self.hex.setText(self.hex_text())
        r, g, b = HOVER_OV                                  # рамка под тему: светлая на тёмной, тёмная на светлой
        self.dot.setStyleSheet(f"background: rgba({c.red()},{c.green()},{c.blue()},{c.alpha()}); "
                               f"border-radius: {max(2, round(5 * self.k))}px; border: 1px solid rgba({r},{g},{b},40);")
        for w in (self.sv, self.hue, self.alpha):
            w.update()

    def set_from(self, c: QColor, keep_alpha: bool = False) -> None:
        h, sat, val, a = c.getHsvF()
        self.h, self.s, self.v = (self.h if h < 0 else h), sat, val
        if not keep_alpha:
            self.a = a

    def on_hex(self, text: str) -> None:
        t = text.strip()
        if not t.startswith("#"):
            t = "#" + t
        c = QColor(t) if len(t) in (7, 9) else QColor()
        if c.isValid():
            self.set_from(c)
            self.sync(hex_text=False)
            self.hex.setStyleSheet(self._hex_css)
        else:
            self.hex.setStyleSheet(self._hex_css + " border: 1px solid #ff6b6b;")

    def copy_hex(self) -> None:
        QApplication.clipboard().setText(self.hex_text())

    def paste_hex(self) -> None:
        t = QApplication.clipboard().text().strip()
        c = QColor(t if t.startswith("#") else "#" + t) if re.fullmatch(r"#?[0-9a-fA-F]{6}([0-9a-fA-F]{2})?", t) else QColor()
        if not c.isValid():
            c = QColor(t)                                   # вдруг имя цвета: red, white...
        if c.isValid():
            self.set_from(c)
            self.sync()
            self.commit()

    def eyedrop(self) -> None:
        scr = self.screen() or QApplication.primaryScreen()
        sp = _ScreenPicker(scr)
        if sp.shot.isNull():                                # например, Wayland не отдаёт снимок экрана
            sp.deleteLater()
            return
        sp.picked.connect(self._picked)
        self._sp = sp
        sp.show()
        sp.activateWindow()
        sp.setFocus()

    def _picked(self, c: QColor) -> None:
        self.set_from(c, keep_alpha=True)                   # прозрачность остаётся прежней
        self.sync()
        self.commit()

    def commit(self) -> None:
        self.committed.emit(cn(self.color()))


class _SV2(QWidget):
    """Большой квадрат: слева направо насыщенность, сверху вниз яркость; кружок показывает выбранную точку."""

    def __init__(self, pn: "ColorPanel2"):
        super().__init__()
        self.pn = pn
        self.setFixedHeight(max(1, round(190 * pn.k)))
        self.setCursor(Qt.CursorShape.CrossCursor)

    def _set(self, pos) -> None:
        r = self.rect()
        self.pn.s = min(max(pos.x() / max(1, r.width()), 0.0), 1.0)
        self.pn.v = 1.0 - min(max(pos.y() / max(1, r.height()), 0.0), 1.0)
        self.pn.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pn.commit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        k, r = self.pn.k, QRectF(self.rect())
        clip = QPainterPath()
        clip.addRoundedRect(r, 10 * k, 10 * k)
        p.setClipPath(clip)
        g1 = QLinearGradient(r.left(), 0, r.right(), 0)
        g1.setColorAt(0, QColor("#ffffff"))
        g1.setColorAt(1, QColor.fromHsvF(min(self.pn.h, 0.9999), 1.0, 1.0))
        p.fillRect(r, g1)
        g2 = QLinearGradient(0, r.top(), 0, r.bottom())
        g2.setColorAt(0, QColor(0, 0, 0, 0))
        g2.setColorAt(1, QColor(0, 0, 0, 255))
        p.fillRect(r, g2)
        p.setClipping(False)
        c = QPointF(r.left() + self.pn.s * r.width(), r.top() + (1 - self.pn.v) * r.height())
        rad = 7 * k
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(0, 0, 0, 90), 3.2 * k))
        p.drawEllipse(c, rad, rad)
        p.setPen(QPen(QColor("#ffffff"), 2 * k))
        p.drawEllipse(c, rad, rad)


class _Hue2(QWidget):
    """Горизонтальная радужная полоса оттенка с белым ползунком-таблеткой."""

    def __init__(self, pn: "ColorPanel2"):
        super().__init__()
        self.pn = pn
        self.setFixedHeight(max(1, round(24 * pn.k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def _set(self, pos) -> None:
        pad = 7 * self.pn.k
        self.pn.h = min(max((pos.x() - pad) / max(1.0, self.width() - 2 * pad), 0.0), 1.0)
        self.pn.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pn.commit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        k, w, h = self.pn.k, self.width(), self.height()
        bar = QRectF(0, (h - 8 * k) / 2, w, 8 * k)
        g = QLinearGradient(bar.left(), 0, bar.right(), 0)
        for i in range(7):
            g.setColorAt(i / 6, QColor.fromHsvF(min(i / 6, 0.9999), 1.0, 1.0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(g)
        p.drawRoundedRect(bar, 4 * k, 4 * k)
        pad = 7 * k
        x = pad + self.pn.h * (w - 2 * pad)
        th = QRectF(x - 7 * k, (h - 22 * k) / 2, 14 * k, 22 * k)
        p.setPen(QPen(QColor(0, 0, 0, 110), 1.4 * k))
        p.setBrush(QColor("#ffffff"))
        p.drawRoundedRect(th, 6 * k, 6 * k)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#1a1d28"))
        p.drawRoundedRect(QRectF(x - 1.5 * k, th.top() + 5 * k, 3 * k, th.height() - 10 * k), 1.5 * k, 1.5 * k)


class _Alpha2(QWidget):
    """Полоса прозрачности под полосой оттенка: шахматка и градиент от прозрачного к выбранному цвету."""

    def __init__(self, pn: "ColorPanel2"):
        super().__init__()
        self.pn = pn
        self.setFixedHeight(max(1, round(24 * pn.k)))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def _set(self, pos) -> None:
        pad = 7 * self.pn.k
        self.pn.a = min(max((pos.x() - pad) / max(1.0, self.width() - 2 * pad), 0.0), 1.0)
        self.pn.sync()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseMoveEvent(self, e):
        if e.buttons() & Qt.MouseButton.LeftButton:
            self._set(e.position())

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.pn.commit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        k, w, h = self.pn.k, self.width(), self.height()
        bar = QRectF(0, (h - 8 * k) / 2, w, 8 * k)
        clip = QPainterPath()
        clip.addRoundedRect(bar, 4 * k, 4 * k)
        p.save()
        p.setClipPath(clip)
        cell = 4 * k                                            # шахматка
        row, y = 0, bar.top()
        while y < bar.bottom():
            col, x = row, bar.left()
            while x < bar.right():
                p.fillRect(QRectF(x, y, cell, cell), QColor("#ffffff") if col % 2 == 0 else QColor("#c4c4c4"))
                x += cell
                col += 1
            y += cell
            row += 1
        base = QColor.fromHsvF(min(self.pn.h, 0.9999), self.pn.s, self.pn.v)
        g = QLinearGradient(bar.left(), 0, bar.right(), 0)
        g.setColorAt(0, QColor(base.red(), base.green(), base.blue(), 0))
        g.setColorAt(1, QColor(base.red(), base.green(), base.blue(), 255))
        p.fillRect(bar, g)
        p.restore()
        pad = 7 * k
        x = pad + self.pn.a * (w - 2 * pad)
        th = QRectF(x - 7 * k, (h - 22 * k) / 2, 14 * k, 22 * k)
        p.setPen(QPen(QColor(0, 0, 0, 110), 1.4 * k))
        p.setBrush(QColor("#ffffff"))
        p.drawRoundedRect(th, 6 * k, 6 * k)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#1a1d28"))
        p.drawRoundedRect(QRectF(x - 1.5 * k, th.top() + 5 * k, 3 * k, th.height() - 10 * k), 1.5 * k, 1.5 * k)


class ColorPanel2(QWidget):
    """Выбор цвета: большой квадрат, полоса оттенка, внизу HEX с кружком и пипетка. Цвет применяется, когда отпустили мышь."""
    committed = pyqtSignal(str)

    def __init__(self, start: QColor, k: float = 1.0):
        super().__init__()
        self.k = k
        sz = lambda v: max(1, round(v * k))
        h, sat, val, _ = start.getHsvF()
        self.h, self.s, self.v, self.a = (0.0 if h < 0 else h), max(sat, 0.0), max(val, 0.0), start.alphaF()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(sz(8), sz(8), sz(8), sz(8))
        lay.setSpacing(sz(10))
        self.sv, self.hue, self.alpha = _SV2(self), _Hue2(self), _Alpha2(self)
        lay.addWidget(self.sv)
        lay.addWidget(self.hue)
        arow = QHBoxLayout()                                   # прозрачность: полоса и процент справа
        arow.setSpacing(sz(8))
        self.apct = QLabel()
        self.apct.setObjectName("muted")
        self.apct.setFixedWidth(sz(36))
        self.apct.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self.apct.setStyleSheet(scale_qss("font-size: 12px;", k))
        arow.addWidget(self.alpha, 1)
        arow.addWidget(self.apct)
        lay.addLayout(arow)
        row = QHBoxLayout()
        row.setSpacing(sz(8))
        chev = QLabel()
        chev.setPixmap(draw_icon("chev_down", MUTED, sz(14)))
        lab = QLabel("HEX")
        lab.setObjectName("muted")
        lab.setStyleSheet(scale_qss("font-size: 12px;", k))
        row.addWidget(chev)
        row.addWidget(lab)
        row.addStretch(1)
        pill = QFrame()
        pill.setObjectName("hexpill")
        pill.setStyleSheet(f"QFrame#hexpill {{ background: {CONTROL}; border: 1px solid {BORDER}; "
                           f"border-radius: {sz(8)}px; }}")
        pl = QHBoxLayout(pill)
        pl.setContentsMargins(sz(8), sz(3), sz(10), sz(3))
        pl.setSpacing(sz(8))
        self.dot = QLabel()
        self.dot.setFixedSize(sz(14), sz(14))
        self.hex = QLineEdit()
        self.hex.setMaxLength(9)
        self.hex.setFixedWidth(sz(82))
        self.hex.setStyleSheet(scale_qss(f"background: transparent; border: none; padding: 2px 0; font-size: 12px; "
                                         f"color: {TEXT};", k))
        self.hex.textEdited.connect(self.on_hex)
        self.hex.returnPressed.connect(self.commit)
        pl.addWidget(self.dot)
        pl.addWidget(self.hex)
        row.addWidget(pill)
        eye = QPushButton()
        eye.setObjectName("pickbtn")
        eye.setIcon(QIcon(eyedropper_icon(TEXT, 16)))
        eye.setToolTip("Пипетка: взять цвет с экрана")
        eye.setFixedWidth(sz(34))
        eye.setCursor(Qt.CursorShape.PointingHandCursor)
        eye.clicked.connect(self.eyedrop)
        row.addWidget(eye)
        lay.addLayout(row)
        self.sync()

    def color(self) -> QColor:
        c = QColor.fromHsvF(min(self.h, 0.9999), self.s, self.v)
        c.setAlphaF(self.a)
        return c

    def hex_text(self) -> str:
        return cn(self.color()).upper()

    def sync(self, hex_text: bool = True) -> None:
        c = self.color()
        if hex_text and not self.hex.hasFocus():
            self.hex.setText(self.hex_text())
        r, g, b = HOVER_OV
        self.dot.setStyleSheet(f"background: rgba({c.red()},{c.green()},{c.blue()},{c.alpha()}); "
                               f"border-radius: {max(2, round(7 * self.k))}px; border: 1px solid rgba({r},{g},{b},50);")
        self.apct.setText(f"{round(self.a * 100)}%")
        self.sv.update()
        self.hue.update()
        self.alpha.update()

    def set_from(self, c: QColor, keep_alpha: bool = False) -> None:
        h, sat, val, a = c.getHsvF()
        self.h, self.s, self.v = (self.h if h < 0 else h), sat, val
        if not keep_alpha:
            self.a = a

    def on_hex(self, text: str) -> None:
        t = text.strip()
        if not t.startswith("#"):
            t = "#" + t
        c = QColor(t) if len(t) in (7, 9) else QColor()
        if c.isValid():
            self.set_from(c, keep_alpha=(len(t) == 7))     # без alpha в HEX прозрачность остаётся прежней
            self.sync(hex_text=False)

    def eyedrop(self) -> None:
        scr = self.screen() or QApplication.primaryScreen()
        sp = _ScreenPicker(scr)
        if sp.shot.isNull():                                # например, Wayland не отдаёт снимок экрана
            sp.deleteLater()
            return
        sp.picked.connect(self._picked)
        self._sp = sp
        sp.show()
        sp.activateWindow()
        sp.setFocus()

    def _picked(self, c: QColor) -> None:
        self.set_from(c, keep_alpha=True)
        self.sync()
        self.commit()

    def commit(self) -> None:
        self.committed.emit(cn(self.color()))


class ColorFlyout(QFrame):
    """Отдельное всплывающее окно с колор пикером: открывается правее меню профиля."""
    PAD = 14
    WIDTH = 262

    def __init__(self, menu: "ProfileMenu", start: QColor, k: float = 1.0):
        super().__init__(menu, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setFixedWidth(max(1, round(self.WIDTH * k)) + 2 * self.PAD)   # подгоняется под размер окна настроек
        lay = QVBoxLayout(self)
        lay.setContentsMargins(self.PAD, self.PAD, self.PAD, self.PAD)
        self.panel = ColorPanel2(start, k)
        lay.addWidget(self.panel)
        self.adjustSize()

    def retheme(self) -> None:
        """Перекрасить под текущую тему: заново применить стили ко всем вложенным виджетам."""
        st = self.style()
        for w in [self] + self.findChildren(QWidget):
            st.unpolish(w)
            st.polish(w)
        self.panel.sync(hex_text=False)
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        box = QRectF(self.PAD, self.PAD, self.width() - 2 * self.PAD, self.height() - 2 * self.PAD)
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(self.PAD, 0, -1):          # мягкая тень
            p.setBrush(QColor(0, 0, 0, 4))
            p.drawRoundedRect(box.adjusted(-i, -i, i, i), 14 + i, 14 + i)
        p.setPen(QPen(QColor(POP_BORDER), 1))
        p.setBrush(QColor(POP_BG))
        p.drawRoundedRect(box, 14, 14)


class _TipBubble(QWidget):
    """Своя подсказка с закруглёнными углами (обычная QToolTip рисуется прямоугольником и ведёт себя капризно)."""

    def __init__(self):
        super().__init__(None, Qt.WindowType.ToolTip | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowTransparentForInput)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)
        self.lines: list = []

    def font_(self) -> QFont:
        f = QFont(self.font())
        f.setPixelSize(12)
        f.setWeight(QFont.Weight.Medium)
        return f

    def show_for(self, anchor: QWidget, lines: list) -> None:
        """Над кружком, по центру: строки вида («Имя:», «Default»)."""
        self.lines = lines
        fm = QFontMetrics(self.font_())
        w = max(fm.horizontalAdvance(f"{a} {b}") for a, b in lines) + 28
        h = len(lines) * 18 + 18
        self.resize(w, h)
        g = anchor.mapToGlobal(QPoint(anchor.width() // 2, 0))
        scr = anchor.screen().availableGeometry() if anchor.screen() else QRect(0, 0, 1920, 1080)
        x = min(max(g.x() - w // 2, scr.left() + 4), scr.right() - w - 4)
        y = g.y() - h - 12                                   # чуть выше кружка
        if y < scr.top():
            y = g.y() + anchor.height() + 8
        self.move(x, y)
        self.show()
        self.raise_()
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        fill = QColor(CARD)
        fill.setAlpha(255)
        p.setPen(QPen(QColor(BORDER_HOVER), 1))
        p.setBrush(fill)
        p.drawRoundedRect(QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5), 10, 10)
        p.setFont(self.font_())
        fm = p.fontMetrics()
        y = 9
        for a, b in self.lines:
            r = QRectF(14, y, self.width() - 28, 18)
            p.setPen(QColor(MUTED))
            p.drawText(r, Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, a)
            p.setPen(QColor(STRONG))
            p.drawText(r.adjusted(fm.horizontalAdvance(a + " "), 0, 0, 0),
                       Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, str(b))
            y += 18


_TIP_BUBBLE = None


def tip_bubble() -> "_TipBubble":
    global _TIP_BUBBLE
    if _TIP_BUBBLE is None:
        _TIP_BUBBLE = _TipBubble()
    return _TIP_BUBBLE


class _Dot(QWidget):
    """Кружок: цвет в редакторе темы или сохранённая тема внизу. ПКМ даёт меню (удалить)."""
    clicked = pyqtSignal()
    menu_requested = pyqtSignal(QPoint)

    def __init__(self, color: str, d: int = 17, ring: bool = False, tip: str = ""):
        super().__init__()
        self.color, self.d, self.ring, self.active = color, d, ring, False
        self.setFixedSize(d + 6, d + 6)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._tip = tip
        self._tt = QTimer(self)                  # обычная подсказка появляется слишком медленно: показываем сами
        self._tt.setSingleShot(True)
        self._tt.setInterval(30)
        self._tt.timeout.connect(self._show_tip)

    def _show_tip(self) -> None:
        if self._tip:
            tip_bubble().show_for(self, self._tip)

    def enterEvent(self, e):
        self._tt.start()

    def leaveEvent(self, e):
        self._tt.stop()
        tip_bubble().hide()

    def hideEvent(self, e):
        self._tt.stop()
        tip_bubble().hide()
        super().hideEvent(e)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(3, 3, self.d, self.d)
        if self.ring:
            p.setPen(QPen(QColor(self.color), 3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawEllipse(r.adjusted(2, 2, -2, -2))
        else:
            p.setPen(QPen(QColor(*HOVER_OV, 40), 1))
            p.setBrush(QColor(self.color))
            p.drawEllipse(r)
        if self.active:                          # выбранная тема: маленький кружок в центре, без обводки
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor("#0b0d18"))
            c, rad = r.center(), self.d * 0.2
            p.drawEllipse(c, rad, rad)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
        elif e.button() == Qt.MouseButton.RightButton:
            self.menu_requested.emit(e.globalPosition().toPoint())


class _ColorRow(QWidget):
    """Строка редактора: название элемента слева, кружок с его цветом справа."""
    clicked = pyqtSignal()

    def __init__(self, title: str, color: str):
        super().__init__()
        self.title, self.color, self.hover = title, color, False
        self.setFixedHeight(34)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def enterEvent(self, e):
        self.hover = True
        self.update()

    def leaveEvent(self, e):
        self.hover = False
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        if self.hover:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(*HOVER_OV, 14))
            p.drawRoundedRect(QRectF(0, 0, w, h), 8, 8)
        f = self.font()
        f.setPixelSize(13)
        f.setWeight(QFont.Weight.Medium)
        p.setFont(f)
        p.setPen(QColor(STRONG if self.hover else TEXT))
        p.drawText(QRectF(10, 0, w - 50, h), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, self.title)
        p.setPen(QPen(QColor(*HOVER_OV, 40), 1))
        p.setBrush(QColor(self.color))
        p.drawEllipse(QRectF(w - 32, (h - 20) / 2, 20, 20))


class _ColorPill(QWidget):
    """Плашка цвета в строке карточки: кружок и HEX в скруглённой рамке (как в современных редакторах тем)."""
    clicked = pyqtSignal()

    def __init__(self, color: str):
        super().__init__()
        self.color, self.hover = color, False
        self.setFixedHeight(30)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def enterEvent(self, e):
        self.hover = True
        self.update()

    def leaveEvent(self, e):
        self.hover = False
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        r = QRectF(0.5, 0.5, w - 1, h - 1)
        p.setPen(QPen(QColor(*HOVER_OV, 60 if self.hover else 30), 1))
        p.setBrush(QColor(*HOVER_OV, 14 if self.hover else 8))
        p.drawRoundedRect(r, h / 2, h / 2)
        dot, col = QRectF(10, (h - 14) / 2, 14, 14), QColor(self.color)
        if col.alpha() < 255:                                    # прозрачный цвет: шахматка под кружком
            ck = QPainterPath()
            ck.addEllipse(dot)
            p.save()
            p.setClipPath(ck)
            for i in range(2):
                for j in range(2):
                    p.fillRect(QRectF(dot.left() + i * 7, dot.top() + j * 7, 7, 7),
                               QColor("#ffffff") if (i + j) % 2 == 0 else QColor("#c4c4c4"))
            p.restore()
        p.setPen(QPen(QColor(*HOVER_OV, 60), 1))
        p.setBrush(col)
        p.drawEllipse(dot)
        f = self.font()
        f.setPixelSize(12)
        p.setFont(f)
        p.setPen(QColor(STRONG if self.hover else TEXT))
        p.drawText(QRectF(32, 0, w - 38, h), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                   cn(col).upper())


class _ModeTiles(QWidget):
    """Выбор режима: светлая или тёмная тема (две плитки с мини-превью)."""
    picked = pyqtSignal(str)
    W, H, GAP = 84, 54, 10

    def __init__(self):
        super().__init__()
        self.setFixedSize(2 * self.W + self.GAP, self.H + 22)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def _tiles(self):
        return [("light", "Светлая", QRectF(0, 0, self.W, self.H)),
                ("dark", "Тёмная", QRectF(self.W + self.GAP, 0, self.W, self.H))]

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            for name, _, r in self._tiles():
                if r.contains(e.position()):
                    self.picked.emit(name)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        for name, cap, r in self._tiles():
            light = name == "light"
            bg, side, line = ("#f3f5fa", "#e1e5f0", "#c2c9da") if light else ("#0b0e16", "#05070c", "#2a3042")
            path = QPainterPath()
            path.addRoundedRect(r, 9, 9)
            p.save()
            p.setClipPath(path)
            p.fillRect(r, QColor(bg))
            p.fillRect(QRectF(r.left(), r.top(), r.width() * 0.3, r.height()), QColor(side))
            p.setPen(QPen(QColor(line), 2))
            for i in range(3):                                   # пункты панели
                y = r.top() + 12 + i * 9
                p.drawLine(QPointF(r.left() + 6, y), QPointF(r.left() + r.width() * 0.3 - 6, y))
            p.setPen(QPen(QColor(ACCENT), 2))
            p.drawLine(QPointF(r.left() + r.width() * 0.4, r.top() + 14), QPointF(r.right() - 10, r.top() + 14))
            p.setPen(QPen(QColor(line), 2))
            for i in range(3):
                y = r.top() + 25 + i * 8
                p.drawLine(QPointF(r.left() + r.width() * 0.4, y), QPointF(r.right() - (10 + i * 7), y))
            p.restore()
            on = THEME_NAME == name
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(QColor(ACCENT if on else BORDER), 2 if on else 1))
            p.drawRoundedRect(r.adjusted(1, 1, -1, -1), 9, 9)
            f = self.font()
            f.setPixelSize(11)
            p.setFont(f)
            p.setPen(QColor(STRONG if on else MUTED))
            p.drawText(QRectF(r.left(), r.bottom() + 3, r.width(), 16), Qt.AlignmentFlag.AlignCenter, T(cap))


def theme_preview(cols) -> dict:
    """Цвета для мини-превью темы: всё берётся из самой темы (фон, панель, текст, акцент, слайдер),
    а чего в теме нет, там цвет обычной светлой / тёмной темы."""
    u = {k: v for k, v in (cols or {}).items() if k in ROLE_VARS and _hex_ok(v)}
    light = QColor(u["bg"]).lightnessF() >= 0.5 if "bg" in u else THEME_NAME == "light"
    base = THEMES["light" if light else "dark"]
    acc = u.get("accent") or (ACCENT_NAME if _hex_ok(ACCENT_NAME)
                              else next((a[1] for a in ACCENTS if a[0] == ACCENT_NAME), ACCENTS[0][1]))
    bg = QColor(u.get("bg", base["BG"]))
    if "bg" in u:                                    # панель считается от фона так же, как в самой теме
        k = 0.4 if bg.lightnessF() < 0.5 else 0.04
        side = QColor(round(bg.red() * (1 - k)), round(bg.green() * (1 - k)), round(bg.blue() * (1 - k)))
    else:
        side = QColor(base["SIDEBAR"])
    return {"bg": bg, "side": side, "text": QColor(u.get("text", base["TEXT"])),
            "muted": QColor(u.get("muted", base["MUTED"])), "accent": QColor(acc),
            "slider": QColor(u.get("slider", acc)), "knob": QColor(u.get("knob", "#ffffff")),
            "groove": QColor(u.get("groove", base["GROOVE"]))}


class _ThemeTiles(QWidget):
    """Выбор темы: одна полоска плиток с мини-превью, нарисованным цветами самой темы (панель, полоска, текст,
    слайдер). Листается колёсиком мыши; у краёв плитки плавно гаснут. Левый клик выбирает тему,
    ПКМ по своей (сохранённой) теме: меню «Удалить»."""
    picked = pyqtSignal(int)
    menu_requested = pyqtSignal(int, QPoint)
    W, H, GAP, LBL = 84, 54, 10, 22
    VISIBLE = 4.5                       # сколько плиток видно сразу: половинка подсказывает, что полоску можно листать

    def __init__(self):
        super().__init__()
        self.items: list = []                    # (название, цвета или None, "default" | "builtin" | "saved" | "custom")
        self.current = -1
        self._hover = -1
        self.offset = 0.0
        self._target = 0.0
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setMouseTracking(True)
        self.setFixedHeight(self.H + self.LBL)
        self._anim = QVariantAnimation(self)
        self._anim.setDuration(180)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._anim.valueChanged.connect(self._set_off)

    # --- размеры и прокрутка ---
    def _vw(self) -> float:
        return float(self.width() if self.isVisible() else getattr(self, "row_width", self.width()))

    def _content_w(self) -> float:
        return max(0, len(self.items)) * (self.W + self.GAP) - self.GAP

    def _max_off(self) -> float:
        return max(0.0, self._content_w() - self._vw())

    def sizeHint(self) -> QSize:
        return QSize(round(self.VISIBLE * (self.W + self.GAP) - self.GAP), self.H + self.LBL)

    def minimumSizeHint(self) -> QSize:
        return QSize(self.W, self.H + self.LBL)

    def _set_off(self, v) -> None:
        if v is None:                       # QVariantAnimation иногда присылает пустое значение: пропускаем
            return
        self.offset = max(0.0, min(float(v), self._max_off()))
        self.update()

    def _scroll_to(self, t: float, animate: bool = True) -> None:
        t = max(0.0, min(t, self._max_off()))
        self._target = t
        self._anim.stop()
        if animate and self.isVisible():
            self._anim.setStartValue(self.offset)
            self._anim.setEndValue(t)
            self._anim.start()
        else:
            self._set_off(t)

    def _reveal(self, i: int, animate: bool = True) -> None:
        """Прокручивает так, чтобы плитка i была видна целиком."""
        if i < 0:
            return
        left, right = i * (self.W + self.GAP), i * (self.W + self.GAP) + self.W
        if left < self._target:
            self._scroll_to(left, animate)
        elif right > self._target + self._vw():
            self._scroll_to(right - self._vw(), animate)

    def set_items(self, items: list, current: int) -> None:
        changed = current != self.current or not self.items
        self.items, self.current = items, current
        self._target = min(self._target, self._max_off())
        self._set_off(min(self.offset, self._max_off()))
        if changed:
            self._reveal(current, animate=self.isVisible())
        self.update()

    def showEvent(self, e):
        self._reveal(self.current, animate=False)
        super().showEvent(e)

    def resizeEvent(self, e):
        self._scroll_to(self._target, animate=False)
        super().resizeEvent(e)

    def wheelEvent(self, e):
        if self._max_off() <= 0:
            e.ignore()
            return
        d = e.angleDelta().y() or e.angleDelta().x()
        if d == 0:
            e.ignore()
            return
        t = max(0.0, min(self._max_off(), self._target - (self.W + self.GAP) * d / 120.0))
        if abs(t - self._target) < 0.5:              # упёрлись в край: колесо отдаём странице
            e.ignore()
            return
        self._scroll_to(t)
        e.accept()

    # --- мышь ---
    def _rect(self, i: int) -> QRectF:
        return QRectF(i * (self.W + self.GAP) - self.offset, 0, self.W, self.H)

    def _at(self, pos) -> int:
        for i in range(len(self.items)):
            if self._rect(i).adjusted(0, 0, 0, self.LBL).contains(pos):
                return i
        return -1

    def mousePressEvent(self, e):
        i = self._at(e.position())
        if i < 0:
            return
        if e.button() == Qt.MouseButton.LeftButton:
            self.picked.emit(i)
        elif e.button() == Qt.MouseButton.RightButton and self.items[i][2] == "saved":
            self.menu_requested.emit(i, e.globalPosition().toPoint())

    def mouseMoveEvent(self, e):
        i = self._at(e.position())
        if i != self._hover:
            self._hover = i
            self.update()

    def leaveEvent(self, e):
        self._hover = -1
        self.update()

    # --- рисование ---
    def _draw(self, p: QPainter) -> None:
        f = self.font()
        f.setPixelSize(11)
        fm = QFontMetrics(f)
        for i, (name, cols, kind) in enumerate(self.items):
            r = self._rect(i)
            if r.right() < 0 or r.left() > self.width():
                continue
            pal, on = theme_preview(cols), i == self.current
            path = QPainterPath()
            path.addRoundedRect(r, 9, 9)
            p.save()
            p.setClipPath(path)
            p.fillRect(r, pal["bg"])
            side_w = r.width() * 0.3
            p.fillRect(QRectF(r.left(), r.top(), side_w, r.height()), pal["side"])
            muted = QColor(pal["muted"])
            muted.setAlpha(170)
            for j in range(3):                                         # пункты панели; первый активный: цвет акцента
                p.setPen(QPen(pal["accent"] if j == 0 else muted, 2))
                y = r.top() + 12 + j * 9
                p.drawLine(QPointF(r.left() + 6, y), QPointF(r.left() + side_w - 6, y))
            p.setPen(QPen(pal["accent"], 2))                           # полоска цветом акцента темы
            p.drawLine(QPointF(r.left() + r.width() * 0.4, r.top() + 14), QPointF(r.right() - 10, r.top() + 14))
            txt = QColor(pal["text"])
            txt.setAlpha(150)
            p.setPen(QPen(txt, 2))                                     # строки текста цветом текста темы
            for j in range(2):
                y = r.top() + 24 + j * 7
                p.drawLine(QPointF(r.left() + r.width() * 0.4, y), QPointF(r.right() - (10 + j * 9), y))
            x0, x1, ys = r.left() + r.width() * 0.4, r.right() - 10, r.top() + 42       # мини-слайдер темы
            xm = x0 + (x1 - x0) * 0.6
            p.setPen(QPen(pal["groove"], 2.4))
            p.drawLine(QPointF(x0, ys), QPointF(x1, ys))
            p.setPen(QPen(pal["slider"], 2.4))
            p.drawLine(QPointF(x0, ys), QPointF(xm, ys))
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(pal["knob"])
            p.drawEllipse(QPointF(xm, ys), 3.2, 3.2)
            p.restore()
            p.setBrush(Qt.BrushStyle.NoBrush)
            if on:
                p.setPen(QPen(QColor(ACCENT), 2))
            else:
                p.setPen(QPen(QColor(BORDER_HOVER if i == self._hover else BORDER), 1))
            p.drawRoundedRect(r.adjusted(1, 1, -1, -1), 9, 9)
            p.setFont(f)
            p.setPen(QColor(STRONG if on else MUTED))
            label = fm.elidedText(T(name) if kind != "saved" else name, Qt.TextElideMode.ElideRight, int(r.width() + 6))
            p.drawText(QRectF(r.left() - 3, r.bottom() + 3, r.width() + 6, 16), Qt.AlignmentFlag.AlignCenter, label)

    def paintEvent(self, _):
        w, h, dpr = self.width(), self.height(), self.devicePixelRatioF()
        pm = QPixmap(max(1, round(w * dpr)), max(1, round(h * dpr)))
        pm.setDevicePixelRatio(dpr)
        pm.fill(Qt.GlobalColor.transparent)
        q = QPainter(pm)
        q.setRenderHint(QPainter.RenderHint.Antialiasing)
        self._draw(q)
        mx, fade = self._max_off(), min(30.0, w * 0.14)
        if mx > 0 and fade > 1:                                        # плитки плавно гаснут там, где есть что листать
            a_l = round(255 * (1 - min(1.0, self.offset / fade)))
            a_r = round(255 * (1 - min(1.0, (mx - self.offset) / fade)))
            g = QLinearGradient(0, 0, w, 0)
            g.setColorAt(0.0, QColor(0, 0, 0, 255 - a_l))
            g.setColorAt(fade / w, QColor(0, 0, 0, 255))
            g.setColorAt(1 - fade / w, QColor(0, 0, 0, 255))
            g.setColorAt(1.0, QColor(0, 0, 0, 255 - a_r))
            q.setCompositionMode(QPainter.CompositionMode.CompositionMode_DestinationIn)
            q.fillRect(QRectF(0, 0, w, h), g)
        q.end()
        QPainter(self).drawPixmap(0, 0, pm)


class _PicTiles(QWidget):
    """Картинка на заднем фоне: «Нет», «Своя» (с миниатюрой) и «Загрузить»."""
    picked = pyqtSignal(str)
    S, GAP = 52, 10

    def __init__(self):
        super().__init__()
        self.setFixedSize(3 * self.S + 2 * self.GAP, self.S + 22)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._thumb = None
        self._thumb_key = None

    def _tiles(self):
        return [("none", "Нет", QRectF(0, 0, self.S, self.S)),
                ("custom", "Своя", QRectF(self.S + self.GAP, 0, self.S, self.S)),
                ("upload", "Загрузить", QRectF(2 * (self.S + self.GAP), 0, self.S, self.S))]

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            for name, _, r in self._tiles():
                if r.contains(e.position()):
                    self.picked.emit(name)

    def _thumbnail(self):
        path = VISUAL.get("bg_file") or ""
        if not path or not os.path.isfile(path):
            return None
        if self._thumb_key != (path, os.path.getmtime(path)):
            img = QImage(path)
            if img.isNull():
                return None
            img = img.scaled(self.S, self.S, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                             Qt.TransformationMode.SmoothTransformation)
            self._thumb = QPixmap.fromImage(img.copy((img.width() - self.S) // 2, (img.height() - self.S) // 2, self.S, self.S))
            self._thumb_key = (path, os.path.getmtime(path))
        return self._thumb

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        active = "custom" if backdrop_on() else "none"
        for name, cap, r in self._tiles():
            path = QPainterPath()
            path.addRoundedRect(r, 10, 10)
            on = name == active
            p.save()
            p.setClipPath(path)
            p.fillRect(r, QColor(CONTROL))
            thumb = self._thumbnail() if name == "custom" else None
            if thumb is not None:
                p.drawPixmap(r.topLeft(), thumb)
            p.restore()
            p.setBrush(Qt.BrushStyle.NoBrush)
            pen = QPen(QColor(ACCENT if on else BORDER), 2 if on else 1)
            if name == "upload":
                pen.setStyle(Qt.PenStyle.DashLine)
            p.setPen(pen)
            p.drawRoundedRect(r.adjusted(1, 1, -1, -1), 10, 10)
            if name != "custom" or thumb is None:       # значок × или +
                c, m = r.center(), 7
                p.setPen(QPen(QColor(MUTED), 1.6))
                if name == "none":
                    p.drawLine(QPointF(c.x() - m, c.y() - m), QPointF(c.x() + m, c.y() + m))
                    p.drawLine(QPointF(c.x() - m, c.y() + m), QPointF(c.x() + m, c.y() - m))
                elif name == "upload":
                    p.drawLine(QPointF(c.x() - m, c.y()), QPointF(c.x() + m, c.y()))
                    p.drawLine(QPointF(c.x(), c.y() - m), QPointF(c.x(), c.y() + m))
                else:
                    p.setPen(QPen(QColor(DIM), 1.4))
                    p.drawRoundedRect(QRectF(c.x() - 9, c.y() - 7, 18, 14), 3, 3)
            if on and name == "custom":                  # галочка выбранной картинки
                b = QRectF(r.right() - 9, r.top() - 5, 16, 16)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(ACCENT))
                p.drawEllipse(b)
                p.setPen(QPen(QColor("#ffffff"), 1.8))
                p.drawLine(QPointF(b.left() + 4, b.center().y()), QPointF(b.left() + 7, b.center().y() + 3))
                p.drawLine(QPointF(b.left() + 7, b.center().y() + 3), QPointF(b.right() - 4, b.top() + 5))
            f = self.font()
            f.setPixelSize(11)
            p.setFont(f)
            p.setPen(QColor(STRONG if on else MUTED))
            p.drawText(QRectF(r.left() - 8, r.bottom() + 3, r.width() + 16, 16), Qt.AlignmentFlag.AlignCenter, T(cap))


class _ValSlider(QWidget):
    """Ползунок с плашкой значения справа («6 px», «86%»)."""
    changed = pyqtSignal(int)
    row_width = 260

    def __init__(self, lo: int, hi: int, val: int, suffix: str):
        super().__init__()
        self.suffix = suffix
        self.slider = QSlider(Qt.Orientation.Horizontal)
        self.slider.setRange(lo, hi)
        self.slider.setValue(val)
        self.slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.box = QLabel()
        self.box.setObjectName("valuebox")
        self.box.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.box.setFixedSize(64, 26)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        lay.addWidget(self.slider, 1)
        lay.addWidget(self.box)
        self.slider.valueChanged.connect(self._on)
        self._on(val, emit=False)

    def _on(self, v: int, emit: bool = True) -> None:
        self.box.setText(f"{v}{self.suffix}")
        if emit:
            self.changed.emit(v)


class ThemeEditor(QFrame):
    """Редактор темы: цвета элементов интерфейса поверх текущей светлой / тёмной темы.
    Сама тема не меняется: выбранные цвета лежат отдельно (USER_COLORS) и сохраняются в настройках.
    Внизу кружки: стандартные цвета и сохранённые свои темы (ПКМ: удалить)."""
    PAD = 0          # встроен в окно настроек: своей тени и поля вокруг нет
    MAX_SAVED = 7

    def __init__(self, dlg: "SettingsDialog"):
        super().__init__(dlg)                    # обычный дочерний виджет, не отдельное окно
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.dlg = dlg
        self._open_role = None
        outer = QVBoxLayout(self)
        outer.setContentsMargins(26, 20, 26, 0)
        outer.setSpacing(3)
        title = QLabel("Редактор темы")
        title.setObjectName("h1")
        hint = QLabel("Цвета элементов интерфейса поверх текущей темы")
        hint.setObjectName("muted")
        outer.addWidget(title)
        outer.addWidget(hint)
        outer.addSpacing(14)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll.setStyleSheet("QScrollArea, QScrollArea > QWidget > QWidget { background: transparent; border: none; }")
        self.body = QWidget()
        bl = QVBoxLayout(self.body)
        bl.setContentsMargins(0, 0, 0, 14)
        bl.setSpacing(14)

        self.rows, self.holders = {}, {}

        def add_role(card, role: str, label: str, desc: str | None = None) -> None:
            pill = _ColorPill(role_color(role))
            pill.row_width = 112
            pill.clicked.connect(lambda r=role: self.toggle_picker(r))
            card.row(label, pill, desc)
            self.rows[role] = pill

        # --- Визуальный стиль ---
        vis = Card("Визуальный стиль")
        self.mode = _ModeTiles()
        self.mode.picked.connect(self.set_mode)
        self.mode.row_width = 2 * _ModeTiles.W + _ModeTiles.GAP
        vis.row("Режим", self.mode, "светлая или тёмная тема")

        self.theme_tiles = _ThemeTiles()
        self.theme_tiles.picked.connect(self.on_theme_pick)
        self.theme_tiles.menu_requested.connect(self.tile_menu)
        self.theme_tiles.row_width = round(_ThemeTiles.VISIBLE * (_ThemeTiles.W + _ThemeTiles.GAP) - _ThemeTiles.GAP)
        vis.row("Тема", self.theme_tiles, "листай колёсиком мыши; правый клик по своей: удалить")

        self.name = QLineEdit()
        self.name.setPlaceholderText("Название темы")
        self.name.setMaxLength(24)
        self.name.returnPressed.connect(self.create_theme)
        make = QPushButton("Сохранить")
        make.setStyleSheet("padding: 6px 12px; font-size: 12px; border-radius: 8px;")
        make.setCursor(Qt.CursorShape.PointingHandCursor)
        make.clicked.connect(self.create_theme)
        name_box = QWidget()
        nl = QHBoxLayout(name_box)
        nl.setContentsMargins(0, 0, 0, 0)
        nl.setSpacing(8)
        nl.addWidget(self.name, 1)
        nl.addWidget(make)
        name_box.row_width = 250
        vis.row("Сохранить как тему", name_box, "запомнить текущие цвета")

        add_role(vis, "accent", "Акцент", "цвет визуальных модулей")
        add_role(vis, "bg", "Фон", "основной цвет окна")
        add_role(vis, "text", "Текст")

        self.font_combo = FlyCombo()
        self.font_combo.row_width = 200
        fams = set(QFontDatabase.families())
        wanted = list(BUNDLED_FONTS) + ["Inter", "Noto Sans", "Roboto", "Ubuntu", "Open Sans", "Montserrat", "Fira Sans",
                                         "Source Sans 3", "DejaVu Sans", "Liberation Sans", "Segoe UI", "JetBrains Mono"]
        seen = []
        for f in wanted:
            if f in fams and f not in seen:
                seen.append(f)
        cur_font = VISUAL.get("font") or ""
        if cur_font and cur_font not in seen:
            seen.append(cur_font)
        self.font_combo.addItem("По умолчанию", "")
        for f in seen:
            self.font_combo.addItem(f, f)
        self.font_combo.setCurrentIndex(max(0, self.font_combo.findData(cur_font)))
        self.font_combo.currentIndexChanged.connect(self.pick_font)
        vis.row("Шрифт", self.font_combo, "каким шрифтом написан текст")
        bl.addWidget(vis)

        # --- остальные цвета ---
        more = Card("Дополнительные цвета")
        for role, label in THEME_ROLES:
            if role not in ("accent", "bg", "text"):
                add_role(more, role, label)
        bl.addWidget(more)

        # --- Задний фон ---
        back = Card("Задний фон")
        self.pics = _PicTiles()
        self.pics.picked.connect(self.pick_pic)
        self.pics.row_width = 3 * _PicTiles.S + 2 * _PicTiles.GAP
        back.row("Картинка", self.pics, "за всем окном, размыта под цветом окна")
        self.blur = _ValSlider(0, 30, VISUAL["bg_blur"], " px")
        self.blur.changed.connect(self.on_blur)
        back.row("Размытие", self.blur)
        self.alpha = _ValSlider(0, 100, VISUAL["bg_alpha"], "%")
        self.alpha.changed.connect(self.on_alpha)
        back.row("Цвет окна поверх картинки", self.alpha, "меньше процент: картинка заметнее")
        bl.addWidget(back)

        # --- Liquid glass ---
        glass = Card("Liquid glass")
        self.g_on = Toggle()
        self.g_on.setChecked(bool(VISUAL["glass_on"]))
        self.g_on.toggled.connect(self.on_glass_on)
        glass.row("Стеклянные плашки", self.g_on, "полупрозрачные карточки с бликом и кромкой")
        self.g_aur = Toggle()
        self.g_aur.setChecked(bool(VISUAL["glass_aurora"]))
        self.g_aur.toggled.connect(self.on_aurora)
        glass.row("Свечение фона", self.g_aur, "без картинки: цветные пятна, сквозь которые видно стекло")
        self.g_sliders = []
        for key, label, desc, lo in (("glass_opacity", "Плотность", "меньше процент: сквозь стекло виднее фон", 10),
                                     ("glass_frost", "Матовость", "размытие фона под плашкой (нужна картинка)", 0),
                                     ("glass_refract", "Преломление", "искажение у краёв, как у линзы (нужна картинка)", 0),
                                     ("glass_shine", "Блик", "свет на поверхности стекла", 0),
                                     ("glass_rim", "Кромка", "светлый край и внутренняя линия", 0)):
            sl = _ValSlider(lo, 100, VISUAL[key], "%")
            sl.changed.connect(lambda v, k=key: self.on_glass(k, v))
            glass.row(label, sl, desc)
            self.g_sliders.append(sl)
        for sl in self.g_sliders + [self.g_aur]:
            sl.setEnabled(bool(VISUAL["glass_on"]))
        bl.addWidget(glass)
        self._g_timer = QTimer(self)
        self._g_timer.setSingleShot(True)
        self._g_timer.timeout.connect(save_visual)
        self._bd_timer = QTimer(self)
        self._bd_timer.setSingleShot(True)
        self._bd_timer.timeout.connect(self._bd_apply)
        self.update_back_state()
        bl.addStretch(1)
        self.scroll.setWidget(self.body)
        outer.addWidget(self.scroll, 1)

        self.xbtn = QPushButton(self)               # маленький крестик в углу
        self.xbtn.setObjectName("winbtn")
        self.xbtn.setIcon(QIcon(draw_icon("close", MUTED, 14)))
        self.xbtn.setFixedSize(24, 24)
        self.xbtn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.xbtn.clicked.connect(self.close)
        self.rebuild_dots()
        self.dlg.installEventFilter(self)       # следим за движением и размером окна настроек
        self.dock()

    # --- положение: ровно на месте правой части окна настроек ---
    def dock(self) -> None:
        rw = getattr(self.dlg, "_rw", None)
        if rw is not None:
            self.setGeometry(rw.geometry().adjusted(0, 1, -1, -1))   # на 1px внутрь: рамка окна остаётся видна
            self.raise_()

    def eventFilter(self, obj, e):
        if obj is self.dlg and e.type() in (QEvent.Type.Move, QEvent.Type.Resize):
            self.dock()
        return False

    def showEvent(self, e):
        self.dock()
        try:
            self.dlg.set_ghost(True)           # страницы настроек гаснут, пока открыт редактор
        except RuntimeError:
            pass
        self.setFocus()
        super().showEvent(e)

    def closeEvent(self, e):
        self.close_picker()
        try:
            self.dlg.set_ghost(False)          # редактор закрыт: страницы настроек появляются снова
        except RuntimeError:
            pass
        super().closeEvent(e)

    def resizeEvent(self, e):
        self.xbtn.move(self.width() - 26 - 24, 18)
        self.xbtn.raise_()

    # --- выбор цвета: отдельное всплывающее окно рядом с плашкой, страница вниз не растёт ---
    def close_picker(self) -> None:
        fl = getattr(self, "_picker", None)
        self._picker = None
        if fl is not None:
            try:
                fl.close()
                fl.deleteLater()
            except RuntimeError:
                pass

    def toggle_picker(self, role: str) -> None:
        self.close_picker()
        self._open_role = role
        fl = ColorFlyout(self, QColor(role_color(role)), getattr(self.dlg, "_k", 1.0))
        fl.panel.committed.connect(lambda hx, r=role: self.set_color(r, hx))
        self._picker = fl
        pill = self.rows[role]
        gp = pill.mapToGlobal(QPoint(0, 0))
        g, sh = self.dlg.frameGeometry(), getattr(self.dlg, "SHADOW", 0)
        b = QRect(g.left() + sh, g.top() + sh, g.width() - 2 * sh, g.height() - 2 * sh)
        scr = self.dlg.screen().availableGeometry() if self.dlg.screen() else None
        if scr is not None:
            b = b.intersected(scr)
        x = gp.x() - fl.width() + fl.PAD - 10                       # слева от плашки, поверх карточки
        if x + fl.PAD < b.left():
            x = gp.x() + pill.width() + 10 - fl.PAD                 # слева нет места: справа от плашки
        y = gp.y() + pill.height() // 2 - fl.height() // 2
        x = max(b.left() - fl.PAD, min(x, b.right() + 1 - fl.width() + fl.PAD))
        y = max(b.top() - fl.PAD, min(y, b.bottom() + 1 - fl.height() + fl.PAD))
        fl.move(x, y)
        fl.show()

    def _keep_picker(self) -> None:
        """После смены цвета стили перерисовываются и могут закрыть всплывающее окно: возвращаем его на место."""
        fl = getattr(self, "_picker", None)
        if fl is None:
            return
        try:
            if not fl.isVisible() and time.monotonic() - getattr(self, "_picker_t", 0) < 0.5:
                fl.show()
            if fl.isVisible():
                fl.retheme()
        except RuntimeError:
            self._picker = None

    def set_color(self, role: str, hx: str) -> None:
        USER_COLORS[role] = cn(QColor(hx))
        self.dlg.opts["theme_colors"] = dict(USER_COLORS)
        apply_overrides()
        self.persist()
        self._picker_t = time.monotonic()
        self.after_change()
        QTimer.singleShot(80, self._keep_picker)

    def after_change(self) -> None:
        restyle()
        self.dlg.refresh_accent()
        self.refresh()

    def refresh(self) -> None:
        for role, row in self.rows.items():
            row.color = role_color(role)
            row.update()
        self.mode.update()
        self.sync_theme_combo()
        self.xbtn.setIcon(QIcon(draw_icon("close", MUTED, 14)))
        self.update()

    # --- свои темы ---
    @staticmethod
    def tip(name, author) -> list:
        return [("Имя:", name), ("Автор:", author)]

    def themes(self) -> list:
        return self.dlg.opts["custom_themes"]

    def persist(self) -> None:
        save_theme_prefs(USER_COLORS, self.themes())

    def create_theme(self) -> None:
        name = self.name.text().strip() or f"Тема {len(self.themes()) + 1}"
        snap = {r: role_color(r) for r, _ in THEME_ROLES}
        rest = [t for t in self.themes() if t.get("name") != name]
        rest.append({"name": name, "author": linux_user(), "colors": snap, "visual": self._visual_snapshot(name)})
        self.dlg.opts["custom_themes"] = rest[-self.MAX_SAVED:]
        self.name.clear()
        self.persist()
        self._gc_theme_pics()
        self.rebuild_dots()

    # картинка фона, размытие, стекло и свечение хранятся внутри сохранённой темы
    GLASS_OFF = {"glass_on": 0, "glass_aurora": 0}
    THEME_VISUAL_KEYS = ("bg_blur", "bg_alpha", "glass_on", "glass_opacity", "glass_shine", "glass_rim",
                         "glass_frost", "glass_refract", "glass_aurora")

    def _visual_snapshot(self, name: str) -> dict:
        snap = {k: VISUAL[k] for k in self.THEME_VISUAL_KEYS}
        snap["bg_file"] = ""
        src = VISUAL.get("bg_image") or ""
        if src and os.path.isfile(src):                 # у темы своя копия картинки: общая «backdrop.*» заменяется при загрузке другой
            dst_dir = DATA_DIR / "backgrounds"
            dst = dst_dir / f"theme_{zlib.crc32(name.encode('utf-8')):08x}{Path(src).suffix.lower()}"
            try:
                dst_dir.mkdir(parents=True, exist_ok=True)
                for old in dst_dir.glob(dst.stem + ".*"):
                    if old != dst:
                        old.unlink()
                if Path(src).resolve() != dst.resolve():
                    shutil.copy2(src, dst)
                snap["bg_file"] = str(dst)
            except OSError:
                snap["bg_file"] = src
        return snap

    def _gc_theme_pics(self) -> None:
        """Удаляет картинки тем, которых уже нет."""
        used = {Path(t["visual"]["bg_file"]).name for t in self.themes()
                if isinstance(t.get("visual"), dict) and t["visual"].get("bg_file")}
        used |= {Path(VISUAL[k]).name for k in ("bg_file", "bg_image") if VISUAL.get(k)}   # то, что сейчас включено, не трогаем
        try:
            for f in (DATA_DIR / "backgrounds").glob("theme_*"):
                if f.name not in used:
                    f.unlink()
        except OSError:
            pass

    def apply_visual(self, v: dict) -> None:
        """Включает фон и стекло, сохранённые вместе с темой, и сразу пишет их в config.json."""
        try:
            for k in self.THEME_VISUAL_KEYS:
                if k in v:
                    VISUAL[k] = int(v[k])
        except (TypeError, ValueError):
            return
        if "bg_file" in v:                                       # без этого ключа картинка остаётся как есть
            f = str(v.get("bg_file") or "")
            VISUAL["bg_file"] = VISUAL["bg_image"] = f if f and os.path.isfile(f) else ""
        save_visual()
        for sl, key in zip(self.g_sliders, ("glass_opacity", "glass_frost", "glass_refract", "glass_shine", "glass_rim")):
            self._set_slider(sl, VISUAL[key])
        self._set_slider(self.blur, VISUAL["bg_blur"])
        self._set_slider(self.alpha, VISUAL["bg_alpha"])
        for tg, key in ((self.g_on, "glass_on"), (self.g_aur, "glass_aurora")):
            tg.blockSignals(True)
            tg.setChecked(bool(VISUAL[key]))
            tg.blockSignals(False)
        for sl in self.g_sliders + [self.g_aur]:
            sl.setEnabled(bool(VISUAL["glass_on"]))
        self.dlg._bd_cache = None
        self.update_back_state()
        self._repaint_glass()

    @staticmethod
    def _set_slider(sl, v: int) -> None:
        sl.slider.blockSignals(True)
        sl.slider.setValue(v)
        sl.slider.blockSignals(False)
        sl._on(sl.slider.value(), emit=False)

    def rebuild_dots(self) -> None:
        """Список тем: «По умолчанию», готовые и сохранённые свои (плитки)."""
        self._themes_cols = ([None] + [dict(c) for _, c in BUILTIN_THEMES] +
                             [{r: c for r, c in (t.get("colors") or {}).items() if r in ROLE_VARS and _hex_ok(c)}
                              for t in self.themes()])
        self.refresh()

    def sync_theme_combo(self) -> None:
        """Подсвечивает плитку той темы, чьи цвета сейчас включены; свои несохранённые показываются отдельной плиткой."""
        cols_list = getattr(self, "_themes_cols", None)
        if cols_list is None:
            return
        idx = 0
        if USER_COLORS:
            idx = next((i for i, c in enumerate(cols_list) if i > 0 and c and
                        all(role_color(r).lower() == cn(QColor(v)).lower() for r, v in c.items())), -1)
        items = [("По умолчанию", None, "default")]
        items += [(name, cols_list[1 + i], "builtin") for i, (name, _) in enumerate(BUILTIN_THEMES)]
        items += [(t.get("name", ""), c, "saved") for t, c in zip(self.themes(), cols_list[1 + NB:])]
        if idx < 0:
            items.append(("Свои цвета", dict(USER_COLORS), "custom"))
            idx = len(items) - 1
        self.theme_tiles.set_items(items, idx)

    def on_theme_pick(self, idx: int) -> None:
        cols_list = getattr(self, "_themes_cols", [])
        if idx == 0:
            self.apply_visual(self.GLASS_OFF)
            self.reset_colors()
        elif 0 < idx < len(cols_list):
            cols = cols_list[idx]
            if cols.get("bg"):                              # светлая тема на тёмном режиме (и наоборот): режим меняется сам
                mode = "light" if QColor(cols["bg"]).lightnessF() >= 0.5 else "dark"
                if mode != THEME_NAME:
                    self.dlg.opts["theme"] = mode
                    set_theme(mode)
            if NB < idx <= NB + len(self.themes()):            # своя сохранённая тема: вместе с ней возвращаются фон и стекло
                vis = self.themes()[idx - 1 - NB].get("visual")
                self.apply_visual(vis if isinstance(vis, dict) else self.GLASS_OFF)
            else:                                              # готовая тема: стекло и свечение выключены
                self.apply_visual(self.GLASS_OFF)
            self.apply_theme(cols)

    def tile_menu(self, idx: int, pos: QPoint) -> None:
        if NB < idx <= NB + len(self.themes()):
            self.dot_menu(self.themes()[idx - 1 - NB].get("name"), pos)

    def delete_theme(self, idx: int | None = None) -> None:
        idx = self.theme_tiles.current if idx is None else idx
        if NB < idx <= NB + len(self.themes()):
            name = self.themes()[idx - 1 - NB].get("name")
            self.dlg.opts["custom_themes"] = [t for t in self.themes() if t.get("name") != name]
            self.persist()
            self._gc_theme_pics()
            self.rebuild_dots()

    def set_mode(self, name: str) -> None:
        """Светлая / тёмная тема: цвета фона и текста сбрасываются, чтобы смена была видна сразу."""
        if name == THEME_NAME:
            return
        self.dlg.opts["theme"] = name
        for r in ("bg", "text", "muted", "heading"):
            USER_COLORS.pop(r, None)
        self.dlg.opts["theme_colors"] = dict(USER_COLORS)
        save_theme_prefs(USER_COLORS, self.themes())
        set_theme(name)
        restyle()
        self.dlg.refresh_accent()
        self.refresh()

    # --- шрифт и задний фон ---
    def pick_font(self, idx: int) -> None:
        VISUAL["font"] = self.font_combo.itemData(idx) or ""
        save_visual()
        restyle()

    def update_back_state(self) -> None:
        on = backdrop_on()
        self.blur.setEnabled(on)
        self.alpha.setEnabled(on)
        self.pics.update()

    def pick_pic(self, kind: str) -> None:
        if kind == "none":
            VISUAL["bg_image"] = ""
        elif kind == "custom":
            f = VISUAL.get("bg_file") or ""
            if f and os.path.isfile(f):
                VISUAL["bg_image"] = f
            else:
                kind = "upload"
        if kind == "upload":
            path, _ = QFileDialog.getOpenFileName(self.dlg, "Выбери картинку для фона", str(Path.home()),
                                                  "Картинки (*.png *.jpg *.jpeg *.webp *.bmp)")
            if not path or QImage(path).isNull():
                return
            dst_dir = DATA_DIR / "backgrounds"
            dst_dir.mkdir(parents=True, exist_ok=True)
            dst = dst_dir / ("backdrop" + Path(path).suffix.lower())
            try:
                if Path(path).resolve() != dst.resolve():
                    for old in dst_dir.glob("backdrop.*"):        # одна картинка: старые копии не копятся
                        old.unlink()
                    shutil.copy2(path, dst)
            except OSError:
                dst = Path(path)
            VISUAL["bg_file"] = VISUAL["bg_image"] = str(dst)
        save_visual()
        self.dlg._bd_cache = None
        self.update_back_state()
        self._bd_apply()

    def _repaint_glass(self) -> None:
        for f in self.dlg.findChildren(GlassFrame):
            f.update()

    def on_glass_on(self, on: bool) -> None:
        VISUAL["glass_on"] = 1 if on else 0
        for sl in self.g_sliders + [self.g_aur]:
            sl.setEnabled(on)
        self.dlg.update()
        self._repaint_glass()
        self._g_timer.start(300)

    def on_aurora(self, on: bool) -> None:
        VISUAL["glass_aurora"] = 1 if on else 0
        self.dlg.update()
        self._repaint_glass()
        self._g_timer.start(300)

    def on_glass(self, key: str, v: int) -> None:
        VISUAL[key] = v
        self._repaint_glass()                      # плашки перерисовываются сразу, на диск пишем, когда ползунок замер
        self._g_timer.start(300)

    def on_blur(self, v: int) -> None:
        VISUAL["bg_blur"] = v
        self.dlg.update()                          # размытие перерисовывается сразу
        self._bd_timer.start(200)

    def on_alpha(self, v: int) -> None:
        VISUAL["bg_alpha"] = v
        self.dlg.update()
        self._bd_timer.start(200)                  # боковая панель перекрашивается чуть позже, когда ползунок остановился

    def _bd_apply(self) -> None:
        save_visual()
        restyle()
        self.dlg.update()

    def apply_theme(self, cols: dict) -> None:
        set_user_colors(cols)
        self.dlg.opts["theme_colors"] = dict(USER_COLORS)
        self.persist()
        self.after_change()

    def reset_colors(self) -> None:
        self.apply_theme({})

    def dot_menu(self, name, pos: QPoint) -> None:
        menu = QMenu(self)
        act = menu.addAction("Удалить тему")
        if menu.exec(pos) == act:
            self.dlg.opts["custom_themes"] = [t for t in self.themes() if t.get("name") != name]
            self.persist()
            self._gc_theme_pics()
            self.rebuild_dots()

    # --- окно ---
    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(e)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        if backdrop_on() or aurora_on() or QColor(BG).alpha() < 255:
            return                                 # фон рисует само окно настроек (картинка или прозрачный фон) 
        rad = 14 * getattr(self.dlg, "_k", 1.0)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(BG))                     # тот же фон, что у окна; скруглены только правые углы
        p.drawRoundedRect(QRectF(-rad - 2, 0, self.width() + rad + 2, self.height()), rad, rad)


class ChoiceFlyout(QFrame):
    """Маленькое всплывающее окно со списком вариантов справа от меню профиля
    (как «Безопасный режим» → «Авто» / «Всегда спрашивать»). Выбранный вариант отмечен галочкой."""
    PAD = 14
    WIDTH = 220

    def __init__(self, menu: "ProfileMenu", items: list, current, on_pick, k: float = 1.0, note: str = ""):
        super().__init__(menu, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setMouseTracking(True)                  # пока окошко открыто, оно получает всю мышь: следим, куда она ушла
        self.menu, self._bg = menu, None
        sz = lambda v: max(1, round(v * k))
        self.setFixedWidth(sz(self.WIDTH) + 2 * self.PAD)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(self.PAD + sz(6), self.PAD + sz(8), self.PAD + sz(6), self.PAD + sz(8))
        lay.setSpacing(sz(2))
        for label, value in items:
            row = MenuRow(None, label, chevron=False, checked=(current == value), k=k)
            if note:
                row.setToolTip(note)
            row.setMouseTracking(True)
            row.clicked.connect(lambda v=value: on_pick(v))
            lay.addWidget(row)
        if LANG == "en":
            retranslate(self)
        self.adjustSize()

    def box(self) -> QRectF:
        return QRectF(self.PAD, self.PAD, self.width() - 2 * self.PAD, self.height() - 2 * self.PAD)

    def blur_under(self, dlg: QWidget) -> None:
        """Снимок окна настроек под окошком, размытый и затемнённый: фон как у меню профиля."""
        tl = dlg.mapToGlobal(QPoint(0, 0))
        try:
            shot = dlg.grab(QRect(QPoint(self.x() - tl.x(), self.y() - tl.y()), self.size()))
            self._bg = blur_pixmap(shot) if not shot.isNull() else None
        except Exception:
            self._bg = None

    def mouseMoveEvent(self, e):
        if not self.box().contains(e.position()):    # мышь вне окошка: меню решает, переключить список или оставить
            self.menu.flyout_outside(e.globalPosition().toPoint())
        super().mouseMoveEvent(e)

    def hideEvent(self, e):
        super().hideEvent(e)
        self.menu._choice_hidden(self)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        box = self.box()
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(self.PAD, 0, -1):          # мягкая тень
            p.setBrush(QColor(0, 0, 0, 4))
            p.drawRoundedRect(box.adjusted(-i, -i, i, i), 14 + i, 14 + i)
        path = QPainterPath()
        path.addRoundedRect(box, 14, 14)
        p.save()
        p.setClipPath(path)
        if self._bg is not None:                   # размытый фон
            p.drawPixmap(0, 0, self._bg)
        else:
            bg = QColor(POP_BG)
            bg.setAlpha(225)
            p.fillRect(box, bg)
        p.restore()
        p.setPen(QPen(QColor(POP_BORDER), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(box, 14, 14)


class ProfileMenu(QFrame):
    """Всплывающее меню профиля. Подменю открываются на месте этого же окна, без вложенных окон."""
    PAD = 14                 # поле под мягкую тень
    WIDTH = 280

    def __init__(self, dlg: "SettingsDialog"):
        super().__init__(dlg, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.dlg, self.opts = dlg, dlg.opts
        self._flyout = None
        self.login = linux_user()
        self.k = float(getattr(dlg, "_k", 1.0) or 1.0)             # масштаб окна настроек
        self.setFixedWidth(self.sz(self.WIDTH) + 2 * self.PAD)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(self.PAD, self.PAD, self.PAD, self.PAD)
        self.pages = QStackedWidget()
        outer.addWidget(self.pages)
        self.main, self.sub = QWidget(), QWidget()
        self.pages.addWidget(self.main)
        self.pages.addWidget(self.sub)
        self.main_l, self.sub_l = QVBoxLayout(self.main), QVBoxLayout(self.sub)
        for lay in (self.main_l, self.sub_l):
            lay.setContentsMargins(self.sz(6), self.sz(12), self.sz(6), self.sz(8))
            lay.setSpacing(0)
        self.build_main()
        self._main_h = self.main.sizeHint().height()               # считаем один раз: после смены темы sizeHint врёт
        self.pages.setFixedHeight(self._main_h)                    # подменю того же размера: окно не прыгает

    # --- вспомогательное ---
    def sz(self, v: float) -> int:
        """Размер в пикселях с учётом масштаба окна настроек."""
        return max(1, round(v * self.k))

    def css(self, qss: str) -> str:
        return scale_qss(qss, self.k)

    def mk_row(self, *a, **kw) -> "MenuRow":
        return MenuRow(*a, k=self.k, **kw)

    def rescale(self) -> None:
        """Окно настроек сменило размер: пересобираем меню под новый масштаб."""
        k = float(getattr(self.dlg, "_k", 1.0) or 1.0)
        if abs(k - self.k) < 1e-6:
            return
        ratio, self.k = k / self.k, k
        self._flyout_wanted = False
        self.close_choice()
        if self.flyout_open():
            self._flyout.close()
        self.setFixedWidth(self.sz(self.WIDTH) + 2 * self.PAD)
        for lay in (self.main_l, self.sub_l):
            lay.setContentsMargins(self.sz(6), self.sz(12), self.sz(6), self.sz(8))
        self.pages.setMinimumHeight(0)
        self.pages.setMaximumHeight(16777215)
        self.pages.setCurrentIndex(0)              # дальше нужна именно главная страница, а не подстраница
        self._main_h = max(1, round(self._main_h * ratio))     # пока раскладка не обновилась: по пропорции
        self.build_main(go_main=False)
        self.pages.setFixedHeight(self._main_h)    # точная высота измеряется позже, в _reanchor

    @staticmethod
    def clear(lay: QVBoxLayout) -> None:
        while lay.count():
            item = lay.takeAt(0)
            w = item.widget()          # спейсеры (addSpacing) виджета не имеют; и после setParent(None) он уже None
            if w is not None:
                w.setParent(None)
                w.deleteLater()

    def scale_label(self) -> str:
        return next((l for l, v in SCALES if v == self.opts["char_scale"]), "Авто")

    def accent_hex(self) -> str:
        """Цвет квадрата в строке «Стиль»: текущий акцент, с учётом цветов из редактора темы."""
        if USER_COLORS.get("accent"):
            return QColor(ACCENT).name()
        acc = self.opts["accent"]
        if isinstance(acc, str) and acc.startswith("#") and QColor(acc).isValid():
            return QColor(acc).name()
        return next((a[1] for a in ACCENTS if a[0] == acc), ACCENTS[0][1])

    def open_data(self) -> None:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        try:
            subprocess.Popen(["xdg-open", str(DATA_DIR)], stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, start_new_session=True)
        except OSError as e:
            print("Не открылась папка данных:", e, file=sys.stderr)
        self.close()

    # --- главная страница ---
    def build_main(self, go_main: bool = True) -> None:
        self.clear(self.main_l)
        head = QWidget()
        hl = QHBoxLayout(head)
        hl.setContentsMargins(self.sz(10), 0, self.sz(10), self.sz(12))
        hl.setSpacing(self.sz(12))
        av = QLabel()
        av.setPixmap(round_avatar(linux_avatar(), self.sz(48), letter=self.login))
        av.setFixedSize(self.sz(48), self.sz(48))
        col = QVBoxLayout()
        col.setSpacing(self.sz(1))
        nm = QLabel(self.login)
        nm.setStyleSheet(self.css(f"color: {STRONG}; font-size: 15px; font-weight: 700;"))
        nm.setText(nm.fontMetrics().elidedText(self.login, Qt.TextElideMode.ElideRight, self.sz(170)))
        st = QLabel("Mimi Typh  ·  в сети")
        st.setStyleSheet(self.css(f"color: {MUTED}; font-size: 12px;"))
        link = LinkLabel("Открыть папку данных")
        link.setStyleSheet(self.css(f"color: {ACCENT}; font-size: 12px; font-weight: 600;"))
        link.clicked.connect(self.open_data)
        col.addWidget(nm)
        col.addWidget(st)
        col.addWidget(link)
        hl.addWidget(av)
        hl.addLayout(col, 1)
        self.main_l.addWidget(head)
        self.main_l.addSpacing(self.sz(4))

        r_scale = self.mk_row("scale", "Масштаб Мими", value=self.scale_label())
        self.bind_choice(r_scale, "Масштаб Мими", "char_scale", [(l, v, None) for l, v in SCALES],
            "Размер персонажа на рабочем столе. Применится после «Сохранить».")
        size_label = next((l for l, v in WIN_SCALES if v == self.opts["win_size"]), "100%")
        r_size = self.mk_row("window", "Размер окна", value=size_label)
        self.bind_choice(r_size, "Размер окна", "win_size", [(l, v, None) for l, v in WIN_SCALES],
            "Применяется сразу, окно остаётся по центру. Авто: как 100%. "
            "Всё содержимое масштабируется вместе с окном.")
        lang_label = next((l for l, v in LANGS if v == self.opts["lang"]), "Русский")
        r_lang = self.mk_row("globe", "Язык", value=lang_label)
        self.bind_choice(r_lang, "Язык", "lang", [(l, v, None) for l, v in LANGS],
            "Язык интерфейса. Голос и распознавание остаются русскими.")
        r_style = self.mk_row("drop", "Стиль", swatch=self.accent_hex(), gear=True)
        self._style_row = r_style
        r_style.clicked.connect(self.open_theme_editor)
        r_style.gear_clicked.connect(self.toggle_theme)
        r_style.setToolTip("Солнце / луна: светлая и тёмная тема")
        short = "Всегда" if self.opts["safe_mode"] == "always" else "Авто"
        r_safe = self.mk_row("shield", "Безопасный режим", value=short)
        self.bind_choice(r_safe, "Безопасный режим", "safe_mode", [(l, v, None) for l, v in SAFE_MODES],
            "Авто: знакомые команды выполняются сразу, незнакомые после «да». "
            "Всегда спрашивать: любая команда и запуск приложений только после «да».")
        tg = Toggle()
        tg.setChecked(bool(self.opts["keep_memory"]))
        tg.toggled.connect(lambda on: self.opts.__setitem__("keep_memory", on))
        r_mem = self.mk_row("clock", "Сохранять историю", chevron=False, toggle=tg)
        dv = Toggle()
        dv.setChecked(dev_is_on())                 # показываем реальное состояние: консоль могли закрыть крестиком
        dv.toggled.connect(set_dev_mode)
        r_dev = self.mk_row("terminal", "Режим разработчика", chevron=False, toggle=dv)
        r_about = self.mk_row("info", "О программе")
        r_about.clicked.connect(self.about)
        for r in (r_scale, r_size, r_lang, r_style, r_safe, r_mem, r_dev):
            self.main_l.addWidget(r)
        self.main_l.addSpacing(self.sz(6))
        self.main_l.addWidget(hline("sep"))
        self.main_l.addSpacing(self.sz(6))
        self.main_l.addWidget(r_about)
        self.main_l.addStretch(1)
        if LANG == "en":
            retranslate(self.main)
        if go_main:
            self.pages.setCurrentIndex(0)
            if getattr(self, "_anchor", None) is not None:
                self.fit_height(self._main_h)

    # --- подстраницы ---
    def sub_header(self, title: str) -> None:
        self.clear(self.sub_l)
        back = self.mk_row(None, "‹   " + title, chevron=False, bold=True)
        back.clicked.connect(lambda: self.pages.setCurrentIndex(0))
        self.sub_l.addWidget(back)
        self.sub_l.addSpacing(self.sz(4))
        self.sub_l.addWidget(hline("sep"))
        self.sub_l.addSpacing(self.sz(6))

    def bind_choice(self, row: "MenuRow", title: str, key: str, items: list, note: str = "") -> None:
        """Список вариантов открывается, когда мышь наведена на строку (и по клику тоже)."""
        row.choice_args = (title, key, items, note)
        row.clicked.connect(lambda r=row: self.open_choice(r))
        row.hovered.connect(lambda r=row: QTimer.singleShot(90, lambda: self._hover_open(r)))

    def _hover_open(self, row: "MenuRow") -> None:
        try:
            if row.hover and self.isVisible():       # за 90 мс мышь не ушла со строки (проходом мимо не открываем)
                self.open_choice(row)
        except RuntimeError:                         # строка уже пересобрана
            pass

    def open_choice(self, row: "MenuRow") -> None:
        title, key, items, note = row.choice_args
        self.choose(title, key, items, note, anchor=row)

    def _row_at(self, gp: QPoint):
        """Строка меню под точкой экрана (не строка из окошка вариантов), иначе None."""
        w = QApplication.widgetAt(gp)
        while w is not None and not isinstance(w, MenuRow):
            w = w.parentWidget()
        return w if (w is not None and w.window() is self) else None

    def _sync_hover(self, gp: QPoint | None = None) -> None:
        """Пока открыто окошко вариантов, оно перехватывает мышь и строки меню не получают «мышь ушла»:
        подсветку наведения ставим сами по настоящему положению курсора."""
        row = self._row_at(gp if gp is not None else QCursor.pos())
        for r in self.findChildren(MenuRow):
            if r.window() is self and r.hover != (r is row):
                r.hover = r is row
                r.update()

    def flyout_outside(self, gp: QPoint) -> None:
        """Мышь вне окошка вариантов (оно перехватывает мышь): переключаем список, закрываем или оставляем."""
        row = self._row_at(gp)
        self._sync_hover(gp)
        fl = getattr(self, "_choice", None)
        if row is None:
            inside = self.frameGeometry().contains(gp) or (fl is not None and fl.frameGeometry().contains(gp))
            if not inside:                           # курсор ушёл с меню и окошка: список закрывается, подсветка гаснет
                self.close_choice()
            return                                   # зазор или тень между ними: оставляем как есть
        if row is getattr(self, "_choice_row", None):
            return
        if hasattr(row, "choice_args"):
            self.open_choice(row)
        else:
            self.close_choice()                      # обычная строка меню: список закрывается

    def _choice_hidden(self, fl) -> None:
        if fl is None or getattr(self, "_choice", None) is not fl:
            return
        self._choice = None
        row, self._choice_row = getattr(self, "_choice_row", None), None
        if row is not None:
            try:
                row.sticky = False
                row.update()
            except RuntimeError:
                pass
        QTimer.singleShot(0, self._sync_hover)       # подсветка по тому, где курсор сейчас

    def close_choice(self) -> None:
        fl = getattr(self, "_choice", None)
        if fl is not None:
            try:
                fl.close()
                fl.deleteLater()
            except RuntimeError:
                pass
            self._choice_hidden(fl)

    def choose(self, title: str, key: str, items: list, note: str = "", anchor=None) -> None:
        """Открывает список вариантов отдельным окошком справа от меню, на уровне нужной строки."""
        cur = getattr(self, "_choice", None)
        if cur is not None and getattr(self, "_choice_key", None) == key and cur.isVisible():
            return                                   # этот список уже открыт
        self.close_choice()
        fl = ChoiceFlyout(self, [(l, v) for l, v, _ in items], self.opts[key],
                          lambda v, k=key: self.choice_picked(k, v), self.k, note)
        self._choice, self._choice_key, self._choice_row = fl, key, anchor
        if anchor is not None:
            anchor.sticky = True                     # строка остаётся подсвеченной, пока список открыт
            anchor.update()
        b = self._bounds()                                           # окошко не выходит за окно программы
        row_y = anchor.mapToGlobal(QPoint(0, 0)).y() if anchor is not None else self.y() + self.PAD
        x = self.x() + self.width() - self.PAD + 6 - fl.PAD           # правее видимого края меню
        if x + fl.width() - fl.PAD > b.right() + 1:                  # справа не помещается: слева от меню
            xl = self.x() + self.PAD - 6 - fl.width() + fl.PAD
            if xl + fl.PAD >= b.left():
                x = xl
        y = row_y - fl.PAD - self.sz(8)                              # первый вариант на уровне строки
        x = max(b.left() - fl.PAD, min(x, b.right() + 1 - fl.width() + fl.PAD))
        y = max(b.top() - fl.PAD, min(y, b.bottom() + 1 - fl.height() + fl.PAD))
        fl.move(x, y)
        fl.blur_under(self.dlg)
        fl.show()

    def choice_picked(self, key: str, value) -> None:
        self.close_choice()
        self.pick(key, value)
        if key != "win_size":                        # при смене размера окна меню встаёт на место само (_reanchor)
            QTimer.singleShot(60, self._keep_open)   # на случай, если закрытие окошка закрыло и меню

    def toggle_theme(self) -> None:
        new = "light" if THEME_NAME == "dark" else "dark"
        self.opts["theme"] = new
        for r in ("bg", "text", "muted", "heading"):      # смена светлой / тёмной видна сразу
            USER_COLORS.pop(r, None)
        self.opts["theme_colors"] = dict(USER_COLORS)
        save_theme_prefs(USER_COLORS, self.opts["custom_themes"])
        set_theme(new)
        restyle()
        self.dlg.refresh_accent()
        self.build_main()
        QTimer.singleShot(60, self._keep_open)

    def _bounds(self) -> QRect:
        """Видимая часть окна настроек (без поля под тень) в экранных координатах, в пределах экрана."""
        dtl = self.dlg.mapToGlobal(QPoint(0, 0))
        sh = getattr(self.dlg, "SHADOW", 0)
        b = QRect(dtl.x() + sh, dtl.y() + sh, self.dlg.width() - 2 * sh, self.dlg.height() - 2 * sh)
        scr = self.dlg.screen().availableGeometry() if self.dlg.screen() else None
        if scr is not None:
            b = b.intersected(scr) if b.isValid() else scr
        return b

    def fit_height(self, h: int) -> None:
        """Подгоняет высоту под страницу и держит низ меню у низа профиля."""
        self.pages.setFixedHeight(h)
        if self.isVisible() and getattr(self, "_anchor", None) is not None and not self.flyout_open():
            self.popup_at(self._anchor)

    def flyout_open(self) -> bool:
        return self._flyout is not None and self._flyout.isVisible()

    def open_picker(self) -> None:
        """Колор пикер в отдельном окне правее меню, верхом на уровне строки «Стиль»."""
        if self.flyout_open():
            self._flyout_wanted = False
            self._flyout.close()
            return
        self.show_flyout()

    def show_flyout(self) -> None:
        if self._flyout is not None:
            self._flyout.deleteLater()
        fl = ColorFlyout(self, QColor(ACCENT), self.k)
        fl.panel.committed.connect(self.apply_accent)
        self._flyout = fl
        b = self._bounds()                                           # окно пикера не выходит за окно программы
        gp = self._style_row.mapToGlobal(QPoint(0, 0))
        x = self.x() + self.width() - self.PAD + 8 - fl.PAD          # правее видимого края меню
        if x + fl.width() - fl.PAD > b.right() + 1:                  # справа не помещается: слева от меню
            xl = self.x() + self.PAD - 8 - fl.width() + fl.PAD
            if xl + fl.PAD >= b.left():
                x = xl
        y = gp.y() - fl.PAD - 6                                      # верх на уровне строки «Стиль»
        x = max(b.left() - fl.PAD, min(x, b.right() + 1 - fl.width() + fl.PAD))
        y = max(b.top() - fl.PAD, min(y, b.bottom() + 1 - fl.height() + fl.PAD))
        fl.move(x, y)
        self._flyout_wanted = True
        fl.show()

    def apply_accent(self, hex_color: str) -> None:
        """Применяет цвет из пикера."""
        self.opts["accent"] = hex_color
        USER_COLORS.pop("accent", None)
        self.opts["theme_colors"] = dict(USER_COLORS)
        save_theme_prefs(USER_COLORS, self.opts["custom_themes"])
        set_accent(hex_color)
        restyle()
        self.dlg.refresh_accent()
        self.build_main()                          # обновить цвет в строке «Стиль»
        QTimer.singleShot(60, self._keep_open)

    def pick(self, key: str, value) -> None:
        self.opts[key] = value
        if key == "accent":
            USER_COLORS.pop("accent", None)
            self.opts["theme_colors"] = dict(USER_COLORS)
            save_theme_prefs(USER_COLORS, self.opts["custom_themes"])
            set_accent(value)
            restyle()
            self.dlg.refresh_accent()
            QTimer.singleShot(30, self._keep_open)   # смена стиля могла закрыть всплывающее меню
        elif key == "lang":
            set_lang(value)
            self.dlg.retranslate()
        elif key == "win_size":
            self.dlg.apply_win_size(value)
            self.rescale()                           # меню и пикер подстраиваются под новый размер окна
            QTimer.singleShot(60, self._reanchor)    # окно сдвинулось: меню встаёт к профилю заново
        self.build_main()

    def _reanchor(self) -> None:
        if getattr(self, "_anchor", None) is not None:
            if self.pages.currentIndex() == 0:     # к этому моменту новые строки уже показаны: высота настоящая
                self.main_l.invalidate()
                self.main_l.activate()
                h = self.main.sizeHint().height()
                if h > self.sz(100):
                    self._main_h = h
                    self.pages.setFixedHeight(h)
            self.layout().activate()
            self.popup_at(self._anchor)

    def _keep_open(self) -> None:
        """После смены стиля/темы: вернуть меню, если закрылось, и пересчитать размер."""
        if getattr(self, "_anchor", None) is None:
            return
        had_flyout = self._flyout is not None and getattr(self, "_flyout_wanted", False)
        if self.pages.currentIndex() == 0:
            self.pages.setFixedHeight(self._main_h)
        self.layout().activate()
        if not self.isVisible():
            self.popup_at(self._anchor)
        else:
            self._refresh_blur()                   # фон меню: снимок окна уже в новой теме
            self.update()
        if self.flyout_open():
            self._flyout.retheme()
        elif had_flyout:
            self.show_flyout()

    def open_theme_editor(self) -> None:
        self.hide()
        self.dlg.toggle_theme_editor()

    def about(self) -> None:
        self.hide()
        self.dlg.show_about()

    # --- показ и рисование ---
    def popup_at(self, anchor: QWidget) -> None:
        """Открывает меню справа от блока профиля, внутри окна настроек (низ по низу профиля)."""
        self._anchor = anchor
        self.layout().activate()
        self.adjustSize()
        gp = anchor.mapToGlobal(QPoint(0, 0))
        # границы — видимая часть окна настроек (без поля под тень), чтобы меню не вылезало за программу
        bounds = self._bounds()
        y = gp.y() + anchor.height() - self.height() + self.PAD      # низ меню по низу профиля
        x = gp.x() + anchor.width() + 2                              # справа от блока профиля, внутри окна
        side = "right"
        if x + self.width() - self.PAD > bounds.right():             # справа не помещается: пробуем слева
            x = gp.x() - 2 - self.width()
            side = "left"
        self.dlg.set_arrow(side)
        # видимая рамка меню (без поля тени) не выходит за окно программы
        x = max(bounds.left() - self.PAD, min(x, bounds.right() + 1 - self.width() + self.PAD))
        y = max(bounds.top() - self.PAD, min(y, bounds.bottom() + 1 - self.height() + self.PAD))
        self.move(x, y)
        self._refresh_blur()
        self.show()

    def hideEvent(self, e):
        super().hideEvent(e)
        self.close_choice()
        try:
            self.dlg.prof.set_open(False)   # меню закрылось: снимаем подсветку плашки
        except Exception:
            pass

    def _refresh_blur(self) -> None:
        """Снимок окна настроек под меню, размытый и затемнённый — фон как в референсе."""
        dlg_tl = self.dlg.mapToGlobal(QPoint(0, 0))
        local = QPoint(self.x() - dlg_tl.x(), self.y() - dlg_tl.y())
        try:
            shot = self.dlg.grab(QRect(local, self.size()))
            self._bg = blur_pixmap(shot) if not shot.isNull() else None
        except Exception:
            self._bg = None

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        box = QRectF(self.PAD, self.PAD, self.width() - 2 * self.PAD, self.height() - 2 * self.PAD)
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(self.PAD, 0, -1):          # мягкая тень
            p.setBrush(QColor(0, 0, 0, 4))
            p.drawRoundedRect(box.adjusted(-i, -i, i, i), 14 + i, 14 + i)
        path = QPainterPath()
        path.addRoundedRect(box, 14, 14)
        p.save()
        p.setClipPath(path)
        if getattr(self, "_bg", None) is not None:
            p.drawPixmap(box.topLeft(), self._bg)
        else:
            bg = QColor(POP_BG)
            bg.setAlpha(225)             # запасной вариант, если снимок не получился
            p.fillRect(box, bg)
        p.restore()
        p.setPen(QPen(QColor(POP_BORDER), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(box, 14, 14)


def mimi_wordmark(px: int = 62) -> QPixmap:
    """Надпись MIMI: белые буквы с объёмной тенью акцентного цвета (в духе экрана «О программе» neverlose)."""
    dpr = 2
    f = QFont()
    f.setFamilies(["Fredoka", "Baloo 2", "Nunito", "Inter", "Noto Sans", "DejaVu Sans"])
    f.setPixelSize(px)
    f.setWeight(QFont.Weight.Black)
    f.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing, 1.5)
    path = QPainterPath()
    path.addText(0, 0, f, "MIMI")
    br = path.boundingRect()
    depth = max(3, px // 13)
    w, h = int(br.width()) + depth + 10, int(br.height()) + depth + 10
    pm = QPixmap(w * dpr, h * dpr)
    pm.setDevicePixelRatio(dpr)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.translate(5 - br.x(), 5 - br.y())
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(ACCENT))
    for k in range(depth, 0, -1):                        # «выдавленная» тень
        p.drawPath(path.translated(k, k))
    p.setBrush(QColor("#ffffff"))
    p.drawPath(path)
    p.end()
    return pm


class BlurOverlay(QWidget):
    """Основа для экранов поверх окна настроек: размытый фон, скруглённые углы, закрытие по клику мимо и Esc."""

    def __init__(self, dlg: "SettingsDialog"):
        super().__init__(dlg)
        self.dlg = dlg
        m = 12                                                   # запас под размытие, чтобы края не светлели
        S = dlg.SHADOW
        box = dlg.rect().adjusted(S, S, -S, -S)
        pix = dlg.grab(box.adjusted(-m, -m, m, m))
        tint = QColor(BG)
        tint.setAlpha(175)
        pp = QPainter(pix)
        pp.fillRect(QRectF(0, 0, pix.width(), pix.height()), tint)
        pp.end()
        self.setGeometry(box)
        self.bg = QLabel(self)
        self.bg.setPixmap(pix)
        self.bg.setGeometry(-m, -m, box.width() + 2 * m, box.height() + 2 * m)
        blur = QGraphicsBlurEffect(self.bg)
        blur.setBlurRadius(14)
        self.bg.setGraphicsEffect(blur)
        path = QPainterPath()                                    # скруглённые углы окна
        path.addRoundedRect(QRectF(0, 0, box.width(), box.height()), 14, 14)
        self.setMask(QRegion(path.toFillPolygon().toPolygon()))
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)

    def open(self) -> None:
        self.show()
        self.raise_()
        self.setFocus()

    def close_about(self) -> None:
        self.hide()
        self.deleteLater()

    def mousePressEvent(self, e):
        if not self.box.geometry().contains(e.position().toPoint()):
            self.close_about()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_Escape, Qt.Key.Key_Return, Qt.Key.Key_Enter):
            self.close_about()
            e.accept()
        else:
            super().keyPressEvent(e)


class PresetNameOverlay(BlurOverlay):
    """Спрашивает имя пресета промта прямо в окне настроек, поверх размытого фона. Enter сохраняет, Esc и клик мимо отменяют."""
    BOX_W = 320

    def __init__(self, dlg: "SettingsDialog", name: str, on_ok):
        super().__init__(dlg)
        self._on_ok = on_ok
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.addStretch(1)
        self.box = QFrame()
        self.box.setObjectName("card")
        self.box.setFixedWidth(self.BOX_W)
        lay = QVBoxLayout(self.box)
        lay.setContentsMargins(18, 16, 18, 16)
        lay.setSpacing(10)
        title = QLabel(T("Сохранить пресет"))
        title.setStyleSheet(f"color: {STRONG}; font-size: 15px; font-weight: 600;")
        lay.addWidget(title)
        hint = QLabel(T("Имя пресета"))
        hint.setStyleSheet(f"color: {MUTED};")
        lay.addWidget(hint)
        self.edit = QLineEdit(name)
        lay.addWidget(self.edit)
        lay.addSpacing(4)
        row = QHBoxLayout()
        row.setSpacing(8)
        cancel = QPushButton(T("Отмена"))
        cancel.setObjectName("pickbtn")
        cancel.setCursor(Qt.CursorShape.PointingHandCursor)
        cancel.setAutoDefault(False)
        cancel.clicked.connect(self.close_about)
        ok = QPushButton(T("Сохранить"))
        ok.setCursor(Qt.CursorShape.PointingHandCursor)
        ok.setAutoDefault(False)
        ok.clicked.connect(self.submit)
        row.addWidget(cancel, 1)
        row.addWidget(ok, 1)
        lay.addLayout(row)
        hl = QHBoxLayout()
        hl.addStretch(1)
        hl.addWidget(self.box)
        hl.addStretch(1)
        outer.addLayout(hl)
        outer.addStretch(1)

    def open(self) -> None:
        super().open()
        self.edit.setFocus()
        self.edit.selectAll()

    def submit(self) -> None:
        name = self.edit.text().strip()
        if not name:
            return
        self.close_about()
        self._on_ok(name)

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            self.submit()
            e.accept()
        elif e.key() == Qt.Key.Key_Escape:
            self.close_about()
            e.accept()
        else:
            super().keyPressEvent(e)


class AboutOverlay(BlurOverlay):
    """«О программе» на всё окно настроек: размытый фон, логотип, карточки. Клик мимо карточек или Esc закрывают."""
    BOX_W = 300

    def __init__(self, dlg: "SettingsDialog", rows: list):
        super().__init__(dlg)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.addStretch(1)
        self.box = QWidget()
        self.box.setFixedWidth(self.BOX_W)
        lay = QVBoxLayout(self.box)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        logo = QLabel()
        logo.setPixmap(mimi_wordmark())
        logo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(logo)
        lay.addSpacing(6)
        chip = QLabel("Голосовой помощник")
        chip.setObjectName("valuebox")
        chip.setAlignment(Qt.AlignmentFlag.AlignCenter)
        chip.setStyleSheet("padding: 3px 12px;")
        crow = QHBoxLayout()
        crow.addStretch(1)
        crow.addWidget(chip)
        crow.addStretch(1)
        lay.addLayout(crow)
        lay.addSpacing(18)

        info = QFrame()
        info.setObjectName("card")
        il = QVBoxLayout(info)
        il.setContentsMargins(0, 4, 0, 4)
        il.setSpacing(0)
        for i, (k, v) in enumerate(rows):
            if i:
                il.addWidget(hline("rowsep"))
            r = QWidget()
            r.setFixedHeight(40)
            rl = QHBoxLayout(r)
            rl.setContentsMargins(16, 0, 16, 0)
            a = QLabel(k)
            a.setStyleSheet(f"color: {STRONG}; font-weight: 500;")
            b = QLabel()
            b.setStyleSheet(f"color: {ACCENT}; font-weight: 500;")
            b.setToolTip(v)
            b.setText(b.fontMetrics().elidedText(v, Qt.TextElideMode.ElideMiddle, 170))
            b.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            rl.addWidget(a)
            rl.addWidget(b, 1)
            il.addWidget(r)
        lay.addWidget(info)
        lay.addSpacing(14)

        acts = QFrame()
        acts.setObjectName("card")
        al = QVBoxLayout(acts)
        al.setContentsMargins(0, 2, 0, 2)
        al.setSpacing(0)
        r1 = MenuRow(None, "Сообщить об ошибке", chevron=False)
        r1.clicked.connect(self.report_issue)
        al.addWidget(r1)
        al.addWidget(hline("rowsep"))
        r2 = MenuRow(None, "Правила пользования")
        r2.clicked.connect(self.show_rules)
        al.addWidget(r2)
        lay.addWidget(acts)
        lay.addSpacing(16)
        foot = QLabel("Mimi Typh © 2026")
        foot.setAlignment(Qt.AlignmentFlag.AlignCenter)
        foot.setStyleSheet(f"color: {STRONG};")
        lay.addWidget(foot)

        hl = QHBoxLayout()
        hl.addStretch(1)
        hl.addWidget(self.box)
        hl.addStretch(1)
        outer.addLayout(hl)
        outer.addStretch(1)

    ISSUE_URL = "https://t.me/killauraupdate"

    def show_rules(self) -> None:
        self.close_about()
        self.dlg.show_rules()

    def report_issue(self) -> None:
        try:
            subprocess.Popen(["xdg-open", self.ISSUE_URL], stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, start_new_session=True)
        except OSError as e:
            print("Не открылась ссылка:", e, file=sys.stderr)
            import webbrowser
            webbrowser.open(self.ISSUE_URL)


RULES_DATE = "21 ноября 2026"
RULES = [
    "Относитесь к другим с уважением: без оскорблений, травли и выяснения личных отношений в чатах и обсуждениях проекта.",
    "Не публикуйте чужие личные данные без согласия. Свои секреты тоже берегите: API-ключ и файл data/config.json никому не показывайте.",
    "Не используйте помощника для противоправных действий, обмана, взлома и всего, что может навредить другим людям.",
    "Команды, которые Мими выполняет на вашем компьютере, выполняются на вашу ответственность. Если не уверены, оставьте безопасный режим включённым и не разрешайте незнакомые команды.",
    "Ответы ИИ могут быть неточными. Важное проверяйте сами и не опирайтесь на них в вопросах здоровья, права и денег.",
    "Не выдавайте себя за автора проекта или других пользователей.",
    "Без спама, флуда и рекламы сторонних сервисов в каналах проекта.",
    "Не распространяйте сборки и обновления от имени проекта без разрешения автора.",
]


class RulesOverlay(BlurOverlay):
    """Правила пользования: прокручиваемый текст на размытом фоне. «‹» возвращает в «О программе»."""

    def __init__(self, dlg: "SettingsDialog"):
        super().__init__(dlg)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.addStretch(1)
        self.box = QFrame()
        self.box.setObjectName("card")
        self.box.setFixedWidth(440)
        lay = QVBoxLayout(self.box)
        lay.setContentsMargins(0, 4, 0, 14)
        lay.setSpacing(0)
        back = MenuRow(None, "‹   Правила пользования", chevron=False, bold=True)
        back.clicked.connect(self.back)
        lay.addWidget(back)
        lay.addWidget(hline("rowsep"))
        html = "".join(f'<p style="margin: 0 0 10px 0;"><b style="color:{ACCENT}">{i}.</b>&nbsp; {t}</p>'
                       for i, t in enumerate(RULES, 1))
        html += (f'<p style="margin: 6px 0 0 0; color:{MUTED};">Нарушение правил может привести к блокировке в каналах '
                 f'проекта. Если считаете блокировку ошибочной, напишите через «Сообщить об ошибке».</p>')
        text = QLabel(html)
        text.setWordWrap(True)
        text.setTextFormat(Qt.TextFormat.RichText)
        text.setStyleSheet(f"color: {TEXT}; background: transparent; padding: 12px 18px 4px 18px;")
        area = QScrollArea()
        area.setWidgetResizable(True)
        area.setFrameShape(QFrame.Shape.NoFrame)
        area.setStyleSheet("QScrollArea { background: transparent; border: none; }")
        area.viewport().setStyleSheet("background: transparent;")
        area.setFixedHeight(380)
        area.setWidget(text)
        lay.addWidget(area)
        upd = QLabel(f"Обновлено: {RULES_DATE}")
        upd.setStyleSheet(f"color: {MUTED}; font-size: 11px; padding: 6px 18px 0 18px;")
        lay.addWidget(upd)
        hl = QHBoxLayout()
        hl.addStretch(1)
        hl.addWidget(self.box)
        hl.addStretch(1)
        outer.addLayout(hl)
        outer.addStretch(1)

    def back(self) -> None:
        self.close_about()
        self.dlg.show_about()


class SettingsDialog(QDialog):
    """Окно настроек в стиле neverlose: панель с иконками и группами слева, карточки справа."""
    # (группа, [(иконка, название страницы)])
    GROUPS = [("ОСНОВНОЕ", [("server", "Сервис"), ("mic", "Голос")]),
              ("ПЕРСОНАЖ", [("user", "Настройки", [("heart", "Характер"), ("eye", "Отрисовка")])]),
              ("СИСТЕМА", [("terminal", "Команды"), ("monitor", "Мониторинг")]),
              ("РАЗРАБОТЧИК", [("wave", "Журнал")])]     # последняя группа видна только в режиме разработчика

    SHADOW = 22      # поле вокруг окна под мягкую тень
    _k = 1.0         # текущий масштаб содержимого (1.0 = как в коде)
    _snap = None     # исходные размеры виджетов и раскладок: снимаются один раз, перед первым масштабированием

    def __init__(self, saved: dict, running: bool = False):
        super().__init__()
        self.setWindowTitle("Помощник — настройка")
        self.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        # WindowModal без родителя ничего не блокирует: консоль разработчика остаётся кликабельной
        # (ApplicationModal по умолчанию у exec() блокировал в ней «Копировать», «Очистить» и переключатель)
        self.setWindowModality(Qt.WindowModality.WindowModal)
        self.cfg = None
        set_lang(saved.get("lang", "ru"))
        # значения из меню профиля (сохраняются кнопкой «Сохранить»)
        self.opts = {"char_scale": float(saved.get("char_scale", 1.0) or 1.0),
                     "accent": saved.get("accent", ACCENT_NAME),
                     "safe_mode": saved.get("safe_mode", "auto"),
                     "keep_memory": bool(saved.get("keep_memory", True)),
                     "theme": saved.get("theme", THEME_NAME),
                     "theme_colors": dict(USER_COLORS),
                     "custom_themes": [t for t in saved.get("custom_themes", []) if isinstance(t, dict)],
                     "lang": LANG,
                     "win_size": next((v for _, v in WIN_SCALES if v == saved.get("win_size")), 1.0)}
        self.apply_win_size(self.opts["win_size"])
        self._theme0 = THEME_NAME       # отмена: возвращаем и тему
        self._accent0 = ACCENT_NAME     # если закрыть без сохранения, цвет вернётся
        self._colors0 = dict(USER_COLORS)   # и цвета из редактора темы
        self._dev0 = dev_is_on()        # и консоль разработчика тоже
        self.titles = []                  # названия страниц по порядку; пункт с вложенными («Настройки») сам страницей не является
        for _, items in self.GROUPS:
            for it in items:
                self.titles += [t for _, t in it[2]] if len(it) == 3 else [it[1]]

        # --- поля (те же, что и раньше) ---
        names = list(PRESETS)
        self.preset = FlyCombo()
        self.preset.addItems(names)
        self.preset.setCurrentText(saved.get("preset", names[0]))
        self.key = QLineEdit(saved.get("api_key", ""))
        self.key.setEchoMode(QLineEdit.EchoMode.Password)
        self.eye = self.key.addAction(QIcon(draw_icon("eye", "#7f8fa9", 18)),
                                      QLineEdit.ActionPosition.TrailingPosition)   # глаз справа в поле
        self.eye.setToolTip("Показать ключ")
        self.eye.triggered.connect(self.toggle_key)
        self.url = QLineEdit()
        self.model = ModelCombo(lambda: (PRESETS[self.preset.currentText()][0], self.url.text().strip(),
                                         self.key.text().strip()))
        self.model.row_width = 220                       # имена моделей длинные
        self.remember = Toggle()
        self.remember.setChecked(bool(saved.get("api_key")))
        self.engine = make_combo(ENGINES, saved.get("tts_engine", TTS_ENGINE))
        self.speaker = make_combo(SPEAKERS, saved.get("silero_speaker", SILERO_SPEAKER))
        self.pitch = StepSlider(PITCHES, saved.get("silero_pitch", SILERO_PITCH))
        self.rate = StepSlider(RATES, saved.get("silero_rate", SILERO_RATE))
        self.stt = make_combo(STT_ENGINES, saved.get("stt", "whisper"))
        mode0 = saved.get("char_mode", "static")
        if saved.get("use_model3d") and mode0 != "model3d":
            mode0 = "model3d"                              # прошлая версия хранила выбор 3D отдельным переключателем
        self.char_mode = make_combo(CHAR_MODES, mode0)
        self.char_gif_path = saved.get("char_gif", "")   # сменить GIF в настройках нельзя: берётся прежний или assets/character.gif
        # выбор 3D-модели: все .glb из assets/ и рядом с main.py + любой файл через «Выбрать…»
        self.model_combo = FlyCombo()
        self.model_combo.row_width = 220
        for mp in list_models():
            self.model_combo.addItem(mp.stem, str(mp))
        saved_model = saved.get("model_path", "")
        if saved_model and Path(saved_model).is_file() and self.model_combo.findData(saved_model) < 0:
            self.model_combo.addItem(Path(saved_model).stem, saved_model)
        if self.model_combo.count() == 0:
            self.model_combo.addItem("нет файлов .glb", "")
        self.model_combo.setCurrentIndex(max(self.model_combo.findData(saved_model), 0))
        self.model_anim = Toggle()                         # оживление модели: говорит / думает
        self.model_anim.setChecked(bool(saved.get("model_anim", MODEL_ANIM)))
        self.model_btn = QPushButton("Выбрать…")
        self.model_btn.setStyleSheet("padding: 7px 14px; font-size: 12px;")
        self.model_btn.clicked.connect(self.pick_model)
        self.model_combo.currentIndexChanged.connect(self.on_model_changed)
        # --- пресеты промта: несколько сохранённых "характеров", можно переключать/сохранять/удалять ---
        self.personas = load_personas()
        preset_names = list(self.personas.keys())
        cur_preset = saved.get("persona_name", preset_names[0])
        if cur_preset not in self.personas:
            cur_preset = preset_names[0]
        self.persona_combo = FlyCombo()
        self.persona_combo.addItems(preset_names)
        self.persona_combo.setCurrentText(cur_preset)
        self.persona_combo.row_width = 220
        self.persona_name_edit = QLineEdit(cur_preset)   # не показывается: хранит имя текущего пресета, имя спрашивается при сохранении

        self.persona = QPlainTextEdit(saved.get("persona") or self.personas.get(cur_preset, PERSONA))
        self.persona.setMinimumHeight(190)

        def _preset_selected(name: str) -> None:
            text = self.personas.get(name)
            if text is not None:
                self.persona.setPlainText(text)
                self.persona_name_edit.setText(name)

        def _preset_save() -> None:
            def done(name: str) -> None:
                self.persona_name_edit.setText(name)
                self.personas[name] = self.persona.toPlainText()
                save_personas(self.personas)
                if self.persona_combo.findText(name) < 0:
                    self.persona_combo.addItem(name)
                self.persona_combo.blockSignals(True)
                self.persona_combo.setCurrentText(name)
                self.persona_combo.blockSignals(False)

            old = getattr(self, "_preset_ov", None)
            if old is not None:
                try:
                    old.close_about()
                except RuntimeError:
                    pass
            self._preset_ov = PresetNameOverlay(self, self.persona_name_edit.text().strip() or "Default", done)
            self._preset_ov.open()

        def _preset_load() -> None:
            _preset_selected(self.persona_combo.currentText())

        def _preset_delete() -> None:
            name = self.persona_combo.currentText()
            if len(self.personas) <= 1:
                return                                    # хотя бы один пресет должен остаться
            self.personas.pop(name, None)
            save_personas(self.personas)
            i = self.persona_combo.currentIndex()
            self.persona_combo.removeItem(i)
            _preset_selected(self.persona_combo.currentText())

        def _preset_import() -> None:
            path, _ = QFileDialog.getOpenFileName(self, "Импорт промта", str(Path.home()),
                                                   "Текст (*.txt);;Все файлы (*)")
            if not path:
                return
            try:
                text = Path(path).read_text(encoding="utf-8")
            except OSError as e:
                self.err.setText(f"Не удалось прочитать файл: {e}")
                return
            self.persona.setPlainText(text)
            self.persona_name_edit.setText(Path(path).stem)

        def _preset_export() -> None:
            default = str(Path.home() / f"{self.persona_name_edit.text().strip() or 'Default'}.txt")
            path, _ = QFileDialog.getSaveFileName(self, "Экспорт промта", default, "Текст (*.txt)")
            if not path:
                return
            try:
                Path(path).write_text(self.persona.toPlainText(), encoding="utf-8")
            except OSError as e:
                self.err.setText(f"Не удалось сохранить файл: {e}")

        self.persona_combo.currentTextChanged.connect(_preset_selected)

        def _mini_btn(text: str, slot) -> QPushButton:
            b = QPushButton(text)
            b.setStyleSheet("padding: 7px 14px; font-size: 12px;")
            b.clicked.connect(slot)
            return b

        def _icon_btn(icon_name: str, tooltip: str, slot, danger: bool = False) -> QPushButton:
            b = QPushButton()
            b.setToolTip(tooltip)
            if danger:
                b.setStyleSheet("background-color: #e5484d;")
            b.setIcon(QIcon(draw_icon(icon_name, "#ffffff", 16)))
            b.setIconSize(QSize(16, 16))
            b.setFixedSize(34, 34)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.clicked.connect(slot)
            return b

        self.persona_row = QWidget()
        prow = QHBoxLayout(self.persona_row)
        prow.setContentsMargins(0, 0, 0, 0)
        prow.setSpacing(8)
        prow.addWidget(_icon_btn("import", "Импорт из файла", _preset_import))
        prow.addWidget(_icon_btn("export", "Экспорт в файл", _preset_export))
        prow.addWidget(_icon_btn("trash", "Удалить пресет", _preset_delete, danger=True))
        prow.addStretch(1)
        prow.addWidget(_mini_btn("Сохранить", _preset_save))
        prow.addWidget(_mini_btn("Загрузить", _preset_load))
        self.shell = Toggle()
        self.shell.setChecked(bool(saved.get("shell", False)))
        self.err = QLabel()
        self.err.setObjectName("err")
        self.err.setWordWrap(True)

        # --- каркас: слева панель, справа верхняя полоса, страницы и низ ---
        root = QHBoxLayout(self)
        root.setContentsMargins(self.SHADOW, self.SHADOW, self.SHADOW, self.SHADOW)
        root.setSpacing(0)

        side = QFrame()
        side.setObjectName("side")
        side.setFixedWidth(220)
        sl = QVBoxLayout(side)
        sl.setContentsMargins(14, 20, 14, 14)
        sl.setSpacing(3)
        head = QHBoxLayout()
        head.setContentsMargins(4, 0, 0, 0)
        head.setSpacing(11)
        badge = QLabel()
        badge.setPixmap(brand_badge(36))
        badge.setFixedSize(36, 36)
        title_box = QVBoxLayout()
        title_box.setSpacing(0)
        logo = QLabel("Mimi")
        logo.setObjectName("logo")
        sub = QLabel("голосовой помощник")
        sub.setObjectName("muted")
        title_box.addWidget(logo)
        title_box.addWidget(sub)
        head.addWidget(badge)
        head.addLayout(title_box, 1)
        sl.addLayout(head)
        sl.addSpacing(16)
        sl.addWidget(hline("sep"))

        self.stack = QStackedWidget()
        self.nav = []
        self.nav_groups = []              # раскрывающиеся пункты: (пункт, [вложенные кнопки], блок, анимация)
        for group, items in self.GROUPS:
            sl.addSpacing(12)
            sec = spaced(QLabel(group), 1.6)
            sec.setObjectName("section")
            sl.addWidget(sec)
            sl.addSpacing(2)
            for item in items:
                icon, title = item[0], item[1]
                if len(item) == 3:                    # раскрывающийся пункт с вложенными страницами
                    wrap = QWidget()                      # пункт и его вложенные кнопки: один элемент панели
                    wl = QVBoxLayout(wrap)
                    wl.setContentsMargins(0, 0, 0, 0)
                    wl.setSpacing(0)
                    parent = NavButton(icon, title)
                    parent.setCheckable(False)
                    wl.addWidget(parent)
                    box = _Drawer()                       # высота этого блока плавно меняется
                    kids = []
                    for cicon, ctitle in item[2]:
                        kb = NavButton(cicon, ctitle)
                        kb.indent = 14
                        kb.clicked.connect(lambda _=False, k=len(self.nav): self.go(k))
                        self.nav.append(kb)
                        box.lay.addWidget(kb)
                        kids.append(kb)
                    wl.addWidget(box)
                    sl.addWidget(wrap)
                    anim = QPropertyAnimation(box, b"h", self)
                    anim.setDuration(230)
                    anim.setEasingCurve(QEasingCurve.Type.InOutCubic)
                    anim.finished.connect(lambda: self._freeze_nav_hover(False))
                    anim.valueChanged.connect(lambda _v: self._repaint_side())   # без остатков старой картинки (двоение текста)
                    anim.finished.connect(self._repaint_side)
                    grp = (parent, kids, box, anim)
                    parent.clicked.connect(lambda _=False, g=grp: self.open_group(g))
                    self.nav_groups.append(grp)
                    continue
                b = NavButton(icon, title)
                b.clicked.connect(lambda _=False, k=len(self.nav): self.go(k))
                self.nav.append(b)
                sl.addWidget(b)
            if group == "РАЗРАБОТЧИК":
                self.dev_sec, self.dev_nav = sec, self.nav[-1]
        sl.addStretch(1)

        # профиль внизу панели: ник и аватарка берутся у пользователя Linux
        sl.addWidget(hline("sep"))
        sl.addSpacing(8)
        prof = ProfileFrame()
        self.prof = prof
        prof.clicked.connect(self.open_profile_menu)
        prof.setObjectName("profile")
        pl = QHBoxLayout(prof)
        pl.setContentsMargins(4, 4, 4, 4)
        pl.setSpacing(10)
        av = QLabel()
        login = linux_user()
        av.setPixmap(round_avatar(linux_avatar(), 38, letter=login))
        av.setFixedSize(38, 38)
        info = QVBoxLayout()
        info.setSpacing(0)
        nm = QLabel(login)
        nm.setObjectName("pname")
        nm.setToolTip(login)
        nm.setMaximumWidth(120)
        nm.setText(nm.fontMetrics().elidedText(login, Qt.TextElideMode.ElideRight, 120))
        st = QLabel("● в сети")
        st.setObjectName("pstatus")
        info.addWidget(nm)
        info.addWidget(st)
        pl.addWidget(av)
        pl.addLayout(info, 1)
        up = QLabel()                     # стрелка вверх: здесь открывается меню
        up.setObjectName("profarrow")
        up.setFixedSize(18, 24)           # только место в раскладке: стрелку рисует сама плашка профиля
        up.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        prof.arrow_slot = up
        self.prof_arrow = up
        self.set_arrow("left")
        pl.addWidget(up)
        sl.addWidget(prof)

        # --- страницы: карточки в две колонки ---
        conn = Card("Подключение", "server")
        conn.row("Сервис", self.preset, "готовые настройки провайдера")
        conn.row("API-ключ", self.key)
        conn.divider("Хранение")
        conn.row("Запомнить ключ", self.remember, "сохранить в data/config.json")
        model = Card("Модель", "cpu")
        model.row("Модель", self.model, "выбери из списка или впиши своё")
        model.row("Адрес API", self.url, "можно свой или локальный")
        self.stack.addWidget(self.page("Сервис", "Куда отправлять запросы и чем ты авторизуешься",
                                       [conn], [model]))

        synth = Card("Синтез речи", "speaker")
        synth.row("Голос", self.engine, "чем Мими разговаривает", stack=True)
        synth.divider("Параметры Silero")
        synth.row("Диктор", self.speaker)
        synth.row("Тон", self.pitch)
        synth.row("Скорость", self.rate)
        recog = Card("Распознавание", "wave")
        recog.row("Распознавание речи", self.stt, "как Мими слышит тебя", stack=True)
        self.stack.addWidget(self.page("Голос", "Как Мими говорит и как слушает тебя", [synth], [recog]))

        prompt = Card("Промт", "chat")
        prompt.row("Пресет", self.persona_combo)
        prompt.wide(self.persona_row)
        prompt.wide(self.persona)
        card_av = Card("Модель", "user")
        big = ModelView(load_pixmap(), 260, 390, model_path=self.model_combo.currentData() or "")   # 3D-модель: растягивается на всю карточку, окно не растёт
        self.model_view = big                      # на неё переключается выбор в «Отрисовке»
        pname = QLabel("Mimi Typh")
        pname.setObjectName("h2")
        phint = QLabel("Так её зовут в ответах: Мими.\nПромт слева задаёт характер и обращение.")
        phint.setObjectName("desc")
        phint.setWordWrap(True)
        box = QVBoxLayout()
        box.setContentsMargins(0, 6, 0, 2)
        box.setSpacing(6)
        box.addWidget(big, 1)
        box.addWidget(pname, 0, Qt.AlignmentFlag.AlignHCenter)
        box.addWidget(phint)
        holder = QWidget()
        holder.setLayout(box)
        card_av.wide(holder, grow=True)
        card_draw = Card("Отрисовка", "eye")
        card_draw.row("Как показывать Мими", self.char_mode,
                      "GIF и 3D-модель оживают, пока она говорит", stack=True)
        card_model = Card("3D-модель", "user")
        self.card_model = card_model
        model_row = QWidget()
        ml = QHBoxLayout(model_row)
        ml.setContentsMargins(0, 0, 0, 0)
        ml.setSpacing(8)
        ml.addWidget(self.model_combo, 1)
        ml.addWidget(self.model_btn)
        card_model.row("Модель персонажа", model_row, "выбранная модель видна и во вкладке «Характер»", stack=True)
        card_model.row("Анимация", self.model_anim, "кивает, пока говорит, и наклоняет голову, пока думает")
        self.char_mode.currentIndexChanged.connect(self.update_char_fields)
        self.update_char_fields()
        self.stack.addWidget(self.page("Характер", "Кто она и как с тобой общается",
                                       [prompt], [card_av], fill_right=True))
        self.stack.addWidget(self.page("Отрисовка", "Как Мими выглядит на экране", [card_draw], [card_model]))

        ctl = Card("Управление ПК", "terminal")
        ctl.row("Выполнять команды", self.shell, "закрыть окно, громкость и т.п.")
        ctl.divider("Важно")
        note = QLabel("Команды подбираются под твою систему. Включай, только если доверяешь модели.")
        note.setObjectName("desc")
        note.setWordWrap(True)
        ctl.wide(note)
        env = Card("Окружение", "info")
        for label, value in (("Система", ENV["distro"]), ("Окружение", ENV["de"]), ("Сессия", ENV["session"])):
            val = QLabel(str(value))
            val.setObjectName("value")
            env.row(label, val)
        self.stack.addWidget(self.page("Команды", "Что помощнику разрешено делать на компьютере", [ctl], [env]))
        self.monitor = MonitorPanel()                    # вкладка «Мониторинг»: данные обновляются, только пока она открыта
        mon_left, mon_right = self.monitor.cards()
        mon_page = self.page("Мониторинг", "Состояние компьютера в реальном времени", mon_left, mon_right, scroll=True)
        self.monitor.attach(mon_page)
        self.stack.addWidget(mon_page)
        self.dev_page = DevConsole(auto=bool(saved.get("dev_console_auto", False)))                   # вкладка «Журнал»: бывшая консоль разработчика
        self.dev_index = self.stack.addWidget(self.dev_page)

        # --- правая часть ---
        right = QVBoxLayout()
        right.setContentsMargins(0, 0, 0, 0)
        right.setSpacing(0)

        top = TopBar()
        top.setFixedHeight(46)
        tl = QHBoxLayout(top)
        tl.setContentsMargins(26, 0, 12, 0)
        self.crumb = QLabel()
        self.crumb.setObjectName("crumb")
        close = QPushButton()
        close.setObjectName("winbtn")
        close.setFlat(True)
        close.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        close.setIcon(QIcon(draw_icon("close", "#7f8594", 16)))
        close.setIconSize(QSize(16, 16))
        close.setFixedSize(30, 30)
        close.setCursor(Qt.CursorShape.PointingHandCursor)
        close.clicked.connect(self.reject)
        tl.addWidget(self.crumb)
        tl.addStretch(1)
        tl.addWidget(close)

        foot = _FootBar()
        fl = QHBoxLayout(foot)
        fl.setContentsMargins(26, 10, 26, 16)
        fl.setSpacing(14)
        start = QPushButton("  Сохранить" if running else "  Начать разговор")
        start.setIcon(QIcon(draw_icon("check", "#ffffff", 16)))
        start.setIconSize(QSize(16, 16))
        start.setDefault(True)
        start.setCursor(Qt.CursorShape.PointingHandCursor)
        glow = QGraphicsDropShadowEffect(start)   # мягкое голубое свечение под кнопкой
        glow.setBlurRadius(28)
        glow.setOffset(0, 4)
        glow.setColor(QColor(75, 126, 255, 105))
        start.setGraphicsEffect(glow)
        self._glow = glow
        self.load_note = LoadNote(foot)                   # внизу слева: пока грузится 3D-модель
        foot.note = self.load_note                        # ставится вручную, на равном расстоянии от краёв
        self.model_view.loadingChanged.connect(self.on_model_loading)
        fl.addWidget(self.err, 1)
        fl.addWidget(start)

        right.addWidget(top)
        right.addWidget(hline("sep"))
        right.addWidget(self.stack, 1)
        right.addWidget(hline("sep"))
        right.addWidget(foot)
        rw = QWidget()
        rw.setLayout(right)
        self._side, self._rw = side, rw     # то, что масштабируется (тень вокруг окна не трогаем)
        root.addWidget(side)
        root.addWidget(rw, 1)

        # --- логика ---
        self.apply_preset(self.preset.currentText())
        if saved.get("preset") == self.preset.currentText():  # подставить сохранённые значения
            self.url.setText(saved.get("base_url", self.url.text()))
            self.model.setText(saved.get("model", self.model.text()))
        self.preset.currentTextChanged.connect(self.apply_preset)
        self.engine.currentIndexChanged.connect(self.update_voice_fields)
        self.update_voice_fields()
        start.clicked.connect(self.submit)
        self.sync_dev_tab()
        self.go(0)
        if LANG == "en":                 # сохранён английский: переводим окно сразу при создании
            self.retranslate()
        self.apply_win_size(self.opts["win_size"])     # теперь раскладка есть: учитываем минимальный размер

    _ghost = False   # страницы настроек временно невидимы (открыт редактор темы)

    def set_ghost(self, on: bool) -> None:
        """Делает правую часть окна невидимой, пока открыт редактор темы. Не hide(): он ломает раскладку
        (боковая панель уезжает), а прозрачность размеры не меняет. Сам диалог тоже не скрываем: hide() завершил бы exec()."""
        if on == self._ghost:
            return
        self._ghost = on
        if on:
            eff = QGraphicsOpacityEffect(self._rw)
            eff.setOpacity(0.0)
            self._rw.setGraphicsEffect(eff)
        else:
            self._rw.setGraphicsEffect(None)
        self._rw.setEnabled(not on)
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        m = self.SHADOW
        rad = 14 * self._k                     # скругление растёт и падает вместе с окном
        body = QRectF(self.rect()).adjusted(m, m, -m, -m)
        p.setPen(Qt.PenStyle.NoPen)
        for k in range(1, m + 1):              # мягкая тень: слои с убывающей прозрачностью
            p.setBrush(QColor(0, 0, 0, int(7 * (1 - k / m) ** 2) + 1))
            p.drawRoundedRect(body.adjusted(-k, -k + 4, k, k + 4), rad + k, rad + k)
        pm = self._backdrop(body)
        if pm is not None:                      # картинка на заднем фоне: размытая, под цветом окна
            clip = QPainterPath()
            clip.addRoundedRect(body.adjusted(0.5, 0.5, -0.5, -0.5), rad, rad)
            p.save()
            p.setClipPath(clip)
            p.drawPixmap(body.topLeft(), pm)
            p.restore()
        bgc = QColor(BG)
        bgc.setAlpha(0 if getattr(self, "_aurora", False) else round((page_alpha() if pm is not None else 255) * bgc.alphaF()))   # прозрачность цвета фона учитывается
        p.setPen(QPen(QColor(BORDER), 1))
        p.setBrush(bgc)
        p.drawRoundedRect(body.adjusted(0.5, 0.5, -0.5, -0.5), rad, rad)

    def _backdrop(self, body: QRectF):
        """Картинка заднего фона под размер окна (по центру, с обрезкой) и размытием; кэшируется.
        Без картинки, но со стеклом: «свечение» (цветные пятна), чтобы стеклу было что преломлять."""
        self._aurora = False
        if not backdrop_on():
            if not aurora_on():
                self._bd_cache = None
                return None
            aw, ah = max(1, int(body.width())), max(1, int(body.height()))
            akey = ("aurora", aw, ah, ACCENT, BG, THEME_NAME)
            c = getattr(self, "_bd_cache", None)
            if not (c and c[0] == akey):
                self._bd_cache = (akey, make_aurora(aw, ah))
            self._aurora = True
            return self._bd_cache[1]
        path = VISUAL["bg_image"]
        w, h = max(1, int(body.width())), max(1, int(body.height()))
        try:
            st = os.stat(path)
        except OSError:
            return None
        key = (path, st.st_mtime_ns, st.st_size, VISUAL["bg_blur"], w, h)
        c = getattr(self, "_bd_cache", None)
        if c and c[0] == key:
            return c[1]
        img = QImage(path)
        if img.isNull():
            return None
        img = img.scaled(w, h, Qt.AspectRatioMode.KeepAspectRatioByExpanding, Qt.TransformationMode.SmoothTransformation)
        img = img.copy(max(0, (img.width() - w) // 2), max(0, (img.height() - h) // 2), w, h)
        b = int(VISUAL["bg_blur"])
        if b > 0:                                # гауссово размытие: картинка остаётся гладкой, без пикселей
            img = smooth_blur(img, (1.0 + b / 1.5) * 1.6)
        pm = QPixmap.fromImage(img)
        self._bd_cache = (key, pm)
        return pm

    def page(self, title: str, hint: str, left: list, right: list, fill_right: bool = False,
             scroll: bool = False) -> QWidget:
        """Одна страница: заголовок, подсказка и две колонки карточек.
        fill_right: последняя карточка правой колонки растягивается на всю высоту.
        scroll: колонки лежат в области прокрутки (заголовок остаётся на месте), если карточек больше, чем влезает."""
        w = QWidget()
        lay = QVBoxLayout(w)
        lay.setContentsMargins(26, 20, 26, 8)
        lay.setSpacing(3)
        h = QLabel(title)
        h.setObjectName("h1")
        t = QLabel(hint)
        t.setObjectName("muted")
        lay.addWidget(h)
        lay.addWidget(t)
        lay.addSpacing(14)
        cols = QHBoxLayout()
        cols.setSpacing(14)
        for col in (left, right):
            v = QVBoxLayout()
            v.setSpacing(14)
            stretch_col = fill_right and col is right and bool(col)
            for card in col:
                v.addWidget(card, 1 if stretch_col and card is col[-1] else 0)
            if stretch_col:
                col[-1].fill()
            else:
                v.addStretch(1)
            cols.addLayout(v, 1)
        if scroll:
            inner = QWidget()
            inner.setLayout(cols)
            cols.setContentsMargins(0, 0, 8, 6)
            sa = QScrollArea()
            sa.setWidgetResizable(True)
            sa.setFrameShape(QFrame.Shape.NoFrame)
            sa.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            sa.setWidget(inner)
            inner.setAutoFillBackground(False)            # setWidget включает заливку, а окно прозрачное: фон рисует диалог
            sa.setAutoFillBackground(False)
            sa.viewport().setAutoFillBackground(False)
            sa.setStyleSheet("QScrollArea { background: transparent; border: none; }")
            lay.addWidget(sa, 1)
        else:
            lay.addLayout(cols, 1)
        return w

    def sync_dev_tab(self) -> None:
        """Вкладка «Журнал» видна только при включённом режиме разработчика."""
        on = dev_is_on()
        self.dev_sec.setVisible(on)
        self.dev_nav.setVisible(on)
        if not on and self.stack.currentIndex() == self.dev_index:
            self.go(0)

    PAGE_FADE_MS = 280      # вся смена страницы: сначала старая гаснет, потом новая проявляется
    PAGE_FADE_SPLIT = 0.4   # доля времени на затухание старой страницы

    def _page_fx_cleanup(self) -> None:
        """Обрывает смену страницы и возвращает всё как есть: без эффекта прозрачности и без «призрака»."""
        a = getattr(self, "_page_anim", None)
        if a is not None:
            self._page_anim = None
            a.stop()
            a.deleteLater()
        g = getattr(self, "_page_ghost", None)
        if g is not None:
            self._page_ghost = None
            g.hide()
            g.deleteLater()
        pg = getattr(self, "_fade_page", None)
        if pg is not None:
            self._fade_page = None
            try:
                pg.setGraphicsEffect(None)
            except RuntimeError:
                pass

    def _fade_switch(self, n: int) -> None:
        """Смена страницы справа как в референсе: старая плавно гаснет, затем новая плавно проявляется, без сдвигов."""
        self._page_fx_cleanup()
        cur = self.stack.currentWidget()
        snap = cur.grab()                                  # снимок старой страницы: гаснет он, а не живые виджеты
        geo = cur.geometry()
        self.stack.setCurrentIndex(n)
        page = self.stack.currentWidget()
        ghost = QLabel(self.stack)
        ghost.setPixmap(snap)
        ghost.setGeometry(geo)
        ghost.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        gfx = QGraphicsOpacityEffect(ghost)
        gfx.setOpacity(1.0)
        ghost.setGraphicsEffect(gfx)
        ghost.show()
        ghost.raise_()
        fx = QGraphicsOpacityEffect(page)
        fx.setOpacity(0.0)
        page.setGraphicsEffect(fx)
        split = self.PAGE_FADE_SPLIT
        state = {"ghost": True}

        def tick(v):
            v = float(v)
            if v < split:
                gfx.setOpacity(1.0 - v / split)
            else:
                if state["ghost"]:
                    state["ghost"] = False
                    ghost.hide()
                k = (v - split) / (1.0 - split)
                fx.setOpacity(1.0 - (1.0 - k) ** 3)         # плавное замедление к концу

        anim = QVariantAnimation(self)
        anim.setDuration(self.PAGE_FADE_MS)
        anim.setStartValue(0.0)
        anim.setEndValue(1.0)
        anim.valueChanged.connect(tick)
        anim.finished.connect(self._page_fx_cleanup)
        self._page_anim, self._page_ghost, self._fade_page = anim, ghost, page
        anim.start()

    def go(self, n: int) -> None:
        ed = getattr(self, "_theme_ed", None)
        if ed is not None:
            try:
                if ed.isVisible():
                    ed.close()                 # выбрали вкладку слева: редактор уступает место страницам
            except RuntimeError:
                pass
        prev = self.stack.currentIndex()
        if n != prev and self.isVisible():
            self._fade_switch(n)
        else:
            self.stack.setCurrentIndex(n)
        for k, b in enumerate(self.nav):
            b.setChecked(k == n)
        self.crumb.setText(f"{T('Настройки')}  /  {T(self.titles[n])}")
        self.sync_groups()

    def sync_groups(self, animate: bool = True) -> None:
        """Раскрывающийся пункт открыт, только пока выбрана одна из его страниц; на другой вкладке плавно сворачивается."""
        cur = self.nav[self.stack.currentIndex()]
        for parent, kids, box, anim in self.nav_groups:
            on = cur in kids
            changed = parent.expanded != on
            parent.expanded = on
            parent.update()
            full = box.full_height()                     # мерим до анимации, внутри кадров высота не пересчитывается
            target = full if on else 0
            box._tok = getattr(box, "_tok", 0) + 1       # любой новый вызов отменяет отложенный старт прошлого
            if animate and changed and self.isVisible():
                anim.stop()
                self._freeze_nav_hover(True)
                box.inner.setVisible(on)                 # при сворачивании вложенные кнопки сразу прячутся: их текст не ездит

                def start(anim=anim, box=box, target=target, tok=box._tok):
                    if box._tok != tok:
                        return
                    anim.stop()
                    anim.setStartValue(box.get_h())
                    anim.setEndValue(target)
                    anim.start()
                if on:
                    start()
                else:
                    QTimer.singleShot(60, start)         # сворачивание стартует после смены страницы справа: рывок и глитч не совпадают
            elif changed or not animate or anim.state() != QPropertyAnimation.State.Running:
                anim.stop()
                box.set_h(target)
                box.inner.setVisible(on)
                self._freeze_nav_hover(False)
                if changed:
                    self._repaint_side()

    def _repaint_side(self) -> None:
        """Окно прозрачное: сдвинутые кнопки Qt копирует вместе со старым текстом, и он остаётся на кадр-два.
        Перерисовываем всю левую панель целиком, а не только сдвинутые куски."""
        side = getattr(self, "_side", None)
        if side is not None:
            side.update()
            side.repaint()

    def _freeze_nav_hover(self, on: bool) -> None:
        """Пока блок «Настройки» едет, кнопки скользят под неподвижной мышью: подсветку не трогаем, иначе цвет текста
        мигает. Когда блок доехал, подсветка снова берётся с реальной позиции курсора."""
        NavButton.freeze_hover = on
        if on:
            return
        pos = QCursor.pos()
        for b in self.nav + [g[0] for g in self.nav_groups]:
            b._hover = b.isVisible() and b.rect().contains(b.mapFromGlobal(pos))
            b.update()

    def open_group(self, group) -> None:
        """Клик по «Настройки»: раскрывается и открывается первая вложенная страница."""
        parent, kids = group[0], group[1]
        if not parent.expanded:
            self.go(self.nav.index(kids[0]))

    def toggle_key(self) -> None:
        """Глаз в поле ключа: показать или скрыть ключ."""
        show = self.key.echoMode() == QLineEdit.EchoMode.Password
        self.key.setEchoMode(QLineEdit.EchoMode.Normal if show else QLineEdit.EchoMode.Password)
        self.eye.setIcon(QIcon(draw_icon("eye_off" if show else "eye", ACCENT if show else "#7f8fa9", 18)))
        self.eye.setToolTip(T("Скрыть ключ" if show else "Показать ключ"))

    def retranslate(self) -> None:
        """Меняет язык всего окна настроек на лету (preset не трогаем: по его тексту ищутся настройки)."""
        retranslate(self, skip=(self.preset,))
        self.setWindowTitle(T("Помощник — настройка"))
        self.eye.setToolTip(T("Скрыть ключ" if self.key.echoMode() == QLineEdit.EchoMode.Normal else "Показать ключ"))
        self.go(self.stack.currentIndex())
        self.apply_win_size(self.opts["win_size"])     # английский текст бывает шире: минимум мог вырасти

    def apply_win_size(self, value) -> None:
        """Размер окна настроек: процент от базового 980x620 («Авто» = 100%).
        Вместе с окном масштабируется всё содержимое: шрифты, отступы, поля, иконки.
        Центр окна остаётся на месте."""
        scr = self.screen().availableGeometry() if self.screen() else None
        base_w, base_h = 980, 620
        try:
            k = 1.0 if value == "auto" else float(value)
        except (TypeError, ValueError):
            k = 1.0
        self.set_content_scale(k)
        W, H = int(base_w * k) + 2 * self.SHADOW, int(base_h * k) + 2 * self.SHADOW
        mh = self.minimumSizeHint()                    # пока раскладки нет (в начале __init__), он невалиден
        if mh.isValid():                               # страховка: меньше минимума содержимого не делаем
            W, H = max(W, mh.width()), max(H, mh.height())
        if scr is not None:
            W, H = min(W, scr.width()), min(H, scr.height())
        center = self.geometry().center() if self.isVisible() else None
        self.setFixedSize(W, H)
        if center is not None:
            x, y = center.x() - W // 2, center.y() - H // 2
            if scr is not None:
                x = max(scr.left(), min(x, scr.right() - W))
                y = max(scr.top(), min(y, scr.bottom() - H))
            self.move(x, y)

    # ---------- масштаб содержимого ----------
    def set_content_scale(self, k: float) -> None:
        """Масштабирует левую панель и страницы в k раз (1.0 = размеры из кода). Ошибка тут не роняет окно."""
        if getattr(self, "_side", None) is None:       # раскладка ещё не собрана (начало __init__)
            return
        if abs(k - self._k) < 1e-6:
            return
        try:
            self._apply_scale(k)
        except Exception:
            traceback.print_exc()
        self._k = k
        self.update()

    def _scale_snapshot(self) -> None:
        """Запоминает исходные размеры, отступы, иконки и стили: масштаб всегда считается от них, без накопления ошибки."""
        if self._snap is not None:
            return
        widgets, layouts, seen = [], [], set()
        for root_w in (self._side, self._rw):
            widgets += [root_w] + root_w.findChildren(QWidget)
            if root_w.layout() is not None:
                layouts.append(root_w.layout())
            layouts += root_w.findChildren(QLayout)
        ws = []
        for w in widgets:
            if id(w) in seen:
                continue
            seen.add(id(w))
            pm = w.pixmap() if isinstance(w, QLabel) else None
            ws.append({"w": w, "min": (w.minimumWidth(), w.minimumHeight()),
                       "max": (w.maximumWidth(), w.maximumHeight()), "ss": w.styleSheet(),
                       "pm": pm if pm is not None and not pm.isNull() else None,
                       "ic": QSize(w.iconSize()) if isinstance(w, QAbstractButton) else None})
        ls = []
        for lay in layouts:
            m = lay.contentsMargins()
            spacers = []
            for i in range(lay.count()):
                it = lay.itemAt(i)
                sp = it.spacerItem() if it is not None else None
                if sp is not None:
                    pol, hint = sp.sizePolicy(), sp.sizeHint()
                    spacers.append((sp, hint.width(), hint.height(), pol.horizontalPolicy(), pol.verticalPolicy()))
            ls.append({"l": lay, "m": (m.left(), m.top(), m.right(), m.bottom()),
                       "sp": lay.spacing() if isinstance(lay, QBoxLayout) else None, "spacers": spacers})
        self._snap = (ws, ls)

    def _apply_scale(self, k: float) -> None:
        self._scale_snapshot()
        ws, ls = self._snap
        qmax = 16777215                                  # QWIDGETSIZE_MAX: «без ограничения», его не трогаем
        sc = lambda v: v if v in (0, qmax) else max(1, round(v * k))
        one = abs(k - 1.0) < 1e-6
        qss = "" if one else scale_qss(build_qss(chevron_png("#7b8190")), k)
        for root_w in (self._side, self._rw):            # шрифты и отступы из общих стилей, увеличенные в k раз
            root_w.setStyleSheet(qss)
        for d in ws:
            w = d["w"]
            try:
                w.setMinimumSize(sc(d["min"][0]), sc(d["min"][1]))
                w.setMaximumSize(sc(d["max"][0]), sc(d["max"][1]))
                if d["ss"] and "px" in d["ss"]:
                    w.setStyleSheet(scale_qss(d["ss"], k))
                if d["pm"] is not None:                  # иконки и аватарки в подписях
                    pm = d["pm"]
                    if one:
                        w.setPixmap(pm)
                    else:
                        big = pm.scaled(max(1, round(pm.width() * k)), max(1, round(pm.height() * k)),
                                        Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.SmoothTransformation)
                        big.setDevicePixelRatio(pm.devicePixelRatio())
                        w.setPixmap(big)
                if d["ic"] is not None:
                    w.setIconSize(QSize(max(1, round(d["ic"].width() * k)), max(1, round(d["ic"].height() * k))))
                if isinstance(w, (NavButton, Toggle, ProfileFrame)):   # самонарисованные: масштаб читают при рисовании
                    w._k = k
                    w.updateGeometry()
                    w.update()
            except RuntimeError:                         # виджет уже удалён
                continue
        for d in ls:
            try:
                lay = d["l"]
                lay.setContentsMargins(*(round(v * k) for v in d["m"]))
                if d["sp"] is not None and d["sp"] >= 0:
                    lay.setSpacing(round(d["sp"] * k))
                for sp, w0, h0, hp, vp in d["spacers"]:
                    sp.changeSize(round(w0 * k), round(h0 * k), hp, vp)
                lay.invalidate()
            except RuntimeError:
                continue
        self._k = k                                      # set_arrow ниже читает масштаб
        self.set_arrow(getattr(self, "_arrow_side", "left"))
        if getattr(self, "nav_groups", None):
            self.sync_groups(animate=False)              # снимок размеров помнит старую высоту раскрывающегося блока

    def refresh_scale_qss(self) -> None:
        """После смены темы или акцента: пересобирает масштабированные стили (при 100% их нет, всё берётся из общих)."""
        if getattr(self, "_side", None) is None or abs(self._k - 1.0) < 1e-6:
            return
        qss = scale_qss(build_qss(chevron_png("#7b8190")), self._k)
        for root_w in (self._side, self._rw):
            root_w.setStyleSheet(qss)

    def show_about(self) -> None:
        """Открывает «О программе» поверх всего окна настроек."""
        import datetime
        months = ["января", "февраля", "марта", "апреля", "мая", "июня", "июля", "августа",
                  "сентября", "октября", "ноября", "декабря"]
        t = datetime.date.today()
        rows = [("Username", linux_user()), ("Версия", "alpha"),
                ("Обновлено", f"{t.day} {months[t.month - 1]} {t.year}")]
        old = getattr(self, "_about", None)
        if old is not None:
            try:
                old.close_about()
            except RuntimeError:
                pass
        self._about = AboutOverlay(self, rows)
        self._about.open()

    def toggle_theme_editor(self) -> None:
        """Редактор темы прикреплён к левой стороне окна; повторный клик по «Стиль» закрывает его."""
        ed = getattr(self, "_theme_ed", None)
        if ed is not None:
            try:
                if ed.isVisible():
                    ed.close()
                    return
            except RuntimeError:
                pass
        ed = ThemeEditor(self)
        ed.destroyed.connect(lambda *_: setattr(self, "_theme_ed", None))
        self._theme_ed = ed
        ed.show()

    def show_rules(self) -> None:
        self._rules = RulesOverlay(self)
        self._rules.open()

    def set_arrow(self, side: str = "left") -> None:
        """Стрелка в блоке профиля смотрит туда, где откроется меню."""
        self._arrow_side = side
        pm = draw_icon("chev_down", MUTED, max(8, round(16 * self._k)))
        self.prof.set_arrow_pixmap(pm.transformed(QTransform().rotate(90 if side == "left" else -90),
                                                  Qt.TransformationMode.SmoothTransformation))

    def refresh_glow(self) -> None:
        """Свечение под кнопкой «Начать разговор» / «Сохранить» берёт цвет самой кнопки."""
        g = getattr(self, "_glow", None)
        if g is not None:
            c = QColor(BTN_HB)
            c.setAlpha(105)
            g.setColor(c)

    def refresh_accent(self) -> None:
        """Перекрашивает то, что нарисовано один раз при создании окна."""
        self.refresh_glow()
        self.set_arrow(getattr(self, "_arrow_side", "left"))
        show = self.key.echoMode() == QLineEdit.EchoMode.Normal
        self.eye.setIcon(QIcon(draw_icon("eye_off" if show else "eye", ACCENT if show else "#7f8fa9", 18)))
        self.update()

    def open_profile_menu(self) -> None:
        self.menu = ProfileMenu(self)
        self.prof.set_open(True)          # плашка остаётся подсвеченной, пока меню открыто
        self.menu.popup_at(self.prof)

    def done(self, r: int) -> None:
        ed = getattr(self, "_theme_ed", None)
        if ed is not None:
            try:
                ed.close()
            except RuntimeError:
                pass
        if r != QDialog.DialogCode.Accepted and (ACCENT_NAME != self._accent0 or THEME_NAME != self._theme0):
            set_accent(self._accent0)       # закрыли без сохранения: прежние цвет и тема
            set_theme(self._theme0)
            restyle()
        if r != QDialog.DialogCode.Accepted and dev_is_on() != self._dev0:
            set_dev_mode(self._dev0)
        super().done(r)

    def update_char_fields(self) -> None:
        self.card_model.setVisible(self.char_mode.currentData() == "model3d")   # выбор модели и анимации только в режиме 3D

    def on_model_loading(self, on: bool) -> None:
        n = self.load_note
        foot = n.parentWidget()
        n.setVisible(on)
        if on:
            foot.place_note()
            # строка ошибок сдвигается вправо от плашки (её левый край — обычный отступ панели, 26)
            self.err.setIndent(max(0, foot.gap() + n.sizeHint().width() - 2 * LoadNote.PAD + 14 - 26))
        else:
            self.err.setIndent(-1)

    def on_model_changed(self) -> None:
        path = self.model_combo.currentData() or ""
        self.model_view.set_model(path)                   # во вкладке «Характер» сразу меняется моделька
        if path:
            save_model_pref(path)                         # и выбор запоминается на диске сразу

    def pick_model(self) -> None:
        start = self.model_combo.currentData() or str(BASE / "assets")
        path, _ = QFileDialog.getOpenFileName(self, "Выбери 3D-модель (.glb)", start, "3D-модель (*.glb)")
        if not path:
            return
        i = self.model_combo.findData(path)
        if i < 0:
            if self.model_combo.count() == 1 and not self.model_combo.itemData(0):
                self.model_combo.clear()                  # убираем заглушку «нет файлов .glb»
            self.model_combo.addItem(Path(path).stem, path)
            i = self.model_combo.findData(path)
        self.model_combo.setCurrentIndex(i)

    def update_voice_fields(self) -> None:
        on = self.engine.currentData() == "silero"  # диктор, тон и скорость есть только у Silero
        for w in (self.speaker, self.pitch, self.rate):
            w.setEnabled(on)

    def apply_preset(self, name: str) -> None:
        _, url, model = PRESETS[name]
        self.url.setText(url)
        self.model.reset_remote()
        self.model.set_models(MODEL_CHOICES.get(name, []))
        self.model.setText(model)

    def submit(self) -> None:
        url, model, key = self.url.text().strip(), self.model.text().strip(), self.key.text().strip()
        local = "localhost" in url or "127.0.0.1" in url
        if not url or not model:
            self.go(0)  # ошибка относится к странице «Сервис»: показываем её
            self.err.setText(T("Заполните модель и адрес API"))
            return
        if not key and not local:
            self.go(0)
            self.err.setText(T("Введите API-ключ"))
            return
        name = self.preset.currentText()
        self.cfg = {"preset": name, "provider": PRESETS[name][0],
                    "base_url": url, "model": model, "api_key": key,
                    "tts_engine": self.engine.currentData(), "silero_speaker": self.speaker.currentData(),
                    "silero_pitch": self.pitch.currentData(), "silero_rate": self.rate.currentData(),
                    "persona": self.persona.toPlainText().strip() or PERSONA,
                    "persona_name": self.persona_name_edit.text().strip() or "Default",
                    "shell": self.shell.isChecked(), "stt": self.stt.currentData(),
                    "char_mode": self.char_mode.currentData(), "char_gif": self.char_gif_path,
                    "model_path": self.model_combo.currentData() or "",
                    "model_anim": self.model_anim.isChecked(),
                    **self.opts, "dev_mode": dev_is_on(),
                    "dev_console_auto": self.dev_page.auto.isChecked()}
        save_config(self.cfg, self.remember.isChecked())
        self.accept()


# ---------- запуск приложений по ярлыкам (.desktop): обычные, Flatpak, Snap ----------
APP_DIRS = [Path("/usr/share/applications"), Path("/usr/local/share/applications"),
            Path.home() / ".local/share/applications",
            Path("/var/lib/flatpak/exports/share/applications"),
            Path.home() / ".local/share/flatpak/exports/share/applications",
            Path("/var/lib/snapd/desktop/applications")]
APP_ALIASES = {"телеграм": "telegram", "телеграмм": "telegram", "дискорд": "discord", "стим": "steam",
               "спотифай": "spotify", "хром": "chrome", "гугл хром": "chrome", "фаерфокс": "firefox",
               "файрфокс": "firefox", "файрфох": "firefox", "ватсап": "whatsapp", "вайбер": "viber",
               "зум": "zoom", "обс": "obs", "ютуб": "youtube", "браузер": "firefox"}


def read_desktop(path: Path) -> dict | None:
    """Читает секцию [Desktop Entry]; None, если ярлык скрыт или это не приложение."""
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None
    entry, inside = {}, False
    for line in lines:
        line = line.strip()
        if line.startswith("["):
            if inside:
                break
            inside = line == "[Desktop Entry]"
        elif inside and "=" in line and not line.startswith("#"):
            k, v = line.split("=", 1)
            entry.setdefault(k.strip(), v.strip())
    if entry.get("Type", "Application") != "Application" or "Exec" not in entry:
        return None
    if entry.get("NoDisplay", "").lower() == "true" or entry.get("Hidden", "").lower() == "true":
        return None
    return entry


def find_desktop_app(name: str) -> tuple[str, str] | None:
    """Ищет установленное приложение по названию. Возвращает (название, строка Exec)."""
    q = APP_ALIASES.get(name.strip().lower(), name.strip().lower())
    if not q:
        return None
    best, best_score = None, 0
    for folder in APP_DIRS:
        if not folder.is_dir():
            continue
        for f in folder.glob("*.desktop"):
            entry = read_desktop(f)
            if not entry:
                continue
            stem = f.stem.lower()
            if q == stem or q in stem.split("."):
                score = 3                       # org.telegram.desktop <- «telegram»
            elif q in stem:
                score = 2
            elif q in (entry.get("Name", "") + " " + entry.get("Name[ru]", "")).lower():
                score = 1
            else:
                continue
            if score > best_score or (score == best_score and len(stem) < len(best[0])):
                best, best_score = (stem, entry["Exec"], entry.get("Name", stem)), score
    return (best[2], best[1]) if best else None


def launch_app(name: str, extra: tuple = ()) -> bool:
    """Запускает приложение по названию (telegram, discord, spotify...). True, если запустилось."""
    found = find_desktop_app(name)
    if not found:
        print(f"Приложение «{name}» не найдено среди установленных", file=sys.stderr)
        return False
    title, exec_line = found
    exec_line = re.sub(r"@@u|@@", "", exec_line)
    exec_line = re.sub(r"%[a-zA-Z]", "", exec_line)    # %u %U %f и т.п. нам не нужны
    exec_line = re.sub(r"\s--\s*$", "", exec_line.strip())   # хвост « --» от Flatpak-ярлыков
    try:
        args = shlex.split(exec_line) + list(extra)
        subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         start_new_session=True, cwd=str(Path.home()))
    except (ValueError, OSError) as e:
        print(f"Не удалось запустить {title}: {e}", file=sys.stderr)
        return False
    print(f"Запущено приложение: {title} ({exec_line.strip()})")
    return True


# ---------- управление музыкой через MPRIS: работает и без playerctl ----------
MEDIA_ACTIONS = {"play", "pause", "play-pause", "next", "previous", "stop"}
MPRIS_METHOD = {"play": "Play", "pause": "Pause", "play-pause": "PlayPause", "next": "Next",
                "previous": "Previous", "stop": "Stop"}
# какой плеер выбирать, когда открыто несколько и никто не играет: сначала музыкальные программы (по порядку списка),
# потом всё остальное, и в самом конце браузеры (вкладка YouTube и т.п.). Свой плеер впиши первым.
MEDIA_PRIORITY = ["spotify", "rhythmbox", "strawberry", "amberol", "lollypop", "clementine", "audacious",
                  "elisa", "vlc", "mpv"]
MEDIA_BROWSERS = ("chrome", "chromium", "firefox", "brave", "vivaldi", "opera", "edge", "zen", "librewolf")


def _player_rank(name: str) -> int:
    n = name.lower()
    for i, key in enumerate(MEDIA_PRIORITY):
        if key in n:
            return i
    return len(MEDIA_PRIORITY) + (1 if any(b in n for b in MEDIA_BROWSERS) else 0)


def _gdbus(*args: str) -> str | None:
    """Вызов gdbus на сессионной шине. None, если gdbus нет или вызов не удался."""
    gdbus = shutil.which("gdbus")
    if not gdbus:
        return None
    try:
        r = subprocess.run([gdbus, "call", "--session", *args], capture_output=True, text=True, timeout=3)
    except (OSError, subprocess.SubprocessError):
        return None
    return r.stdout if r.returncode == 0 else None


def mpris_players() -> list[tuple[str, str]]:
    """Плееры на шине (Spotify, браузер, VLC...) и их состояние: [(имя, Playing / Paused / Stopped)]."""
    out = _gdbus("--dest", "org.freedesktop.DBus", "--object-path", "/org/freedesktop/DBus",
                 "--method", "org.freedesktop.DBus.ListNames") or ""
    players = []
    for name in re.findall(r"'(org\.mpris\.MediaPlayer2\.[^']+)'", out):
        st = _gdbus("--dest", name, "--object-path", "/org/mpris/MediaPlayer2",
                    "--method", "org.freedesktop.DBus.Properties.Get",
                    "org.mpris.MediaPlayer2.Player", "PlaybackStatus") or ""
        m = re.search(r"'(Playing|Paused|Stopped)'", st)
        players.append((name, m.group(1) if m else "Stopped"))
    return players


def media_control(action: str) -> bool:
    """Пауза / продолжить / следующий трек. «Продолжить» будит именно тот плеер, который стоит на паузе
    (а не первый попавшийся, как делает playerctl). True, если команда дошла или делать было нечего."""
    players = mpris_players()
    if not players:                                   # gdbus нет или плееров не видно: пробуем сам playerctl
        if shutil.which("playerctl"):
            try:
                return subprocess.run(["playerctl", action], capture_output=True, timeout=5).returncode == 0
            except (OSError, subprocess.SubprocessError):
                return False
        return False
    players.sort(key=lambda ps: _player_rank(ps[0]))  # музыкальные программы раньше браузеров (сортировка устойчивая)
    playing = [n for n, s in players if s == "Playing"]
    paused = [n for n, s in players if s == "Paused"]
    first = [players[0][0]]
    if action == "play-pause":
        action = "pause" if playing else "play"       # переключатель превращаем в явную команду
    if action == "play":
        # уже играет: ничего делать не нужно; иначе будим лучший по рангу (Spotify раньше браузера),
        # а при равном ранге того, что стоит на паузе, раньше остановленного
        idle = [n for n, st in sorted(players, key=lambda ps: (_player_rank(ps[0]), ps[1] != "Paused"))
                if st != "Playing"]
        targets = [] if playing else idle[:1]
    elif action == "pause":
        targets = playing                                    # на паузе уже всё: тоже нечего делать
    else:
        targets = playing[:1] or paused[:1] or first
    ok = False
    for name in targets:
        res = _gdbus("--dest", name, "--object-path", "/org/mpris/MediaPlayer2",
                     "--method", f"org.mpris.MediaPlayer2.Player.{MPRIS_METHOD[action]}")
        ok = ok or res is not None
    print(f"Музыка: {action} -> {', '.join(targets) or 'ничего делать не нужно'}")
    return ok or not targets


# ---------- Spotify: «включи трек ...» голосом ----------
# Нужны бесплатные ключи с https://developer.spotify.com/dashboard (создай приложение, скопируй Client ID и Secret).
# Положи их в data/spotify.json: {"client_id": "...", "client_secret": "..."}
# или задай переменные окружения SPOTIFY_CLIENT_ID и SPOTIFY_CLIENT_SECRET. Premium для поиска не нужен.
SPOTIFY_PATH = DATA_DIR / "spotify.json"
SPOTIFY_HELP = ("Spotify: нет ключей. Создай приложение на https://developer.spotify.com/dashboard, "
                f"скопируй Client ID и Client Secret и впиши в {CFG_PATH} в поля "
                '"spotify_client_id" и "spotify_client_secret".')
_PLAY_VERB = r"(?:включи|включай|включить|поставь|поставить|запусти|запускай|сыграй|воспроизведи)"
PLAY_TRACK_RE = re.compile(
    rf"^(?:мими[,\s]+)?(?:пожалуйста[,\s]+)?{_PLAY_VERB}\s+(?:мне\s+)?(?:пожалуйста\s+)?(?P<rest>.+)$", re.I)
SPOTIFY_WORD_RE = re.compile(r"\b(?:в|на|через)\s+(?:спотифа\w*|спотик\w*|spotify)\b", re.I)
_SP_TOKEN = {"v": "", "exp": 0.0}


def parse_track_request(text: str) -> str | None:
    """«включи трек Кино Группа крови» -> «кино группа крови». None, если это не просьба включить трек.
    Просто «включи музыку» сюда не попадает (это пауза/продолжить), а «включи музыку в спотифае» без названия — тоже."""
    m = PLAY_TRACK_RE.match(text.strip().lower().strip(" .!?,"))
    if not m:
        return None
    rest = m.group("rest")
    has_spot = bool(SPOTIFY_WORD_RE.search(rest))
    rest = SPOTIFY_WORD_RE.sub(" ", rest).strip()
    noun = None
    nm = re.match(r"(трек|песню|песенку|композицию|музыку|музон)\s+(.*)", rest)
    if nm:
        noun, rest = nm.group(1), nm.group(2)
    if noun in (None, "музыку", "музон") and not has_spot:
        return None                                       # «включи свет», «включи музыку» — не про трек
    rest = re.sub(r"^(?:под названием|называется|с названием|которая называется|который называется)\s+", "", rest)
    rest = re.sub(r"\s+", " ", rest).strip()
    if rest in ("трек", "песню", "песенку", "композицию", "музыку", "музон"):
        return None                                       # название не назвали
    return rest or None


def spotify_creds() -> tuple[str, str] | None:
    cid = os.environ.get("SPOTIFY_CLIENT_ID", "")
    sec = os.environ.get("SPOTIFY_CLIENT_SECRET", "")
    if not (cid and sec):
        c = read_json(CFG_PATH, {})                          # основной вариант: поля в data/config.json
        cid, sec = str(c.get("spotify_client_id", "")), str(c.get("spotify_client_secret", ""))
    if not (cid and sec):
        d = read_json(SPOTIFY_PATH, {})                      # запасной: отдельный data/spotify.json
        cid, sec = str(d.get("client_id", "")), str(d.get("client_secret", ""))
    if not (cid and sec) or cid.startswith("СЮДА") or sec.startswith("СЮДА"):
        return None                                           # ключи не заполнены (стоят заглушки)
    return cid, sec


def spotify_token(cid: str, sec: str) -> str:
    if _SP_TOKEN["v"] and time.time() < _SP_TOKEN["exp"] - 30:
        return _SP_TOKEN["v"]
    import base64
    auth = base64.b64encode(f"{cid}:{sec}".encode()).decode()
    req = urllib.request.Request("https://accounts.spotify.com/api/token", data=b"grant_type=client_credentials",
                                 headers={"Authorization": f"Basic {auth}",
                                          "Content-Type": "application/x-www-form-urlencoded"})
    with urllib.request.urlopen(req, timeout=10) as r:
        d = json.loads(r.read().decode("utf-8"))
    _SP_TOKEN["v"], _SP_TOKEN["exp"] = d["access_token"], time.time() + int(d.get("expires_in", 3600))
    return _SP_TOKEN["v"]


def spotify_find_track(query: str, cid: str, sec: str) -> tuple[str, str, str] | None:
    """Ищет трек в каталоге Spotify. Возвращает (uri, название, исполнители) лучшего совпадения."""
    from urllib.parse import quote
    req = urllib.request.Request(f"https://api.spotify.com/v1/search?type=track&limit=5&q={quote(query)}",
                                 headers={"Authorization": f"Bearer {spotify_token(cid, sec)}"})
    with urllib.request.urlopen(req, timeout=10) as r:
        items = json.loads(r.read().decode("utf-8")).get("tracks", {}).get("items", [])
    if not items:
        return None
    t = items[0]
    return t["uri"], t["name"], ", ".join(a["name"] for a in t.get("artists", []))


_UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64; rv:128.0) Gecko/20100101 Firefox/128.0"}


def _get_json(url: str):
    with urllib.request.urlopen(urllib.request.Request(url, headers=_UA), timeout=10) as r:
        return json.loads(r.read().decode("utf-8", "replace"))


SPOTIFY_ID_RE = re.compile(r"open\.spotify\.com(?:%2F|/|\\/)(?:intl-[a-z]+(?:%2F|/|\\/))?track(?:%2F|/|\\/)([A-Za-z0-9]{22})")


def _get_text(url: str) -> str:
    with urllib.request.urlopen(urllib.request.Request(url, headers=_UA), timeout=8) as r:
        return r.read().decode("utf-8", "replace")


def _spotify_id_from(page: str) -> str | None:
    """Ищет в тексте страницы ссылку на трек Spotify (в том числе внутри редиректов Bing, закодированных в base64)."""
    import base64
    m = SPOTIFY_ID_RE.search(page)
    if m:
        return m.group(1)
    for b in re.findall(r"[?&;]u=a1([A-Za-z0-9_\-]+)", page):
        try:
            dec = base64.urlsafe_b64decode(b + "=" * (-len(b) % 4)).decode("utf-8", "replace")
        except ValueError:
            continue
        m = SPOTIFY_ID_RE.search(dec)
        if m:
            return m.group(1)
    return None


def spotify_anon_search(text: str) -> str | None:
    """Без ключей: берём гостевой токен веб-плеера со страницы open.spotify.com и ищем трек в каталоге Spotify."""
    from urllib.parse import quote
    page = _get_text("https://open.spotify.com/")
    m = re.search(r'"accessToken"\s*:\s*"([^"]+)"', page)
    if not m:
        print(f"Spotify веб: гостевой токен на странице не найден (страница {len(page)} байт)", file=sys.stderr)
        return None
    req = urllib.request.Request("https://api.spotify.com/v1/search?type=track&limit=5&q=" + quote(text),
                                 headers={**_UA, "Authorization": "Bearer " + m.group(1)})
    with urllib.request.urlopen(req, timeout=8) as r:
        items = json.loads(r.read().decode("utf-8", "replace")).get("tracks", {}).get("items", [])
    print(f"Spotify веб: найдено {len(items)}" + (f", первый: {items[0]['name']} — {items[0]['artists'][0]['name']}" if items else ""))
    return items[0]["id"] if items else None


def _anon_search_safe(text: str) -> str | None:
    try:
        return spotify_anon_search(text)
    except urllib.error.HTTPError as e:
        print(f"Spotify веб: HTTP {e.code}", file=sys.stderr)
    except (urllib.error.URLError, OSError, ValueError, KeyError, IndexError) as e:
        print(f"Spotify веб: {e}", file=sys.stderr)
    return None


def _resolve_spotify_id(title: str, url: str) -> str | None:
    """Знаем точное «трек — исполнитель» и ссылку из каталога. Ищем ID в Spotify несколькими способами без ключей."""
    from urllib.parse import quote
    text = title.replace(" — ", " ")
    sid = _anon_search_safe(text)
    if sid:
        return sid
    sq = quote("site:open.spotify.com/track " + text)
    attempts = [("Bing", f"https://www.bing.com/search?q={sq}"),
                ("DuckDuckGo", f"https://html.duckduckgo.com/html/?q={sq}")]
    for name, u in attempts:
        try:
            page = _get_text(u)
        except (urllib.error.URLError, OSError, ValueError) as e:
            print(f"{name}: {e}", file=sys.stderr)
            continue
        sid = _spotify_id_from(page)
        print(f"{name}: {'ссылка найдена' if sid else f'ссылки на Spotify нет (страница {len(page)} байт)'}")
        if sid:
            return sid
    return None


_LAST_CATALOG = {"title": ""}      # лучшее совпадение из каталога Deezer/iTunes: «трек — исполнитель»


def itunes_songlink_track(query: str) -> tuple[str, str] | None:
    """Без ключей: ищем трек в каталогах Deezer и iTunes, затем ID в Spotify (song.link, Mojeek, Bing, DuckDuckGo).
    Возвращает (spotify:track:<id>, «трек — исполнитель»). Ход поиска печатается в консоль."""
    from urllib.parse import quote
    q = quote(query)
    cands: list[tuple[str, str]] = []
    try:
        data = _get_json(f"https://api.deezer.com/search?q={q}&limit=3").get("data", [])
        print(f"Каталог Deezer: найдено {len(data)}")
        cands += [(f"{it['title']} — {it['artist']['name']}", it["link"]) for it in data if it.get("link")]
    except (urllib.error.URLError, OSError, ValueError, KeyError) as e:
        print(f"Каталог Deezer: {e}", file=sys.stderr)
    for country in ("US", "RU"):
        try:
            res = _get_json(f"https://itunes.apple.com/search?term={q}&entity=song&limit=3&country={country}").get("results", [])
        except (urllib.error.URLError, OSError, ValueError) as e:
            print(f"Каталог iTunes {country}: {e}", file=sys.stderr)
            continue
        print(f"Каталог iTunes {country}: найдено {len(res)}")
        cands += [(f"{it.get('trackName', '')} — {it.get('artistName', '')}", it["trackViewUrl"])
                  for it in res if it.get("trackViewUrl")]
        if res:
            break
    _LAST_CATALOG["title"] = cands[0][0] if cands else ""
    for title, url in cands[:2]:
        sid = _resolve_spotify_id(title, url)
        if sid:
            return f"spotify:track:{sid}", title
    if not cands:
        sid = _anon_search_safe(query)
        if sid:
            return f"spotify:track:{sid}", query
    return None


SPOTAPI_AUTO_INSTALL = True       # True: если SpotAPI не установлена, Мими сама выполнит pip install spotapi
_SPOTAPI = {"song": None, "warned": False}
_SPOTAPI_LOCK = threading.Lock()


def ensure_spotapi() -> bool:
    """Проверяет, что SpotAPI доступна; если нет и разрешено, один раз ставит её через pip в то же окружение,
    в котором запущена программа (venv проекта). True, если библиотеку можно импортировать."""
    import importlib
    with _SPOTAPI_LOCK:
        try:
            importlib.import_module("spotapi")
            return True
        except ImportError:
            pass
        except Exception as e:                        # установлена, но не импортируется (например, нет tls-client)
            if not _SPOTAPI["warned"]:
                _SPOTAPI["warned"] = True
                print(f"SpotAPI установлена, но не запускается: {type(e).__name__}: {e}", file=sys.stderr)
            return False
        if not SPOTAPI_AUTO_INSTALL or _SPOTAPI["warned"]:
            return False
        _SPOTAPI["warned"] = True                     # пробуем только один раз за запуск
        print("SpotAPI не найдена, устанавливаю: pip install spotapi (может занять минуту)…")
        try:
            r = subprocess.run([sys.executable, "-m", "pip", "install", "spotapi>=2.0.0"],
                               capture_output=True, text=True, timeout=600)
        except (OSError, subprocess.SubprocessError) as e:
            print(f"Не удалось запустить pip: {e}", file=sys.stderr)
            return False
        if r.returncode != 0:
            print("Не удалось установить SpotAPI:\n" + (r.stderr or r.stdout)[-800:], file=sys.stderr)
            return False
        importlib.invalidate_caches()
        try:
            importlib.import_module("spotapi")
        except Exception as e:
            print(f"SpotAPI установилась, но не запускается: {type(e).__name__}: {e}", file=sys.stderr)
            return False
        print("SpotAPI установлена")
        return True


def _dig(obj, *path):
    """Достаёт вложенное поле и из объектов (атрибуты), и из словарей."""
    for key in path:
        if obj is None:
            return None
        obj = obj.get(key) if isinstance(obj, dict) else getattr(obj, key, None)
    return obj


def _spotapi_diag() -> str:
    """Что реально лежит в установленной SpotAPI: версия, файлы пакета, публичные имена."""
    import importlib.metadata as md
    import os
    import spotapi
    try:
        ver = md.version("spotapi")
    except Exception:
        ver = "?"
    path = list(getattr(spotapi, "__path__", []))
    files = sorted(os.listdir(path[0]))[:30] if path else []
    names = [n for n in dir(spotapi) if not n.startswith("_")][:30]
    return f"версия {ver}; файлы пакета: {files}; имена: {names}"


def _spotapi_public():
    """Находит класс Public в SpotAPI v2 (spotapi.v2 или spotapi.sync), импортируя подмодули явно."""
    import importlib
    for modname in ("spotapi.v2", "spotapi.sync"):
        try:
            mod = importlib.import_module(modname)
        except Exception as e:
            print(f"SpotAPI: {modname}: {type(e).__name__}: {e}", file=sys.stderr)
            continue
        public = getattr(mod, "Public", None)
        if public is not None:
            return public
    return None


def _spotapi_v2_first_page(query: str, public) -> list:
    """SpotAPI v2: Public.search_tracks(...) отдаёт страницы асинхронно."""
    import asyncio
    import inspect
    gen = public.search_tracks(query)

    async def first():
        if hasattr(gen, "__aiter__"):
            async for page in gen:
                return list(page)
        elif inspect.isawaitable(gen):
            return list(await gen)
        else:
            for page in gen:
                return list(page)
        return []

    return asyncio.run(first())


def _artist_name(track) -> str:
    try:
        arts = _dig(track, "artists")
        if isinstance(arts, dict):
            arts = arts.get("items")
        elif arts is not None and not isinstance(arts, (list, tuple)):
            arts = getattr(arts, "items", None)
        first = list(arts)[0] if arts else None
        return str(_dig(first, "profile", "name") or _dig(first, "name") or "")
    except (TypeError, IndexError):
        return ""


def spotapi_track(query: str) -> tuple[str, str] | None:
    """Поиск трека через библиотеку SpotAPI (github.com/Aran404/SpotAPI): запросы как у веб-плеера Spotify,
    без ключей и без Premium. Поддержаны: 2.x (await Public.search), v1 (Song) и ранняя бета v2."""
    if not ensure_spotapi():
        return None
    import asyncio
    import importlib
    import inspect
    import spotapi

    async def _await(x):
        return await x

    public = getattr(spotapi, "Public", None)
    song_cls = getattr(spotapi, "Song", None)
    if public is not None and hasattr(public, "search"):         # SpotAPI 2.x: results = await Public.search(...)
        res = public.search(query, limit=5)
        if inspect.isawaitable(res):
            res = asyncio.run(_await(res))
        raw = list(_dig(res, "tracks") or [])
    elif song_cls is not None:                                   # v1
        if _SPOTAPI["song"] is None:
            _SPOTAPI["song"] = song_cls()
        data = _SPOTAPI["song"].query_songs(query, limit=5)
        raw = [it["item"]["data"] for it in data["data"]["searchV2"]["tracksV2"]["items"]]
    else:                                                        # ранняя бета v2
        pub = _spotapi_public()
        if pub is None:
            raise RuntimeError("в SpotAPI не нашлось ни Public.search, ни Song. " + _spotapi_diag())
        raw = _spotapi_v2_first_page(query, pub)
    print(f"SpotAPI: найдено {len(raw)}")
    for d in raw:
        uri = _dig(d, "uri") or (f"spotify:track:{_dig(d, 'id')}" if _dig(d, "id") else "")
        if not str(uri).startswith("spotify:track:"):
            fields = list(d)[:20] if isinstance(d, dict) else [a for a in dir(d) if not a.startswith("_")][:20]
            print(f"SpotAPI: у результата нет track-uri ({uri!r}), поля: {fields}", file=sys.stderr)
            continue
        return str(uri), f"{_dig(d, 'name') or ''} — {_artist_name(d)}"
    return None


def find_track_keyless(query: str) -> tuple[str, str] | None:
    """Перебирает источники без ключей: iTunes + Songlink, потом поисковик. Возвращает (uri, название) или None."""
    for name, fn in (("SpotAPI", spotapi_track),
                     ("iTunes+Songlink", itunes_songlink_track),
                     ("DuckDuckGo", lambda q: (lambda u: (u, "") if u else None)(web_find_track(q)))):
        try:
            res = fn(query)
        except Exception as e:                    # SpotAPI бросает свои исключения: любая ошибка источника не должна ронять помощника
            print(f"Поиск трека ({name}): {type(e).__name__}: {e}", file=sys.stderr)
            continue
        if res:
            print(f"Трек найден через {name}")
            return res
        print(f"Поиск трека ({name}): ничего не нашлось", file=sys.stderr)
    return None


def web_find_track(query: str) -> str | None:
    """Без ключей и Premium: ищем в DuckDuckGo страницу трека open.spotify.com/track/<id>. Возвращает spotify:track:<id>."""
    from urllib.parse import quote
    url = "https://html.duckduckgo.com/html/?q=" + quote("site:open.spotify.com/track " + query)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64; rv:128.0) Gecko/20100101 Firefox/128.0"})
    with urllib.request.urlopen(req, timeout=10) as r:
        page = r.read().decode("utf-8", "replace")
    m = re.search(r"open\.spotify\.com(?:%2F|/)(?:intl-[a-z]+(?:%2F|/))?track(?:%2F|/)([A-Za-z0-9]{22})", page)
    return f"spotify:track:{m.group(1)}" if m else None


def spotify_open_search(query: str) -> None:
    """Запасной вариант: открыть в Spotify страницу поиска, дальше выбрать можно руками."""
    from urllib.parse import quote
    try:
        subprocess.Popen(["xdg-open", "spotify:search:" + quote(query)], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL, start_new_session=True)
    except OSError:
        pass


def _spotify_player() -> str | None:
    for name, _ in mpris_players():
        if "spotify" in name.lower():
            return name
    return None


SPOTIFY_KEEP_MINIMIZED = True    # True: запущенный Мими Spotify остаётся свёрнутым; False: окно открывается как обычно


def _minimize_windows_loop(wm_class: str, seconds: float = 15.0) -> None:
    """Сворачивает окна программы, пока они не появились/не свернулись (окно открывается с задержкой).
    Нужен xdotool (X11 / XWayland) или wmctrl. На чистом Wayland окно свернуть снаружи нельзя."""
    end = time.time() + seconds
    while time.time() < end:
        if shutil.which("xdotool"):
            subprocess.run(["xdotool", "search", "--onlyvisible", "--class", wm_class, "windowminimize", "%@"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        elif shutil.which("wmctrl"):
            subprocess.run(["wmctrl", "-x", "-r", f"{wm_class}.{wm_class}", "-b", "add,hidden"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            return
        time.sleep(0.5)


def spotify_play_uri(uri: str) -> bool:
    """Включает spotify:track:... в десктопном Spotify (если не запущен — запускает и ждёт до 30 секунд)."""
    name = _spotify_player()
    if not name:
        if not launch_app("spotify", ("--minimized",) if SPOTIFY_KEEP_MINIMIZED else ()):
            return False
        if SPOTIFY_KEEP_MINIMIZED:
            threading.Thread(target=_minimize_windows_loop, args=("spotify",), daemon=True).start()
        for _ in range(30):
            time.sleep(1)
            name = _spotify_player()
            if name:
                break
        else:
            return False
        time.sleep(2)                                     # плееру нужно секунду-две после появления на шине
    return _gdbus("--dest", name, "--object-path", "/org/mpris/MediaPlayer2",
                  "--method", "org.mpris.MediaPlayer2.Player.OpenUri", uri) is not None


# ---------- основной цикл помощника (в отдельном потоке) ----------
class Assistant(threading.Thread):
    def __init__(self, cfg: dict):
        super().__init__(daemon=True)
        self.cfg = cfg
        self.state = "Запуск…"
        self.running = True
        self.user_paused = False   # зелёная кнопка: микрофон на паузе
        self.hold = False          # окно настроек открыто: на это время микрофон тоже не слушает
        self.open_settings = False  # флаг: окно персонажа откроет настройки в главном потоке
        self.history = clean_history(read_json(MEM_PATH, []))
        self.rec = self.mic = None  # появляются в run()
        self._preroll: list[bytes] = []   # начало фразы, которой тебя перебили
        self._interrupted = False         # последнюю её фразу оборвали

    @property
    def paused(self) -> bool:
        return self.user_paused or self.hold

    @paused.setter
    def paused(self, on: bool) -> None:
        self.user_paused = bool(on)

    def toggle_pause(self) -> None:
        self.user_paused = not self.user_paused

    def ask(self, text: str) -> tuple[str, str | None]:
        msgs = [{"role": m["role"], "content": m["content"]} for m in self.history[-HISTORY_LIMIT:]]
        msgs.append({"role": "user", "content": text})
        answer, cmd = split_command(ask_llm(self.cfg, msgs))
        seen = {norm(split_command(m["content"])[0]) for m in self.history[-10:] if m["role"] == "assistant"}
        if REFUSAL_RE.search(answer) or (answer and norm(answer) in seen):
            # отказ или повтор прежнего ответа: ещё раз, с подсказкой и свободнее по температуре
            hint = text + "\n(Ответь по-новому, другими словами, не повторяя прежние ответы.)"
            retry, cmd2 = split_command(ask_llm(self.cfg, msgs[:-1] + [{"role": "user", "content": hint}], 1.0))
            if retry and not REFUSAL_RE.search(retry) and norm(retry) not in seen:
                answer, cmd = retry, cmd2 or cmd
            else:
                answer = random.choice(FALLBACKS)
        if not answer and cmd:                  # модель написала только команду: добавим короткую фразу вслух
            answer = random.choice(ACK_PHRASES)
        stored = answer + (" {{cmd: " + cmd + "}}" if cmd else "")   # в памяти остаётся и команда: так модель помнит формат
        now = time.strftime("%Y-%m-%d %H:%M:%S")
        self.history += [
            {"role": "user", "content": text, "time": now},
            {"role": "assistant", "content": stored, "time": now},
        ]
        if self.cfg.get("keep_memory", True):      # переключатель «Сохранять историю» в меню профиля
            write_json(MEM_PATH, self.history)
        return answer, cmd

    def transcribe(self, rec, audio) -> str:
        """Речь в текст: Whisper (если сервис его даёт и выбран), иначе или при ошибке Google."""
        if len(audio.frame_data) / (audio.sample_rate * audio.sample_width) < MIN_PHRASE_SEC:
            return ""  # хлопок, щелчок, стук
        model = next((m for host, m in WHISPER_MODELS.items() if host in self.cfg["base_url"]), None)
        if model and self.cfg.get("stt", "whisper") == "whisper":
            try:
                text = whisper_text(self.cfg, model, audio)
                junk = len(text) < 60 and any(j in text.lower() for j in WHISPER_JUNK)
                return "" if junk else text
            except Exception as e:
                print("Whisper:", e, "— пробую Google", file=sys.stderr)
        return rec.recognize_google(audio, language=STT_LANG)

    def listen(self, mic, rec, timeout: float = 10, phrase_limit: float = 15):
        """Слушает одну фразу короткими кусками (~20-60 мс). В отличие от rec.listen, пауза и
        закрытие окна срабатывают сразу, а не через 10-25 секунд. Возвращает AudioData или None."""
        sec = mic.CHUNK / mic.SAMPLE_RATE
        keep = max(1, round(rec.non_speaking_duration / sec))   # тишина до и после фразы
        need = max(1, round(rec.phrase_threshold / sec))        # меньше этого — шум, не фраза
        lead = deque(maxlen=keep)
        frames: list[bytes] = list(self._preroll)               # ею перебили: фраза уже идёт
        self._preroll = []
        started, voiced, quiet, waited, length = bool(frames), len(frames), 0, 0.0, len(frames) * sec
        while self.running and not self.paused:
            buf = mic.stream.read(mic.CHUNK)
            e = rms(buf)
            if not started:
                waited += sec
                if e > rec.energy_threshold:
                    started, frames, voiced, quiet, length = True, list(lead) + [buf], 1, 0, 0.0
                    continue
                lead.append(buf)
                if rec.dynamic_energy_threshold:   # подстройка под шум, как в speech_recognition
                    damp = rec.dynamic_energy_adjustment_damping ** sec
                    rec.energy_threshold = (rec.energy_threshold * damp
                                            + e * rec.dynamic_energy_ratio * (1 - damp))
                if waited > timeout:
                    return None
                continue
            frames.append(buf)
            length += sec
            if e > rec.energy_threshold:
                voiced, quiet = voiced + 1, 0
            else:
                quiet += 1
            if quiet * sec > rec.pause_threshold or length > phrase_limit:
                if voiced < need:           # щелчок или шорох: слушаем дальше
                    started, frames, voiced, quiet = False, [], 0, 0
                    continue
                if quiet > keep:            # лишнюю тишину в конце срезаем
                    del frames[len(frames) - (quiet - keep):]
                return sr.AudioData(b"".join(frames), mic.SAMPLE_RATE, mic.SAMPLE_WIDTH)
        return None

    def _watch_interrupt(self, stop: threading.Event) -> None:
        """Пока она говорит, слушает микрофон. Если ты заговорил заметно громче её эха из колонок,
        обрывает озвучку и оставляет начало твоей фразы для listen(), чтобы оно не потерялось."""
        mic, rec = self.mic, self.rec
        sec = mic.CHUNK / mic.SAMPLE_RATE
        need = max(1, round(BARGE_IN_SEC / sec))   # столько кусков подряд громче порога
        warm = round(BARGE_IN_WARM / sec)          # сначала идёт только замер её эха
        ring = deque(maxlen=need + round(0.15 / sec))
        echo, loud, ticks = 0.0, 0, 0
        while not stop.is_set() and self.running and not self.paused:
            buf = mic.stream.read(mic.CHUNK)
            if not _playing.is_set():              # звук ещё не пошёл (синтез) или уже кончился
                ring.clear()
                echo, loud, ticks = 0.0, 0, 0
                continue
            e = rms(buf)
            ring.append(buf)
            ticks += 1
            if ticks > warm and e > max(rec.energy_threshold * BARGE_IN_FLOOR, echo * BARGE_IN_FACTOR):
                loud += 1                          # при серии громких кусков эхо не обновляем
                if loud >= need:
                    self._preroll = list(ring)
                    self._interrupted = True
                    stop_speaking()
                    return
            else:
                loud = 0
                echo = max(e, echo * BARGE_IN_DECAY)   # огибающая эха: быстро растёт, медленно спадает

    def say(self, text: str) -> None:
        """Говорит вслух; пока говорит, её можно перебить голосом."""
        self._interrupted = False
        stop, watcher = threading.Event(), None
        if BARGE_IN and self.mic is not None and self.mic.stream is not None and not self.paused:
            watcher = threading.Thread(target=self._watch_interrupt, args=(stop,), daemon=True)
            watcher.start()
        try:
            speak(text)
        finally:
            stop.set()
            if watcher:
                watcher.join(timeout=1.0)   # поток микрофона должен остановиться до закрытия потока

    def confirm(self, rec, mic) -> bool:
        """Ждёт голосовое «да» после вопроса помощника."""
        self.state = "Жду ответ…"
        audio = self.listen(mic, rec, timeout=8, phrase_limit=5)
        if audio is None:
            return False
        try:
            text = rec.recognize_google(audio, language=STT_LANG).lower()
        except (sr.UnknownValueError, sr.RequestError):
            return False
        print("Вы:", text)
        words = set(re.findall(r"\w+", text))
        return bool(words & YES_WORDS) and "нет" not in words

    def play_track(self, query: str) -> None:
        """Голосовое «включи трек X»: ищем трек и запускаем в приложении Spotify.
        Если в config.json есть ключи Spotify и у владельца Premium, ищем через API; иначе без ключей, через поисковик."""
        query = re.sub(r"[\-\u2010-\u2015\u2212+«»\",.;:!?]+", " ", query)    # неразрывный дефис и т.п. ломают поиск
        query = re.sub(r"\s+", " ", query).strip()
        uri, title = None, ""
        creds = spotify_creds()
        if creds:
            try:
                found = spotify_find_track(query, *creds)
                if found:
                    uri, title = found[0], f"{found[1]} — {found[2]}"
            except urllib.error.HTTPError as e:
                print(f"Spotify API: HTTP {e.code}, ищу без API", file=sys.stderr)
            except (urllib.error.URLError, OSError, ValueError, KeyError) as e:
                print("Spotify API:", e, file=sys.stderr)
        if not uri:
            res = find_track_keyless(query)
            if res:
                uri, title = res
        if not uri:
            canon = _LAST_CATALOG["title"].replace(" — ", " ").strip()
            print(f"Трек не найден по запросу «{query}», открываю поиск Spotify: «{canon or query}»")
            self.say("Сама включить не смогла, открываю поиск в спотифае. Нажми воспроизведение.")
            spotify_open_search(canon or query)
            return
        print(f"Spotify: {title or query} ({uri})")
        if not spotify_play_uri(uri):
            self.say("Не получилось включить. Проверь, что спотифай установлен.")

    def execute(self, cmd: str, rec, mic) -> None:
        """Запускает команду из ответа модели с защитой от опасных действий."""
        print("Команда:", cmd)
        if cmd == "__settings__":
            self.open_settings = True
            return
        if cmd == "__exit__":
            self.running = False
            return
        if cmd.startswith("__play__"):
            q = cmd[len("__play__"):].strip(" «»\"'.,!?")
            if q:
                self.play_track(q)
            return
        always = self.cfg.get("safe_mode") == "always"     # «Безопасный режим: всегда спрашивать»
        if cmd.startswith("__open__"):
            name = cmd[len("__open__"):].strip()
            if always:
                self.state = "Говорю…"
                self.say(f"Запустить {name}? Скажи да или нет.")
                if not self.confirm(rec, mic):
                    self.say("Хорошо, не буду.")
                    return
            if not launch_app(name):
                self.say("Не нашла такое приложение, мой господин.")
            return
        try:
            args = shlex.split(cmd)  # без shell: pipe, && и подстановки не работают
        except ValueError:
            self.say("Не поняла команду.")
            return
        prog = Path(args[0]).name if args else ""
        if not prog or prog in DENY_CMDS:
            self.say("Такое я выполнять не буду.")
            return
        if prog not in SAFE_CMDS or always:
            self.state = "Говорю…"
            self.say("Это не из моего списка безопасных команд. Выполнить? Скажи да или нет."
                     if prog not in SAFE_CMDS else "Выполнить команду? Скажи да или нет.")
            if not self.confirm(rec, mic):
                self.say("Хорошо, не буду.")
                return
        if prog == "playerctl" and len(args) == 2 and args[1] in MEDIA_ACTIONS:
            if not media_control(args[1]):            # не вышло: плеера не видно или нет ни gdbus, ни playerctl
                self.say("Не вижу запущенного плеера. Включи музыку, и я смогу ей управлять.")
            return
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        with open(CMD_LOG, "a", encoding="utf-8") as log:
            log.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {cmd}\n")
            log.flush()
            try:
                proc = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=log,
                                        start_new_session=True)
            except FileNotFoundError:
                if not launch_app(prog):          # нет такого файла: ищем среди установленных приложений
                    self.say("Не нашла такую программу.")
                return
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                return  # приложение запущено и продолжает работать, его не трогаем
        if proc.returncode != 0:
            print(f"Команда завершилась с кодом {proc.returncode}, подробности в {CMD_LOG}", file=sys.stderr)
            scheme = re.match(r"([a-z][a-z0-9+.-]*)://", args[1]) if prog == "xdg-open" and len(args) > 1 else None
            if scheme and scheme.group(1) not in ("http", "https", "file", "mailto"):
                if launch_app(scheme.group(1)):   # xdg-open не знает такую ссылку: открываем приложение напрямую
                    return
            self.say("Не получилось выполнить команду.")

    def run(self):
        threading.Thread(target=ensure_spotapi, daemon=True).start()   # SpotAPI ставится в фоне, пока грузится голос
        if TTS_ENGINE == "silero":
            self.state = "Загрузка голоса…"
            try:
                load_silero()
            except Exception:
                pass  # ошибка уже напечатана, дальше будет говорить espeak-ng
        self.rec = rec = sr.Recognizer()
        try:
            self.mic = mic = sr.Microphone()
        except OSError as e:
            self.state = "Микрофон не найден"
            print("Микрофон:", e, file=sys.stderr)
            return
        calibrated = False
        while self.running:
            if self.paused and PAUSE_CLOSES_MIC:  # поток микрофона закрыт совсем, он не просто «не слушается»
                self.state = "Пауза"
                time.sleep(0.2)
                continue
            try:
                with mic:
                    if not calibrated:
                        self.state = "Калибровка микрофона…"
                        rec.adjust_for_ambient_noise(mic, duration=1)
                        calibrated = True
                    self.converse(mic, rec)
            except OSError as e:  # микрофон занят или отключили
                print("Микрофон:", e, file=sys.stderr)
                time.sleep(2)

    def converse(self, mic, rec) -> None:
        """Слушаем, думаем, отвечаем. Выходит, когда нажата пауза (если PAUSE_CLOSES_MIC) или окно закрыто."""
        while self.running and (not self.paused or not PAUSE_CLOSES_MIC):
            if self.paused:                     # пауза без закрытия микрофона: звук читаем и выбрасываем,
                self.state = "Пауза"            # поток не закрывается, поэтому паузу можно снять сразу
                mic.stream.read(mic.CHUNK)
                continue
            self.state = "Слушаю…"
            audio = self.listen(mic, rec)
            if audio is None:
                continue
            t_heard = time.time()
            try:
                text = self.transcribe(rec, audio)
            except (sr.WaitTimeoutError, sr.UnknownValueError):
                continue
            except sr.RequestError as e:
                print("Ошибка распознавания:", e, file=sys.stderr)
                time.sleep(3)
                continue
            if not text or self.paused:  # нажали «выключить микрофон» — эту фразу выбрасываем
                continue

            print(f"Вы: {text}   (⏱ распознавание: {time.time() - t_heard:.1f} с)")
            if text.lower().strip() in EXIT_WORDS:
                self.state = "Говорю…"
                self.say("До встречи!")
                self.running = False
                break

            if SETTINGS_RE.search(text):  # без модели: быстро и без отказов
                self.state = "Говорю…"
                self.say("Открываю настройки, мой господин.")
                self.open_settings = True
                continue

            track = parse_track_request(text)
            if track:                     # «включи трек ...»: без модели, сразу в Spotify
                self.state = "Думаю…"
                self.play_track(track)
                continue

            self.state = "Думаю…"
            t_ask = time.time()
            try:
                answer, cmd = self.ask(text)
            except Exception as e:  # неверный ключ, сеть, лимиты
                print("Ошибка API:", e, file=sys.stderr)
                answer, cmd = "Не получилось получить ответ. Проверьте ключ и интернет.", None
            if not self.running:  # окно закрыли, пока шёл запрос
                break
            print(f"Помощник: {answer}   (⏱ модель: {time.time() - t_ask:.1f} с)")

            self.state = "Говорю…"
            if answer:
                self.say(answer)
            if cmd and not self._interrupted:  # перебили — команду не выполняем, сначала выслушаем
                self.execute(cmd, rec, mic)


# ---------- окно с персонажем ----------
BUTTONS = [("#ff5f57", "×"), ("#febc2e", "−")]  # закрыть, свернуть: столбиком слева (пауза микрофона — правый кружок)
BTN_X, BTN_STEP, BTN_Y, BTN_R = 19, 22, 19, 7          # центр по x, шаг по вертикали, y первой кнопки, радиус
BTN_PLATE = QRectF(6, 6, 26, 22 * (len(BUTTONS) - 1) + 26)   # зона наведения над кнопками (самой плашки не видно)
MIC_R = BTN_R               # радиус правого кружка с микрофоном: такой же, как у кнопок слева
DOT_COLORS = {"Слушаю": "#3ddc84", "Думаю": "#ffc107", "Говорю": "#4aa3ff",
              "Пауза": "#9e9e9e", "Микрофон": "#e74c3c"}


class _CharOverlay(QWidget):
    """Прозрачный слой над 3D-моделью: на нём рисуются кнопки окна и кружок микрофона."""

    def __init__(self, owner: "CharacterWindow"):
        super().__init__(owner)
        self.owner = owner
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        self.owner.paint_controls(p)
        p.end()


class CharacterWindow(QWidget):
    def __init__(self, bot: Assistant, cfg: dict):
        super().__init__()
        self.bot, self.hover, self.movie = bot, False, None
        self.model_view, self.overlay = None, None             # 3D-модель и слой с кнопками поверх неё
        self.pix, movie = load_character(cfg)
        pixmap = self.pix
        self.mic_on_pix = draw_icon("mic", "#ffffff", 9)       # значок в правом кружке: микрофон слушает
        self.mic_off_pix = draw_icon("mic_off", "#ffffff", 9)  # он же, когда микрофон выключен (кружок красный)
        self.setWindowTitle("Помощник")
        if QApplication.windowIcon().isNull():     # иначе остаётся значок приложения MI
            self.setWindowIcon(QIcon(pixmap))
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint)  # поверх всех окон
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)  # прозрачные места PNG
        self.setMouseTracking(True)
        if self.show_model(cfg):
            if movie is not None:
                movie.deleteLater()                            # GIF не нужен: вместо него 3D-модель
        else:
            self.set_character(self.pix, movie)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(100)

    def set_character(self, pix: QPixmap, movie: QMovie | None) -> None:
        """Подставляет картинку или GIF и подгоняет под них размер окна."""
        if self.movie is not None:
            self.movie.stop()
            try:
                self.movie.frameChanged.disconnect(self.update)
            except TypeError:
                pass
            self.movie.deleteLater()
        self.pix, self.movie = pix, movie
        if movie is not None:
            movie.setParent(self)
            movie.frameChanged.connect(self.update)   # новый кадр: перерисовать окно
        self.mic_rect = QRectF(self.pix.width() - BTN_X - 11, BTN_Y - 11, 22, 22)   # зона клика чуть больше кружка  # клик по кружку справа: микрофон вкл / выкл
        self.setFixedSize(self.pix.size())
        self.adjustSize()
        self.update()

    def apply_character(self, cfg: dict) -> None:
        if not self.show_model(cfg):
            self.set_character(*load_character(cfg))

    def hide_model(self) -> None:
        if self.model_view is not None:
            self.model_view.hide()
            self.model_view.deleteLater()
            self.model_view = None
        if self.overlay is not None:
            self.overlay.hide()
            self.overlay.deleteLater()
            self.overlay = None

    def show_model(self, cfg: dict) -> bool:
        """Настройка «3D-модель вместо картинки»: в окне ставится покачивающаяся 3D-фигура.
        False — модель не нужна или недоступна, тогда окно рисует картинку или GIF как раньше."""
        self.hide_model()
        if not model3d_ready(cfg):
            return False
        if self.movie is not None:                             # GIF от прошлых настроек останавливаем
            self.movie.stop()
            try:
                self.movie.frameChanged.disconnect(self.update)
            except TypeError:
                pass
            self.movie.deleteLater()
            self.movie = None
        scale = float(cfg.get("char_scale", 1.0) or 1.0)
        w, h = max(120, round(MODEL_WIN_SIZE[0] * scale)), max(180, round(MODEL_WIN_SIZE[1] * scale))
        self.pix = QPixmap(w, h)
        self.pix.fill(Qt.GlobalColor.transparent)
        self.mic_rect = QRectF(w - BTN_X - 11, BTN_Y - 11, 22, 22)
        self.setFixedSize(w, h)
        mv = ModelView(load_pixmap(scale), w, h, parent=self, model_path=cfg.get("model_path", ""),
                       render=(max(w, MODEL_WIN_SIZE[0]), max(h, MODEL_WIN_SIZE[1])),
                       interactive=False, animate=bool(cfg.get("model_anim", MODEL_ANIM)))
        mv.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)   # перетаскивание и клики ловит окно
        mv.setGeometry(0, 0, w, h)
        mv.show()
        ov = _CharOverlay(self)                                # кнопки рисуются поверх модели
        ov.setGeometry(0, 0, w, h)
        ov.show()
        ov.raise_()
        self.model_view, self.overlay = mv, ov
        self.update()
        return True

    def sync_model_mood(self) -> None:
        """Говорит — пока реально звучит голос; думает — пока ждёт ответ модели."""
        if self.model_view is None:
            return
        now = time.time()
        if _playing.is_set():
            self._model_talk_until = now + 0.4            # короткая пауза между предложениями не считается тишиной
        if now < getattr(self, "_model_talk_until", 0):
            mood = "talk"
        elif self.bot.state.startswith(("Думаю", "Жду ответ")):
            mood = "think"
        else:
            mood = "idle"
        self.model_view.set_mood(mood)

    def repaint_all(self) -> None:
        self.update()
        if self.overlay is not None:
            self.overlay.update()

    def sync_movie(self) -> None:
        """GIF идёт, пока реально звучит голос; в тишине замирает на первом кадре."""
        if self.movie is None:
            return
        now = time.time()
        if _playing.is_set():
            self._talk_until = now + 0.4      # короткая пауза между предложениями не считается тишиной
        talking = now < getattr(self, "_talk_until", 0)
        state = self.movie.state()
        if talking:
            if state == QMovie.MovieState.NotRunning:
                self.movie.start()
            elif state == QMovie.MovieState.Paused:
                self.movie.setPaused(False)
        elif state != QMovie.MovieState.NotRunning:
            self.movie.stop()
            self.movie.jumpToFrame(0)
            self.update()

    def current_pix(self) -> QPixmap:
        return self.movie.currentPixmap() if self.movie is not None else self.pix

    def tick(self) -> None:
        if not self.bot.running and self.bot.state != "Микрофон не найден":
            self.close()
            return
        if self.bot.open_settings:
            self.bot.open_settings = False
            self.show_settings()
        self.setWindowTitle(f"Помощник — {self.bot.state}")
        self.sync_movie()
        self.sync_model_mood()
        self.repaint_all()

    def show_settings(self) -> None:
        """Открывает окно настроек поверх работающего помощника, без перезапуска."""
        if getattr(self, "_settings_open", False):      # окно настроек уже открыто (оно больше не блокирует остальное)
            return
        self._settings_open = True
        self.bot.hold = True  # на время настройки микрофон не слушает
        try:
            dlg = SettingsDialog(read_json(CFG_PATH, {}), running=True)
            if dlg.exec() == QDialog.DialogCode.Accepted and dlg.cfg:
                self.bot.cfg = dlg.cfg      # новые ключ, модель, промт и режим команд подхватываются сразу
                apply_voice(dlg.cfg)        # голос, тон и скорость тоже
                self.apply_character(dlg.cfg)   # и как она нарисована: 3D-модель, картинка или GIF
        finally:
            self._settings_open = False
            self.bot.hold = False           # кнопка паузы остаётся как была: настройки её состояние не трогают

    def button_at(self, pos) -> int | None:
        for i in range(len(BUTTONS)):
            dx, dy = pos.x() - BTN_X, pos.y() - (BTN_Y + i * BTN_STEP)
            if dx * dx + dy * dy <= (BTN_R + 2) ** 2:
                return i
        return None

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        if self.model_view is None:                    # в режиме 3D картинку рисует сама модель, кнопки — слой поверх
            p.drawPixmap(QRect(0, 0, self.width(), self.height()), self.current_pix())   # кадр всегда по размеру окна
            self.paint_controls(p)

    def paint_controls(self, p: QPainter) -> None:
        for i, (color, glyph) in enumerate(BUTTONS):   # без плашки: кнопки рисуются прямо поверх картинки
            c = QPointF(BTN_X, BTN_Y + i * BTN_STEP)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(color))
            p.drawEllipse(c, BTN_R, BTN_R)
            if self.hover:  # значки на кнопках появляются при наведении, как в macOS
                p.setPen(QColor(60, 20, 20))
                p.drawText(QRectF(c.x() - BTN_R, c.y() - BTN_R, 2 * BTN_R, 2 * BTN_R),
                           Qt.AlignmentFlag.AlignCenter, glyph)
        if STATUS_DOT:                        # правый кружок: состояние, а при выключенном микрофоне он красный
            p.setPen(Qt.PenStyle.NoPen)           # без обводки, как у кнопок слева
            color = "#e74c3c" if self.bot.paused else next(
                (c for k, c in DOT_COLORS.items() if self.bot.state.startswith(k)), "#888888")
            p.setBrush(QColor(color))
            cx = self.width() - BTN_X             # зеркально красной кнопке слева
            p.drawEllipse(QPointF(cx, BTN_Y), MIC_R, MIC_R)
            icon = self.mic_off_pix if self.bot.paused else self.mic_on_pix
            p.drawPixmap(int(cx - icon.width() / icon.devicePixelRatio() / 2),
                         int(BTN_Y - icon.height() / icon.devicePixelRatio() / 2), icon)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.RightButton:  # правый клик по персонажу = настройки
            self.show_settings()
            return
        if e.button() != Qt.MouseButton.LeftButton:
            return
        if self.mic_rect.contains(e.position()):  # клик по правому кружку: микрофон включить / выключить
            self.bot.toggle_pause()
            self.repaint_all()
            return
        i = self.button_at(e.position())
        if i == 0:
            self.close()
        elif i == 1:
            self.showMinimized()
        else:
            self.windowHandle().startSystemMove()  # перетаскивание средствами композитора (Wayland/X11)

    def mouseMoveEvent(self, e):
        hover = BTN_PLATE.contains(e.position())
        if hover != self.hover:
            self.hover = hover
            self.repaint_all()

    def leaveEvent(self, _):
        self.hover = False
        self.repaint_all()

    def closeEvent(self, e):
        self.bot.running = False
        shutdown_speech()                 # замолчать сразу, плеер убиваем, новых фраз не будет
        if self.bot.is_alive():
            self.bot.join(timeout=1.5)    # дать потоку закрыть микрофон
        close_dev_window()                # отдельная консоль закрывается вместе с Мими
        super().closeEvent(e)


# ---------- тема в стиле neverlose ----------
ACCENT = "#4b7eff"          # единый акцентный цвет (взят со скриншота): меняется здесь, и везде сразу
ACCENT_LIGHT = "#5b8aff"
ACCENT_HOVER = "#6b94ff"
ACCENT_DOWN = "#3a67e6"
ACCENT_NAME = "Синий"
# (название, основной, светлый край кнопки, при наведении, при нажатии)
ACCENTS = [("Синий", "#4b7eff", "#5b8aff", "#6b94ff", "#3a67e6"),
           ("Фиолетовый", "#8b5cf6", "#9b72f8", "#a78bfa", "#7040e0"),
           ("Розовый", "#ec4899", "#f05ba8", "#f472b6", "#cf3584"),
           ("Зелёный", "#22c55e", "#3dd073", "#4ade80", "#16a34a"),
           ("Оранжевый", "#f59e0b", "#f7ae2b", "#fbbf24", "#d98706")]


def set_accent(name: str) -> None:
    """Меняет акцентный цвет в переменных; стили применяет restyle()."""
    global ACCENT, ACCENT_LIGHT, ACCENT_HOVER, ACCENT_DOWN, ACCENT_NAME
    row = next((a for a in ACCENTS if a[0] == name), None)
    if row is None:
        c = QColor(name) if isinstance(name, str) and name.startswith("#") else QColor()
        if c.isValid():                                    # свой цвет: остальные оттенки считаем сами
            row = (cn(c), cn(c), cn(c.lighter(108)), cn(c.lighter(122)), cn(c.darker(118)))
        else:
            row = ACCENTS[0]
    ACCENT_NAME, ACCENT, ACCENT_LIGHT, ACCENT_HOVER, ACCENT_DOWN = row
    apply_overrides()


def restyle() -> None:
    """Перекрашивает уже открытые окна под новый акцент."""
    app = QApplication.instance()
    if app is None:
        return

    def do():
        apply_dark_theme(app)
        for w in app.topLevelWidgets():
            if isinstance(w, SettingsDialog):
                w.refresh_scale_qss()          # свои стили окна настроек (при масштабе не 100%)
                w.refresh_glow()
        for w in app.allWidgets():
            w.update()
    QTimer.singleShot(0, do)    # после обработки клика: не посреди события всплывающего меню
THEMES = {
    "dark": dict(BG="#080a11", SIDEBAR="#05070c", CARD="#0d1019", CONTROL="#171a24", SELECTED="#1d212c",
                 BORDER="#1a1e2b", BORDER_HOVER="#2a3042", TEXT="#c9ccd6", MUTED="#6b7180", DIM="#4a505c",
                 NAV_IDLE="#838998", STRONG="#ffffff", POP_BG="#0b0e16", POP_BORDER="#222839",
                 GROOVE="#232736", DISABLED_BG="#101319", SEL_BG="#1b2548", SCROLL="#262b39",
                 ROWSEP="#141824", VALUEBOX="#aab0be", VALUE_C="#9399a6", WINBTN_HOVER="#2a1820",
                 HOVER_OV=(255, 255, 255), HOVER_RGBA="rgba(255, 255, 255, 12)"),
    "light": dict(BG="#f3f5fa", SIDEBAR="#e8ebf3", CARD="#ffffff", CONTROL="#eceff6", SELECTED="#dde3f0",
                  BORDER="#d9deea", BORDER_HOVER="#b9c1d4", TEXT="#2a2f3d", MUTED="#667087", DIM="#8a92a6",
                  NAV_IDLE="#566074", STRONG="#10131b", POP_BG="#ffffff", POP_BORDER="#d3d9e6",
                  GROOVE="#cdd3e2", DISABLED_BG="#e3e6ee", SEL_BG="#cfdcff", SCROLL="#c1c8da",
                  ROWSEP="#e6e9f1", VALUEBOX="#4a5163", VALUE_C="#566074", WINBTN_HOVER="#fde2e2",
                  HOVER_OV=(0, 0, 0), HOVER_RGBA="rgba(0, 0, 0, 10)"),
}
THEME_NAME = "dark"
BUNDLED_FONTS: list[str] = []   # заполняется в main() из файлов assets/fonts/


# ---------- редактор темы: свои цвета поверх выбранной светлой / тёмной темы ----------
THEME_ROLES = [("bg", "Основной"), ("accent", "Визуальные модули"), ("text", "Текст"),
               ("muted", "Неактивный текст"), ("heading", "Текст заголовков"), ("premium", "Премиум текст"),
               ("slider", "Слайдер"), ("knob", "Круг слайдера"), ("groove", "Окно слайдера"),
               ("toggle_on", "Переключатель"), ("toggle_off", "Неактивный переключатель"),
               ("btn", "Кнопка"), ("btn_off", "Неактивная кнопка")]
# роль -> переменная, из которой берётся текущий цвет
ROLE_VARS = {"bg": "BG", "accent": "ACCENT", "text": "TEXT", "muted": "MUTED", "heading": "STRONG",
             "premium": "PREMIUM", "slider": "SLIDER_C", "knob": "KNOB_C", "groove": "GROOVE_C",
             "toggle_on": "TOGGLE_ON", "toggle_off": "TOGGLE_OFF", "btn": "BTN_BASE", "btn_off": "BTN_OFF_C"}
# готовые темы: набор цветов поверх светлой / тёмной (режим выбирается по яркости фона)
BUILTIN_THEMES = [
    ("Неон", {"bg": "#0b0714", "accent": "#ff3df0", "text": "#f3e8ff", "muted": "#8f7ab0", "heading": "#ffffff",
              "slider": "#22e5ff", "toggle_on": "#22e5ff"}),
    ("Закат", {"bg": "#150c10", "accent": "#ff6b3d", "text": "#ffe8dc", "muted": "#a67c72", "heading": "#fff4ee"}),
    ("Океан", {"bg": "#06111d", "accent": "#38bdf8", "text": "#d8ecff", "muted": "#6d8da9", "heading": "#ffffff"}),
    ("Мята", {"bg": "#07130f", "accent": "#2ee6a6", "text": "#ddfbef", "muted": "#6f9b8c", "heading": "#f2fff9"}),
    ("Золото", {"bg": "#100d07", "accent": "#f5b942", "text": "#f5ecd6", "muted": "#9d9072", "heading": "#fff8e6"}),
    ("Сакура", {"bg": "#fbf0f4", "accent": "#e0457b", "text": "#3b2430", "muted": "#9b7a88", "heading": "#2a1019"}),
    ("Лаванда", {"bg": "#f2effb", "accent": "#7c5cff", "text": "#2d2644", "muted": "#7e789a", "heading": "#1d1633"}),
]
NB = len(BUILTIN_THEMES)
USER_COLORS: dict = {}          # свои цвета (роль -> #rrggbb); пусто = обычная тема без изменений
PREMIUM = SLIDER_C = KNOB_C = GROOVE_C = TOGGLE_ON = TOGGLE_OFF = BTN_BASE = BTN_OFF_C = "#000000"
KNOB_H = "#dfe8ff"
BTN_A = BTN_B = BTN_HA = BTN_HB = BTN_DOWN = "#000000"
BTN_OFF_SET = False


def _hex_ok(c) -> bool:
    return isinstance(c, str) and len(c) in (7, 9) and c.startswith("#") and QColor(c).isValid()


def cn(c: QColor) -> str:
    """Цвет строкой: #rrggbb, а с прозрачностью #aarrggbb."""
    return c.name(QColor.NameFormat.HexArgb) if c.alpha() < 255 else c.name()


def role_color(role: str) -> str:
    """Текущий цвет элемента (с учётом своих цветов)."""
    return cn(QColor(globals()[ROLE_VARS[role]]))


def apply_overrides() -> None:
    """Накладывает USER_COLORS поверх переменных темы. Вызывается в конце set_theme() и set_accent()."""
    global BG, SIDEBAR, CARD, CONTROL, PANEL, SELECTED, BORDER, BORDER_HOVER, TEXT, MUTED, STRONG
    global POP_BG, POP_BORDER, DISABLED_BG, SCROLL, ROWSEP, ACCENT, ACCENT_LIGHT, ACCENT_HOVER, ACCENT_DOWN
    global PREMIUM, SLIDER_C, KNOB_C, KNOB_H, GROOVE_C, TOGGLE_ON, TOGGLE_OFF
    global BTN_BASE, BTN_A, BTN_B, BTN_HA, BTN_HB, BTN_DOWN, BTN_OFF_C, BTN_OFF_SET
    u = {k: v for k, v in USER_COLORS.items() if k in ROLE_VARS and _hex_ok(v)}
    if "bg" in u:                       # от фона считаем остальные поверхности, чтобы всё выглядело цельно
        b = QColor(u["bg"])
        white, black = QColor(255, 255, 255), QColor(0, 0, 0)

        def mix(t, to):
            return cn(QColor(round(b.red() + (to.red() - b.red()) * t), round(b.green() + (to.green() - b.green()) * t),
                             round(b.blue() + (to.blue() - b.blue()) * t), b.alpha()))
        BG = cn(b)
        if b.lightnessF() < 0.5:
            SIDEBAR, CARD, CONTROL, SELECTED = mix(.4, black), mix(.03, white), mix(.07, white), mix(.10, white)
            BORDER, BORDER_HOVER, POP_BG, POP_BORDER = mix(.08, white), mix(.16, white), mix(.02, white), mix(.12, white)
            DISABLED_BG, SCROLL, ROWSEP = mix(.04, white), mix(.13, white), mix(.05, white)
        else:
            SIDEBAR, CARD, CONTROL, SELECTED = mix(.04, black), mix(.6, white), mix(.05, black), mix(.09, black)
            BORDER, BORDER_HOVER, POP_BG, POP_BORDER = mix(.09, black), mix(.20, black), mix(.6, white), mix(.12, black)
            DISABLED_BG, SCROLL, ROWSEP = mix(.06, black), mix(.17, black), mix(.06, black)
        PANEL = CONTROL
    if "text" in u:
        TEXT = u["text"]
    if "muted" in u:
        MUTED = u["muted"]
    if "heading" in u:
        STRONG = u["heading"]
    if "accent" in u:
        c = QColor(u["accent"])
        ACCENT, ACCENT_LIGHT, ACCENT_HOVER, ACCENT_DOWN = cn(c), cn(c.lighter(108)), cn(c.lighter(122)), cn(c.darker(118))
    PREMIUM = u.get("premium", DIM)
    SLIDER_C = u.get("slider", ACCENT)
    KNOB_C = u.get("knob", "#ffffff")
    KNOB_H = cn(QColor(u["knob"]).darker(106)) if "knob" in u else "#dfe8ff"
    GROOVE_C = u.get("groove", GROOVE)
    TOGGLE_ON = u.get("toggle_on", ACCENT)
    TOGGLE_OFF = u.get("toggle_off", GROOVE)
    BTN_BASE = u.get("btn", ACCENT)
    if "btn" in u:
        c = QColor(u["btn"])
        BTN_A, BTN_B, BTN_HA, BTN_HB, BTN_DOWN = (cn(c.lighter(108)), cn(c.darker(118)), cn(c.lighter(122)),
                                                  cn(c), cn(c.darker(118)))
    else:
        BTN_A, BTN_B, BTN_HA, BTN_HB, BTN_DOWN = ACCENT_LIGHT, ACCENT_DOWN, ACCENT_HOVER, ACCENT, ACCENT_DOWN
    BTN_OFF_SET = "btn_off" in u
    BTN_OFF_C = u.get("btn_off", CONTROL)


def set_user_colors(d) -> None:
    """Заменяет свои цвета целиком (None или {} = вернуть обычную тему) и пересчитывает переменные."""
    USER_COLORS.clear()
    if isinstance(d, dict):
        USER_COLORS.update({k: cn(QColor(v)) for k, v in d.items() if k in ROLE_VARS and _hex_ok(v)})
    set_theme(THEME_NAME)
    set_accent(ACCENT_NAME)


def set_theme(name: str) -> None:
    """Переключает светлую / тёмную тему: меняет переменные цветов (стили применяет restyle())."""
    global THEME_NAME, BG, SIDEBAR, CARD, CONTROL, PANEL, SELECTED, BORDER, BORDER_HOVER, TEXT, MUTED, DIM
    global NAV_IDLE, STRONG, POP_BG, POP_BORDER, GROOVE, DISABLED_BG, SEL_BG, SCROLL, ROWSEP, VALUEBOX
    global VALUE_C, WINBTN_HOVER, HOVER_OV, HOVER_RGBA
    THEME_NAME = name if name in THEMES else "dark"
    t = THEMES[THEME_NAME]
    BG, SIDEBAR, CARD, CONTROL, SELECTED = t["BG"], t["SIDEBAR"], t["CARD"], t["CONTROL"], t["SELECTED"]
    PANEL = CONTROL             # (старое имя, чтобы ничего не сломать)
    BORDER, BORDER_HOVER, TEXT, MUTED, DIM = t["BORDER"], t["BORDER_HOVER"], t["TEXT"], t["MUTED"], t["DIM"]
    NAV_IDLE, STRONG, POP_BG, POP_BORDER = t["NAV_IDLE"], t["STRONG"], t["POP_BG"], t["POP_BORDER"]
    GROOVE, DISABLED_BG, SEL_BG, SCROLL = t["GROOVE"], t["DISABLED_BG"], t["SEL_BG"], t["SCROLL"]
    ROWSEP, VALUEBOX, VALUE_C, WINBTN_HOVER = t["ROWSEP"], t["VALUEBOX"], t["VALUE_C"], t["WINBTN_HOVER"]
    HOVER_OV, HOVER_RGBA = t["HOVER_OV"], t["HOVER_RGBA"]
    apply_overrides()           # свои цвета из редактора темы (если заданы)


set_theme("dark")


def hover_solid() -> str:
    """Подсветка при наведении как ОДИН непрозрачный цвет: HOVER_RGBA поверх фона боковой панели.
    Полупрозрачный фон при частичной перерисовке накладывался дважды и давал тёмный/светлый квадрат."""
    r, g, b, a = (int(x) for x in re.findall(r"\d+", HOVER_RGBA)[:4])
    base = QColor(SIDEBAR)
    mix = lambda bc, oc: round(bc + (oc - bc) * a / 255)
    return QColor(mix(base.red(), r), mix(base.green(), g), mix(base.blue(), b)).name()


def scale_qss(qss: str, k: float) -> str:
    """Умножает все размеры в px (шрифты, отступы, скругления, ползунки) на k.
    Шрифт не мельче 8px, а линии в 1px остаются 1px, чтобы рамки не пропадали."""
    if abs(k - 1.0) < 1e-6:
        return qss

    def repl(m) -> str:
        n = float(m.group(2))
        if m.group(1):                                        # font-size: Npx
            return f"{m.group(1)}{max(8, round(n * k))}px"
        return m.group(0) if n <= 1 else f"{max(1, round(n * k))}px"
    return re.sub(r"(font-size:\s*)?(\d+(?:\.\d+)?)px", repl, qss)


def _build_qss_raw(chev: str) -> str:
    """Стили. Функция, а не константа: стрелке списка нужен файл, а рисовать можно только после QApplication."""
    off_qss = f"QPushButton:disabled {{ background: {BTN_OFF_C}; color: {MUTED}; }}" if BTN_OFF_SET else ""
    ov, dark_bg = HOVER_OV, QColor(BG).lightnessF() < 0.5
    g_fill = f"rgba({ov[0]},{ov[1]},{ov[2]},{15 if dark_bg else 9})"     # стеклянная заливка контролов на плашках
    g_edge = f"rgba({ov[0]},{ov[1]},{ov[2]},{28 if dark_bg else 24})"
    return f"""
QWidget {{ font-family: {user_font_css()}{", ".join(f'"{f}"' for f in BUNDLED_FONTS) + ", " if BUNDLED_FONTS else ""}"Inter", "Noto Sans", "Segoe UI", "Roboto", sans-serif; font-size: 13px; }}
QLabel {{ color: {TEXT}; background: transparent; }}
QLineEdit, QPlainTextEdit, QComboBox {{
    background: {CONTROL}; color: {TEXT}; border: 1px solid {BORDER};
    border-radius: 8px; padding: 6px 10px;
    selection-background-color: {ACCENT}; selection-color: #ffffff;
}}
QLineEdit:hover, QPlainTextEdit:hover, QComboBox:hover {{ border: 1px solid {BORDER_HOVER}; }}
QLineEdit:focus, QPlainTextEdit:focus, QComboBox:focus {{ border: 1px solid {ACCENT}; }}
QLineEdit:disabled, QComboBox:disabled {{ color: {DIM}; background: {DISABLED_BG}; }}
QLineEdit, QComboBox, QPlainTextEdit {{ background: {g_fill}; border: 1px solid {g_edge}; }}
QComboBox::drop-down {{ background: transparent; border: none; width: 28px;
    border-top-right-radius: 8px; border-bottom-right-radius: 8px; }}
QComboBox::drop-down:hover, QComboBox::drop-down:pressed, QComboBox::drop-down:on {{ background: {HOVER_RGBA}; }}
QComboBox::down-arrow {{ image: url("{chev}"); width: 14px; height: 14px; margin-right: 6px; }}
QComboBox::down-arrow:on {{ top: 0px; left: 0px; }}
QComboBox QAbstractItemView {{
    background: {CARD}; color: {TEXT}; border: 1px solid {POP_BORDER}; border-radius: 8px;
    padding: 4px; selection-background-color: {SEL_BG}; selection-color: #ffffff; outline: 0;
}}
QPushButton {{ background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 {BTN_A}, stop:1 {BTN_B});
    color: #ffffff; border: none; border-radius: 10px;
    padding: 10px 22px; font-size: 14px; font-weight: 600; }}
QPushButton:hover {{ background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 {BTN_HA}, stop:1 {BTN_HB}); }}
QPushButton:pressed {{ background: {BTN_DOWN}; }}
{off_qss}
QSlider::groove:horizontal {{ height: 4px; background: {GROOVE_C}; border-radius: 2px; }}
QSlider::sub-page:horizontal {{ background: {SLIDER_C}; border-radius: 2px; }}
QSlider::handle:horizontal {{ background: {KNOB_C}; width: 14px; height: 14px; margin: -5px 0; border-radius: 7px; }}
QSlider::handle:horizontal:hover {{ background: {KNOB_H}; }}
QSlider::sub-page:horizontal:disabled {{ background: #2c3347; }}
QSlider::handle:horizontal:disabled {{ background: #555b69; }}
QScrollBar:vertical {{ background: transparent; width: 8px; margin: 2px; }}
QScrollBar::handle:vertical {{ background: {SCROLL}; border-radius: 4px; min-height: 24px; }}
QScrollBar::handle:vertical:hover {{ background: {ACCENT}; }}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
#side {{ background: {side_bg()}; border-right: 1px solid {BORDER};
    border-top-left-radius: 14px; border-bottom-left-radius: 14px; }}
#devbar {{ background: {SIDEBAR}; }}
#card {{ background: {CARD}; border: 1px solid {BORDER}; border-radius: 12px; }}
#profile {{ background: transparent; border: none; border-radius: 10px; }}
#profarrow, #profarrow:hover {{ background: transparent; border: none; padding: 0; }}
#sep {{ background: {BORDER}; border: none; }}
#rowsep {{ background: {ROWSEP}; border: none; }}
#valuebox {{ background: {g_fill}; color: {VALUEBOX}; border: 1px solid {g_edge}; border-radius: 6px; font-size: 12px; }}
#logo {{ color: {STRONG}; font-size: 16px; font-weight: 800; }}
#h1 {{ color: {STRONG}; font-size: 20px; font-weight: 700; }}
#h2 {{ color: {STRONG}; font-size: 16px; font-weight: 700; }}
#muted {{ color: {MUTED}; font-size: 11px; }}
#desc {{ color: {MUTED}; font-size: 11px; }}
#value {{ color: {VALUE_C}; font-size: 13px; }}
#cardTitle {{ color: {PREMIUM}; font-size: 10px; font-weight: 700; padding-left: 4px; }}
#divLabel {{ color: {ACCENT}; font-size: 10px; font-weight: 700; }}
#section {{ color: {PREMIUM}; font-size: 10px; font-weight: 700; padding-left: 6px; }}
#crumb {{ color: #7f8594; font-size: 12px; }}
#pname {{ color: {STRONG}; font-size: 13px; font-weight: 600; }}
#pstatus {{ color: #3ddc97; font-size: 11px; }}
#err {{ color: #ff6b6b; font-size: 12px; }}
QPushButton#winbtn {{ background: transparent; border-radius: 8px; padding: 0; outline: none; border: none; }}
QPushButton#winbtn:hover {{ background: {WINBTN_HOVER}; }}
QPushButton#winbtn:pressed {{ background: {HOVER_RGBA}; }}
QPushButton#winbtn:focus {{ background: transparent; border: none; outline: none; }}
QToolTip {{ background: {CARD}; color: {TEXT}; border: 1px solid {POP_BORDER}; }}
QPushButton#pickbtn {{ background: {g_fill}; color: {TEXT}; border: 1px solid {g_edge}; border-radius: 8px;
    padding: 5px 10px; font-size: 12px; font-weight: 500; }}
QPushButton#pickbtn:hover {{ background: {SELECTED}; border: 1px solid {BORDER_HOVER}; }}
QPushButton#pickbtn:pressed {{ background: {CONTROL}; }}
QPushButton#seg {{ background: {CONTROL}; color: {MUTED}; border: 1px solid {BORDER}; border-radius: 6px;
    padding: 3px 12px; font-size: 11px; font-weight: 600; }}
QPushButton#seg:hover {{ color: {TEXT}; border: 1px solid {BORDER_HOVER}; }}
QPushButton#seg:checked {{ background: {ACCENT}; color: #ffffff; border: 1px solid {ACCENT}; }}
"""


def build_qss(chev: str) -> str:
    """Те же стили, но цвета с прозрачностью (#aarrggbb) переводятся в rgba(): так их точно понимает Qt."""
    def fix(m) -> str:
        a, r, g, b = (int(m.group(i), 16) for i in (1, 2, 3, 4))
        return f"rgba({r},{g},{b},{a})"
    return re.sub(r"#([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})(?![0-9a-fA-F])", fix,
                  _build_qss_raw(chev))


class Toggle(QCheckBox):
    """Переключатель-таблетка с плавной анимацией (как в меню neverlose).
    Наследует QCheckBox, поэтому isChecked / setChecked / toggled работают как обычно."""
    W, H = 38, 20
    _k = 1.0                       # масштаб окна настроек (у переключателей в меню остаётся 1)

    def __init__(self, text: str = ""):
        super().__init__(text)
        self._pos = 0.0
        self._anim = QPropertyAnimation(self, b"knob", self)
        self._anim.setDuration(160)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self.toggled.connect(self._animate)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def _animate(self, on: bool) -> None:
        self._anim.stop()
        self._anim.setEndValue(1.0 if on else 0.0)
        self._anim.start()

    def setChecked(self, on: bool) -> None:
        super().setChecked(on)
        self._anim.stop()
        self._pos = 1.0 if on else 0.0   # при загрузке настроек без анимации
        self.update()

    def get_knob(self) -> float:
        return self._pos

    def set_knob(self, v: float) -> None:
        self._pos = v
        self.update()

    knob = pyqtProperty(float, get_knob, set_knob)

    def sizeHint(self) -> QSize:
        k = self._k
        W, H = self.W * k, self.H * k
        w = self.fontMetrics().horizontalAdvance(self.text()) + W + 12 * k if self.text() else W
        return QSize(int(w), int(max(H + 8 * k, 26 * k)))

    def hitButton(self, p) -> bool:
        return self.rect().contains(p)

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        k = self._k
        W, H = self.W * k, self.H * k
        y = (self.height() - H) / 2
        track = QRectF(1, y, W, H)
        off, on = QColor(TOGGLE_OFF), QColor(TOGGLE_ON)
        t = self._pos
        mix = QColor(int(off.red() + (on.red() - off.red()) * t),
                     int(off.green() + (on.green() - off.green()) * t),
                     int(off.blue() + (on.blue() - off.blue()) * t))
        if not self.isEnabled():
            mix.setAlpha(110)
        p.setPen(QPen(QColor(BORDER), 1))
        p.setBrush(mix)
        p.drawRoundedRect(track, H / 2, H / 2)
        r = H - 6 * k
        x = 1 + 3 * k + (W - r - 6 * k) * t
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#ffffff") if t > 0.5 else QColor("#8a909c"))
        p.drawEllipse(QRectF(x, y + 3 * k, r, r))
        if self.text():
            p.setPen(QColor(TEXT if self.isEnabled() else MUTED))
            p.setFont(self.font())
            p.drawText(QRectF(W + 12 * k, 0, self.width() - W - 12 * k, self.height()),
                       Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, self.text())


_STYLE_SET = False


def apply_dark_theme(app: QApplication) -> None:
    """Почти чёрная тема с синим акцентом в стиле neverlose: палитра + стили."""
    global _STYLE_SET
    if not _STYLE_SET:          # setStyle второй раз (при смене акцента) ломал стили и закрывал меню
        app.setStyle("Fusion")
        _STYLE_SET = True
    pal = QPalette()
    for role, color in {
        QPalette.ColorRole.Window: BG, QPalette.ColorRole.WindowText: TEXT,
        QPalette.ColorRole.Base: PANEL, QPalette.ColorRole.AlternateBase: CARD,
        QPalette.ColorRole.Text: TEXT, QPalette.ColorRole.Button: PANEL,
        QPalette.ColorRole.ButtonText: TEXT, QPalette.ColorRole.ToolTipBase: CARD,
        QPalette.ColorRole.ToolTipText: TEXT, QPalette.ColorRole.Highlight: ACCENT,
        QPalette.ColorRole.HighlightedText: "#ffffff", QPalette.ColorRole.PlaceholderText: MUTED,
    }.items():
        pal.setColor(role, QColor(color))
    pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Text, QColor(MUTED))
    pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.WindowText, QColor(MUTED))
    app.setPalette(pal)
    app.setStyleSheet(build_qss(chevron_png("#7b8190")))


class StartSplash(QWidget):
    """Заставка после «Начать разговор» на весь экран: лаунчер уже закрыт, фон затемнён и размыт, по центру
    логотип в круге с вращающейся дугой, бегущая точка, свечение, полоска загрузки и «с возвращением, имя».
    В конце плавно гаснет, и только потом запускается Мими."""
    finished = pyqtSignal()
    DURATION = 2.6      # сколько всего идёт заставка, секунд
    FADE_IN = 0.4       # появление фона и логотипа
    FADE_OUT = 0.6      # растворение в конце: сквозь заставку проступает рабочий стол

    def __init__(self):
        super().__init__()
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint)   # заставка — обычное окно: поверх всех только Мими
        self.setCursor(Qt.CursorShape.BlankCursor)
        # стекло: окно прозрачное, сквозь тёмную вуаль видны живые окна; solid: свой сплошной фон
        self.glass = SPLASH_MODE == "glass"
        if self.glass:
            self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.logo = QPixmap(str(BASE / "launcher" / "mimi.png"))
        self.avatar = QPixmap(str(BASE / "assets" / "character.png"))   # маленький аватар у приветствия
        self.name = getpass.getuser()
        self.sparks = [(random.random(), random.random(), random.uniform(0.6, 1.8), random.uniform(0, 6.28))
                       for _ in range(60)]                   # пылинки, медленно плывущие по экрану
        self.t0 = time.monotonic()
        self.done = False
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(16)                                 # ~60 кадров в секунду

    @staticmethod
    def _out_back(x: float) -> float:
        c1, c3 = 1.4, 2.4
        return 1 + c3 * (x - 1) ** 3 + c1 * (x - 1) ** 2

    def _tick(self) -> None:
        if time.monotonic() - self.t0 >= self.DURATION:
            if not self.done:
                self.done = True
                self.timer.stop()
                self.hide()
                self.finished.emit()
        else:
            if not self.glass:                           # сплошной фон не растворяется сам: гасим окно целиком
                t = time.monotonic() - self.t0
                self.setWindowOpacity(max(0.0, min(1.0, (self.DURATION - t) / self.FADE_OUT)))
            self.update()

    def paintEvent(self, _):
        t = time.monotonic() - self.t0
        if t >= self.DURATION:
            return
        appear = min(1.0, t / self.FADE_IN)                           # 0 -> 1 в начале
        leave = 1.0 - max(0.0, (t - (self.DURATION - self.FADE_OUT)) / self.FADE_OUT)   # 1 -> 0 в конце
        a = appear
        w, h = self.width(), self.height()
        u = max(1.0, h / 760)                                         # масштаб под размер экрана
        cx, cy = w / 2, h / 2 - 50 * u
        acc = QColor(ACCENT)

        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        if self.glass:
            p.setOpacity(leave * appear)                              # прозрачность отдаём композитору
            p.fillRect(QRectF(0, 0, w, h), QColor(8, 9, 20, 175))
        else:
            p.setOpacity(1.0)                                         # режим solid: свой непрозрачный фон
            bg = QLinearGradient(0, 0, w, h)
            bg.setColorAt(0, QColor(12, 15, 32))
            bg.setColorAt(1, QColor(4, 5, 12))
            p.fillRect(QRectF(0, 0, w, h), bg)
        vig = QRadialGradient(QPointF(cx, h / 2), max(w, h) * 0.75)   # виньетка: края темнее
        v0 = QColor(0, 0, 0, 0)
        v1 = QColor(0, 0, 0, 110)
        vig.setColorAt(0.35, v0)
        vig.setColorAt(1, v1)
        p.setOpacity(leave * appear)
        p.fillRect(QRectF(0, 0, w, h), vig)
        p.setOpacity(leave)

        # пылинки
        p.setPen(Qt.PenStyle.NoPen)
        for fx, fy, sz, ph in self.sparks:
            x = (fx * w + math.sin(t * 0.5 + ph) * 30 * u) % w
            y = (fy * h - t * (10 + sz * 6) * u) % h
            p.setBrush(QColor(255, 255, 255, int(80 * a * (0.5 + 0.5 * math.sin(t * 1.7 + ph)))))
            p.drawEllipse(QPointF(x, y), sz * u, sz * u)

        # мягкое свечение за логотипом, слегка «дышит»
        pulse = 0.85 + 0.15 * math.sin(t * 2.4)
        gr = 190 * u * pulse * (0.7 + 0.3 * appear)
        glow = QRadialGradient(QPointF(cx, cy), gr)
        g0 = QColor(acc)
        g0.setAlpha(int(130 * a))
        g1 = QColor(acc)
        g1.setAlpha(0)
        glow.setColorAt(0, g0)
        glow.setColorAt(1, g1)
        p.setBrush(glow)
        p.drawEllipse(QPointF(cx, cy), gr, gr)

        # логотип: выезжает с небольшим «отскоком»
        sc = (0.55 + 0.45 * self._out_back(appear)) * u
        R_out, R_in, R_logo = 52 * sc, 44 * sc, 34 * sc
        p.setBrush(QColor(18, 20, 34, int(235 * a)))                  # тёмный круг под значком
        p.drawEllipse(QPointF(cx, cy), R_in, R_in)
        if not self.logo.isNull():
            lp = QPainterPath()
            lp.addEllipse(QPointF(cx, cy), R_logo, R_logo)
            p.save()
            p.setClipPath(lp)
            p.setOpacity(leave * a)
            p.drawPixmap(QRectF(cx - R_logo, cy - R_logo, 2 * R_logo, 2 * R_logo), self.logo,
                         QRectF(self.logo.rect()))
            p.restore()
            p.setOpacity(leave)

        # тонкое внешнее кольцо и бегущая по нему точка
        p.setPen(QPen(QColor(255, 255, 255, int(48 * a)), max(1.0, u)))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawEllipse(QPointF(cx, cy), R_out, R_out)
        ang = t * 2 * math.pi / 2.1 - math.pi / 2                     # полный оборот за ~2 секунды
        dx, dy = cx + R_out * math.cos(ang), cy + R_out * math.sin(ang)
        halo = QRadialGradient(QPointF(dx, dy), 10 * u)
        halo.setColorAt(0, QColor(255, 255, 255, int(170 * a)))
        halo.setColorAt(1, QColor(255, 255, 255, 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(halo)
        p.drawEllipse(QPointF(dx, dy), 10 * u, 10 * u)
        p.setBrush(QColor(255, 255, 255, int(255 * a)))
        p.drawEllipse(QPointF(dx, dy), 2.4 * u, 2.4 * u)

        # дуга-спиннер внутри кольца: крутится и «дышит» длиной
        span = 95 + 45 * math.sin(t * 3.0)
        start = -(t * 260) % 360
        pen = QPen(QColor(acc.red(), acc.green(), acc.blue(), int(255 * a)), 4 * u)
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        p.setPen(pen)
        p.drawArc(QRectF(cx - R_in, cy - R_in, 2 * R_in, 2 * R_in), int(start * 16), int(span * 16))

        # название: mimi белым, .typh акцентным, рядом плашка
        f = QFont()
        f.setFamilies(["Inter", "Noto Sans", "Segoe UI", "DejaVu Sans"])
        f.setPixelSize(int(32 * u))
        f.setWeight(QFont.Weight.Bold)
        fc = QFont(f)
        fc.setPixelSize(int(11 * u))
        chip_txt = "VOICE"
        fmc = QFontMetrics(fc)
        chip_w, chip_h = fmc.horizontalAdvance(chip_txt) + 14 * u, 19 * u
        gap = 10 * u
        p.setFont(f)
        fm = p.fontMetrics()
        w1, w2 = fm.horizontalAdvance("mimi"), fm.horizontalAdvance(".typh")
        ty = cy + R_out + 56 * u
        x0 = cx - (w1 + w2 + gap + chip_w) / 2
        p.setPen(QColor(255, 255, 255, int(255 * a)))
        p.drawText(QPointF(x0, ty), "mimi")
        p.setPen(QColor(acc.red(), acc.green(), acc.blue(), int(255 * a)))
        p.drawText(QPointF(x0 + w1, ty), ".typh")
        chip = QRectF(x0 + w1 + w2 + gap, ty - 20 * u, chip_w, chip_h)
        p.setPen(QPen(QColor(acc.red(), acc.green(), acc.blue(), int(110 * a)), 1))
        p.setBrush(QColor(acc.red(), acc.green(), acc.blue(), int(60 * a)))
        p.drawRoundedRect(chip, 4 * u, 4 * u)
        p.setFont(fc)
        p.setPen(QColor(acc.lighter(150).red(), acc.lighter(150).green(), acc.lighter(150).blue(), int(255 * a)))
        p.drawText(chip, Qt.AlignmentFlag.AlignCenter, chip_txt)

        # полоска загрузки: заполняется плавно, на конце яркая точка
        lw = 260 * u
        lx0, lx1, ly = cx - lw / 2, cx + lw / 2, ty + 26 * u
        prog = min(1.0, max(0.0, (t - 0.2) / (self.DURATION - self.FADE_OUT - 0.2)))
        prog = 1 - (1 - prog) ** 3                                    # быстро в начале, мягко в конце
        base = QLinearGradient(lx0, 0, lx1, 0)
        for pos, al in ((0, 0), (0.15, 60), (0.85, 60), (1, 0)):
            base.setColorAt(pos, QColor(255, 255, 255, int(al * a)))
        p.setPen(QPen(QBrush(base), 1.5 * u))
        p.drawLine(QPointF(lx0, ly), QPointF(lx1, ly))
        px = lx0 + lw * prog
        fill = QLinearGradient(lx0, 0, px, 0)
        fill.setColorAt(0, QColor(acc.red(), acc.green(), acc.blue(), 0))
        fill.setColorAt(1, QColor(acc.red(), acc.green(), acc.blue(), int(255 * a)))
        p.setPen(QPen(QBrush(fill), 2 * u))
        p.drawLine(QPointF(lx0, ly), QPointF(px, ly))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(255, 255, 255, int(255 * a)))
        p.drawEllipse(QPointF(px, ly), 2.6 * u, 2.6 * u)

        # аватар и «с возвращением, имя»
        f2 = QFont(f)
        f2.setPixelSize(int(15 * u))
        f2.setWeight(QFont.Weight.Normal)
        f3 = QFont(f2)
        f3.setWeight(QFont.Weight.Bold)
        fm2, fm3 = QFontMetrics(f2), QFontMetrics(f3)
        s1 = "с возвращением, "
        av = 24 * u
        tot = av + 8 * u + fm2.horizontalAdvance(s1) + fm3.horizontalAdvance(self.name)
        sx, sy = cx - tot / 2, ly + 34 * u
        ap = QPainterPath()
        ap.addEllipse(QPointF(sx + av / 2, sy - 5 * u), av / 2, av / 2)
        src_pix = self.avatar if not self.avatar.isNull() else self.logo
        if not src_pix.isNull():
            p.save()
            p.setClipPath(ap)
            p.drawPixmap(QRectF(sx, sy - 5 * u - av / 2, av, av), src_pix, QRectF(src_pix.rect()))
            p.restore()
        p.setPen(QPen(QColor(255, 255, 255, int(70 * a)), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawPath(ap)
        tx = sx + av + 8 * u
        p.setFont(f2)
        p.setPen(QColor(200, 205, 218, int(255 * a)))
        p.drawText(QPointF(tx, sy), s1)
        p.setFont(f3)
        p.setPen(QColor(255, 255, 255, int(255 * a)))
        p.drawText(QPointF(tx + fm2.horizontalAdvance(s1), sy), self.name)

        # мелкая строка: сборка и дата
        f4 = QFont(f2)
        f4.setPixelSize(int(11.5 * u))
        p.setFont(f4)
        p.setPen(QColor(150, 156, 172, int(255 * a)))
        p.drawText(QRectF(0, sy + 8 * u, w, 20 * u), Qt.AlignmentFlag.AlignHCenter,
                   f"голосовой помощник  ·  {time.strftime('%d.%m.%Y')}")

        # надпись с разрядкой: по буквам бежит подсветка
        f5 = QFont(f2)
        f5.setPixelSize(int(13 * u))
        p.setFont(f5)
        fm5 = QFontMetrics(f5)
        letters = "мими всегда рядом"
        step = 9 * u
        widths = [fm5.horizontalAdvance(ch) + step for ch in letters]
        lx = cx - sum(widths) / 2
        ly2 = sy + 78 * u
        hot = (t * 7) % (len(letters) + 6)                           # подсветка бежит и ненадолго уходит за край
        for i, ch in enumerate(letters):
            d = abs(i - hot)
            k = max(0.0, 1 - d / 2.5)
            col = QColor(int(120 + (acc.lighter(140).red() - 120) * k), int(126 + (acc.lighter(140).green() - 126) * k),
                         int(142 + (acc.lighter(140).blue() - 142) * k), int((110 + 145 * k) * a))
            p.setPen(col)
            p.drawText(QPointF(lx, ly2), ch)
            lx += widths[i]
        p.end()

    def mousePressEvent(self, e):          # клик или Esc пропускают заставку
        self.skip()

    def keyPressEvent(self, e):
        self.skip()

    def skip(self) -> None:
        self.t0 = min(self.t0, time.monotonic() - (self.DURATION - self.FADE_OUT))


FONT_DIR = BASE / "assets" / "fonts"   # положи сюда .ttf/.otf — подхватится сама, без установки в систему


def load_bundled_fonts() -> list[str]:
    """Грузит все шрифты из assets/fonts/ в приложение (не трогая систему).
    Возвращает названия семейств в порядке файлов — их можно подставить первыми в QSS."""
    families: list[str] = []
    if not FONT_DIR.is_dir():
        return families
    for f in sorted(FONT_DIR.iterdir()):
        if f.suffix.lower() not in (".ttf", ".otf"):
            continue
        fid = QFontDatabase.addApplicationFont(str(f))
        if fid == -1:
            print(f"Не удалось загрузить шрифт: {f.name}", file=sys.stderr)
            continue
        for fam in QFontDatabase.applicationFontFamilies(fid):
            if fam not in families:
                families.append(fam)
                print(f"Шрифт из программы: {fam} ({f.name})")
    return families


def restart_launcher() -> None:
    """Мими закрыта: запускаем программу заново, чтобы снова открылось окно настроек (лаунчер).
    Новый процесс чистый: голос, микрофон и тема загружаются с нуля."""
    try:
        subprocess.Popen([sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
                         cwd=str(BASE), start_new_session=True)
    except OSError as e:
        print(f"Не удалось заново открыть настройки: {e}", file=sys.stderr)


def prefer_xwayland() -> None:
    """На чистом Wayland «поверх всех окон» невозможно: композитор игнорирует эту просьбу у обычных программ.
    Через XWayland (платформа xcb) GNOME её выполняет, поэтому на Wayland переключаемся на xcb, если она
    доступна. Свой выбор можно задать вручную: QT_QPA_PLATFORM=wayland python main.py."""
    if os.environ.get("QT_QPA_PLATFORM") or ENV["session"] != "wayland" or not os.environ.get("DISPLAY"):
        return
    import ctypes.util
    if ctypes.util.find_library("xcb-cursor"):       # без неё плагин xcb в Qt 6 не запустится
        os.environ["QT_QPA_PLATFORM"] = "xcb"
    else:
        print("Поверх всех окон на Wayland нужна библиотека xcb-cursor (Fedora: sudo dnf install xcb-util-cursor)",
              file=sys.stderr)


def main():
    prefer_xwayland()
    app = QApplication(sys.argv)
    BUNDLED_FONTS[:] = load_bundled_fonts()  # до apply_dark_theme(): он читает этот список
    install_log_capture()             # логи и ошибки попадают и в консоль разработчика
    # окно привязывается к ярлыку «Мими» (иначе док GNOME называет его python3 и ставит значок Python):
    # на Wayland работает имя ярлыка, на X11 класс окна, который Qt берёт из имени приложения
    app.setApplicationName("mimi-assistant")
    app.setDesktopFileName("mimi-assistant")
    icon_file = BASE / "launcher" / "mimi.png"
    if icon_file.is_file():
        app.setWindowIcon(QIcon(str(icon_file)))   # запасной значок, если ярлык не нашёлся
    set_theme(read_json(CFG_PATH, {}).get("theme", "dark"))
    set_lang(read_json(CFG_PATH, {}).get("lang", "ru"))
    set_accent(read_json(CFG_PATH, {}).get("accent", ACCENT_NAME))
    set_user_colors(read_json(CFG_PATH, {}).get("theme_colors"))
    load_visual()
    apply_dark_theme(app)
    print(f"Система: {ENV['distro']} | окружение: {ENV['de']} | сессия: {ENV['session']}")
    if read_json(CFG_PATH, {}).get("dev_mode"):
        set_dev_mode(True)            # режим разработчика был включён: консоль открывается вместе с программой
    dlg = SettingsDialog(read_json(CFG_PATH, {}))
    if dlg.exec() != QDialog.DialogCode.Accepted:
        return
    cfg = dlg.cfg
    app.setQuitOnLastWindowClosed(False)      # пока идёт заставка, окон нет: приложение не должно закрыться
    dlg.hide()                                # лаунчер закрыт до заставки
    dlg.deleteLater()
    apply_voice(cfg)
    k = cfg["api_key"]
    print(f"Адрес: {cfg['base_url']} | модель: {cfg['model']} | "
          f"ключ: {k[:4]}…{k[-4:]} (длина {len(k)})")
    bot = Assistant(cfg)
    bot.start()                               # голос и микрофон грузятся, пока играет заставка
    splash = StartSplash()                    # анимация на весь экран
    loop = QEventLoop()
    splash.finished.connect(loop.quit)
    if splash.glass:                          # прозрачное окно: полноэкранный режим Mutter делает его непрозрачным,
        scr = QApplication.primaryScreen()    # поэтому растягиваем окно на экран вручную
        if QApplication.platformName() == "xcb" and scr is not None:
            splash.setGeometry(scr.geometry())
            splash.show()
        else:
            splash.showMaximized()
    else:
        splash.showFullScreen()               # непрозрачное окно: Mutter (GNOME) тут не мешает
    splash.raise_()
    splash.activateWindow()
    loop.exec()
    splash.deleteLater()
    win = CharacterWindow(bot, cfg)
    win.show()
    if dev_is_on() and cfg.get("dev_console_auto"):
        open_dev_window()                     # «Запускать вместе с Мими» во вкладке «Журнал»
    app.setQuitOnLastWindowClosed(True)
    code = app.exec()                         # возвращается, когда Мими закрыта
    restart_launcher()                        # и сразу открываются настройки, вручную запускать не надо
    sys.exit(code)


if __name__ == "__main__":
    main()
