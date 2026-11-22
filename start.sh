#!/usr/bin/env bash
# Запуск помощника: сам создаёт окружение, ставит модули и стартует main.py.
# Работает на Arch, Fedora и Debian/Ubuntu. Из терминала пишет сообщения в консоль,
# из меню приложений показывает их окошком, а вывод программы кладёт в data/last_run.log.
cd "$(dirname "$(readlink -f "$0")")" || exit 1

say() {   # сообщение: в консоль, а если запуск из меню (консоли нет), то ещё и окошком
    echo "$1"
    [ -t 1 ] && return
    if command -v kdialog >/dev/null; then kdialog --title "Мими" --error "$1"
    elif command -v zenity >/dev/null; then zenity --error --title="Мими" --text="$1" --no-markup
    elif command -v notify-send >/dev/null; then notify-send "Мими" "$1"
    fi
}

note() {  # необязательная подсказка: не мешает запуску
    echo "$1"
    [ -t 1 ] && return
    command -v notify-send >/dev/null && notify-send "Мими" "$1"
}

# --- команды установки под твой дистрибутив ---
if command -v pacman >/dev/null; then
    PKGS="sudo pacman -S --needed python python-pyqt6 python-pyaudio espeak-ng"
    TORCH="sudo pacman -S python-pytorch"
    PLAYER="sudo pacman -S mpv"
elif command -v dnf >/dev/null; then
    PKGS="sudo dnf install python3 python3-pyqt6 python3-pyaudio espeak-ng"
    TORCH="sudo dnf install python3-torch"
    PLAYER="sudo dnf install mpv"
elif command -v apt >/dev/null; then
    PKGS="sudo apt install python3 python3-venv python3-pyqt6 python3-pyaudio espeak-ng"
    TORCH="sudo apt install python3-torch"
    PLAYER="sudo apt install mpv"
else
    PKGS="установите через менеджер пакетов: python3, PyQt6, PyAudio, espeak-ng"
    TORCH="установите PyTorch для Python через менеджер пакетов"
    PLAYER="установите mpv через менеджер пакетов"
fi

PY="$(command -v python3 || command -v python)"
[ -n "$PY" ] || { say "Не найден Python. Выполните в терминале:
$PKGS"; exit 1; }

if [ ! -d .venv ]; then
    note "Первый запуск: создаю окружение…"
    "$PY" -m venv --system-site-packages .venv || { say "Не удалось создать окружение (.venv). Выполните в терминале:
$PKGS"; exit 1; }
fi

if ! .venv/bin/python -c "import pyaudio, PyQt6.QtWidgets" 2>/dev/null; then
    say "Не хватает системных пакетов. Выполните в терминале:
$PKGS"
    exit 1
fi

if ! .venv/bin/python -c "import speech_recognition" 2>/dev/null; then
    note "Ставлю модули (только при первом запуске)…"
    .venv/bin/pip install -r requirements.txt || { say "Не удалось установить модули из requirements.txt"; exit 1; }
fi

# Голос Silero: нужен PyTorch из системных пакетов (pip не трогаем, чтобы не тянуть гигабайты)
if .venv/bin/python -c "import torch" 2>/dev/null; then
    .venv/bin/python -c "import silero" 2>/dev/null || .venv/bin/pip install silero || { say "Не удалось установить silero"; exit 1; }
else
    note "Для голоса Silero установите PyTorch:  $TORCH
(пока его нет, помощник будет говорить роботом espeak-ng)"
fi

if ! command -v mpv >/dev/null && ! command -v ffplay >/dev/null; then
    note "Для воспроизведения голоса нужен плеер:  $PLAYER"
fi

if [ -t 1 ]; then
    exec .venv/bin/python main.py
fi
mkdir -p data
exec .venv/bin/python main.py > data/last_run.log 2>&1   # из меню: вывод в лог
