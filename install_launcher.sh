#!/usr/bin/env bash
# Делает из помощника обычное приложение «mimi-alpha»: ярлык в меню (и на рабочем столе, если это не GNOME).
#   bash install_launcher.sh              меню приложений (+ рабочий стол вне GNOME)
#   bash install_launcher.sh --pin        ещё и закрепить в панели избранного GNOME
#   bash install_launcher.sh --desktop    принудительно положить ярлык на рабочий стол
#   bash install_launcher.sh --no-desktop без ярлыка на рабочем столе
#   bash install_launcher.sh --remove     убрать всё
cd "$(dirname "$(readlink -f "$0")")" || exit 1
DIR="$(pwd)"
DATA="${XDG_DATA_HOME:-$HOME/.local/share}"
APPS="$DATA/applications"
ICON_DIR="$DATA/icons/hicolor/256x256/apps"
FILE="$APPS/mimi-alpha.desktop"
DESKTOP_DIR="$(xdg-user-dir DESKTOP 2>/dev/null || echo "$HOME/Desktop")"
APP_ID="mimi-alpha.desktop"

WANT_DESKTOP=auto; WANT_PIN=0; REMOVE=0
for a in "$@"; do
    case "$a" in
        --no-desktop) WANT_DESKTOP=0 ;;
        --desktop) WANT_DESKTOP=1 ;;
        --pin) WANT_PIN=1 ;;
        --remove) REMOVE=1 ;;
    esac
done

is_gnome() { case "${XDG_CURRENT_DESKTOP,,}" in *gnome*|*unity*|*budgie*|*cosmic*) return 0 ;; esac; return 1; }

# В GNOME значков на рабочем столе нет, поэтому лишний ярлык туда не кладём
if [ "$WANT_DESKTOP" = auto ]; then
    if is_gnome; then WANT_DESKTOP=0; else WANT_DESKTOP=1; fi
fi

favorites() {   # $1 = add | del : правка списка избранного в панели GNOME
    command -v gsettings >/dev/null || return 0
    local cur new
    cur="$(gsettings get org.gnome.shell favorite-apps 2>/dev/null)" || return 0
    case "$1" in
        add)
            case "$cur" in *"$APP_ID"*) return 0 ;; esac
            if [ "$cur" = "@as []" ] || [ "$cur" = "[]" ]; then new="['$APP_ID']"
            else new="${cur%]}, '$APP_ID']"; fi ;;
        del)
            case "$cur" in *"$APP_ID"*) ;; *) return 0 ;; esac
            new="$(echo "$cur" | sed "s/, '$APP_ID'//; s/'$APP_ID', //; s/'$APP_ID'//")" ;;
    esac
    gsettings set org.gnome.shell favorite-apps "$new" 2>/dev/null
}

refresh() {   # GNOME сам видит новые ярлыки; иконка указана полным путём, кэш иконок не трогаем
    # (обновление кэша перерисовывает значки и может уронить оболочку из-за глючных расширений)
    command -v kbuildsycoca6 >/dev/null && kbuildsycoca6 >/dev/null 2>&1
    return 0
}

if [ "$REMOVE" = 1 ]; then
    rm -f "$FILE" "$DESKTOP_DIR/$APP_ID"
    favorites del
    refresh
    echo "Ярлык «mimi-alpha» удалён."
    exit 0
fi

if [ ! -f launcher/mimi.png ]; then
    echo "Не найдена иконка launcher/mimi.png"
    exit 1
fi

mkdir -p "$APPS"
chmod +x start.sh

TMP="$(mktemp "$DATA/.mimi-desktop.XXXXXX")"
cat > "$TMP" <<DESK
[Desktop Entry]
Type=Application
Version=1.0
Name=mimi-alpha
GenericName=Голосовой помощник
Comment=Голосовая подруга-помощница
Exec="$DIR/start.sh"
Path=$DIR
Icon=$DIR/launcher/mimi.png
Terminal=false
Categories=Utility;
Keywords=mimi-alpha;mimi;Мими;помощник;голос;
StartupNotify=false
StartupWMClass=Mimi-alpha
DESK
chmod +x "$TMP"
mv -f "$TMP" "$FILE"   # одним действием, чтобы оболочка не прочитала недописанный файл

if [ "$WANT_DESKTOP" = 1 ]; then
    mkdir -p "$DESKTOP_DIR"
    cp "$FILE" "$DESKTOP_DIR/$APP_ID"
    chmod +x "$DESKTOP_DIR/$APP_ID"
    # GNOME не запускает ярлыки на рабочем столе, пока им не разрешили («Allow Launching»)
    command -v gio >/dev/null && gio set "$DESKTOP_DIR/$APP_ID" metadata::trusted true 2>/dev/null
    echo "Ярлык положен на рабочий стол: $DESKTOP_DIR"
fi

[ "$WANT_PIN" = 1 ] && favorites add
refresh

echo "Готово: «mimi-alpha» теперь в меню приложений (поиск по слову «mimi»)."
if is_gnome; then
    echo
    echo "У тебя GNOME: в нём по умолчанию нет значков на рабочем столе, поэтому ярлык там не виден."
    echo "  • Открой «Обзор» (клавиша Super) и набери «mimi»: приложение уже там."
    echo "  • Чтобы иконка была в панели избранного, запусти:  bash install_launcher.sh --pin"
    echo "  • Чтобы значки появились на рабочем столе, поставь расширение Desktop Icons NG (DING)"
    echo "    через «Менеджер расширений» (Extension Manager)."
fi
