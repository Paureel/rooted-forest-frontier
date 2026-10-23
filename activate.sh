# Source from bash or zsh; launchers already set the checkout root.
if [ -z "${BOOTSCIENCE_ROOT:-}" ]; then
    if [ -n "${ZSH_VERSION:-}" ]; then
        BOOTSCIENCE_ROOT=$(CDPATH= cd -- "$(dirname -- "${(%):-%x}")" && pwd)
    else
        BOOTSCIENCE_ROOT=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE:-$0}")" && pwd)
    fi
fi
export BOOTSCIENCE_ROOT
if [ -f "$BOOTSCIENCE_ROOT/.venv/bin/activate" ]; then
    . "$BOOTSCIENCE_ROOT/.venv/bin/activate"
fi
export PYTHONPATH="$BOOTSCIENCE_ROOT/bootloops/tools:$BOOTSCIENCE_ROOT/bootloops:$BOOTSCIENCE_ROOT/dashboard${PYTHONPATH:+:$PYTHONPATH}"
export MPLCONFIGDIR="$BOOTSCIENCE_ROOT/.runtime/matplotlib"
if [ -x "$BOOTSCIENCE_ROOT/.runtime/elan/bin/lean" ]; then
    export ELAN_HOME="$BOOTSCIENCE_ROOT/.runtime/elan"
    export PATH="$ELAN_HOME/bin:$PATH"
fi
