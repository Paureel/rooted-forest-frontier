# Source this file from bash or zsh to use this workspace's BootLoops install.
export BOOTSCIENCE_ROOT="/Users/paurel/Documents/ChatGPT/bootscience"
. "$BOOTSCIENCE_ROOT/.venv/bin/activate"
export PATH="$BOOTSCIENCE_ROOT/.runtime/julia-1.11.9/bin:$BOOTSCIENCE_ROOT/.runtime/pari/bin:$PATH"
export PYTHONPATH="$BOOTSCIENCE_ROOT/bootloops/tools:$BOOTSCIENCE_ROOT/bootloops:$BOOTSCIENCE_ROOT/dashboard${PYTHONPATH:+:$PYTHONPATH}"
export JULIA_DEPOT_PATH="$BOOTSCIENCE_ROOT/.runtime/julia-depot"
export JULIA_NUM_PRECOMPILE_TASKS=4
export MPLCONFIGDIR="$BOOTSCIENCE_ROOT/.runtime/matplotlib"
export ELAN_HOME="$BOOTSCIENCE_ROOT/.runtime/elan"
export PATH="$ELAN_HOME/bin:$PATH"
