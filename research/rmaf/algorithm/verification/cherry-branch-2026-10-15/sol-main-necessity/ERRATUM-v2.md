# Origin driver path failure

The first origin pilot failed before starting Lean: driver v1 selected the seventh parent of its source file, yielding `/Users/paurel/Documents/ChatGPT` rather than the workspace. The command list is empty and no audit pass is credited. `origin-pilot-run1.json` and the driver log preserve the exception. Driver v2 corrects this deterministic path to the sixth parent, uses new receipt/log/build names, and preserves all frozen fixture and audit source bytes. No scientific source or candidate was contacted.
