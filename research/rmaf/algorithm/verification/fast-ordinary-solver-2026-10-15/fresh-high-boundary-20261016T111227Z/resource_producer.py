#!/usr/bin/env python3
"""Tiny synthetic resource producer, never a scientific proof program."""
import os, pathlib, random, subprocess, sys, time
mode=sys.argv[1]
if mode=='clean':
    print('CONTROL_OK')
    time.sleep(0.03)
elif mode=='wall': time.sleep(2)
elif mode=='raw':
    for _ in range(32): os.write(1,b'x'*4095+b'\n')
elif mode=='line': os.write(1,b'x'*65536)
elif mode=='compressed': os.write(1,random.Random(20261016).randbytes(131072))
elif mode=='memory':
    blocks=[]
    for _ in range(24):
        blocks.append(bytearray(b'x'*(4*1024**2)))
        time.sleep(0.02)
    time.sleep(2)
elif mode=='child-memory':
    subprocess.run([sys.executable,str(pathlib.Path(__file__).resolve()),'memory'],check=True)
elif mode=='child-raw':
    subprocess.run([sys.executable,str(pathlib.Path(__file__).resolve()),'raw'],check=True)
else: raise SystemExit('unknown synthetic mode')
