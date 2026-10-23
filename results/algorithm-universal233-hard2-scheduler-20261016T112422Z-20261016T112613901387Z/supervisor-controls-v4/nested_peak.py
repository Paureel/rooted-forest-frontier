import subprocess,sys;p=subprocess.Popen([sys.executable,'-c','import time;x=bytearray(96*1024**2);time.sleep(.1)']);p.wait()
