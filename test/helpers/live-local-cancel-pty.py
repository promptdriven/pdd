"""Actual PTY, public bridge and host; only bounded temporary scratch effects."""
import errno,json,os,pty,select,signal,subprocess,sys,tempfile,time
from pathlib import Path
scenario=sys.argv[1]
with tempfile.TemporaryDirectory(prefix='pdd-cancel-') as scratch:
 m,s=pty.openpty();p=subprocess.Popen([os.environ.get('PDD_TEST_NODE','node'),str(Path(__file__).with_name('live-local-cancel-child.mjs')),scenario,scratch],stdin=s,stdout=s,stderr=s);os.close(s);out=bytearray()
 def read(sec):
  end=time.monotonic()+sec
  while time.monotonic()<end:
   if select.select([m],[],[],.02)[0]:
    try:chunk=os.read(m,65536)
    except OSError as e:
     if e.errno==errno.EIO:return
     raise
    if not chunk:return
    out.extend(chunk)
 def until(pred,message,seconds=3):
  end=time.monotonic()+seconds
  while not pred() and time.monotonic()<end:read(.02)
  assert pred(),message
 def has(text):return text.encode() in out
 def prompts():return out.count(b'Type yes to confirm:')
 def send(data):
  try:os.write(m,data)
  except OSError as e:
   if e.errno!=errno.EIO:raise
 try:
  until(lambda:prompts()>=1,'A terminal prompt must be displayed')
  if scenario.startswith('abort-'):
   read(.1);p.send_signal(signal.SIGUSR1)
   until(lambda:has({'abort-service':'SIGNAL_ABORTED','abort-remote':'REMOTE_CLOSED_READ','abort-close':'CLOSE_REQUESTED'}[scenario]),'Cancellation must be observed')
   until(lambda:has('SERVICE_SETTLED'),'Cancellation must settle service without any terminal answer',7 if scenario=='abort-close' else 3)
   until(lambda:has('COMPLETE'),'Shutdown must release active and queued terminal consent')
   send(b'yes\nyes\n');read(.1)
   assert prompts()==1,'Cancelled queued confirmation must never display a prompt'
  elif scenario=='host-queued':
   p.send_signal(signal.SIGUSR1)
   until(lambda:has('DONE B {"confirmed":false}'),'Queued cancellation must settle while another host prompt stays active')
   read(.1);assert prompts()==1 and not has('DONE A'),'Queued cancellation must preserve the active prompt'
   os.write(m,b'yes\n')
   until(lambda:prompts()==2,'A cancelled queue slot must not block a later host prompt')
   read(.1);assert not has('DONE C'),'The later host still needs its own answer'
   os.write(m,b'yes\n')
  elif scenario=='host-both':
   p.send_signal(signal.SIGUSR1)
   until(lambda:has('COMPLETE'),'Active and queued cancellations must settle without an answer')
   send(b'yes\nyes\n');read(.1)
   assert prompts()==1,'Aborted queued call must not display a prompt'
  else:
   if scenario=='host-race':os.write(m,b'yes\n')
   elif scenario not in ('host-before','host-drain'):p.send_signal(signal.SIGUSR1)
   until(lambda:has('DONE A {"confirmed":false}'),'Aborted confirmation must decline without an answer')
   expected=1 if scenario in ('host-before','host-drain') else 2
   until(lambda:prompts()==expected,'The next call must own a fresh prompt')
   read(.1);assert not has('DONE B'),'Cancellation or its answer must not approve the next host'
   os.write(m,b'yes\n')
  until(lambda:has('COMPLETE'),'All calls must settle and release their readers')
  p.wait(timeout=2);assert p.returncode==0,'Child assertions and cleanup must pass'
  assert b'STARTED' not in out,'Cancellation must not grant a started permit'
  assert not list((Path(scratch)/'workspace').glob('marker-*')),'Cancellation must not write physical markers'
  print(json.dumps({'scenario':scenario,'passed':True,'physical_writes':0,'provider_calls':0}))
 except BaseException:
  print(out.decode(errors='replace'),file=sys.stderr);raise
 finally:
  if p.poll() is None:p.kill();p.wait()
  os.close(m)
