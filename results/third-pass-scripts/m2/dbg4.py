import time
from subalgs import closure, all_mats, unflat
p,d=2,4
t0=time.time()
mats=all_mats(p,d); print("all_mats", len(mats), time.time()-t0)
ident=[[1 if i==j else 0 for j in range(d)] for i in range(d)]
others=[M for M in mats if M!=ident]; print("others", len(others))
t0=time.time()
b=closure(p,[others[1]],d); print("closure1 dim", len(b), time.time()-t0)
t0=time.time()
b=closure(p,[others[1],others[2]],d); print("closure2 dim", len(b), time.time()-t0)
