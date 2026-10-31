import subprocess
from build2 import T, M
A=T(3,2)
print("p,n",A.p,A.n)
for i in range(A.n):
    print(" e_%d:"%i,[list(A.mult[i][j]) for j in range(A.n)])
n=A.n
s="%d %d\n"%(A.p,n)+" ".join(str(x) for i in range(n) for j in range(n) for x in A.mult[i][j])
print("feed:", s)
o=subprocess.run(["./bruteder"],input=s,capture_output=True,text=True)
print("out:",o.stdout,"err:",o.stderr)
