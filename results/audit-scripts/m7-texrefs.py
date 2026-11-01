#!/usr/bin/env python3
r"""Structural audit of paper/braided-sym-zpd.tex.

(1) every \label with the environment it sits in and the number LaTeX will print
    (the preamble puts theorem/lemma/corollary/proposition/definition/example/question/remark
    on one shared counter numbered within section, so the numbers below are forced);
(2) every \ref/\eqref on the line it appears, resolved;
(3) dangling refs, duplicate labels, labels never referenced;
(4) the \cite keys used and how often.
"""
import re, os, collections

PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "paper", "braided-sym-zpd.tex")
lines = open(PATH).read().split("\n")

ENVS = ("theorem|lemma|corollary|proposition|definition|example|question|remark")
beg = re.compile(r"\\begin\{(" + ENVS + r")\}")
end = re.compile(r"\\end\{(" + ENVS + r")\}")
lab = re.compile(r"\\label\{([^}]*)\}")
REF = re.compile(r"\\(?:ref|eqref|cref|Cref)\{([^}]*)\}")

section, counter = 0, 0
envstack = []            # (env, number, startline)
labels = {}              # label -> (env, number, line)
order = []               # (env, number, label, first line)
seclabels = {}           # label -> (section title, line)
for i, L in enumerate(lines, 1):
    if "\\section{" in L:
        section += 1; counter = 0
        t = re.search(r"\\section\{(.*)$", L).group(1)
        m = re.search(r"\\label\{([^}]*)\}", L)
        if m: seclabels[m.group(1)] = (t[:40], i)
    if beg.search(L):
        counter += 1
        envstack.append((beg.search(L).group(1), f"{section}.{counter}", i))
        order.append([envstack[-1][0], envstack[-1][1], None, i])
    for m in lab.finditer(L):
        if envstack:
            e, n, sl = envstack[-1]
            labels[m.group(1)] = (e, n, i)
            if order and order[-1][1] == n: order[-1][2] = m.group(1)
        else:
            labels[m.group(1)] = ("plain", "-", i)
    if end.search(L) and envstack:
        envstack.pop()

refs = [(i, m.group(1), L.strip()) for i, L in enumerate(lines, 1) for m in REF.finditer(L)]

print("=== labelled theorem-like environments, with the number they print ===")
for e, n, l, sl in order:
    print(f"  {e:12s} {n:5s} {str(l):22s} line {sl}")
print("\n=== section labels ===")
for k, v in seclabels.items(): print(f"  {k:14s} line {v[1]:4d}  {v[0]}")
print("\n=== dangling references ===")
bad = [(i, l) for (i, l, t) in refs if l not in labels and l not in seclabels]
print("  none" if not bad else "\n".join(f"  line {i}: \\ref{{{l}}}" for i, l in bad))
print("\n=== duplicate label definitions ===")
c = collections.Counter(m.group(1) for L in lines for m in lab.finditer(L))
print("  none" if not [k for k, v in c.items() if v > 1] else "  " + str([k for k, v in c.items() if v > 1]))
print("\n=== labels never \\ref'ed ===")
used = {l for _, l, _ in refs}
never = [k for k in labels if k not in used]
print("  " + ", ".join(never) if never else "  (none)")
print("\n=== every reference resolved ===")
for i, l, t in refs:
    if l in labels:
        e, n, _ = labels[l]
        print(f"  line {i:4d}  {l:22s} -> {e} {n}")
    else:
        print(f"  line {i:4d}  {l:22s} -> section {seclabels[l][0] if l in seclabels else 'MISSING'}")
print("\n=== cite keys ===")
cites = collections.Counter()
for L in lines:
    for m in re.finditer(r"\\cite[a-z]*\s*(?:\[[^\]]*\]\s*)*\{([^}]*)\}", L):
        for k in m.group(1).split(","): cites[k.strip()] += 1
for k, v in sorted(cites.items()): print(f"  {k}: {v}")
