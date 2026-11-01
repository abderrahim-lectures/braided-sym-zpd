#!/usr/bin/env python3
"""m2 / Task C: cross-reference and internal-consistency checks on paper/braided-sym-zpd.tex.

Checks
  1. every \\ref/\\eqref target exists (dangling reference)
  2. every \\label is referenced at least once (orphan label)
  3. the prose word in front of \\ref ("Theorem~\\ref{...}") matches the
     LaTeX environment that carries the label
  4. label uniqueness
  5. enumerated parts ("\\ref{x}(a)") exist in the target environment
  6. the section order against the Introduction's plan
Usage: python3 m2-xref.py [path/to/braided-sym-zpd.tex]
"""
import re, sys, collections

PATH = sys.argv[1] if len(sys.argv) > 1 else "paper/braided-sym-zpd.tex"
src = open(PATH, encoding="utf-8").read()

ENVS = ["theorem", "lemma", "corollary", "proposition", "definition", "example",
        "question", "remark", "notation", "proof", "abstract"]
env_re = re.compile(r"\\begin\{(" + "|".join(ENVS) + r")\}(\*?)")
label_re = re.compile(r"\\label\{([^}]*)\}")
end_re = re.compile(r"\\end\{(" + "|".join(ENVS) + r")\}")

labels, stack, stripped = {}, [], []
for ln, raw in enumerate(src.split("\n"), 1):
    s = re.sub(r"(?<!\\)%.*$", "", raw)
    stripped.append(s)
    for m in env_re.finditer(s):
        stack.append((m.group(1), ln))
    for m in label_re.finditer(s):
        labels[m.group(1)] = dict(kind=stack[-1][0] if stack else "TOPLEVEL",
                                  line=ln, env_line=stack[-1][1] if stack else None)
    for m in end_re.finditer(s):
        if stack and stack[-1][0] == m.group(1):
            stack.pop()
        else:
            print("!! unbalanced \\end{%s} at line %d" % (m.group(1), ln))

ref_re = re.compile(r"\\(ref|eqref|autoref)\{([^}]*)\}")
refs = []
for ln, s in enumerate(stripped, 1):
    for m in ref_re.finditer(s):
        w = re.search(r"([A-Za-z]+)~?\s*$", s[:m.start()])
        refs.append(dict(line=ln, kind=m.group(1), target=m.group(2),
                         word=w.group(1) if w else ""))

print("labels: %d (%d distinct)   references: %d"
      % (len(re.findall(r"\\label\{", src)), len(labels), len(refs)))
print("label kinds:", dict(collections.Counter(v["kind"] for v in labels.values())))

print("\n--- 1. dangling references ---")
bad = [r for r in refs if r["target"] not in labels]
print("none" if not bad else "\n".join("%d: \\%s{%s}" % (r["line"], r["kind"], r["target"]) for r in bad))

used = collections.Counter(r["target"] for r in refs)
print("\n--- 2. labels never referenced ---")
orph = [k for k in labels if used[k] == 0]
print("none" if not orph else "\n".join("%-22s line %-4d kind %-11s" % (k, labels[k]["line"], labels[k]["kind"]) for k in orph))

MAP = {"Theorem": "theorem", "Lemma": "lemma", "Corollary": "corollary",
       "Proposition": "proposition", "Definition": "definition",
       "Example": "example", "Question": "question", "Remark": "remark",
       "Notation": "notation", "Section": "TOPLEVEL", "Sections": "TOPLEVEL"}
print("\n--- 3. prose word vs environment kind ---")
mm = 0
for r in refs:
    if r["target"] not in labels:
        continue
    k, w = labels[r["target"]]["kind"], r["word"]
    if w == "":
        print("line %-4d: no prose word before \\ref{%s} (kind %s)" % (r["line"], r["target"], k)); continue
    if MAP.get(w) != k:
        mm += 1
        print("line %-4d: '%s~\\ref{%s}' but the label sits in %s (line %d)"
              % (r["line"], w, r["target"], k, labels[r["target"]]["line"]))
if mm == 0:
    print("none")

print("\n--- 4. duplicate labels ---")
dups = [k for k, c in collections.Counter(re.findall(r"\\label\{([^}]*)\}", src)).items() if c > 1]
print("none" if not dups else dups)

print("\n--- 5. \\ref{target}(part) against the target's enumerate label ---")
for m in re.finditer(r"\\ref\{([^}]*)\}(\([a-z0-9]+\))", src):
    tgt, part = m.group(1), m.group(2)[1:-1]
    ln = src[:m.start()].count("\n") + 1
    if tgt not in labels:
        continue
    start = src.rfind("\\label{%s}" % tgt, 0, m.start())
    opts = [o for o in re.findall(r"label=\(([^)]+)\)", src[start:start + 2500])]
    flat = [o.replace("\\roman*", "").replace("*", "") for o in opts]
    ok = (not flat) or part in flat
    print("line %-4d %s(%s): enumerate labels %s -> %s"
          % (ln, tgt, part, flat if flat else "(none)", "ok" if ok else "MISMATCH"))

print("\n--- 6. sections ---")
for i, (t, _) in enumerate(re.findall(r"\\section\{([^}]*)\}(\\label\{([^}]*)\})?", src), 1):
    print("%d. %s" % (i, t))
