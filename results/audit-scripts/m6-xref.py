"""Task C, mechanical part: every \\ref resolves, no duplicated numbering.

Compares the label set of paper/braided-sym-zpd.tex with the \\newlabel set recorded in
paper/build/braided-sym-zpd-v8.aux (the compiled v8), and lists dangling refs and labels
that are never referenced.
"""
import re, sys

tex = open('paper/braided-sym-zpd.tex', encoding='utf-8').read()
aux = open('paper/build/braided-sym-zpd-v8.aux', encoding='utf-8', errors='replace').read()
labels = re.findall(r'\\label\{([^}]*)\}', tex)
auxl = re.findall(r'\\newlabel\{([^}]*)\}', aux)
refs = re.findall(r'\\ref\{([^}]*)\}', tex)

print('labels in .tex :', len(labels), '(distinct', len(set(labels)), ')')
print('labels in .aux :', len(auxl), '(distinct', len(set(auxl)), ')')
print('in .tex not in .aux:', sorted(set(labels) - set(auxl)))
print('in .aux not in .tex:', sorted(set(auxl) - set(labels)))
print('duplicated labels  :', sorted({l for l in labels if labels.count(l) > 1}))
print('\\ref sites         :', len(refs), 'distinct', len(set(refs)))
print('dangling \\ref      :', sorted(set(refs) - set(labels)))
print('never referenced   :', sorted(set(labels) - set(refs)))
sys.exit(1 if (set(refs) - set(labels)) or set(labels) != set(auxl) else 0)
