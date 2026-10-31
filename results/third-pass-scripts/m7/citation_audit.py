#!/usr/bin/env python3
"""Reproducible evidence for the citation audit of paper/braided-sym-zpd.tex (v8).

Run:  python3 citation_audit.py
Network required.  Prints, for every bibliographic question the report answers,
the query and the raw answer.
"""
import json
import re
import urllib.request

UA = {"User-Agent": "citation-audit/1.0 (review of a preprint)"}


def get(url, raw=False):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=60) as r:
        b = r.read()
    return b if raw else b.decode("utf-8", "replace")


def head(t):
    print("\n" + "=" * 78 + "\n" + t + "\n" + "=" * 78)


# ---------------------------------------------------------------- 1. Adrabi 2026
def adrabi():
    head("1. Existence of 'A. Adrabi, Braided-symmetric derivations of algebras, 2026'")

    q = "http://export.arxiv.org/api/query?search_query=au:Adrabi&start=0&max_results=50"
    x = get(q)
    print("[arXiv API au:Adrabi] totalResults =",
          re.search(r"<opensearch:totalResults[^>]*>(\d+)<", x).group(1))

    q = ("https://api.crossref.org/works?query.author=Adrabi&rows=30"
         "&select=title,author,DOI,issued,container-title")
    d = json.loads(get(q))["message"]["items"]
    print("\n[Crossref query.author=Adrabi] %d records:" % len(d))
    for it in d:
        print("   ", it.get("issued", {}).get("date-parts"), (it.get("title") or [""])[0],
              "|", ", ".join(a.get("family", "") for a in it.get("author", [])),
              "|", it.get("DOI"))

    q = "https://api.openalex.org/works?search=braided-symmetric%20derivations&per-page=5"
    d = json.loads(get(q))
    print("\n[OpenAlex search 'braided-symmetric derivations'] count =", d["meta"]["count"])
    for w in d["results"]:
        print("   ", w["publication_year"], w["display_name"])

    q = "https://api.openalex.org/authors?search=Adrabi"
    a = [x for x in json.loads(get(q))["results"] if x["display_name"] == "Abderrahim Adrabi"]
    aid = a[0]["id"].split("/")[-1]
    print("\n[OpenAlex author Abderrahim Adrabi] id =", aid, "works =", a[0]["works_count"])
    q = ("https://api.openalex.org/works?filter=author.id:%s&per-page=50"
         "&sort=publication_year:desc" % aid)
    for w in json.loads(get(q))["results"]:
        print("   ", w["publication_year"], "|", w["display_name"], "|", w.get("doi"))

    q = "https://api.archives-ouvertes.fr/search/?q=Adrabi&fl=title_s&rows=20"
    print("\n[HAL q=Adrabi] numFound =", json.loads(get(q))["response"]["numFound"])


# ------------------------------------------------------- 2. Bresar 2021 structure
def bresar_book():
    head("2. Bresar, Zero Product Determined Algebras (Birkhauser 2021) - real structure")
    print("Official record: https://link.springer.com/book/10.1007/978-3-030-80242-4")
    print("DOI 10.1007/978-3-030-80242-4, ISBN 978-3-030-80241-7, VIII+185 pp.")
    print("(The chapter/section list below is transcribed by hand from that official page;")
    print(" it is not scraped here because the page sits behind a bot check.  Everything")
    print(" after it IS queried live: the per-chapter reference lists.)")
    print("""
Part I  Algebraic Theory
  ch.1 Zero Product Determined Nonassociative Algebras   pp.   3-16
       1.1 The Definition of a zpd Nonassociative Algebra
       1.2 Symmetrically zpd Nonassociative Algebras
       1.3 Stability Under Algebraic Constructions
  ch.2 Zero Product Determined Rings and Algebras        pp.  17-32
       2.1 zpd Rings / 2.2 Examples and Non-examples / 2.3 The Finite-Dimensional Case
  ch.3 Zero Lie/Jordan Product Determined Algebras       pp.  33-58
       3.1 Lie and Jordan Algebras / 3.2 zLpd / 3.3 zJpd
Part II Analytic Theory (ch.4-6)
Part III Applications
  ch.7 Homomorphisms and Related Maps                    pp. 113-137
       7.1 Zero Product Preserving Maps / 7.2 Commutativity Preserving / 7.3 Jordan Homomorphisms
  ch.8 Derivations and Related Maps                      pp. 139-156
       8.1 Characterizing Derivations by Action on Zero Products
       8.2 Local Derivations
       8.3 Derivations and Quasinilpotent Elements
  ch.9 Miscellany                                         pp. 157-174
""")
    print("Chapter bibliographies as deposited by Springer (Crossref/OpenAlex).")
    for n in (1, 2, 3, 7, 8):
        doi = "10.1007/978-3-030-80242-4_%d" % n
        d = json.loads(get("https://api.openalex.org/works/doi:" + doi))
        ids = d.get("referenced_works", [])
        print("\n-- %s (%d references)" % (d["display_name"], len(ids)))
        if not ids:
            continue
        filt = "|".join(i.split("/")[-1] for i in ids)
        r = json.loads(get("https://api.openalex.org/works?filter=openalex_id:%s"
                           "&per-page=100&select=display_name,publication_year" % filt))
        for w in sorted(r["results"], key=lambda w: w["publication_year"] or 0):
            t = w["display_name"]
            if n == 1 or (n == 8 and "ocal" in (t or "")):
                print("   ", w["publication_year"], "|", t)


# ------------------------------------------------------------- 3. Brice-Huang
def brice_huang():
    head("3. Brice-Huang: which theorem number carries the criterion?")
    import os
    import subprocess
    import tempfile
    for label, url in [
        ("PUBLISHED (author's copy of LAMA 63(2):326-342)",
         "https://www.danielbrice.net/assets/publications/brice2015zero.pdf"),
        ("arXiv:1110.5848 (earlier draft)", "https://arxiv.org/pdf/1110.5848"),
    ]:
        try:
            fd, path = tempfile.mkstemp(suffix=".pdf")
            os.close(fd)
            with open(path, "wb") as fh:
                fh.write(get(url, raw=True))
            txt = subprocess.run(["pdftotext", "-layout", path, "-"],
                                 capture_output=True, text=True).stdout
            os.unlink(path)
        except Exception as e:                                    # pragma: no cover
            print(label, "FAILED:", e)
            continue
        print("\n" + label)
        for m in re.finditer(r"(Lemma|Theorem) 2\.\d[^\n]*", txt):
            print("   ", m.group(0)[:110])


if __name__ == "__main__":
    adrabi()
    bresar_book()
    brice_huang()
