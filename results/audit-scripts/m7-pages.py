#!/usr/bin/env python3
"""Locate a phrase in a pdftotext -layout dump and report PDF page + printed page number.

Usage: python3 m7-pages.py bresar 'Definition 1\.1' [more regexes...]
The printed page number is read off the running head of the same page (line 0/1 of the page
text) and cross-checked against the nearest printed page marker, so an offset is inferred once
and then applied to every hit.
"""
import re, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
TXT = {"bresar": "../../.scratch/audit/m7/bresar.txt",
       "adrabi": "../../.scratch/audit/m7/adrabi.txt",
       "hj":     "../../.scratch/audit/m7/hj.txt"}

def pages(name):
    raw = open(os.path.join(HERE, TXT[name]), encoding="utf-8", errors="replace").read()
    return raw.split("\f")

def printed_of(chunk, pdfpage):
    for L in chunk.split("\n")[:6]:
        m = re.match(r"^\s*(\d{1,3})\s+\S", L)
        if m: return int(m.group(1)), pdfpage - int(m.group(1))
        m = re.match(r"^.*?\s(\d{1,3})\s*$", L)
        if m and len(L.strip()) > 5: return int(m.group(1)), pdfpage - int(m.group(1))
    return None, None

def main():
    name = sys.argv[1]
    pages_ = pages(name)
    # infer offset from any page whose head starts with a number
    off = None
    for i, c in enumerate(pages_):
        p, o = printed_of(c, i + 1)
        if p is not None: off = o; break
    for pat in sys.argv[2:]:
        rx = re.compile(pat)
        hits = 0
        for i, c in enumerate(pages_):
            if rx.search(c):
                p, o = printed_of(c, i + 1)
                pp = p if p is not None else (i + 1 - off if off is not None else None)
                print(f"{pat!r}: pdf page {i+1}, printed page {pp}")
                hits += 1
        if not hits: print(f"{pat!r}: NOT FOUND")

main()
