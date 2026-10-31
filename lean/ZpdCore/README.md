# A self-contained machine check of the paper's core

`Zpd.lean` (Mathlib only) checks the paper's main results over an arbitrary field, for an arbitrary
bilinear `μ`, with no unitality, associativity or finiteness assumptions where the paper has none:

| Paper | Declaration |
|---|---|
| `cor:criterion` | `determined_iff` |
| `thm:zpd-fxy` | `determined_comp_of_right_id` (the unit used only as a right identity) |
| `prop:injective` | `determined_of_injective_comp` |
| `cor:identity` (ii), char-2 remark | `identity_iff`, `determined_zero` |
| `cor:twisted`, `cor:anti` | `twisted_determined` (α only multiplicative), `anti_braiding` |
| `thm:codim` | `codim_determined`, `codim_determined_of_f_one_zero` |
| lines 292 and 395 | `jordan_forces_comm`, `twisted_forces_comm` |
| the abstract's three-braidings sentence | `braidings_commutative` (α not assumed unital) |

Check it with

```sh
lean lean/ZpdCore/Zpd.lean      # with Mathlib on LEAN_PATH
```

The file ends with twelve `#print axioms` commands; each reports only `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry` and no added axiom.

This is **not** part of `lake build`: it is a standalone check, and it is deliberately independent of
`Research.BraidedSymZpd`, whose two imported modules are not published here.

Provenance: written by an independent review pass (Open Math OS), not by the author.

Not covered: the numerical claims of `prop:matrix` (417 zero pairs, rank 4, dimensions 12 and 13),
which are checked in the review report and by the `#guard`s of the author's file.
