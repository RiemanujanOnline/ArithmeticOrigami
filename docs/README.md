# Arithmetic Origami · Śūnya Conjecture

**Sambuddha Sarkar** · https://riemanujan.com

Arithmetic Origami is exact arithmetic derived from [0; *z*] = 1/*z*, in pure Integers (ℤ) and Rationals (ℚ). This record holds *Origami Arithmetica*, a three-page Gazette, with the Lean 4 proofs of its statements, the Foldcyclopedia's public entries and their term tables. 48 parameters and observables of the Standard Model and ΛCDM: 47 numerically computed, each an exact rational inside its measured 1σ interval. Nothing fitted. Selected by today's measurement; tested by the next.

## Contents

- `menu_tasting.pdf`: the opening, Riemanujan's Thanksgiving Tasting Menu.
- `gazette.pdf`: page 1, front page.
- `free_parameters.pdf`: page 2, Standard Model.
- `bigbang_fold.pdf`: page 3, ΛCDM and the Big Bang.
- `foldcyclopedia.pdf`: Foldcyclopedia, public entries.
- The live pages: https://gazette.riemanujan.com
- `lean/`: Lean 4 proofs, one file a PDF, each built on the one before: `Sunya.lean` (page 1), `Foldcyclopedia.lean` (the Foldcyclopedia), `FreeParameters.lean` (page 2), `BigBang.lean` (page 3), in `lean/OrigamiArithmetica/`. Each page of https://riemanujan.com carries its own proof.
- `tables.zip`: term tables, one file a sequence, one line "n a(n)". The git repository holds none; each table is at `https://bfiles.riemanujan.com/<file name>`.
- `data/digits/`: each candidate's digits.
- `GLOSSARY.md`: every word defined. `CLAIMS.md`: every claim with its file and check.
- `SHA256SUMS`: every file.

## Checking

1. `shasum -a 256 -c SHA256SUMS`. Every line should print `OK`.
2. `unzip tables.zip && shasum -a 256 -c tables.SHA256SUMS`. Every line should print `OK`.
3. In `lean/` (Lean 4.34.1, Mathlib v4.34.1): `lake exe cache get`, then `lake build`. The output is the axiom report alone, 720 theorems; an error is a false statement. `grep -r sorry OrigamiArithmetica` should return no results.

## Scope

A Lean check shows that stated numbers follow from stated definitions. A definition read as a physical thing is a reading, marked as one on every page.

## Citing

Cite the DOI on this record's page; the concept DOI there resolves to the latest version. Sequence identifiers (A000012 and the like) are cross-references to the OEIS.

## Licence

CC BY-SA 4.0 for the files of this record. The Lean files also stand under the Apache License 2.0 (`LICENSE`, `NOTICE` at the git repository's root). Copyright and licence cover the files, never the mathematics they state.

## Workflow Delineation
* Author: Sambuddha Sarkar.
  Computation, Śūnya conjecture and axiom, and the methodology. Definitions, theorems and kernel checks formulated, reviewed and validated.
* AI assistance:
  Principal investigation within bounded searches.
  Text, code and computation runs drafted and executed under the author's review.
