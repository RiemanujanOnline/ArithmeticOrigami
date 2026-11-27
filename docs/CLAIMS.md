# Claims index

Each claim of the record, under its qualifier, with the file that states it and the check that holds it. `GLOSSARY.md`, section 6, defines the qualifiers. No measured figure and no count is restated here: the named file prints it.

## 0. The direction; what is classical, what is new

The record runs one way, in order:

1. Axiom Ś comes first: the given, the empty tail 1/0, and two letters, the crease J̇ (J-bindu; written J in Lean) and the shift T (`GLOSSARY.md`, section 1).
2. A number is a word in those letters, and a sequence is a list of integers. Euclid's division reads either one, and its
   quotients are the object's letters.
3. Every object here is a list of integers or of exact fractions: a word, a list of terms, a list of letters. A list of N
   entries has N coordinates. The Foldcyclopedia's addresses form a tree in that space of lists, and an object reached by more
   than one path has more than one address.
4. Every number a page prints is a count: a term, a quotient, a number of paths, a determinant of counts.
5. A curve, a physical quantity or a measured value enters last, as a reading set beside a list. Nothing measured enters
   a derivation.

The thesis behind the direction is the author's and has no check: the integer lists come first, and
continuous geometry is their projection, not their source.

- **Classical:** Peano's axioms, the free product and its normal form, Euclid, Gosper's tensor, Lagrange's theorem, the
  modular group on the hyperbolic plane, Stern–Brocot's two shifts, and the fold as the paths of the J-fraction
  (Stieltjes 1889, Flajolet 1980); the chakravāla is Jayadeva's, refined by Bhāskara II (Bījagaṇita, 1150, v. 75; Colebrooke 1817,
  §§ 83–86).
- **New:** the steps from ∞ with the crease as a step of the arithmetic, which neither Peano nor Stern–Brocot has (as a
  matrix factor it is classical: a quotient's matrix is TᵃJ̇); the origami as a derived hypergraph of sequences; and these
  connections assembled in one origami.
- **Each connection is classical where it is cited.** Together they are not found in the sources cited here.
- **Every step carries a name already trusted.** The names are citations; the novelty is a claim, with no check.
- **The notion of proof is upapatti,** demonstration by rationale and computation: a claim holds when its check reruns,
  and the Lean kernel is the referee a stranger can trust.

## 1. Theorems: what each Lean file states

Every file is in `lean/`. Each statement is checked by the Lean kernel. A file's subject is given in its own header's terms.

| File | States |
|---|---|
| `Sunya.lean` | Axiom Ś and the Śūnya conjecture's five points; the model's faithfulness; Peano's axioms on the letters; the two shifts as Stern–Brocot's letters; the unimodular group generated and presented; the convergence of every regular infinite word; the J-fraction's step and its three kinds (elliptic, parabolic, hyperbolic); the atoms' multipliers; the Dirac cone; every Dirac level a rational curve; Euclid's measurement of α's lock. The Foldcyclopedia's entries open it. |
| `Foldcyclopedia.lean` | The concise origami's transformation steps on their first terms; each continued fraction's leading quotients by Euclid's algorithm; determinant identities; general algebraic identities; each element a period and a seat under the noble-gas closures; the table's blocks, periods and closures in closed form; the one-electron ion's lines and sizes, exact. The Foldcyclopedia's entries open it. |
| `FreeParameters.lean` | Page 2's one file. Each candidate row's arithmetic, a block a row of the Gazette's table: Euclid's division of the lock to remainder 0 gives its word; the row's fraction is the lock's value by the row's rule (a ratio, an angle or a coupling); Euclid's division of the fraction gives the printed letters; the lock is the product of its spinors. After the rows, unchanged from `Sunya.lean`: the lock's square as the flagpole (`tri_square`), the rule at every lock (`loop_rule`), α's lock's word, factors and norm (`node_word`, `node_inv_frac`, `node_factors`, `hermite_serret`, `lor_pythagoras`); and from `Foldcyclopedia.lean` the central binomials, the arcsine row (`step18_centralDiagonal`). |
| `BigBang.lean` | Page 3's one file. Every statement the page cites: the transformation steps the epochs cite; the elements' closures and seats; the shell closures of the nucleus read off (n+1)!'s division as it runs, with the onset at every odd N from 3 and a readout that is never 34; the helium fraction 8/33 inside its 1σ interval and the simplest fraction there; the lock's square; Table 1's cosmology rows. |

The site's other pages each carry their own Lean file in their proof download; they are outside this record.

- **`SHA256SUMS` names every Lean file, by its path in `lean/`.**
- **What a Lean check shows:** that the stated numbers follow from the stated definitions. That a definition is the physical thing its name reads it as is a reading (section 4).

## 2. Derived

| Claim | Stated in | Check |
|---|---|---|
| The Śūnya conjecture's points 1–5; every nonnegative unimodular matrix is exactly one reduced word; Peano's axioms on the letters | `Sunya.lean` | `point1_position` to `point5_swap`; `faithful`; `peano_succ_inj`, `peano_succ_ne_zero`, `peano_induction` |
| Each entry's terms, letters, Hankel zeros and kind | `tables.zip` | computed; "undetermined at N terms" is a result at N terms |
| The shell closures of the nucleus, 2, 8, 20, 28, 50, 82, 126: the Euclid division of (n+1)! read as it runs. Its letters are α_N = 2(N + 1) and β_N = N(N + 1). The list's formula: a(N) = Σ α_k (k = 0 … N) + Σ β_k (k = 1 … N − 1) + (β_N where β_N ≤ α_N, else 0). No inputs. | `BigBang.lean` | `onset_euclid`, `rest_le_top`, `readout_closure`, `readout_not_34`; the published list compared last, `readout_published` |
| The noble-gas closures, 2, 10, 18, 36, 54, 86, 118: n!'s finer division read the same way, running sums of 2c². Each element is a period and a seat under them. | `Foldcyclopedia.lean`; `BigBang.lean` | `closures_closed_form`, `closures_continue`; `closes_are_period_sums`, `el_closures` |
| α's family and rule: a coupling 2mn/(m² + n²) at every lock (m, n); the lock's word; its spinors | `FreeParameters.lean`, from `Sunya.lean` | `loop_rule` (an identity for every m and n), `node_word`, `node_inv_frac`, `node_factors` |
| The first fold f = 1 − 2w, the reciprocal of 2ⁿ's generating function 1/(1 − 2w); the rod ν = 2ⁿ/(n + 1), with letters α = 1 and β_k = k²/(4k² − 1) | `bigbang_fold.pdf`, the lines marked computed and theorem | the page's own checks. Their reading as Schwarzschild's f and Weyl's rod takes the static spherical form as an input, and the page says so. |
| **The first fold's metric is not flat: its Kretschmann scalar is 48/r⁶.** With the static spherical form as an input, the metric built from f has Ricci tensor 0 and Kretschmann scalar 48/r⁶ (G = c = M = 1), nowhere 0 at finite r. A flat spacetime has 0 everywhere. | `bigbang_fold.pdf`: the Kretschmann lines marked computed, and its line "Not flat" | the page's own check, at its sampled points; a proof at every rational r and y where the form is defined is not in this record. "Flat" has two senses here: this is spacetime curvature of the first fold's metric, while Ω_K is the curvature of FLRW's space slice, a different quantity, set beside it and not compared. "The universe is not flat" would also rest on the page's reading of the model's t = 0 as this black hole. |

## 3. Derived and mapped: the lock lines

The lock entries of the list, under the Stern–Brocot tree, and the lines of `free_parameters.pdf`. Three columns a line, each printed by the sheet:

| Column | Holds | Where |
|---|---|---|
| Structure | the lock (m, n); its word to remainder 0; the exact value in its family; the norm's spinors | the sheet's Mathematical read; its Readings under Rule, Lock, Value and Factors |
| Measurement | the 1σ interval; its source; its checkpoint; the human choices behind it | the sheet's Experiment; its Readings under Measurement |
| Chance | p beside the line; the sheet's combined test over the lines | the sheet's Readings under Chance; its legend, under p |

- **The origami is derived first.** The measurement is lined up last and selects the lock.
- **Which lock (m, n) a continuous parameter takes is not yet decided by mathematics alone.** Axiom Ś unfolds the sequence list, the boundary locks (1, 1) and (2, 1), and the four Gaussian rational families from the root `[0; z] = 1/z`; the measurement's 1σ interval selects the simplest lock (m, n) inside it, and Euclid's division traces m/n down to remainder 0.
- **Each lock is the simplest fraction in its measurement's 1σ interval, and every 1σ interval contains one.**
- **Spinor norm and prime spinors (`FreeParameters.lean`, from `Sunya.lean`).** A lock (m, n) is the Gaussian integer m + ni (Penrose's real 2-spinor), whose square (m + ni)² = (m² − n²) + 2mn·i is the null flagpole rationalizing both 2mn/(m² + n²) and √(1 − α²) = (m² − n²)/(m² + n²) (`tri_square`, `lor_pythagoras`). By Fermat's two-square theorem and Euclid's division stopped below √P (Hermite–Serret, `hermite_serret`), the norm m² + n² splits into prime spinors a² + b² = p (p = 2 or p ≡ 1 mod 4): on α's lock (1150813, 4199), the edge lock (1, 1), the self-recoil lock (2, 1), and the prime spinor (116341, −344824) of norm P = 132438819257 (`node_factors`).
- **The sheet prints its combined test's result in full on its legend.** Read the figures there.
- **A 1/N lock restates its 1σ interval's upper end.** Its digits are not a test.
- **Predicted digits are exact digits of the lock's fraction.** Because Euclid's division stops at remainder 0, every unmeasured letter before remainder 0 is fixed today, making the next empirical measurement the blind falsifiability test. Another lock of the same 1σ interval states others.
- **Every cosmology measurement is a fit inside the standard cosmological model,** with that model's assumptions. Its line cites the source.
- **Two cosmology lines are 1σ interval and reading only:** the primordial amplitude and the spectral index, the fit of an assumed power-law source.

## 4. Readings

- **The list's reading column.** A reading marked † is checked by count in the list's own check. One without it is a name compared last.
- **The Big Bang page.** Its key marks each line: computed, theorem, measured, compared, reading, open, imported, model or struck.
- **The physical names in the Lean files** (shell, spinor, clock, mass and the like) name integer objects. The statements are about the integers. Two of the names are Penrose's own objects on the integers, not nicknames: the lock is his spin-vector with real components (SL(2, ℝ) in place of SL(2, ℂ)), its square the flagpole, a null vector of the plane; the integer twistor (ω, π) is his twistor pair, helicity ω·π, null at 0 (GLOSSARY §5).
- **The Śūnya conjecture's foundational reading** is the author's thesis.

## 5. Compared

- **Measured values** stand as their sources print them, enter as measurements with their 1σ intervals, and are compared last.
- **The standard cosmological model's assumed lines** are struck on the Big Bang page, in its pane "Model lines struck". A strike marks an assumption of the model, not a measurement. No measured value is struck, and beside each struck line stands what the list holds, or that it holds none.
- **Prior art** is cited on the pages, in their Sources and prior-art tables. A line marked "not found" is a result at its search's stated bound, and claims no priority.
- **OEIS identifiers** name the sequences. Where an entry compares its terms with a published list, it says how many agree.

## 6. Not claimed

- No file proves the Śūnya conjecture's foundational reading.
- No line states that a constant equals its lock past the measured digits.
- No file claims an a priori derivation of which Gaussian lock (m, n) each continuous parameter occupies; the 1σ interval selects the lock, and Euclid's division to remainder 0 fixes the unmeasured letters for the next empirical measurement.
- No Lean check shows that an integer object is the physical thing it is read as.
- No search that did not find is stated as absence.
- No struck line is a measured value.
- The line "Not flat" is not a statement about the curvature of the standard cosmological model's space slice.
- The novelty stated in section 0 is a claim with no check.
- Copyright and the licence cover files, never the mathematics they state.
