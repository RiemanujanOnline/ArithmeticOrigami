# Glossary

The pages and files of this record use a small set of house words. Each is defined here by one concise statement, with its standard name beside it. Where a word carries more than one sense, the senses are numbered and listed apart; section 7 gathers them.

A name in code type, with its file, is a theorem the Lean kernel checks. The files are in `lean/`.

Read section 1 first. Every later word rests on it.

## 1. Axiom Ś

- **Ś0, the given.** The empty tail 1/0, the unwritten sheet, and two letters, J̇ and T. Nothing else. We write ∞ for 1/0. J̇ is J-bindu: J with the bindu, the zero's dot (śūnya-bindu), which the pages draw large; the Lean files write J.
- **Ś1, zero is a crease.** J̇J̇ = ε: the crease undoes itself. 0 := J̇∞.
- **Ś2, one is a shift.** No nonempty string of T's is ε. 1 := T0 = TJ̇∞.
- **Ś3, a number is a word.** A numeral is a finite word applied to ∞. Two words are the same word when they agree after every J̇J̇ is deleted, and nothing else makes two words equal. The reduced word T^a₀ J̇ T^a₁ J̇ ⋯ T^aₙ J̇ is the numeral [a₀; a₁, …, aₙ]: its positions are its creases, its quotients are counts of shifts.
- **Ś4, infinite words.** An infinite word denotes what its prefixes converge to, when they converge; a real number enters only as a proved prefix.
- **Ś5, the wheel (chakravāla).** When a word's kept pair returns after a cycle of divisions, the cycle turns about one fixed point, the wheel's kha, a śūnya. The word is that fixed point, a root of an integer quadratic; no limit is taken. A rule of evidence beside Ś4: it adds no letter and no relation, and runs on Ś0–Ś3's words. A point a cycle's matrix fixes is a root of the cycle's integer quadratic (`wheel_fixed_point_quadratic`); the golden word's point is a root of x² − x − 1 (`wheel_golden`); Bhāskara's two questions after the cakravāla (Bījagaṇita 76) are answered in their own cycles' matrices, 67 in one turn (`wheel_bhaskara_67`), 61 with the sign turned in one turn and +1 in two (`wheel_bhaskara_61_one_turn`, `wheel_bhaskara_61`).

In the model, T is the matrix [[1, 1], [0, 1]], x ↦ x + 1, and J̇ is [[0, 1], [1, 0]], x ↦ 1/x (written J in Lean). Every nonnegative integer matrix of determinant ±1 is exactly one reduced word (`faithful`, `exists_word`, `unique_word`, in `Sunya.lean`). The checks named in this section are theorems of that file.

| Word | Statement | Standard name | Check |
|---|---|---|---|
| the given, the empty tail, 1/0, ∞ | The pair (1, 0): what every word is applied to. Given, not made. Every shift leaves it where it is, and no other word does. | value of the empty continued fraction | `inf_fixed_Tpow`, `stab_inf` |
| shift, T | x ↦ x + 1. No nonempty string of shifts is the empty word. | translation by 1 | `T_pow_ne_one`, `T_fixed_iff` |
| crease, J̇ (J-bindu) | x ↦ 1/x. It undoes itself, and it is the only quotient that does. It exchanges 1/0 and 0. | inversion, an involution | `point3_JJ`, `quotient_involution_iff`, `point5_swap` |
| zero | 0 := J̇∞: one crease of the given. | | `zero_from_inf` |
| one | 1 := T0. | | `one_from_zero` |
| natural number | n := TⁿJ̇∞: a count of shifts. Peano's axioms hold on the letters. | Peano numeral | `nat_from_inf`, `peano_succ_inj`, `peano_succ_ne_zero`, `peano_induction` |
| quotient, Q(a) | The word TᵃJ̇, the map x ↦ a + 1/x. The zero quotient is J̇ alone. | partial quotient | `point3_det`, `word_det` |
| word (sense 1) | A finite string of the letters J̇ and T. | element of the free product ℕ ∗ ℤ/2; nonnegative integer matrix of determinant ±1 | `faithful`, `same_word_iff` |
| numeral | A word applied to ∞, written [a₀; a₁, …, aₙ]. Each nonnegative rational has exactly one in Euclid's normal form. | finite simple continued fraction | `rational_once` |
| position | A quotient's place in a word. [0; q₁, q₂, …] = 1/[q₁; q₂, …]: the leading 0 moves every quotient one place. | | `point1_position` |
| crease limit | An interior zero merges its neighbours: [… a, 0, b …] = [… a + b …]. A trailing zero deletes its predecessor: [… a, b, 0] = [… a]. | | `point4_crease_limit`, `point4_trailing` |
| place (sense 1), D_b | x ↦ bx, of determinant b. A digit d at a new place is the word TᵈD_b. The zero digit holds a place; the zero quotient merges two. | positional notation, base b | `digit_word`, `place_det`, `zero_digit_holds` |
| the two shifts, R and L | R = T and L = J̇TJ̇. Together they reach every positive rational from ∞, and never zero. | Stern–Brocot's two letters | `JTJ`, `reach`, `zero_needs_crease` |
| elliptic, parabolic, hyperbolic | A word in T, T⁻¹ and J̇ of determinant 1, by its trace: elliptic at trace −1, 0 or 1 (order 3, 4 or 6); parabolic at trace ±2; hyperbolic at trace 3 or more in size. | standard | `trace_neg1_order3`, `trace0_order4`, `trace1_order6`, `crystallographic` |
| kha | The crease's axle: J̇ fixes exactly +1 and −1. A name in continued-fraction arithmetic, not a line of geometry. | fixed points of x ↦ 1/x | `J_fixed_iff` |

**The Śūnya conjecture.** Zero is an operator, to be defined before arithmetic. Its five points are theorems (`point1_position`, `point2_unit`, `point3_det`, `point4_crease_limit`, `point5_swap`). That arithmetic cannot be defined before the operator is the author's thesis, in the sense of Church–Turing. The theorems are consistent with it and do not prove it.

## 2. Division: letters and words

Every object of this record is read by Euclid's division. The quotients are the object's letters, and their list is its word.

| Word | Statement | Standard name |
|---|---|---|
| Euclid's division | dividend = quotient × divisor + remainder; then the same on (divisor, remainder), until the remainder is 0 or without end. | Euclidean algorithm |
| letter | One quotient of a division. For a number m/n it is a natural number a, the word TᵃJ̇. For a sequence it is an entry of its J-fraction (section 3), a rational. | partial quotient |
| word (sense 2) | The list of one object's letters, in order. | continued-fraction expansion |
| to remainder 0 | The division ends: the word is finite, and a number so read is rational. | terminating continued fraction |
| Chakravāla | A division shown whole: dividend, divisor, quotient and remainder at every step. The name is the cyclic method's (Jayadeva; Bhāskara II, Bījagaṇita, 1150, v. 75; Colebrooke 1817, §§ 83–86): each division's remainder is kept, and is the next division's divisor. Two divisions carry the name and are kept apart, in the next two lines. | the Euclidean algorithm's remainder sequence |
| kept pair | Take the fraction whose numerator and denominator are each of degree about half the terms and which agrees with the series on all its terms, and divide its numerator by its denominator with every step shown. The kept pair is each step's (dividend, divisor), read against the pair P steps on by cross-multiplying. Where the pair returns, the two cross products agree up to a constant except for a short polynomial of one fixed length at every step (for Catalan and Motzkin the constant is the sign turned P times and that length is P); on other objects they do not. | |
| remainder k | Step k's remainder, k = 1, 2, …, of the series' own division at infinity, Σ a(n)/xⁿ⁺¹. It is taken on N terms, and only its leading entries are the series' own. | |

## 3. Sequences

| Word | Statement | Standard name | Check |
|---|---|---|---|
| sequence | A list of integers a(0), a(1), …. Its first N terms are N integer coordinates. | integer sequence | |
| series | F(z) = Σ a(n) z^(−n−1): the terms written positionally in base z. | generating function at infinity | |
| continued fraction of a series | Of a sequence: [0; q₁(z), q₂(z), …] of its series, with polynomial quotients. Where every quotient has degree 1 it is the J-fraction. | continued fraction of a power series | |
| J-fraction, α and β | Where every quotient has degree 1: G.f. = 1/(1 − α₀x − β₁x²/(1 − α₁x − β₂x²/(1 − …))). The letters α₀, β₁, α₁, β₂, … are rationals. The terms, divided by a(0), are the moments (Jⁿ)₀₀ of the tridiagonal matrix with diagonal α, superdiagonal 1 and subdiagonal β. | Jacobi continued fraction (Stieltjes 1889; Flajolet 1980: the terms count weighted paths) | `Sunya.lean`: `fold_letter` |
| level | The index k of a pair (α_k, β_k). One more level fixes two more terms. | | |
| unit | 1, 0, 0, 0, … (A000007): the terms 0ⁿ, with 0⁰ = 1. This is a definition, and the conjecture and every computation here rest on it. Its series is 1/z = [0; z]; at z = 0 it is the given, 1/0. The list's root. | | `point2_unit` |
| seed | 1, 1, 1, … (A000012): the unit's binomial transform. | | |
| fold | A step of the list: a named map from listed objects to one more object. The list's fold column names it: B, partial sums, Euler transform, S-fraction and others. | sequence transform | |
| B | The binomial transform, a(n) = Σ C(n, k) b(k). It raises every α by 1 and leaves every β. | binomial transform | `binomial_is_shift`, `binomial_moves_alpha` |
| closed word | An object named by its own finite letter list, attached to the root. | terminating J-fraction; rational generating function | |
| Hankel determinant | det(a(i + j)), an n × n array of the terms. | Hankel determinant | |
| Hankel zero | Of a sequence: an order n at which the Hankel determinant is 0. There the J-fraction stops, and the division's quotient has degree 2 or more or the word ends. | vanishing Hankel determinant | |
| tail (a, b) | Letters constant from some level on: α = a, β = b. | eventually constant J-fraction | |
| band, edge | For a tail (a, b): the z with (z − a)² < 4b. Its two ends are its edges. | spectral band and its endpoints | |
| atom | A point mass of the measure whose moments are an object's terms: a pole of its series. | point mass | |
| rod | ν = 2ⁿ/(n + 1): the uniform density ½ on [0, 2]. Read on the Big Bang page as Weyl's rod of 1917. | uniform measure on a segment | |
| Meru | The triangle C(n, k). | Piṅgala's Meru-prastāra; Pascal's triangle | |
| topology | A column of the list: the kind of an object's letter law. Seven kinds: rational of order d; periodic J-fraction with preperiod and period; J-fraction letters rational in k; algebraic of degree d; triangle; finite word; undetermined at N terms. A cell may open with the mathematics' own kind where one is read: "hypergeometric, a(n)/a(n-1) = …", "multiplicative (Hecke)", "modular (eta quotient)" or "quasi-modular (E₂)". | | |
| undetermined at N terms, no law read at N terms | No law read on N terms. A result at N terms, never a statement of absence. | | |

## 4. The list and its addresses

| Word | Statement | Standard name | Check |
|---|---|---|---|
| list, fold list | The table of objects, one line an address. | | |
| entry | One address of the list. The Foldcyclopedia's entries are its public lines. | | |
| ID, address | The parent's address, a dot, then the object's own word (sense 2). | path in a rooted tree | |
| ॐ | The root: the unit. Every ID opens with it. | root | |
| ॐ.0 | Axiom Ś. Its five children are the Śūnya conjecture's points 1–5. These labels are numbers, not words. | | |
| ॐ.ॐ | The Stern–Brocot tree: the empty word, the root's 1/0 again. Its child steps are fractions m/n. | Stern–Brocot tree | |
| parent | The object a fold step starts from. Where several paths reach an object, its first address takes the parent with the fewest steps. | | `shortest_parent` |
| second address | The same object reached again by another path. | | |
| depth (sense 1) | Of an entry: the number of fold steps from the root. | depth in a tree | |
| rank | A sibling's order. Display only, never part of an ID. | | |
| kind | root, axiom, fold, period, element or word (sense 3). | | |
| word (sense 3) | An entry kind: a string of characters under a family's address, written family address / letters. A DNA strand; a pairing of bonds. | word over an alphabet | |
| closure | A running sum at which a shell is full. Noble-gas closures: 2, 10, 18, 36, 54, 86, 118. Shell closures of the nucleus: 2, 8, 20, 28, 50, 82, 126. | atomic numbers of the noble gases; nuclear magic numbers | `BigBang.lean`: `readout_closure`, `readout_published`, `closes_are_period_sums` |
| period, element | Under the noble-gas closures' address: period N, then seat j, written .N.j. These labels are numbers, not words. | | |
| seat | One state of a shell, counted. | | |
| † | A reading or count checked by count in the list's own check. Without it: a name compared last. | | |
| verse | The same count read in metre: lines of syllables, laghu short, guru long. | Piṅgala's counts | |
| dressing | A fold: each bare loop weighted t − 1. | | |
| science letter | P physics, C chemistry, B biology, A arithmetic: the field of an entry's reading. A where no science is named. | | |
| b-file | A term table, one line "n a(n)". | OEIS b-file format | |

Marks inside an ID:

| Mark | Meaning |
|---|---|
| `.` | a fold step: the parent's ID, then the object's own word |
| `,` | separates letters α₀, β₁, α₁, β₂, …, Hankel orders or coefficients |
| `-` | a negative letter or coefficient, never a separator |
| `/` | a rational letter p/q in lowest terms; in a word of sense 3, family address / letters |
| `a×` | scale: a(0) written first, then the letters of the series divided by a(0) |
| `\|` | Hankel zeros: the orders that follow. |
| `.\|` | an object's own list of Hankel zero orders, the first order of each run |
| `( )` | cycle: the bracketed letters repeat without end |
| `…` | cut: the word continues past 6 letters. A cut label is a prefix of the object's word. `addresses_distinct` holds for the listed lines; a cut label is not claimed to identify every sequence. |
| `{ }` | an algebraic number, by its integer polynomial, highest power first; `#k` after it is the root's rank from the left. |

## 5. Locks and measurements

| Word | Statement | Standard name | Check |
|---|---|---|---|
| lock (m, n) | A pair of whole numbers. Also the fraction m/n, a node of the Stern–Brocot tree, the Gaussian integer m + ni, and a real 2-spinor: Penrose's spin-vector with real components, SL(2, ℝ) in place of SL(2, ℂ), the double cover of the plane's Lorentz group. | rational number; Gaussian integer; real 2-spinor (Cartan 1913; Penrose and Rindler 1984) | |
| word of a lock | The continued fraction of m/n. It ends at remainder 0. | | `FreeParameters.lean`: each row's `_lock` and `_word`; `node_word` |
| depth (sense 2) | Of a lock: its level on the tree, the sum of its word's quotients less 1. | Stern–Brocot depth | |
| measurement | A published value with its uncertainty, as its source prints it. | | |
| 1σ interval | The published interval of a measurement: the value with one standard uncertainty, unless its line says otherwise. | uncertainty interval | |
| candidate | Numerically exact rational approximant that Arithmetic Origami generates inside a measured constant's error bar: the simplest one there. Its pair is a lock. | | |
| compatible | Candidate lies inside the error bar the laboratories publish. | | |
| tension, in tension | Candidate lies outside the published error bar for measurement. | | |
| standing | What a line's measurement says of its candidate, as the pages print it: compatible, in tension, bound, scale or reading only. | | |
| reading only | A standing: the measurement is a fit inside an assumed model, so the candidate beside it is read, not tested. | | |
| selection rule | Euclid's division to remainder 0 gives a lock's prime spinors; the spinor lock and the candidate are then compared. | | |
| control | The combined test over the lock lines: intervals moved off their measurements, the locks they select, Fisher's combined P against its threshold. Above it, a null: no line selected, none refuted. | Fisher's method | |
| simplest lock | The fraction of the 1σ interval reached first on the tree. Every 1σ interval contains one. | simplest rational in an interval | |
| family | The quantity a line reads off its lock: a coupling 2mn/(m² + n²); an angle with cot θ = m/n and sin²θ = n²/(m² + n²); the ratio m/n itself; a phase arg(m + ni). | | |
| α's rule | 1/α = (m² + n²)/(2mn) at a lock (m, n). The identity behind it holds for every m and n. | | `FreeParameters.lean`: `loop_rule`, `node_inv_frac` |
| norm | m² + n². | norm of a Gaussian integer | |
| spinor | A pair (a, b) with a² + b² = p, p a prime factor of the norm. A lock is the product of its spinors, up to a unit (Brahmagupta's identity): the Clifford product of real 2-spinors (Kocik 2007). ±(a, b) are one spinor up to its sign, Penrose's turn of 2π. | Gaussian prime; real 2-spinor | `FreeParameters.lean`: each row's `_spinors`; `node_factors` |
| flagpole of a lock | The lock's square: (m + ni)² = (m² − n²) + 2mn·i, the Pythagorean triple (m² − n², 2mn; m² + n²). It is the spinor's flagpole, a null vector of x² + y² = t², and the Hopf map S³ → S² on the real pair (m, n). | flagpole (Penrose); Euclid's triple; Hopf image | |
| twistor | A pair (ω, π) of integer quaternions, each a complex spin-vector whole, with helicity ω·π; null at 0. A lock is a real spin-vector of such a pair. | Penrose twistor (1967); a null twistor is a light ray of real Minkowski space | |
| place (sense 2) | "Place N, primes 4k + 1": p is the N-th prime of that form. | | |
| edge lock | (1, 1), of norm 2. | 1 + i | |
| self-recoil | (2, 1), of norm 5. | 2 + i | |
| unit lock | (1, 0): the given. A one-sided bound's 1σ interval contains it by construction. | | |
| checkpoint | The scale or configuration at which the laboratory reads the quantity. | renormalisation scale; experimental configuration | |
| letters decided, letter open | The leading quotients every number of the 1σ interval shares; then the first quotient the 1σ interval leaves open, with its range. | common prefix of two continued fractions | |
| measured digits | The leading digits both ends of the 1σ interval share. Each is cut, never rounded. | | |
| predicted digits | The lock's digits past the measured ones. They are exact digits of the lock's fraction and are not yet measured. Another lock of the same 1σ interval states others. | | |
| 1/N lock | A simplest lock (1, N): N restates the 1σ interval's upper end. | | |
| p | The share of intervals of equal width, moved off the measurement, whose simplest lock is as simple. It stands in its line's Readings, under Chance. The sheet's legend prints its combined test over the lines. | empirical p-value | |
| status | A field of the sheet's data; the pages print it as a standing. family: the family and its rule are derived; the measurement's 1σ interval selects the candidate. framed: read as a lock in a derived family; the measurement's 1σ interval selects the lock, or, where no measurement exists yet, a set of cases read on other rows' locks. bound: a one-sided bound; its interval, [0, bound], contains the unit lock by construction. scale: the scale the other rows are read in. open: no measurement selects a lock yet. Family and framed print as compatible, bound and scale as themselves. | | |
| state | A working field of the sheet's data. match: the line has a mathematical read. fill: it has none yet. scale: the line is the scale. It does not judge the measurement. | | |

## 6. Qualifiers

| Word | Statement |
|---|---|
| derived | Computed exactly, in integers or exact fractions, from an object of the list. |
| mapped | A known result or a measurement selects the object, or the object is read as a physical thing. |
| derived and mapped | Both hold. The numbers are computed exactly from the object first; the measurement is lined up last and selects which object. |
| origami-derived | Reached from the root by a trail of folds that replays, or read off a division of the list as it runs. |
| reading | An identification of an integer object with a physical one. Stated, not proved. |
| compared | A published result or a measurement set beside a derived one, last. Nothing measured enters a derivation. |
| measured | A value as its source prints it. |
| input | A measured value, a fitted number or an imported equation that enters a computation. "No inputs" says that none does. |
| imported | An equation brought in from physics, and named as such. |
| model | A statement of the standard model being compared, in that model's own terms. |
| struck | A line the standard cosmological model assumes, shown struck on the Big Bang page. Measured values stand: none is struck. |
| theorem | A statement the Lean kernel checks, in a named file. |
| computed | Recomputed by a check run for the page or for the list. |
| open | No object of the list yet. |
| result at N terms | What a term count, or a search, shows up to its stated bound. Never a statement of absence. |
| upapatti | The record's notion of proof: demonstration by rationale and computation. A claim holds when its check reruns. The Lean kernel is the referee a stranger can trust. |

A page's own key governs its marks; the words above are the ones the pages share.

## 7. Words with more than one sense

| Word | Senses | Sections |
|---|---|---|
| word | 1: a string of the letters J̇ and T. 2: one object's list of letters. 3: an entry kind, a string of characters under a family's address. | 1, 2, 4 |
| letter | J̇ or T; a quotient of a number's division, a natural number; a quotient of a sequence's division, a rational; a character of a word of sense 3. | 1, 2, 4 |
| fold | A step of the list, from listed objects to one more. A sequence's continued fraction is its J-fraction. | 3 |
| crease | The letter J̇, the zero quotient. An order at which a sequence's Hankel determinant is 0 is a Hankel zero. | 1, 3 |
| edge | An end of a band. The edge lock is (1, 1). A word of trace ±2 is parabolic. | 1, 3, 5 |
| depth | 1: of an entry, its fold steps from the root. 2: of a lock, its level on the Stern–Brocot tree. | 4, 5 |
| place | 1: D_b, a digit's place in positional notation. 2: a prime's index among the primes 4k + 1. | 1, 5 |
| open | 1: of a letter, the first quotient a 1σ interval leaves undetermined ("letter open"). 2: a page's mark on a line: no object of the list yet. | 5, 6 |

Where the senses of letter and crease meet: a quotient a is the word TᵃJ̇, and at integer z, α and β the J-fraction's letter of degree 1, x ↦ 1/(z − α − βx), is the word J̇ T^(z−α) D_(−β) (`fold_letter`, in `Sunya.lean`).
