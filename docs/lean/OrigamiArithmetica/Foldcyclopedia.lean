/-
Copyright (c) 2026 Sambuddha Sarkar. All rights reserved.
Author: Sambuddha Sarkar
-/
/-
Origami Arithmetica, the Foldcyclopedia: the folds from the unit, in the order of their steps, then the elements,
Lean 4 theorems; the proof that accompanies the Foldcyclopedia's PDF. It stands on page 1's Śūnya
(OrigamiArithmetica.Sunya), whose Mathlib it imports.
Lean 4.34.1, Mathlib v4.34.1. Check: lake build OrigamiArithmetica.Foldcyclopedia (a project requiring Mathlib v4.34.1).
Output: the axiom report alone; an error is a false statement.
The folds from the unit (namespace Origami): the concise origami, verified (Online Resource 1).
* Paper: "Arithmetic Origami, concise", Sambuddha Sarkar.
* Proved: the 45 steps on their first terms; each continued fraction's leading partial
  quotients, by Euclid's algorithm; determinant identities; general algebraic identities.
* Acknowledgments: sequence identifiers (`A000012`, ...), the On-Line Encyclopedia of Integer
  Sequences (OEIS). `all_*` theorems: the Mathlib4 library.
* Sequences: the list of the first 40 terms over `Rat`; a triangle, its first rows, read by rows.
* `stepNN_*`: step `NN` of the concise paper, on the window its docstring states.
* A J-fraction: its two lists, the alphas, then the betas.
* Docstrings: the kernel checks the statement or the printed list alone; a docstring may add a
  closed form, or the measure whose moments a list is.
* `cf_X`: Euclid's algorithm (`continuedFractionOf`) on the first terms of `X` gives the partial
  quotients `q_X`; `cfLeadingQuotients`: it gives them first, where later coefficients outgrow a line.
* Steps 21 and 23: the factorial's J-fraction coefficients, read off its first terms (`jacobiAlphas`,
  `jacobiBetas`).
* Each computation reads a coefficient only from the terms before it: its result holds for every
  sequence with the same leading terms.
* `decide +kernel`: the kernel evaluates each statement.
* `all_*`: for every index, a closed form; `all_stepNN_*`: the identity behind step `NN`.
* `all_rec1`: two sequences with the same first-order recurrence, equal at 0, are equal at every
  index.
The elements (namespace PeriodicTable): the periodic-table page's proof.
G  Carbon's address: each element a period N and a position j under the shell closures 2, 10, 18, 36, 54, 86, 118,
   read as the noble gases' atomic numbers; its valence read off j. Madelung's rule: the run n + l = N + 1
   corresponds to the partitions of N into parts 1 and 2 (run_is_partitions); in a tie, smaller n is the lower level
   (ionLevel_rises); that the runs fill in n + l order is a reading.
M  The table's places: Madelung's blocks and periods, every block and every period; their states; the closures in
   closed form; the edge Z = 118; each element's place from its last subshell.
O  The one-electron ion's lines and sizes, exact over ℚ.
P  The address map: element Z = 1 … 137 at its address (the closures' address, then N, j); radius N − 1 + j/L and
   turn j/L; valence, the turn's distance from the closures' ray; hyperedges read off N.j; the walk on a hypergraph's
   hyperedges; the stair's lift.
Q  The explored table: a press opens a period; the explored count is the sum of the opened periods'.
R  Gnomon squares: each period a square of side a(N), its subshells nested gnomons, each cell an orbital (two states).
Proofs: `decide +kernel` for closed integer statements; M, O and P's laws for every n, by induction, omega or ring.
Ranges: to Z = 118 (γ₁ ≥ 1/2 at 1/α = 662194096285/4832263787), to Z = 137 (Zα < 1, the point-Coulomb Dirac 1s
bound; the address map's last element), or over an input's terms.

## Workflow Delineation
* Author: Sambuddha Sarkar.
  Computation, Śūnya conjecture and axiom, and the methodology. Definitions, theorems and kernel
  checks formulated, reviewed and validated.
* AI assistance:
  Principal investigation within bounded searches.
  Text, code and computation runs drafted and executed under the author's review.
-/
import OrigamiArithmetica.Sunya

/-! # The folds from the unit -/

namespace Origami

open scoped BigOperators

/-! ### 1. Operations
A sequence is the list of its first terms over `Rat`; `f[n]` is its `n`-th listed term (0-indexed). -/

/-- PSUM: t[n] = f[0] + ... + f[n] -/
def partialSums (f : List Rat) : List Rat := (f.scanl (fun a b => a + b) 0).tail

/-- ADJACENT_SUMS: t[n] = f[n] + f[n-1] -/
def adjacentSums (f : List Rat) : List Rat :=
  (List.range f.length).map fun n => f.getD n 0 + (if n = 0 then 0 else f.getD (n - 1) 0)

/-- times e_k = 1/(1 - x^k): t[n] = f[n] + t[n-k] -/
def timesEulerFactor (k : Nat) (f : List Rat) : List Rat :=
  f.foldl (fun acc v => acc ++ [v + (if k <= acc.length then acc.getD (acc.length - k) 0 else 0)]) []

/-- EULER_FACTORS: times e_k for each k listed -/
def timesEulerFactors (ks : List Nat) (f : List Rat) : List Rat :=
  ks.foldl (fun s k => timesEulerFactor k s) f

/-- EULER: sum t[n] x^n = prod_n (1 - x^n)^(-c(n)), for nonnegative integer c(n) = f[n-1]/n -/
def eulerTransform (f : List Rat) : List Rat :=
  (List.range f.length).foldl
    (fun s i => Nat.iterate (timesEulerFactor (i + 1)) (f.getD i 0 / ((i + 1 : Nat) : Rat)).num.toNat s)
    (1 :: List.replicate (f.length - 1) 0)

/-- LOG_DERIVATIVE: sum t[n-1] x^n = x F'(x)/F(x), F = sum f[n] x^n, f[0] = 1 -/
def logDerivative (p : List Rat) : List Rat :=
  (List.range (p.length - 1)).foldl
    (fun s i =>
      s ++ [((i + 1 : Nat) : Rat) * p.getD (i + 1) 0
        - ((List.range i).map (fun j => s.getD j 0 * p.getD (i - j) 0)).sum]) []

/-- the Moebius function on 1..n, by sum_(d|m) mu(d) = [m = 1] -/
def moebiusMu (n : Nat) : List Rat :=
  (List.range n).foldl
    (fun s i =>
      s ++ [if i = 0 then 1 else
        -((((List.range i).filter (fun j => (i + 1) % (j + 1) = 0)).map (fun j => s.getD j 0)).sum)]) []

/-- MOBIUS: t[n-1] = sum_(d|n) mu(n/d) f[d-1] -/
def moebiusInversion (f : List Rat) : List Rat :=
  let mu := moebiusMu f.length
  (List.range f.length).map fun i =>
    (((List.range (i + 1)).filter (fun j => (i + 1) % (j + 1) = 0)).map
      (fun j => mu.getD ((i + 1) / (j + 1) - 1) 0 * f.getD j 0)).sum

/-- polynomials, low-first -/
def polyAdd (a b : List Rat) : List Rat :=
  (List.range (max a.length b.length)).map fun i => a.getD i 0 + b.getD i 0

def polyMul (a b : List Rat) : List Rat :=
  if a.isEmpty || b.isEmpty then [] else
  (List.range (a.length + b.length - 1)).map fun n =>
    ((List.range (n + 1)).map fun i => a.getD i 0 * b.getD (n - i) 0).sum

/-- the first n rows of C(r, k) -/
def pascal (n : Nat) : List (List Rat) :=
  (List.range n).foldl (fun acc _ =>
    acc ++ [match acc.getLast? with | none => [1] | some r => polyAdd (0 :: r) r]) []

/-- BINOMIAL: t[n] = sum_k C(n,k) f[k] -/
def binomialTransform (f : List Rat) : List Rat :=
  let P := pascal f.length
  (List.range f.length).map fun n =>
    ((List.range (n + 1)).map fun k => (P.getD n []).getD k 0 * f.getD k 0).sum

/-- BINOMIALi: t[n] = sum_k (-1)^(n-k) C(n,k) f[k] -/
def binomialInverse (f : List Rat) : List Rat :=
  let P := pascal f.length
  (List.range f.length).map fun n =>
    ((List.range (n + 1)).map fun k =>
      (if (n - k) % 2 = 0 then 1 else -1) * (P.getD n []).getD k 0 * f.getD k 0).sum

/-- DIV_TWO_POW: t[n] = f[n]/2^n -/
def divideByTwoPow (f : List Rat) : List Rat :=
  (List.range f.length).map fun n => f.getD n 0 / ((2 ^ n : Nat) : Rat)

/-- DIV_N_PLUS_ONE: t[n] = f[n]/(n+1) -/
def divideByNPlusOne (f : List Rat) : List Rat :=
  (List.range f.length).map fun n => f.getD n 0 / ((n + 1 : Nat) : Rat)

/-- PARTIAL_PRODUCTS: t[n] = f[0] f[1] ... f[n-1] -/
def partialProducts (f : List Rat) : List Rat := (f.scanl (fun a b => a * b) 1).take f.length

/-- row m of a triangle read by rows starts at m(m+1)/2 -/
def row0 (m : Nat) : Nat := m * (m + 1) / 2

/-- ANTIDIAGONAL_SUMS, the line 2k + m = n: t[n] = sum_k T(n-k, k) -/
def antidiagonalSums (T : List Rat) (n : Nat) : List Rat :=
  (List.range n).map fun m => ((List.range (m / 2 + 1)).map fun k => T.getD (row0 (m - k) + k) 0).sum

/-- CENTRAL_DIAGONAL, the line k = m: t[n] = T(2n, n) -/
def centralDiagonal (T : List Rat) (n : Nat) : List Rat :=
  (List.range n).map fun m => T.getD (row0 (2 * m) + m) 0

/-- the first n terms of the J-fraction 1/(1 - al[0] x - be[0] x^2/(1 - al[1] x - be[1] x^2/(1 - ...))):
    weighted Motzkin paths -/
def jacobiMoments (al be : List Rat) (n : Nat) : List Rat :=
  ((List.range (n - 1)).foldl
    (fun (st : Prod (List Rat) (List Rat)) i =>
      let m := i + 1
      let T := st.1
      let T' := (List.range (min m (n - 1 - m) + 1)).map fun h =>
        (if 1 <= h && h <= T.length then T.getD (h - 1) 0 else 0)
        + (if h < T.length then al.getD h 0 * T.getD h 0 else 0)
        + (if h + 1 < T.length then be.getD h 0 * T.getD (h + 1) 0 else 0)
      (T', st.2 ++ [T'.getD 0 0])) ([1], [1])).2

/-- SFRACTION: the first n terms of 1/(1 - c[0] x/(1 - c[1] x/(1 - ...))), by its contraction
    alpha_0 = c[0], alpha_k = c[2k-1] + c[2k], beta_k = c[2k-2] c[2k-1]
    (the beta list's entry k is beta_(k+1) = c[2k] c[2k+1]) -/
def sfractionMoments (c : List Rat) (n : Nat) : List Rat :=
  jacobiMoments
    ((List.range n).map fun k => if k = 0 then c.getD 0 0 else c.getD (2 * k - 1) 0 + c.getD (2 * k) 0)
    ((List.range n).map fun k => c.getD (2 * k) 0 * c.getD (2 * k + 1) 0) n

/-- det(z - J_i), i = 0..R, low-first: D_(i+1) = (z - alpha_i) D_i - beta_i D_(i-1) -/
def charpolyRows (al be : List Rat) (R : Nat) : List (List Rat) :=
  ((List.range R).foldl
    (fun (st : Prod (List (List Rat)) (Prod (List Rat) (List Rat))) i =>
      let next := polyAdd (polyAdd (0 :: st.2.2) (st.2.2.map fun c => -(al.getD i 0) * c))
        (st.2.1.map fun c => -(be.getD (i - 1) 0) * c)
      (st.1 ++ [next], st.2.2, next)) ([[1]], [], [1])).1

/-- CHARPOLY: row i of the triangle T is lc(row i) det(z - J_i), i = 0..R -/
def charpolyRowsAre (al be T : List Rat) (R : Nat) : Bool :=
  let D := charpolyRows al be R
  (List.range (R + 1)).all fun i =>
    let row := (List.range (i + 1)).map fun j => T.getD (row0 i + j) 0
    row == (D.getD i []).map fun c => row.getD i 0 * c

/-- lambda_1 = 1, lambda_(i+1) = -1/(beta_i lambda_i) -/
def leadingScalars (be : List Rat) (n : Nat) : List Rat :=
  (List.range (n - 1)).foldl (fun acc i => acc ++ [-1 / (be.getD i 0 * acc.getD i 0)]) [1]

/-- POLE_AT_TWO, alpha = 1 so q_i(2) = lambda_i: t[m] = (-1)^m q_(m+1)(2) B_m(2)^2,
    B_m = q_m(2) B_(m-1) + B_(m-2) -/
def poleAtTwo (be : List Rat) (n : Nat) : List Rat :=
  let lam := leadingScalars be n
  ((List.range n).foldl
    (fun (st : Prod (List Rat) (Prod Rat Rat)) m =>
      let q := lam.getD m 0
      (st.1 ++ [(if m % 2 = 0 then 1 else -1) * q * st.2.1 * st.2.1], q * st.2.1 + st.2.2, st.2.1))
    ([], 1, 0)).1

/-- the J-fraction's first n terms with coefficients in Q[t], each a polynomial low-first: the
    weighted Motzkin paths of `jacobiMoments`, over polynomials -/
def jacobiMomentsPoly (al be : List (List Rat)) (n : Nat) : List (List Rat) :=
  ((List.range (n - 1)).foldl
    (fun (st : Prod (List (List Rat)) (List (List Rat))) i =>
      let m := i + 1
      let T := st.1
      let T' := (List.range (min m (n - 1 - m) + 1)).map fun h =>
        polyAdd (polyAdd (if 1 <= h && h <= T.length then T.getD (h - 1) [] else [])
            (if h < T.length then polyMul (al.getD h []) (T.getD h []) else []))
          (if h + 1 < T.length then polyMul (be.getD h []) (T.getD (h + 1) []) else [])
      (T', st.2 ++ [T'.getD 0 []])) ([[1]], [[1]])).2

/-- ALTERNATE_BETA: alpha = 0 and the betas be with every other one times t (t be[0], be[1], t be[2],
    ...): row i is the coefficients of t^1 .. t^(i+1) in the moment m_(2i+2), i < R, read by rows -/
def alternateBetaRows (be : List Rat) (R : Nat) : List Rat :=
  let m := jacobiMomentsPoly []
    ((List.range R).map fun k => if k % 2 = 0 then [0, be.getD k 0] else [be.getD k 0]) (2 * R + 2)
  (List.range R).foldl (fun acc i =>
    acc ++ (List.range (i + 1)).map fun j => (m.getD (2 * i + 2) []).getD (j + 1) 0) []

/-- ROW_SUMS: t[i] is the sum of row i of the triangle T, i < R -/
def rowSums (T : List Rat) (R : Nat) : List Rat :=
  (List.range R).map fun i => ((List.range (i + 1)).map fun j => T.getD (row0 i + j) 0).sum

/-- DRESSED_LOOPS: c with each bare loop weighted t - 1, the binomials read off Pascal's rows P:
    row i is the coefficients of t^1 .. t^(i+1) in sum_k C(i+1+k, 2k) (t - 1)^(i+1-k) c_k,
    i < R, read by rows -/
def dressedLoops (P c : List Rat) (R : Nat) : List Rat :=
  (List.range R).foldl (fun acc i =>
    acc ++ (List.range (i + 1)).map fun j =>
      ((List.range (i + 2)).map fun k =>
        if j + 1 + k <= i + 1 then
          P.getD (row0 (i + 1 + k) + 2 * k) 0 * P.getD (row0 (i + 1 - k) + (j + 1)) 0 *
            (-1) ^ (i + 1 - k - (j + 1)) * c.getD k 0
        else 0).sum) []

/-- A_i, B_i of [0; q_1, ..., q_i]: A = q A' + A'', B = q B' + B'' -/
def convergents (qs : List (List Rat)) : Prod (List Rat) (List Rat) :=
  (qs.foldl (fun (st : Prod (Prod (List Rat) (List Rat)) (Prod (List Rat) (List Rat))) q =>
    ((polyAdd (polyMul q st.1.1) st.2.1, polyAdd (polyMul q st.1.2) st.2.2), st.1))
    (([0], [1]), ([1], [0]))).1

/-- the inverse of the power series u (u_0 /= 0), to the length u is known:
    v_0 = 1/u_0, v_n = -(u_1 v_(n-1) + ... + u_n v_0)/u_0 -/
def seriesInverse (u : List Rat) : List Rat :=
  (List.range u.length).foldl (fun v n =>
    v ++ [if n = 0 then 1 / u.headD 0
          else -((List.range n).foldl (fun acc j => acc + u.getD (n - j) 0 * v.getD j 0) 0)
            / u.headD 0]) []

/-- Euclid's algorithm on F = sum s_n z^(-n-1) = [0; q_1, q_2, ...], reading only the terms given
    * With w = 1/z the remainder is w r(w), r known to its length; its first nonzero coefficient, at
      index e, gives the next quotient's degree e + 1, read off 1/(w r) = z^(e+1) v(w), v = 1/r'
      (r' = r from index e): q has coefficient v_(e+1-m) at z^m; the next remainder is v from index
      e + 2.
    * Each coefficient is computed from the terms before it: every sequence that begins with the
      given terms has these quotients.
    * It stops at the first quotient they do not decide: fewer than e + 2 coefficients of r' known,
      or no nonzero one. -/
def continuedFractionOf (s : List Rat) : List (List Rat) :=
  ((List.range s.length).foldl (fun (st : Prod (List (List Rat)) (Prod (List Rat) Bool)) _ =>
    if st.2.2 then st else
    match st.2.1.findIdx? (fun x => x != 0) with
    | none => (st.1, st.2.1, true)
    | some e =>
      let u := st.2.1.drop e
      if u.length < e + 2 then (st.1, st.2.1, true) else
      let v := seriesInverse u
      (st.1 ++ [(List.range (e + 2)).map fun m => v.getD (e + 1 - m) 0], v.drop (e + 2), false))
    ([], s, false)).1

/-- the quotients Euclid's algorithm reads off the terms s are qs -/
def cfQuotientsAre (s : List Rat) (qs : List (List Rat)) : Bool := continuedFractionOf s == qs

/-- the first quotients Euclid's algorithm reads off the terms s are qs -/
def cfLeadingQuotients (s : List Rat) (qs : List (List Rat)) : Bool :=
  (continuedFractionOf s).take qs.length == qs

/-- the J-fraction coefficients the terms decide: sum m_n z^(-n-1) = m_0/(z - alpha_0 - beta_1 G),
    G = z^(-1) + ...; with v = 1/m as a power series, alpha_0 = -v_1/v_0, beta_1 = -v_2/v_0, and G's
    terms are v_(n+2)/v_2
    * Each depth reads two more terms; it stops where a coefficient needs a term not given, or at a
      beta of 0. -/
def jacobiCoefficients (m : List Rat) : Prod (List Rat) (List Rat) :=
  let r := (List.range m.length).foldl
    (fun (st : Prod (List Rat) (Prod (List Rat) (Prod (List Rat) Bool))) _ =>
    if st.2.2.2 || st.2.2.1.length < 2 then (st.1, st.2.1, st.2.2.1, true) else
    let g := st.2.2.1
    let v := seriesInverse g
    let al := st.1 ++ [-(v.getD 1 0) / v.headD 0]
    if g.length < 3 || v.getD 2 0 == 0 then (al, st.2.1, g, true) else
    (al, st.2.1 ++ [-(v.getD 2 0) / v.headD 0], (v.drop 2).map (fun x => x / v.getD 2 0), false))
    ([], [], m, false)
  (r.1, r.2.1)

/-- the alphas the terms decide, alpha_0 first -/
def jacobiAlphas (m : List Rat) : List Rat := (jacobiCoefficients m).1

/-- the betas the terms decide, beta_1 first -/
def jacobiBetas (m : List Rat) : List Rat := (jacobiCoefficients m).2

/-- the relation b_i a_i a_(i+1) == s_i, i < n (0-indexed) -/
def betaRelation (b a s : List Rat) (n : Nat) : Bool :=
  (List.range n).all fun i => b.getD i 0 * (a.getD i 0 * a.getD (i + 1) 0) == s.getD i 0

/-! ### 2. Objects
The first 40 terms of each sequence, a triangle by rows; the partial quotients each prints,
low degree first. -/

def A000007 : List Rat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def A000012 : List Rat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def A000027 : List Rat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
def A000041 : List Rat := [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297,
    385, 490, 627, 792, 1002, 1255, 1575, 1958, 2436, 3010, 3718, 4565, 5604, 6842, 8349, 10143,
    12310, 14883, 17977, 21637, 26015, 31185]
def A000203 : List Rat := [1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24, 31, 18, 39, 20, 42,
    32, 36, 24, 60, 31, 42, 40, 56, 30, 72, 32, 63, 48, 54, 48, 91, 38, 60, 56, 90]
def A000217_1 : List Rat := [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153,
    171, 190, 210, 231, 253, 276, 300, 325, 351, 378, 406, 435, 465, 496, 528, 561, 595, 630, 666,
    703, 741, 780, 820]
def A000292_1 : List Rat := [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 560, 680, 816,
    969, 1140, 1330, 1540, 1771, 2024, 2300, 2600, 2925, 3276, 3654, 4060, 4495, 4960, 5456, 5984,
    6545, 7140, 7770, 8436, 9139, 9880, 10660, 11480]
def A000332_4 : List Rat := [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1365, 1820, 2380,
    3060, 3876, 4845, 5985, 7315, 8855, 10626, 12650, 14950, 17550, 20475, 23751, 27405, 31465,
    35960, 40920, 46376, 52360, 58905, 66045, 73815, 82251, 91390, 101270, 111930, 123410]
def A008619 : List Rat := [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12,
    12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20]
def A001399 : List Rat := [1, 1, 2, 3, 4, 5, 7, 8, 10, 12, 14, 16, 19, 21, 24, 27, 30, 33, 37, 40,
    44, 48, 52, 56, 61, 65, 70, 75, 80, 85, 91, 96, 102, 108, 114, 120, 127, 133, 140, 147]
def A008638 : List Rat := [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 41, 54, 73, 94, 123, 157, 201, 252,
    318, 393, 488, 598, 732, 887, 1076, 1291, 1549, 1845, 2194, 2592, 3060, 3589, 4206, 4904, 5708,
    6615, 7657, 8824, 10156, 11648]
def oddM : List Rat := [1, 0, 3, 0, 5, 0, 7, 0, 9, 0, 11, 0, 13, 0, 15, 0, 17, 0, 19, 0, 21, 0, 23,
    0, 25, 0, 27, 0, 29, 0, 31, 0, 33, 0, 35, 0, 37, 0, 39, 0]
def A000009 : List Rat := [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32, 38, 46, 54, 64,
    76, 89, 104, 122, 142, 165, 192, 222, 256, 296, 340, 390, 448, 512, 585, 668, 760, 864, 982]
def A000593 : List Rat := [1, 1, 4, 1, 6, 4, 8, 1, 13, 6, 12, 4, 14, 8, 24, 1, 18, 13, 20, 6, 32,
    12, 24, 4, 31, 14, 40, 8, 30, 24, 32, 1, 48, 18, 48, 13, 38, 20, 56, 6]
def A000079 : List Rat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384,
    32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432,
    67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592,
    17179869184, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888]
def A007318 : List Rat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6, 4, 1, 1, 5, 10, 10, 5, 1, 1, 6,
    15, 20, 15, 6, 1, 1, 7, 21, 35, 35, 21, 7, 1, 1, 8, 28, 56, 70, 56, 28, 8, 1, 1, 9, 36, 84, 126,
    126, 84, 36, 9, 1, 1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1, 1, 11, 55, 165, 330, 462, 462,
    330, 165, 55, 11, 1, 1, 12, 66, 220, 495, 792, 924, 792, 495, 220, 66, 12, 1, 1, 13, 78, 286,
    715, 1287, 1716, 1716, 1287, 715, 286, 78, 13, 1, 1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003,
    2002, 1001, 364, 91, 14, 1, 1, 15, 105, 455, 1365, 3003, 5005, 6435, 6435, 5005, 3003, 1365,
    455, 105, 15, 1, 1, 16, 120, 560, 1820, 4368, 8008, 11440, 12870, 11440, 8008, 4368, 1820, 560,
    120, 16, 1, 1, 17, 136, 680, 2380, 6188, 12376, 19448, 24310, 24310, 19448, 12376, 6188, 2380,
    680, 136, 17, 1, 1, 18, 153, 816, 3060, 8568, 18564, 31824, 43758, 48620, 43758, 31824, 18564,
    8568, 3060, 816, 153, 18, 1, 1, 19, 171, 969, 3876, 11628, 27132, 50388, 75582, 92378, 92378,
    75582, 50388, 27132, 11628, 3876, 969, 171, 19, 1, 1, 20, 190, 1140, 4845, 15504, 38760, 77520,
    125970, 167960, 184756, 167960, 125970, 77520, 38760, 15504, 4845, 1140, 190, 20, 1, 1, 21, 210,
    1330, 5985, 20349, 54264, 116280, 203490, 293930, 352716, 352716, 293930, 203490, 116280, 54264,
    20349, 5985, 1330, 210, 21, 1, 1, 22, 231, 1540, 7315, 26334, 74613, 170544, 319770, 497420,
    646646, 705432, 646646, 497420, 319770, 170544, 74613, 26334, 7315, 1540, 231, 22, 1, 1, 23,
    253, 1771, 8855, 33649, 100947, 245157, 490314, 817190, 1144066, 1352078, 1352078, 1144066,
    817190, 490314, 245157, 100947, 33649, 8855, 1771, 253, 23, 1, 1, 24, 276, 2024, 10626, 42504,
    134596, 346104, 735471, 1307504, 1961256, 2496144, 2704156, 2496144, 1961256, 1307504, 735471,
    346104, 134596, 42504, 10626, 2024, 276, 24, 1, 1, 25, 300, 2300, 12650, 53130, 177100, 480700,
    1081575, 2042975, 3268760, 4457400, 5200300, 5200300, 4457400, 3268760, 2042975, 1081575,
    480700, 177100, 53130, 12650, 2300, 300, 25, 1, 1, 26, 325, 2600, 14950, 65780, 230230, 657800,
    1562275, 3124550, 5311735, 7726160, 9657700, 10400600, 9657700, 7726160, 5311735, 3124550,
    1562275, 657800, 230230, 65780, 14950, 2600, 325, 26, 1, 1, 27, 351, 2925, 17550, 80730, 296010,
    888030, 2220075, 4686825, 8436285, 13037895, 17383860, 20058300, 20058300, 17383860, 13037895,
    8436285, 4686825, 2220075, 888030, 296010, 80730, 17550, 2925, 351, 27, 1, 1, 28, 378, 3276,
    20475, 98280, 376740, 1184040, 3108105, 6906900, 13123110, 21474180, 30421755, 37442160,
    40116600, 37442160, 30421755, 21474180, 13123110, 6906900, 3108105, 1184040, 376740, 98280,
    20475, 3276, 378, 28, 1, 1, 29, 406, 3654, 23751, 118755, 475020, 1560780, 4292145, 10015005,
    20030010, 34597290, 51895935, 67863915, 77558760, 77558760, 67863915, 51895935, 34597290,
    20030010, 10015005, 4292145, 1560780, 475020, 118755, 23751, 3654, 406, 29, 1, 1, 30, 435, 4060,
    27405, 142506, 593775, 2035800, 5852925, 14307150, 30045015, 54627300, 86493225, 119759850,
    145422675, 155117520, 145422675, 119759850, 86493225, 54627300, 30045015, 14307150, 5852925,
    2035800, 593775, 142506, 27405, 4060, 435, 30, 1, 1, 31, 465, 4495, 31465, 169911, 736281,
    2629575, 7888725, 20160075, 44352165, 84672315, 141120525, 206253075, 265182525, 300540195,
    300540195, 265182525, 206253075, 141120525, 84672315, 44352165, 20160075, 7888725, 2629575,
    736281, 169911, 31465, 4495, 465, 31, 1, 1, 32, 496, 4960, 35960, 201376, 906192, 3365856,
    10518300, 28048800, 64512240, 129024480, 225792840, 347373600, 471435600, 565722720, 601080390,
    565722720, 471435600, 347373600, 225792840, 129024480, 64512240, 28048800, 10518300, 3365856,
    906192, 201376, 35960, 4960, 496, 32, 1, 1, 33, 528, 5456, 40920, 237336, 1107568, 4272048,
    13884156, 38567100, 92561040, 193536720, 354817320, 573166440, 818809200, 1037158320,
    1166803110, 1166803110, 1037158320, 818809200, 573166440, 354817320, 193536720, 92561040,
    38567100, 13884156, 4272048, 1107568, 237336, 40920, 5456, 528, 33, 1, 1, 34, 561, 5984, 46376,
    278256, 1344904, 5379616, 18156204, 52451256, 131128140, 286097760, 548354040, 927983760,
    1391975640, 1855967520, 2203961430, 2333606220, 2203961430, 1855967520, 1391975640, 927983760,
    548354040, 286097760, 131128140, 52451256, 18156204, 5379616, 1344904, 278256, 46376, 5984, 561,
    34, 1, 1, 35, 595, 6545, 52360, 324632, 1623160, 6724520, 23535820, 70607460, 183579396,
    417225900, 834451800, 1476337800, 2319959400, 3247943160, 4059928950, 4537567650, 4537567650,
    4059928950, 3247943160, 2319959400, 1476337800, 834451800, 417225900, 183579396, 70607460,
    23535820, 6724520, 1623160, 324632, 52360, 6545, 595, 35, 1, 1, 36, 630, 7140, 58905, 376992,
    1947792, 8347680, 30260340, 94143280, 254186856, 600805296, 1251677700, 2310789600, 3796297200,
    5567902560, 7307872110, 8597496600, 9075135300, 8597496600, 7307872110, 5567902560, 3796297200,
    2310789600, 1251677700, 600805296, 254186856, 94143280, 30260340, 8347680, 1947792, 376992,
    58905, 7140, 630, 36, 1, 1, 37, 666, 7770, 66045, 435897, 2324784, 10295472, 38608020,
    124403620, 348330136, 854992152, 1852482996, 3562467300, 6107086800, 9364199760, 12875774670,
    15905368710, 17672631900, 17672631900, 15905368710, 12875774670, 9364199760, 6107086800,
    3562467300, 1852482996, 854992152, 348330136, 124403620, 38608020, 10295472, 2324784, 435897,
    66045, 7770, 666, 37, 1, 1, 38, 703, 8436, 73815, 501942, 2760681, 12620256, 48903492,
    163011640, 472733756, 1203322288, 2707475148, 5414950296, 9669554100, 15471286560, 22239974430,
    28781143380, 33578000610, 35345263800, 33578000610, 28781143380, 22239974430, 15471286560,
    9669554100, 5414950296, 2707475148, 1203322288, 472733756, 163011640, 48903492, 12620256,
    2760681, 501942, 73815, 8436, 703, 38, 1, 1, 39, 741, 9139, 82251, 575757, 3262623, 15380937,
    61523748, 211915132, 635745396, 1676056044, 3910797436, 8122425444, 15084504396, 25140840660,
    37711260990, 51021117810, 62359143990, 68923264410, 68923264410, 62359143990, 51021117810,
    37711260990, 25140840660, 15084504396, 8122425444, 3910797436, 1676056044, 635745396, 211915132,
    61523748, 15380937, 3262623, 575757, 82251, 9139, 741, 39, 1]
def A000045_1 : List Rat := [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597,
    2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811, 514229, 832040,
    1346269, 2178309, 3524578, 5702887, 9227465, 14930352, 24157817, 39088169, 63245986, 102334155]
def A000984 : List Rat := [1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756, 705432, 2704156,
    10400600, 40116600, 155117520, 601080390, 2333606220, 9075135300, 35345263800, 137846528820,
    538257874440, 2104098963720, 8233430727600, 32247603683100, 126410606437752, 495918532948104,
    1946939425648112, 7648690600760440, 30067266499541040, 118264581564861424, 465428353255261088,
    1832624140942590534, 7219428434016265740, 28453041475240576740, 112186277816662845432,
    442512540276836779204, 1746130564335626209832, 6892620648693261354600, 27217014869199032015600]
def A000108 : List Rat := [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900,
    2674440, 9694845, 35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452, 18367353072152, 69533550916004,
    263747951750360, 1002242216651368, 3814986502092304, 14544636039226909, 55534064877048198,
    212336130412243110, 812944042149730764, 3116285494907301262, 11959798385860453492,
    45950804324621742364, 176733862787006701400, 680425371729975800390]
def A000142 : List Rat := [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800,
    479001600, 6227020800, 87178291200, 1307674368000, 20922789888000, 355687428096000,
    6402373705728000, 121645100408832000, 2432902008176640000, 51090942171709440000,
    1124000727777607680000, 25852016738884976640000, 620448401733239439360000,
    15511210043330985984000000, 403291461126605635584000000, 10888869450418352160768000000,
    304888344611713860501504000000, 8841761993739701954543616000000,
    265252859812191058636308480000000, 8222838654177922817725562880000000,
    263130836933693530167218012160000000, 8683317618811886495518194401280000000,
    295232799039604140847618609643520000000, 10333147966386144929666651337523200000000,
    371993326789901217467999448150835200000000, 13763753091226345046315979581580902400000000,
    523022617466601111760007224100074291200000000, 20397882081197443358640281739902897356800000000]
def A005408 : List Rat := [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37,
    39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79]
def A001147 : List Rat := [1, 1, 3, 15, 105, 945, 10395, 135135, 2027025, 34459425, 654729075,
    13749310575, 316234143225, 7905853580625, 213458046676875, 6190283353629375, 191898783962510625,
    6332659870762850625, 221643095476699771875, 8200794532637891559375, 319830986772877770815625,
    13113070457687988603440625, 563862029680583509947946875, 25373791335626257947657609375,
    1192568192774434123539907640625, 58435841445947272053455474390625,
    2980227913743310874726229193921875, 157952079428395476360490147277859375,
    8687364368561751199826958100282265625, 495179769008019818390136611716089140625,
    29215606371473169285018060091249259296875, 1782151988659863326386101665566204817109375,
    112275575285571389562324404930670903477890625, 7297912393562140321551086320493608726062890625,
    488960130368663401543922783473071784646213671875,
    33738248995437774706530672059641953140588743359375,
    2395415678676082004163677716234578672981800778515625,
    174865344543353986303948473285124243127671456831640625,
    13114900840751548972796135496384318234575359262373046875,
    1009847364737869270905302433221592504062302663202724609375]
def A000290_1 : List Rat := [1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256,
    289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1024, 1089, 1156,
    1225, 1296, 1369, 1444, 1521, 1600]
def c_a : List Rat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def c_t : List Rat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
def c_tt : List Rat := [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12,
    12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20]
def A021009 : List Rat := [1, 1, -1, 2, -4, 1, 6, -18, 9, -1, 24, -96, 72, -16, 1, 120, -600, 600,
    -200, 25, -1, 720, -4320, 5400, -2400, 450, -36, 1, 5040, -35280, 52920, -29400, 7350, -882, 49,
    -1, 40320, -322560, 564480, -376320, 117600, -18816, 1568, -64, 1]
/-- nu_n = 2^n/(n + 1) = (1/2) integral_0^2 t^n dt: the moments of the density 1/2 on [0, 2], the unit
    mass at 2 (A000079) spread evenly over [0, 2] -/
def nu : List Rat := [1, 1, 4/3, 2, 16/5, 16/3, 64/7, 16, 256/9, 256/5, 1024/11, 512/3, 4096/13,
    4096/7, 16384/15, 2048, 65536/17, 65536/9, 262144/19, 131072/5, 1048576/21, 1048576/11,
    4194304/23, 1048576/3, 16777216/25, 16777216/13, 67108864/27, 33554432/7, 268435456/29,
    268435456/15, 1073741824/31, 67108864, 4294967296/33, 4294967296/17, 17179869184/35,
    8589934592/9, 68719476736/37, 68719476736/19, 274877906944/39, 68719476736/5]
/-- the S-fraction coefficients of nu: c_0 = 1, c_(2m-1) = m/(2m + 1), c_(2m) = (m + 1)/(2m + 1);
    contracted, alpha_k = 1 and beta_l = c_(2l-2) c_(2l-1) = l^2/(4l^2 - 1) -/
def c_nu : List Rat := [1, 1/3, 2/3, 2/5, 3/5, 3/7, 4/7, 4/9, 5/9, 5/11, 6/11, 6/13, 7/13, 7/15,
    8/15, 8/17, 9/17, 9/19, 10/19, 10/21, 11/21, 11/23, 12/23, 12/25, 13/25, 13/27, 14/27, 14/29,
    15/29, 15/31, 16/31, 16/33, 17/33, 17/35, 18/35, 18/37, 19/37, 19/39, 20/39, 20/41]
/-- nu0 = B^-1 nu, nu0_n = (1 + (-1)^n)/(2(n + 1)) = (1/2) integral_(-1)^1 x^n dx: the uniform measure
    on [-1, 1], the density of nu moved by -1; also the mean of x^n over the unit sphere S^2, x one
    coordinate -/
def nu0 : List Rat := [1, 0, 1/3, 0, 1/5, 0, 1/7, 0, 1/9, 0, 1/11, 0, 1/13, 0, 1/15, 0, 1/17, 0,
    1/19, 0, 1/21, 0, 1/23, 0, 1/25, 0, 1/27, 0, 1/29, 0, 1/31, 0, 1/33, 0, 1/35, 0, 1/37, 0, 1/39,
    0]
def A100258 : List Rat := [1, 0, 1, -1, 0, 3, 0, -3, 0, 5, 3, 0, -30, 0, 35, 0, 15, 0, -70, 0, 63,
    -5, 0, 105, 0, -315, 0, 231, 0, -35, 0, 315, 0, -693, 0, 429, 35, 0, -1260, 0, 6930, 0, -12012,
    0, 6435]
def A000108_1 : List Rat := [1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900,
    2674440, 9694845, 35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452, 18367353072152, 69533550916004,
    263747951750360, 1002242216651368, 3814986502092304, 14544636039226909, 55534064877048198,
    212336130412243110, 812944042149730764, 3116285494907301262, 11959798385860453492,
    45950804324621742364, 176733862787006701400, 680425371729975800390, 2622127042276492108820]
def A001006 : List Rat := [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798, 15511, 41835, 113634,
    310572, 853467, 2356779, 6536382, 18199284, 50852019, 142547559, 400763223, 1129760415,
    3192727797, 9043402501, 25669818476, 73007772802, 208023278209, 593742784829, 1697385471211,
    4859761676391, 13933569346707, 40002464776083, 114988706524270, 330931069469828,
    953467954114363, 2750016719520991, 7939655757745265, 22944749046030949]
def A126120 : List Rat := [1, 0, 1, 0, 2, 0, 5, 0, 14, 0, 42, 0, 132, 0, 429, 0, 1430, 0, 4862, 0,
    16796, 0, 58786, 0, 208012, 0, 742900, 0, 2674440, 0, 9694845, 0, 35357670, 0, 129644790, 0,
    477638700, 0, 1767263190, 0]
def omegaS : List Rat := [1, 0, 1/4, 0, 1/8, 0, 5/64, 0, 7/128, 0, 21/512, 0, 33/1024, 0, 429/16384,
    0, 715/32768, 0, 2431/131072, 0, 4199/262144, 0, 29393/2097152, 0, 52003/4194304, 0,
    185725/16777216, 0, 334305/33554432, 0, 9694845/1073741824, 0, 17678835/2147483648, 0,
    64822395/8589934592, 0, 119409675/17179869184, 0, 883631595/137438953472, 0]
def A040000 : List Rat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def A000330_1 : List Rat := [1, 5, 14, 30, 55, 91, 140, 204, 285, 385, 506, 650, 819, 1015, 1240,
    1496, 1785, 2109, 2470, 2870, 3311, 3795, 4324, 4900, 5525, 6201, 6930, 7714, 8555, 9455, 10416,
    11440, 12529, 13685, 14910, 16206, 17575, 19019, 20540, 22140]
def G1 : List Rat := [1, 1, 3/2, 5/2, 35/8, 63/8, 231/16, 429/16, 6435/128, 12155/128, 46189/256,
    88179/256, 676039/1024, 1300075/1024, 5014575/2048, 9694845/2048, 300540195/32768,
    583401555/32768, 2268783825/65536, 4418157975/65536, 34461632205/262144, 67282234305/262144,
    263012370465/524288, 514589420475/524288, 8061900920775/4194304, 15801325804719/4194304,
    61989816618513/8388608, 121683714103007/8388608, 956086325095055/33554432,
    1879204156221315/33554432, 7391536347803839/67108864, 14544636039226909/67108864,
    916312070471295267/2147483648, 1804857108504066435/2147483648, 7113260368810144185/4294967296,
    14023284727082855679/4294967296, 110628135069209194801/17179869184,
    218266320541953276229/17179869184, 861577581086657669325/34359738368,
    1701063429324939500975/34359738368]
def G3 : List Rat := [1, 1, 5/4, 7/4, 21/8, 33/8, 429/64, 715/64, 2431/128, 4199/128, 29393/512,
    52003/512, 185725/1024, 334305/1024, 9694845/16384, 17678835/16384, 64822395/32768,
    119409675/32768, 883631595/131072, 1641030105/131072, 6116566755/262144, 11435320455/262144,
    171529806825/2097152, 322476036831/2097152, 1215486600363/4194304, 2295919134019/4194304,
    17383387729001/16777216, 32968493968795/16777216, 125280277081421/33554432,
    238436656380769/33554432, 14544636039226909/1073741824, 27767032438524099/1073741824,
    106168065206121555/2147483648, 203236010537432691/2147483648, 1558142747453650631/8589934592,
    2989949596465113373/8589934592, 11487701081155435591/17179869184,
    22091732848375837675/17179869184, 340212685864987900195/137438953472,
    655531760569123027205/137438953472]
def A001263 : List Rat := [1, 1, 1, 1, 3, 1, 1, 6, 6, 1, 1, 10, 20, 10, 1, 1, 15, 50, 50, 15, 1, 1,
    21, 105, 175, 105, 21, 1, 1, 28, 196, 490, 490, 196, 28, 1, 1, 36, 336, 1176, 1764, 1176, 336,
    36, 1, 1, 45, 540, 2520, 5292, 5292, 2520, 540, 45, 1, 1, 55, 825, 4950, 13860, 19404, 13860,
    4950, 825, 55, 1, 1, 66, 1210, 9075, 32670, 60984, 60984, 32670, 9075, 1210, 66, 1, 1, 78, 1716,
    15730, 70785, 169884, 226512, 169884, 70785, 15730, 1716, 78, 1, 1, 91, 2366, 26026, 143143,
    429429, 736164, 736164, 429429, 143143, 26026, 2366, 91, 1, 1, 105, 3185, 41405, 273273,
    1002001, 2147145, 2760615, 2147145, 1002001, 273273, 41405, 3185, 105, 1, 1, 120, 4200, 63700,
    496860, 2186184, 5725720, 9202050, 9202050, 5725720, 2186184, 496860, 63700, 4200, 120, 1, 1,
    136, 5440, 95200, 866320, 4504864, 14158144, 27810640, 34763300, 27810640, 14158144, 4504864,
    866320, 95200, 5440, 136, 1, 1, 153, 6936, 138720, 1456560, 8836464, 32821152, 77364144,
    118195220, 118195220, 77364144, 32821152, 8836464, 1456560, 138720, 6936, 153, 1, 1, 171, 8721,
    197676, 2372112, 16604784, 71954064, 200443464, 367479684, 449141836, 367479684, 200443464,
    71954064, 16604784, 2372112, 197676, 8721, 171, 1]
def zeros : List Rat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def ones : List Rat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
/-- beta_l = l^2/(4l^2 - 1), l = 1 .. 40: the betas of nu0's J-fraction (its alphas 0), the recurrence
    of the monic Legendre polynomials, P_(l+1) = z P_l - beta_l P_(l-1) -/
def beta_nu0 : List Rat := [1/3, 4/15, 9/35, 16/63, 25/99, 36/143, 49/195, 64/255, 81/323, 100/399,
    121/483, 144/575, 169/675, 196/783, 225/899, 256/1023, 289/1155, 324/1295, 361/1443, 400/1599,
    441/1763, 484/1935, 529/2115, 576/2303, 625/2499, 676/2703, 729/2915, 784/3135, 841/3363,
    900/3599, 961/3843, 1024/4095, 1089/4355, 1156/4623, 1225/4899, 1296/5183, 1369/5475, 1444/5775,
    1521/6083, 1600/6399]
/-- the list beta_nu0 again: nu's J-fraction has alpha = 1 and these betas, nu0's alpha = 0 and the same
    betas; moving a measure by -1 lowers every alpha by 1 and leaves every beta -/
def beta_nu : List Rat := [1/3, 4/15, 9/35, 16/63, 25/99, 36/143, 49/195, 64/255, 81/323, 100/399,
    121/483, 144/575, 169/675, 196/783, 225/899, 256/1023, 289/1155, 324/1295, 361/1443, 400/1599,
    441/1763, 484/1935, 529/2115, 576/2303, 625/2499, 676/2703, 729/2915, 784/3135, 841/3363,
    900/3599, 961/3843, 1024/4095, 1089/4355, 1156/4623, 1225/4899, 1296/5183, 1369/5475, 1444/5775,
    1521/6083, 1600/6399]
def beta_G1 : List Rat := [1/2, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4,
    1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4,
    1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4]
def beta_G3 : List Rat := [1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4,
    1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4,
    1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4]
def q_A000007 : List (List Rat) := [
    [0, 1]]
def q_A000012 : List (List Rat) := [
    [-1, 1]]
def q_A000027 : List (List Rat) := [
    [-2, 1],
    [0, 1]]
def q_A000041 : List (List Rat) := [
    [-1, 1],
    [0, -1],
    [1, 0, -1],
    [1, 1],
    [0, 1],
    [-1, 1, -1],
    [1, 1, 1],
    [-1, 1],
    [1, 1],
    [-1, 1],
    [-2, -1],
    [1/3, -1/3],
    [9, -9],
    [-1/12, -1/6],
    [-4, 8],
    [1/16, 1/16]]
def q_A000203 : List (List Rat) := [
    [-3, 1],
    [2/5, 1/5],
    [-4, -5],
    [-4/9, -5/21],
    [-99/640, -189/80],
    [-120448/389205, -7168/12555],
    [203554215/342591488, -4021785/2931712],
    [-525171339136/10896832071225, -8757494912/9516883905],
    [265288574562870599325/56324728904284266272, -37430618164657875/14203689044076224],
    [-1603610550621987600285059184256/11461971561339804516917500276125,
      -1786845699759514063212928/17168072221324896338134125],
    [-4271082921840884283101814881179968363675375/45135502311023122834251266982627638281216,
      -2550796819803992569681060487283387375/71533855670776954792011732757224448]]
def q_A000217_1 : List (List Rat) := [
    [-3, 1],
    [1/9, 1/3],
    [-9, 27]]
def q_A000292_1 : List (List Rat) := [
    [-4, 1],
    [1/9, 1/6],
    [-144/25, 108/5],
    [-25/81, 125/162]]
def q_A000332_4 : List (List Rat) := [
    [-5, 1],
    [1/10, 1/10],
    [-4, 20],
    [-13/98, 5/14],
    [-147/5, 343/5]]
def q_A008619 : List (List Rat) := [
    [-1, 1],
    [-1, -1],
    [1, -1]]
def q_A001399 : List (List Rat) := [
    [-1, 1],
    [0, -1],
    [1, -1],
    [-3, -1],
    [5/16, -1/4],
    [48, -64]]
def q_A008638 : List (List Rat) := [
    [-1, 1],
    [0, -1],
    [1, 0, -1],
    [1, 1],
    [-19/8, -1/4, -1/2],
    [2200/3721, -16/61],
    [1760033/1280, 226981/1280],
    [-89600/124612569, 12800/124612569],
    [-14579670573/20480, 1121513121/5120],
    [17518592/10844408817225, 16384/36760707855],
    [1310755259197794575/37704318976, 355455622342375/12427264],
    [-34949754544570368/1688673637189525944105625, 3574840742912/420800806675685508125],
    [1298590026998745451017225625/93589693719199112,
      -6776647306041567613695873125/2039060561031061504],
    [5307964186963519505645568/679867140978620270844038471265625,
      18017139117270459449344/135973428195724054168807694253125],
    [-2410657271537749248092562198528814015625/18995204811290386818066717147136,
      3399335704893101354220192356328125/1417975874237861064352546816],
    [-566271502253158561774403690021092524032/406024891160240237321245744804896181031640625,
      254459763652046021814821742903033856/2626989636062864261034593552008593359375]]
def q_oddM : List (List Rat) := [
    [0, 1],
    [0, -1/3],
    [0, -9/4],
    [0, 4/3]]
def q_A000009 : List (List Rat) := [
    [-1, 1],
    [0, -1, -1],
    [1, -1, 1, -1],
    [1, 1, 1],
    [-1, 1],
    [1, 1, 1],
    [-1, 1],
    [-3, -2, -1],
    [1/4, -1/4],
    [16, -16],
    [3/4, 1/4],
    [-5/4, 1/2],
    [4, -8]]
def q_A000593 : List (List Rat) := [
    [-1, 1],
    [-2/3, -1/3],
    [72/169, -9/13],
    [-716560/1587, -2197/69],
    [257653153/117135744128, -12167/81798704],
    [104994272841900416/68561045, -167738385591296/9794435],
    [-34894927963/53504854759140415488, -20866405/2972491931063356416],
    [-6833718825703886433050338176/5640671950821649, 1655306444110906604160/3680115943],
    [-13834668528067239768828073/869405631649544814864304114750998240,
      710586048156343121/34314315461549707366749320640]]
def q_A000079 : List (List Rat) := [
    [-2, 1]]
def q_A000045_1 : List (List Rat) := [
    [-1, 1],
    [0, -1]]
def q_A000984 : List (List Rat) := [
    [-2, 1],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2],
    [-4, 2],
    [1, -1/2]]
def q_A000108 : List (List Rat) := [
    [-1, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1]]
def q_A000142 : List (List Rat) := [
    [-1, 1],
    [3, -1],
    [-5/4, 1/4],
    [28/9, -4/9],
    [-81/64, 9/64],
    [704/225, -64/225],
    [-325/256, 25/256],
    [768/245, -256/1225],
    [-20825/16384, 1225/16384],
    [311296/99225, -16384/99225],
    [-83349/65536, 3969/65536],
    [1507328/480249, -65536/480249],
    [-1334025/1048576, 53361/1048576],
    [3145728/1002001, -1048576/9018009],
    [-5337189/4194304, 184041/4194304],
    [130023424/41409225, -4194304/41409225],
    [-1366504425/1073741824, 41409225/1073741824],
    [7516192768/2393453205, -1073741824/11967266025],
    [-5466528925/4294967296, 147744025/4294967296],
    [12884901888/4102737925, -4294967296/53335593025]]
def q_A005408 : List (List Rat) := [
    [-3, 1],
    [1/4, 1/4]]
def q_A001147 : List (List Rat) := [
    [-1, 1],
    [5/2, -1/2],
    [-3/2, 1/6],
    [13/5, -1/5],
    [-85/56, 5/56],
    [196/75, -28/225],
    [-1875/1232, 75/1232],
    [2552/975, -88/975],
    [-195/128, 65/1408],
    [26048/9945, -704/9945],
    [-81549/53504, 1989/53504],
    [12160/4641, -2432/41769],
    [-682227/447488, 13923/447488],
    [11858432/4524975, -223744/4524975],
    [-71825/47104, 71825/2684928],
    [27296768/10414625, -447488/10414625],
    [-676950625/443908096, 10414625/443908096],
    [5104943104/1947534875, -221954048/5842604625],
    [-28434009175/18644140032, 389506975/18644140032],
    [3434446848/1310159825, -490635264/14411758075]]
def q_A000290_1 : List (List Rat) := [
    [-4, 1],
    [8/49, 1/7],
    [-49/8, 343/8]]
def q_nu : List (List Rat) := [
    [-1, 1],
    [3, -3],
    [-5/4, 5/4],
    [28/9, -28/9],
    [-81/64, 81/64],
    [704/225, -704/225],
    [-325/256, 325/256],
    [768/245, -768/245],
    [-20825/16384, 20825/16384],
    [311296/99225, -311296/99225],
    [-83349/65536, 83349/65536],
    [1507328/480249, -1507328/480249],
    [-1334025/1048576, 1334025/1048576],
    [3145728/1002001, -3145728/1002001],
    [-5337189/4194304, 5337189/4194304],
    [130023424/41409225, -130023424/41409225],
    [-1366504425/1073741824, 1366504425/1073741824],
    [7516192768/2393453205, -7516192768/2393453205],
    [-5466528925/4294967296, 5466528925/4294967296],
    [12884901888/4102737925, -12884901888/4102737925]]
def q_nu0 : List (List Rat) := [
    [0, 1],
    [0, -3],
    [0, 5/4],
    [0, -28/9],
    [0, 81/64],
    [0, -704/225],
    [0, 325/256],
    [0, -768/245],
    [0, 20825/16384],
    [0, -311296/99225],
    [0, 83349/65536],
    [0, -1507328/480249],
    [0, 1334025/1048576],
    [0, -3145728/1002001],
    [0, 5337189/4194304],
    [0, -130023424/41409225],
    [0, 1366504425/1073741824],
    [0, -7516192768/2393453205],
    [0, 5466528925/4294967296],
    [0, -12884901888/4102737925]]
def q_A000108_1 : List (List Rat) := [
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1],
    [-2, 1],
    [2, -1]]
def q_A001006 : List (List Rat) := [
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1],
    [-1, 1],
    [1, -1]]
def q_A126120 : List (List Rat) := [
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1],
    [0, 1],
    [0, -1]]
def q_omegaS : List (List Rat) := [
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4],
    [0, 1],
    [0, -4]]
def q_A040000 : List (List Rat) := [
    [-2, 1],
    [1/2, 1/2]]
def q_A000330_1 : List (List Rat) := [
    [-5, 1],
    [15/121, 1/11],
    [-3751/2401, 1331/49],
    [-36015/234256, 117649/234256]]
def q_G1 : List (List Rat) := [
    [-1, 1],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2],
    [-2, 2],
    [2, -2]]
def q_G3 : List (List Rat) := [
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4],
    [-1, 1],
    [4, -4]]
def q_A000041_bent : List (List Rat) := [
    [-1, 1],
    [0, -1],
    [1, 0, -1],
    [1, 1],
    [0, 1],
    [-1, 1, -1],
    [1, 1, 1],
    [-1, 1],
    [1, 1],
    [-1, 1],
    [-2, -1],
    [1/3, -1/3],
    [9, -9],
    [-1/12, -1/6],
    [-4, 8],
    [17/16, 1/16]]

/-! ### 3. Kernel-Evaluated Steps, Fractions, and Relations
Each statement on a finite window: `decide +kernel`, evaluated by the kernel. -/

/-- Step 1: the binomial transform of A000007 is A000012, on the first 40 terms. -/
theorem step01_binomialTransform : binomialTransform A000007 = A000012 := by decide +kernel
/-- Step 2: the partial sums of A000012 are A000027, on the first 40 terms. -/
theorem step02_partialSums : partialSums A000012 = A000027 := by decide +kernel
/-- Step 3: the Euler transform of f_k/k (OEIS EULER) takes A000027 to A000041, on the first 40 terms.
    -/
theorem step03_eulerTransform : eulerTransform A000027 = A000041 := by decide +kernel
/-- Step 4: the logarithmic derivative of A000041 is A000203, on the first 39 terms. -/
theorem step04_logDerivative : logDerivative A000041 = A000203.take 39 := by decide +kernel
/-- Step 5: the Moebius inversion of A000203 is A000027, on the first 40 terms. -/
theorem step05_moebiusInversion : moebiusInversion A000203 = A000027 := by decide +kernel
/-- Step 6: the partial sums of A000027 are A000217_1, on the first 40 terms. -/
theorem step06_partialSums : partialSums A000027 = A000217_1 := by decide +kernel
/-- Step 7: the partial sums of A000217_1 are A000292_1, on the first 40 terms. -/
theorem step07_partialSums : partialSums A000217_1 = A000292_1 := by decide +kernel
/-- Step 8: the partial sums of A000292_1 are A000332_4, on the first 40 terms. -/
theorem step08_partialSums : partialSums A000292_1 = A000332_4 := by decide +kernel
/-- Step 9: A000012 times e_k for each k in [2] is A008619, on the first 40 terms. -/
theorem step09_timesEulerFactors : timesEulerFactors [2] A000012 = A008619 := by decide +kernel
/-- Step 10: A008619 times e_k for each k in [3] is A001399, on the first 40 terms. -/
theorem step10_timesEulerFactors : timesEulerFactors [3] A008619 = A001399 := by decide +kernel
/-- Step 11: A001399 times e_k for each k in [4, 5, 6, 7, 8, 9] is A008638, on the first 40 terms. -/
theorem step11_timesEulerFactors :
    timesEulerFactors [4, 5, 6, 7, 8, 9] A001399 = A008638 := by
  decide +kernel
/-- Step 12: A008638 times e_k for each k in [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] is A000041, on the first 40 terms.
    -/
theorem step12_timesEulerFactors :
    timesEulerFactors [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] A008638 = A000041 := by
  decide +kernel
/-- Step 13: the Euler transform of f_k/k (OEIS EULER) takes oddM to A000009, on the first 40 terms. -/
theorem step13_eulerTransform : eulerTransform oddM = A000009 := by decide +kernel
/-- Step 14: the logarithmic derivative of A000009 is A000593, on the first 39 terms. -/
theorem step14_logDerivative : logDerivative A000009 = A000593.take 39 := by decide +kernel
/-- Step 15: the Moebius inversion of A000593 is oddM, on the first 40 terms. -/
theorem step15_moebiusInversion : moebiusInversion A000593 = oddM := by decide +kernel
/-- Step 16: the binomial transform of A000012 is A000079, on the first 40 terms. -/
theorem step16_binomialTransform : binomialTransform A000012 = A000079 := by decide +kernel
/-- Step 17: the triangle A007318 summed along the lines 2k + m = n is A000045_1, on the first 40 terms.
    -/
theorem step17_antidiagonalSums : antidiagonalSums A007318 40 = A000045_1 := by decide +kernel
/-- Step 18: the diagonal T(2n, n) of the triangle A007318 is A000984, on the first 20 terms. -/
theorem step18_centralDiagonal : centralDiagonal A007318 20 = A000984.take 20 := by decide +kernel
/-- Step 19: A000984 divided by n + 1 is A000108, on the first 40 terms. -/
theorem step19_divideByNPlusOne : divideByNPlusOne A000984 = A000108 := by decide +kernel
/-- Step 20: the partial products of A000027 are A000142, on the first 40 terms. -/
theorem step20_partialProducts : partialProducts A000027 = A000142 := by decide +kernel
/-- Step 21: alpha_0 .. alpha_19 of A000142's J-fraction, read off its first 40 terms, two terms per
    depth (`jacobiAlphas`), are the first 20 of `A005408`. -/
theorem step21_jacobiAlphas : jacobiAlphas A000142 = A005408.take 20 := by decide +kernel
/-- Step 22: the partial products of A005408 are A001147, on the first 40 terms. -/
theorem step22_partialProducts : partialProducts A005408 = A001147 := by decide +kernel
/-- Step 23: beta_1 .. beta_19 of A000142's J-fraction, read off its first 40 terms, two terms per depth
    (`jacobiBetas`), are the first 19 of `A000290_1`. -/
theorem step23_jacobiBetas : jacobiBetas A000142 = A000290_1.take 19 := by decide +kernel
/-- Step 24: the S-fraction with coefficients c_a is A000108, on the first 40 terms. -/
theorem step24_sfractionMoments : sfractionMoments c_a 40 = A000108 := by decide +kernel
/-- Step 25: the S-fraction with coefficients c_t is A001147, on the first 40 terms. -/
theorem step25_sfractionMoments : sfractionMoments c_t 40 = A001147 := by decide +kernel
/-- Step 26: the S-fraction with coefficients c_tt is A000142, on the first 40 terms. -/
theorem step26_sfractionMoments : sfractionMoments c_tt 40 = A000142 := by decide +kernel
/-- Step 27: the J-fraction A005408 A000290_1 reproduces A000142, and lc(row i) det(z - J_i) is row i of
    A021009, i = 0 .. 8, on the first 40 terms. -/
theorem step27_charpolyRowsAre :
    jacobiMoments A005408 A000290_1 40 = A000142 /\ charpolyRowsAre A005408 A000290_1 A021009 8 =
      true := by
  decide +kernel
/-- Step 28: A000079 divided by n + 1 is nu, on the first 40 terms. -/
theorem step28_divideByNPlusOne : divideByNPlusOne A000079 = nu := by decide +kernel
/-- Step 29: the S-fraction with coefficients c_nu is nu, on the first 40 terms. -/
theorem step29_sfractionMoments : sfractionMoments c_nu 40 = nu := by decide +kernel
/-- Step 30: the inverse binomial transform of nu is nu0, on the first 40 terms. -/
theorem step30_binomialInverse : binomialInverse nu = nu0 := by decide +kernel
/-- Step 31: the J-fraction zeros beta_nu0 reproduces nu0, and lc(row i) det(z - J_i) is row i of
    A100258, i = 0 .. 8, on the first 40 terms. -/
theorem step31_charpolyRowsAre :
    jacobiMoments zeros beta_nu0 40 = nu0 /\ charpolyRowsAre zeros beta_nu0 A100258 8 = true := by
  decide +kernel
/-- Step 32: the inverse binomial transform of A000108_1 is A001006, on the first 40 terms. -/
theorem step32_binomialInverse : binomialInverse A000108_1 = A001006 := by decide +kernel
/-- Step 33: the inverse binomial transform of A001006 is A126120, on the first 40 terms. -/
theorem step33_binomialInverse : binomialInverse A001006 = A126120 := by decide +kernel
/-- Step 34: A126120 divided by 2^n is omegaS, on the first 40 terms. -/
theorem step34_divideByTwoPow : divideByTwoPow A126120 = omegaS := by decide +kernel
/-- Step 35: f[n] + f[n - 1] of A000012 is A040000, on the first 40 terms. -/
theorem step35_adjacentSums : adjacentSums A000012 = A040000 := by decide +kernel
/-- Step 36: the partial sums of A040000 are A005408, on the first 40 terms. -/
theorem step36_partialSums : partialSums A040000 = A005408 := by decide +kernel
/-- Step 37: the partial sums of A005408 are A000290_1, on the first 40 terms. -/
theorem step37_partialSums : partialSums A005408 = A000290_1 := by decide +kernel
/-- Step 38: the partial sums of A000290_1 are A000330_1, on the first 40 terms. -/
theorem step38_partialSums : partialSums A000290_1 = A000330_1 := by decide +kernel
/-- Step 39: A000984 divided by 2^n is G1, on the first 40 terms. -/
theorem step39_divideByTwoPow : divideByTwoPow A000984 = G1 := by decide +kernel
/-- Step 40: the J-fraction ones beta_G1 reproduces G1; `poleAtTwo` of its betas gives the first 20
    terms of A040000, on the first 40 terms. -/
theorem step40_poleAtTwo :
    jacobiMoments ones beta_G1 40 = G1 /\ poleAtTwo beta_G1 20 = A040000.take 20 := by
  decide +kernel
/-- Step 41: A000108_1 divided by 2^n is G3, on the first 40 terms. -/
theorem step41_divideByTwoPow : divideByTwoPow A000108_1 = G3 := by decide +kernel
/-- Step 42: the J-fraction ones beta_G3 reproduces G3; `poleAtTwo` of its betas gives the first 20
    terms of A000290_1, on the first 40 terms. -/
theorem step42_poleAtTwo :
    jacobiMoments ones beta_G3 40 = G3 /\ poleAtTwo beta_G3 20 = A000290_1.take 20 := by
  decide +kernel
/-- Step 43: the J-fraction zeros ones reproduces A126120; with every other beta times t, its even
    moments' coefficients, read by rows, are the first 19 rows of A001263, on the first 40 terms. -/
theorem step43_alternateBetaRows :
    jacobiMoments zeros ones 40 = A126120 /\ alternateBetaRows ones 19 = A001263 := by
  decide +kernel
/-- Step 44: the row sums of the triangle A001263 are A000108_1, on the first 19 terms. -/
theorem step44_rowSums : rowSums A001263 19 = A000108_1.take 19 := by decide +kernel
/-- Step 45: A000108 with each bare loop weighted t - 1, the binomials read off Pascal's rows A007318,
    is the triangle A001263: row n is the coefficients of t^1 .. t^n in sum_k C(n+k, 2k) (t - 1)^(n-k)
    A000108(k), on the first 19 terms. -/
theorem step45_dressedLoops : dressedLoops A007318 A000108 19 = A001263 := by decide +kernel
/-- the partial quotients of A000007 that its first 40 terms decide are `q_A000007` -/
theorem cf_A000007 : cfQuotientsAre A000007 q_A000007 = true := by decide +kernel
/-- the partial quotients of A000012 that its first 40 terms decide are `q_A000012` -/
theorem cf_A000012 : cfQuotientsAre A000012 q_A000012 = true := by decide +kernel
/-- the partial quotients of A000027 that its first 40 terms decide are `q_A000027` -/
theorem cf_A000027 : cfQuotientsAre A000027 q_A000027 = true := by decide +kernel
/-- the partial quotients of A000041 that its first 40 terms decide are `q_A000041` -/
theorem cf_A000041 : cfQuotientsAre A000041 q_A000041 = true := by decide +kernel
/-- the first 11 partial quotients of A000203 that its first 40 terms give are `q_A000203` -/
theorem cf_A000203 : cfLeadingQuotients A000203 q_A000203 = true := by decide +kernel
/-- the partial quotients of A000217_1 that its first 40 terms decide are `q_A000217_1` -/
theorem cf_A000217_1 : cfQuotientsAre A000217_1 q_A000217_1 = true := by decide +kernel
/-- the partial quotients of A000292_1 that its first 40 terms decide are `q_A000292_1` -/
theorem cf_A000292_1 : cfQuotientsAre A000292_1 q_A000292_1 = true := by decide +kernel
/-- the partial quotients of A000332_4 that its first 40 terms decide are `q_A000332_4` -/
theorem cf_A000332_4 : cfQuotientsAre A000332_4 q_A000332_4 = true := by decide +kernel
/-- the partial quotients of A008619 that its first 40 terms decide are `q_A008619` -/
theorem cf_A008619 : cfQuotientsAre A008619 q_A008619 = true := by decide +kernel
/-- the partial quotients of A001399 that its first 40 terms decide are `q_A001399` -/
theorem cf_A001399 : cfQuotientsAre A001399 q_A001399 = true := by decide +kernel
/-- the first 16 partial quotients of A008638 that its first 40 terms give are `q_A008638` -/
theorem cf_A008638 : cfLeadingQuotients A008638 q_A008638 = true := by decide +kernel
/-- the partial quotients of oddM that its first 40 terms decide are `q_oddM` -/
theorem cf_oddM : cfQuotientsAre oddM q_oddM = true := by decide +kernel
/-- the partial quotients of A000009 that its first 40 terms decide are `q_A000009` -/
theorem cf_A000009 : cfQuotientsAre A000009 q_A000009 = true := by decide +kernel
/-- the first 9 partial quotients of A000593 that its first 40 terms give are `q_A000593` -/
theorem cf_A000593 : cfLeadingQuotients A000593 q_A000593 = true := by decide +kernel
/-- the partial quotients of A000079 that its first 40 terms decide are `q_A000079` -/
theorem cf_A000079 : cfQuotientsAre A000079 q_A000079 = true := by decide +kernel
/-- the partial quotients of A000045_1 that its first 40 terms decide are `q_A000045_1` -/
theorem cf_A000045_1 : cfQuotientsAre A000045_1 q_A000045_1 = true := by decide +kernel
/-- the partial quotients of A000984 that its first 40 terms decide are `q_A000984` -/
theorem cf_A000984 : cfQuotientsAre A000984 q_A000984 = true := by decide +kernel
/-- the partial quotients of A000108 that its first 40 terms decide are `q_A000108` -/
theorem cf_A000108 : cfQuotientsAre A000108 q_A000108 = true := by decide +kernel
/-- the partial quotients of A000142 that its first 40 terms decide are `q_A000142` -/
theorem cf_A000142 : cfQuotientsAre A000142 q_A000142 = true := by decide +kernel
/-- the partial quotients of A005408 that its first 40 terms decide are `q_A005408` -/
theorem cf_A005408 : cfQuotientsAre A005408 q_A005408 = true := by decide +kernel
/-- the partial quotients of A001147 that its first 40 terms decide are `q_A001147` -/
theorem cf_A001147 : cfQuotientsAre A001147 q_A001147 = true := by decide +kernel
/-- the partial quotients of A000290_1 that its first 40 terms decide are `q_A000290_1` -/
theorem cf_A000290_1 : cfQuotientsAre A000290_1 q_A000290_1 = true := by decide +kernel
/-- the partial quotients of nu that its first 40 terms decide are `q_nu` -/
theorem cf_nu : cfQuotientsAre nu q_nu = true := by decide +kernel
/-- the partial quotients of nu0 that its first 40 terms decide are `q_nu0` -/
theorem cf_nu0 : cfQuotientsAre nu0 q_nu0 = true := by decide +kernel
/-- the partial quotients of A000108_1 that its first 40 terms decide are `q_A000108_1` -/
theorem cf_A000108_1 : cfQuotientsAre A000108_1 q_A000108_1 = true := by decide +kernel
/-- the partial quotients of A001006 that its first 40 terms decide are `q_A001006` -/
theorem cf_A001006 : cfQuotientsAre A001006 q_A001006 = true := by decide +kernel
/-- the partial quotients of A126120 that its first 40 terms decide are `q_A126120` -/
theorem cf_A126120 : cfQuotientsAre A126120 q_A126120 = true := by decide +kernel
/-- the partial quotients of omegaS that its first 40 terms decide are `q_omegaS` -/
theorem cf_omegaS : cfQuotientsAre omegaS q_omegaS = true := by decide +kernel
/-- the partial quotients of A040000 that its first 40 terms decide are `q_A040000` -/
theorem cf_A040000 : cfQuotientsAre A040000 q_A040000 = true := by decide +kernel
/-- the partial quotients of A000330_1 that its first 40 terms decide are `q_A000330_1` -/
theorem cf_A000330_1 : cfQuotientsAre A000330_1 q_A000330_1 = true := by decide +kernel
/-- the partial quotients of G1 that its first 40 terms decide are `q_G1` -/
theorem cf_G1 : cfQuotientsAre G1 q_G1 = true := by decide +kernel
/-- the partial quotients of G3 that its first 40 terms decide are `q_G3` -/
theorem cf_G3 : cfQuotientsAre G3 q_G3 = true := by decide +kernel
/-- with its last quotient moved by 1, `q_A000041` is not the quotient list of A000041 -/
theorem cf_A000041_bent : cfQuotientsAre A000041 q_A000041_bent = false := by decide +kernel
/-- b_i a_i a_(i+1) = s_i for i < 19: b the betas of nu0, a = A005408, s = A000290_1 -/
theorem rel_beta_nu0 : betaRelation beta_nu0 A005408 A000290_1 19 = true := by decide +kernel
/-- the J-fraction with alpha = 1 and beta_nu reproduces the first 40 terms of nu; `poleAtTwo` of
    beta_nu gives the first 20 terms of A005408 -/
theorem rel_pole_nu :
    jacobiMoments ones beta_nu 40 = nu /\ poleAtTwo beta_nu 20 = A005408.take 20 := by
  decide +kernel

/-! ### 4. Universal Index Identities (Mathlib)
* Each holds for every index `n`: a closed form, the identity behind the step its docstring names.
* That step's lists are checked on their window by the step's own theorem above. -/

/-- the binomial transform of the unit is ones: the sum of C(n, m) [m = 0] over m is 1, for every n -/
theorem all_step01_binomialTransform (n : Nat) :
    (Finset.range (n + 1)).sum (fun m => Nat.choose n m * (if m = 0 then 1 else 0)) = 1 := by
  rw [Finset.sum_eq_single 0]
  . simp
  . intro b _ hb
    simp [hb]
  . intro h
    simp at h

/-- the partial sums of ones count up: the sum of 1 over m from 0 to n is n + 1, for every n -/
theorem all_step02_partialSums (n : Nat) :
    (Finset.range (n + 1)).sum (fun _ => (1 : Nat)) = n + 1 := by
  simp

/-- the hockey stick: the sum of C(m, k) over m from k to n is C(n + 1, k + 1), for every n and k -/
theorem all_columns_partialSums (n k : Nat) :
    (Finset.Icc k n).sum (fun m => Nat.choose m k) = Nat.choose (n + 1) (k + 1) :=
  Nat.sum_Icc_choose n k

/-- the hockey stick at k = 1: the partial sums of C(m, 1) are C(n + 2, 2), for every n -/
theorem all_step06_partialSums (n : Nat) :
    (Finset.Icc 1 (n + 1)).sum (fun m => Nat.choose m 1) = Nat.choose (n + 2) 2 :=
  Nat.sum_Icc_choose (n + 1) 1

/-- the hockey stick at k = 2: the partial sums of C(m, 2) are C(n + 3, 3), for every n -/
theorem all_step07_partialSums (n : Nat) :
    (Finset.Icc 2 (n + 2)).sum (fun m => Nat.choose m 2) = Nat.choose (n + 3) 3 :=
  Nat.sum_Icc_choose (n + 2) 2

/-- the hockey stick at k = 3: the partial sums of C(m, 3) are C(n + 4, 4), for every n -/
theorem all_step08_partialSums (n : Nat) :
    (Finset.Icc 3 (n + 3)).sum (fun m => Nat.choose m 3) = Nat.choose (n + 4) 4 :=
  Nat.sum_Icc_choose (n + 3) 3

/-- the coefficient of x^n in 1/((1 - x)(1 - x^2)) counts the b with 2b <= n: floor(n/2) + 1, for
    every n -/
theorem all_step09_timesEulerFactors (n : Nat) :
    ((Finset.range (n + 1)).filter (fun b => 2 * b <= n)).card = n / 2 + 1 := by
  have h : (Finset.range (n + 1)).filter (fun b => 2 * b <= n) = Finset.range (n / 2 + 1) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h, Finset.card_range]

/-- the coefficient of x^n in 1/((1 - x)(1 - x^2)(1 - x^3)) is ((n + 3)^2 + 6) / 12 rounded down, for
    every n: both sides grow by n + 6 from n to n + 6, and they agree for n < 6 -/
theorem all_step10_timesEulerFactors (n : Nat) :
    (Finset.range (n / 3 + 1)).sum (fun c => (n - 3 * c) / 2 + 1) = ((n + 3) ^ 2 + 6) / 12 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 6
    . interval_cases n <;> decide
    . have hex : Exists (fun m => n = m + 6) := Exists.intro (n - 6) (by omega)
      cases hex with
      | intro m hmn =>
      subst hmn
      have hm := ih m (by omega)
      have hr : (m + 6) / 3 + 1 = (m / 3 + 1) + 1 + 1 := by omega
      rw [hr, Finset.sum_range_succ, Finset.sum_range_succ]
      have hs : (Finset.range (m / 3 + 1)).sum (fun c => (m + 6 - 3 * c) / 2 + 1)
          = (Finset.range (m / 3 + 1)).sum (fun c => (m - 3 * c) / 2 + 1 + 3) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mem_range] at hc
        omega
      rw [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, hm]
      have hsq : (m + 6 + 3) ^ 2 + 6 = ((m + 3) ^ 2 + 6) + 12 * (m + 6) := by ring
      rw [hsq, Nat.add_mul_div_left _ _ (by norm_num : 0 < 12)]
      generalize ((m + 3) ^ 2 + 6) / 12 = X
      omega

/-- Moebius inversion of sigma is the identity: the sum of mu(d) sigma(e) over d e = n is n,
    for every n > 0 -/
theorem all_step05_moebiusInversion (n : Nat) (hn : 0 < n) :
    n.divisorsAntidiagonal.sum (fun x => (ArithmeticFunction.moebius x.1 : Int)
      * (ArithmeticFunction.sigma 1 x.2 : Int)) = n := by
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := fun m : Nat => (m : Int))
    (g := fun m => (ArithmeticFunction.sigma 1 m : Int))).1 ?_ n hn
  intro m _
  simp [ArithmeticFunction.sigma_one_apply]

/-- Moebius inversion of the sum of the odd divisors is n for odd n and 0 for even n, for every n > 0 -/
theorem all_step15_moebiusInversion (n : Nat) (hn : 0 < n) :
    n.divisorsAntidiagonal.sum (fun x => (ArithmeticFunction.moebius x.1 : Int)
      * ((x.2.divisors.filter (fun d => d % 2 = 1)).sum (fun d => (d : Int)))) =
      if n % 2 = 1 then (n : Int) else 0 := by
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun m : Nat => if m % 2 = 1 then (m : Int) else 0)
    (g := fun m => (m.divisors.filter (fun d => d % 2 = 1)).sum (fun d => (d : Int)))).1 ?_ n hn
  intro m _
  rw [Finset.sum_filter]

/-- the binomial transform of ones is 2^n: the sum of C(n, m) over m is 2^n, for every n -/
theorem all_step16_binomialTransform (n : Nat) :
    (Finset.range (n + 1)).sum (fun m => Nat.choose n m) = 2 ^ n :=
  Nat.sum_range_choose n

/-- Pascal's shallow diagonals are Fibonacci's: F(n + 1) is the sum of C(a, b) over a + b = n,
    for every n -/
theorem all_step17_antidiagonalSums (n : Nat) :
    Nat.fib (n + 1) = (Finset.HasAntidiagonal.antidiagonal n).sum (fun p => Nat.choose p.1 p.2) :=
  Nat.fib_succ_eq_sum_choose n

/-- by definition: Mathlib's centralBinom is C(2n, n), the entry CENTRAL_DIAGONAL reads -/
theorem all_step18_centralDiagonal (n : Nat) :
    Nat.centralBinom n = Nat.choose (2 * n) n := rfl

/-- Catalan from the central binomial: (n + 1) Catalan(n) = C(2n, n), for every n -/
theorem all_step19_divideByNPlusOne (n : Nat) :
    (n + 1) * catalan n = Nat.centralBinom n :=
  succ_mul_catalan_eq_centralBinom n

/-- the partial products of 1, 2, 3, ... are the factorials: the product of (i + 1) over i below n
    is n!, for every n -/
theorem all_step20_partialProducts (n : Nat) :
    (Finset.range n).prod (fun i => i + 1) = Nat.factorial n :=
  Finset.prod_range_add_one_eq_factorial n

/-- the partial products of the odd numbers are the double factorials: the product of (2i + 1) over
    i below n is (2n - 1)!!, for every n -/
theorem all_step22_partialProducts (n : Nat) :
    (Finset.range n).prod (fun i => 2 * i + 1) = Nat.doubleFactorial (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    cases k with
    | zero => simp
    | succ j =>
      have h : 2 * (j + 1 + 1) - 1 = (2 * (j + 1) - 1) + 2 := by omega
      rw [h, Nat.doubleFactorial_add_two]
      have h2 : 2 * (j + 1) - 1 + 2 = 2 * (j + 1) + 1 := by omega
      rw [h2]
      ring

/-- the inverse binomial transform of 2^k/(k + 1) is (1 + (-1)^n)/(2(n + 1)), for every n: the moments
    (1/2) integral_(-1)^1 x^n dx of the uniform measure on [-1, 1] -/
theorem all_step30_binomialInverse (n : Nat) :
    (Finset.range (n + 1)).sum
      (fun k => (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * 2 ^ k / ((k : Rat) + 1)) =
      (1 + (-1 : Rat) ^ n) / (2 * ((n : Rat) + 1)) := by
  have hterm : forall k,
      (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * 2 ^ k / ((k : Rat) + 1) * ((n : Rat) + 1)
        = (-1 : Rat) ^ (n - k) * 2 ^ k * (Nat.choose (n + 1) (k + 1) : Rat) := by
    intro k
    have h' : ((n : Rat) + 1) * (Nat.choose n k : Rat)
        = (Nat.choose (n + 1) (k + 1) : Rat) * ((k : Rat) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    have hk : Ne ((k : Rat) + 1) 0 := by positivity
    field_simp
    linear_combination h'
  have hb : (Finset.range (n + 1)).sum
      (fun k => (2 : Rat) ^ (k + 1) * (-1) ^ (n + 1 - (k + 1)) * (Nat.choose (n + 1) (k + 1) : Rat))
      + (-1 : Rat) ^ (n + 1) = 1 := by
    have h := add_pow (2 : Rat) (-1) (n + 1)
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one] at h
    have h2 : (2 + (-1 : Rat)) ^ (n + 1) = 1 := by norm_num
    rw [h2] at h
    linarith [h]
  rw [eq_div_iff (by positivity : Ne (2 * ((n : Rat) + 1)) 0)]
  have hs : (Finset.range (n + 1)).sum
      (fun k => (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * 2 ^ k / ((k : Rat) + 1))
        * (2 * ((n : Rat) + 1))
      = 2 * (Finset.range (n + 1)).sum
        (fun k => (-1 : Rat) ^ (n - k) * 2 ^ k * (Nat.choose (n + 1) (k + 1) : Rat)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [<- hterm k]
    ring
  have hs2 : 2 * (Finset.range (n + 1)).sum
      (fun k => (-1 : Rat) ^ (n - k) * 2 ^ k * (Nat.choose (n + 1) (k + 1) : Rat))
      = (Finset.range (n + 1)).sum
        (fun k => (2 : Rat) ^ (k + 1) * (-1) ^ (n + 1 - (k + 1))
          * (Nat.choose (n + 1) (k + 1) : Rat)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have e : n + 1 - (k + 1) = n - k := by omega
    rw [e, pow_succ]
    ring
  rw [hs, hs2]
  have hpow : (-1 : Rat) ^ (n + 1) = -((-1 : Rat) ^ n) := by rw [pow_succ]; ring
  rw [hpow] at hb
  linarith [hb]

/-- f(n) + f(n - 1) of ones is 1 at n = 0 and 2 after, for every n -/
theorem all_step35_adjacentSums (n : Nat) :
    (1 : Nat) + (if n = 0 then 0 else 1) = if n = 0 then 1 else 2 := by
  split <;> rfl

/-- the partial sums of 1, 2, 2, 2, ... are the odd numbers: 2n + 1, for every n -/
theorem all_step36_partialSums (n : Nat) :
    (Finset.range (n + 1)).sum (fun m => if m = 0 then 1 else 2) = 2 * n + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp
    ring

/-- the partial sums of the odd numbers are the squares: (n + 1)^2, for every n -/
theorem all_step37_partialSums (n : Nat) :
    (Finset.range (n + 1)).sum (fun m => 2 * m + 1) = (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- six times the partial sums of the squares is (n + 1)(n + 2)(2n + 3), for every n -/
theorem all_step38_partialSums (n : Nat) :
    6 * (Finset.range (n + 1)).sum (fun m => (m + 1) ^ 2) = (n + 1) * (n + 2) * (2 * n + 3) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- two sequences with u (n + 1) = r n * u n and v (n + 1) = r n * v n for every n, equal at 0, are
    equal for every n -/
theorem all_rec1 {R : Type*} [Semiring R] (u v r : Nat -> R) (hu : forall n, u (n + 1) = r n * u n)
    (hv : forall n, v (n + 1) = r n * v n) (h0 : u 0 = v 0) : forall n, u n = v n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hu, hv, ih]

/-- Catalan's first-order recurrence, shifted: (n + 3) C(n + 2) = 2(2n + 3) C(n + 1), for every n -/
theorem all_catalan_rec (n : Nat) : (n + 3) * catalan (n + 2) = 2 * (2 * n + 3) * catalan (n + 1) := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 2)
  have h2 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h3 := Nat.succ_mul_centralBinom_succ (n + 1)
  have key : (n + 2) * ((n + 3) * catalan (n + 2)) = (n + 2) * (2 * (2 * n + 3) * catalan (n + 1)) := by
    have e1 : (n + 2 + 1) * catalan (n + 2) = Nat.centralBinom (n + 2) := h1
    have e2 : (n + 1 + 1) * catalan (n + 1) = Nat.centralBinom (n + 1) := h2
    have e3 : (n + 1 + 1) * Nat.centralBinom (n + 1 + 1) = 2 * (2 * (n + 1) + 1) * Nat.centralBinom
        (n + 1) := h3
    calc (n + 2) * ((n + 3) * catalan (n + 2)) = (n + 2) * Nat.centralBinom (n + 2) := by rw [<- e1]
      _ = 2 * (2 * (n + 1) + 1) * Nat.centralBinom (n + 1) := e3
      _ = 2 * (2 * (n + 1) + 1) * ((n + 1 + 1) * catalan (n + 1)) := by rw [e2]
      _ = (n + 2) * (2 * (2 * n + 3) * catalan (n + 1)) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- Touchard's summand C(n, 2j) 2^(n - 2j) C(j) -/
def touchardTerm (n j : Nat) : Rat := (Nat.choose n (2 * j) : Rat) * 2 ^ (n - 2 * j) * (catalan j : Rat)

/-- the telescoping partner of `touchardTerm`: -4 j (j + 1) C(n + 1, 2j) 2^(n + 1 - 2j) C(j)/(n + 1) -/
def touchardPartner (n j : Nat) : Rat :=
  -4 * (j : Rat) * ((j : Rat) + 1) * (Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j) *
      (catalan j : Rat)
    / ((n : Rat) + 1)

/-- the summand's shape against C(n + 1, 2j):
    touchardTerm n j * 2(n + 1) = C(n + 1, 2j) 2^(n + 1 - 2j) C(j) (n + 1 - 2j) -/
theorem all_touchard_term_shape (n j : Nat) :
    touchardTerm n j * (2 * ((n : Rat) + 1))
      = (Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j) * (catalan j : Rat)
          * ((n : Rat) + 1 - 2 * j) := by
  unfold touchardTerm
  by_cases h : 2 * j <= n
  . have hc := Nat.choose_mul_succ_eq n (2 * j)
    have hsub : n + 1 - 2 * j = (n - 2 * j) + 1 := by omega
    have hcq : (Nat.choose n (2 * j) : Rat) * ((n : Rat) + 1)
        = (Nat.choose (n + 1) (2 * j) : Rat) * ((n : Rat) + 1 - 2 * j) := by
      have hc' : ((Nat.choose n (2 * j) * (n + 1) : Nat) : Rat)
          = ((Nat.choose (n + 1) (2 * j) * (n + 1 - 2 * j) : Nat) : Rat) := by
        rw [hc]
      push_cast [Nat.cast_sub (by omega : 2 * j <= n + 1)] at hc'
      linarith [hc']
    rw [hsub, pow_succ]
    linear_combination (2 : Rat) ^ (n - 2 * j) * (catalan j : Rat) * 2 * hcq
  . have h0 : Nat.choose n (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0]
    by_cases h' : 2 * j = n + 1
    . have e : ((n : Rat) + 1 - 2 * j) = 0 := by
        have : ((2 * j : Nat) : Rat) = ((n + 1 : Nat) : Rat) := by rw [h']
        push_cast at this
        linarith
      rw [e]
      simp
    . have h1 : Nat.choose (n + 1) (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h1]
      simp

/-- Catalan's ratio: (j + 2) C(j + 1) = 2(2j + 1) C(j), for every j -/
theorem all_catalan_ratio (j : Nat) : (j + 2) * catalan (j + 1) = 2 * (2 * j + 1) * catalan j := by
  have h1 := succ_mul_catalan_eq_centralBinom (j + 1)
  have h2 := succ_mul_catalan_eq_centralBinom j
  have h3 := Nat.succ_mul_centralBinom_succ j
  have key : (j + 1) * ((j + 2) * catalan (j + 1)) = (j + 1) * (2 * (2 * j + 1) * catalan j) := by
    have e1 : (j + 1 + 1) * catalan (j + 1) = Nat.centralBinom (j + 1) := h1
    have e2 : (j + 1) * catalan j = Nat.centralBinom j := h2
    have e3 : (j + 1) * Nat.centralBinom (j + 1) = 2 * (2 * j + 1) * Nat.centralBinom j := h3
    calc (j + 1) * ((j + 2) * catalan (j + 1)) = (j + 1) * Nat.centralBinom (j + 1) := by rw [<- e1]
      _ = 2 * (2 * j + 1) * Nat.centralBinom j := e3
      _ = 2 * (2 * j + 1) * ((j + 1) * catalan j) := by rw [e2]
      _ = (j + 1) * (2 * (2 * j + 1) * catalan j) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- the telescoping partner one step on:
    touchardPartner n (j + 1) * (n + 1) = -C(n + 1, 2j) 2^(n + 1 - 2j) C(j) (n + 1 - 2j)(n - 2j) -/
theorem all_touchard_partner_shape (n j : Nat) :
    touchardPartner n (j + 1) * ((n : Rat) + 1)
      = -((Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j) * (catalan j : Rat)
          * (((n : Rat) + 1 - 2 * j) * ((n : Rat) - 2 * j))) := by
  have hn : Ne ((n : Rat) + 1) 0 := by positivity
  have hdc : forall x : Rat, x / ((n : Rat) + 1) * ((n : Rat) + 1) = x := fun x => by field_simp
  unfold touchardPartner
  rw [hdc]
  push_cast
  by_cases hA : 2 * j + 2 <= n + 1
  . have hcat : ((j : Rat) + 2) * (catalan (j + 1) : Rat)
        = 2 * (2 * (j : Rat) + 1) * (catalan j : Rat) := by
      exact_mod_cast all_catalan_ratio j
    have hc1 := Nat.choose_succ_right_eq (n + 1) (2 * j)
    have hc2 := Nat.choose_succ_right_eq (n + 1) (2 * j + 1)
    have hc1q : (Nat.choose (n + 1) (2 * j + 1) : Rat) * (2 * (j : Rat) + 1)
        = (Nat.choose (n + 1) (2 * j) : Rat) * ((n : Rat) + 1 - 2 * j) := by
      have := congrArg (fun x : Nat => (x : Rat)) hc1
      push_cast [Nat.cast_sub (by omega : 2 * j <= n + 1)] at this
      linarith [this]
    have hc2q : (Nat.choose (n + 1) (2 * j + 1 + 1) : Rat) * (2 * (j : Rat) + 2)
        = (Nat.choose (n + 1) (2 * j + 1) : Rat) * ((n : Rat) - 2 * j) := by
      have := congrArg (fun x : Nat => (x : Rat)) hc2
      push_cast [Nat.cast_sub (by omega : 2 * j <= n)] at this
      linear_combination this
    have he : n + 1 - 2 * j = (n + 1 - 2 * (j + 1)) + 2 := by omega
    have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    rw [he, pow_add, hidx]
    linear_combination
      (-4 * ((j : Rat) + 1) * (Nat.choose (n + 1) (2 * j + 1 + 1) : Rat)
          * 2 ^ (n + 1 - 2 * (j + 1))) * hcat
      + (-2 * 2 ^ (n + 1 - 2 * (j + 1)) * (catalan j : Rat) * 2 * ((n : Rat) - 2 * j)) * hc1q
      + (-2 * 2 ^ (n + 1 - 2 * (j + 1)) * (catalan j : Rat) * 2 * (2 * (j : Rat) + 1)) * hc2q
  . have hz : Nat.choose (n + 1) (2 * (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]
    by_cases hB : 2 * j + 1 = n + 1
    . have e : ((n : Rat) - 2 * j) = 0 := by
        have : ((2 * j + 1 : Nat) : Rat) = ((n + 1 : Nat) : Rat) := by rw [hB]
        push_cast at this
        linarith
      rw [e]
      simp
    . by_cases hC : 2 * j = n + 1
      . have e : ((n : Rat) + 1 - 2 * j) = 0 := by
          have : ((2 * j : Nat) : Rat) = ((n + 1 : Nat) : Rat) := by rw [hC]
          push_cast at this
          linarith
        rw [e]
        simp
      . have h0 : Nat.choose (n + 1) (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [h0]
        simp

/-- Touchard's telescoping step: (n + 3) touchardTerm (n + 1) j - 2(2n + 3) touchardTerm n j
    = touchardPartner n (j + 1) - touchardPartner n j -/
theorem all_touchard_telescope (n j : Nat) :
    ((n : Rat) + 3) * touchardTerm (n + 1) j - 2 * (2 * (n : Rat) + 3) * touchardTerm n j
      = touchardPartner n (j + 1) - touchardPartner n j := by
  have hn : Ne ((n : Rat) + 1) 0 := by positivity
  have hF : touchardTerm n j = (Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j)
      * (catalan j : Rat) * ((n : Rat) + 1 - 2 * j) / (2 * ((n : Rat) + 1)) := by
    rw [eq_div_iff (by positivity)]
    exact all_touchard_term_shape n j
  have hG : touchardPartner n (j + 1) = -((Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j)
      * (catalan j : Rat) * (((n : Rat) + 1 - 2 * j) * ((n : Rat) - 2 * j))) / ((n : Rat) + 1) := by
    rw [eq_div_iff hn]
    exact all_touchard_partner_shape n j
  have hF1 : touchardTerm (n + 1) j
      = (Nat.choose (n + 1) (2 * j) : Rat) * 2 ^ (n + 1 - 2 * j) * (catalan j : Rat) := rfl
  rw [hF, hG, hF1]
  unfold touchardPartner
  field_simp
  ring

/-- Touchard's sum T(n) = sum over j <= n of C(n, 2j) 2^(n - 2j) C(j) -/
def touchardSum (n : Nat) : Rat := (Finset.range (n + 1)).sum (fun j => touchardTerm n j)

/-- its first-order recurrence, by telescoping: (n + 3) T(n + 1) = 2(2n + 3) T(n), for every n -/
theorem all_touchard_rec (n : Nat) :
    ((n : Rat) + 3) * touchardSum (n + 1) = 2 * (2 * (n : Rat) + 3) * touchardSum n := by
  have hsum := Finset.sum_range_sub (fun j => touchardPartner n j) (n + 2)
  have hl : (Finset.range (n + 2)).sum
      (fun j => ((n : Rat) + 3) * touchardTerm (n + 1) j - 2 * (2 * (n : Rat) + 3) * touchardTerm n j)
      = (Finset.range (n + 2)).sum (fun j => touchardPartner n (j + 1) - touchardPartner n j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact all_touchard_telescope n j
  rw [hsum] at hl
  have hG0 : touchardPartner n 0 = 0 := by unfold touchardPartner; simp
  have hGe : touchardPartner n (n + 2) = 0 := by
    unfold touchardPartner
    rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < 2 * (n + 2))]
    simp
  have hFe : touchardTerm n (n + 1) = 0 := by
    unfold touchardTerm
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * (n + 1))]
    simp
  rw [hG0, hGe, sub_zero, Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum,
    Finset.sum_range_succ (fun j => touchardTerm n j) (n + 1), hFe, add_zero] at hl
  unfold touchardSum
  linarith [hl]

/-- Touchard's identity, for every n: the sum of C(n, 2j) 2^(n - 2j) C(j) over j is C(n + 1) -/
theorem all_touchard (n : Nat) : touchardSum n = (catalan (n + 1) : Rat) := by
  refine all_rec1 touchardSum (fun m => (catalan (m + 1) : Rat))
    (fun m => 2 * (2 * (m : Rat) + 3) / ((m : Rat) + 3)) ?_ ?_ ?_ n
  . intro m
    have h := all_touchard_rec m
    have hm : Ne ((m : Rat) + 3) 0 := by positivity
    field_simp
    linarith [h]
  . intro m
    have h : ((m : Rat) + 3) * (catalan (m + 2) : Rat)
        = 2 * (2 * (m : Rat) + 3) * (catalan (m + 1) : Rat) := by
      exact_mod_cast all_catalan_rec m
    have hm : Ne ((m : Rat) + 3) 0 := by positivity
    field_simp
    linarith [h]
  . unfold touchardSum touchardTerm
    simp

/-- the sum over k of (-1)^(n - k) C(n, k) C(k, i) is 1 at i = n and 0 otherwise -/
theorem all_alt_choose (n i : Nat) :
    (Finset.range (n + 1)).sum
      (fun k => (-1 : Int) ^ (n - k) * ((Nat.choose n k : Int) * (Nat.choose k i : Int)))
      = if n = i then 1 else 0 := by
  by_cases hi : i <= n
  . rw [<- Finset.sum_range_add_sum_Ico _ (show i <= n + 1 by omega)]
    have h1 : (Finset.range i).sum
        (fun k => (-1 : Int) ^ (n - k) * ((Nat.choose n k : Int) * (Nat.choose k i : Int))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      simp [Nat.choose_eq_zero_of_lt hk]
    rw [h1, zero_add, Finset.sum_Ico_eq_sum_range]
    have h2 : forall t, t < n + 1 - i ->
        (-1 : Int) ^ (n - (i + t)) * ((Nat.choose n (i + t) : Int) * (Nat.choose (i + t) i : Int))
          = (Nat.choose n i : Int) * ((-1 : Int) ^ ((n - i) - t) * (Nat.choose (n - i) t : Int)) := by
      intro t ht
      have hc := Nat.choose_mul (n := n) (k := i + t) (s := i) (by omega)
      have e1 : i + t - i = t := by omega
      have e2 : n - (i + t) = (n - i) - t := by omega
      rw [e1] at hc
      rw [e2]
      have hc' : (Nat.choose n (i + t) : Int) * (Nat.choose (i + t) i : Int)
          = (Nat.choose n i : Int) * (Nat.choose (n - i) t : Int) := by exact_mod_cast hc
      rw [hc']
      ring
    rw [Finset.sum_congr rfl (fun t ht => h2 t (Finset.mem_range.mp ht)), <- Finset.mul_sum]
    have hN : n + 1 - i = (n - i) + 1 := by omega
    rw [hN]
    have hr2 : (Finset.range ((n - i) + 1)).sum (fun t => (-1 : Int) ^ ((n - i) - t) * (Nat.choose
        (n - i) t : Int))
        = (Finset.range ((n - i) + 1)).sum (fun t => (-1 : Int) ^ t * (Nat.choose (n - i) t : Int))
            := by
      rw [<- Finset.sum_range_reflect (fun t => (-1 : Int) ^ t * (Nat.choose (n - i) t : Int)) ((n
          - i) + 1)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      have e3 : (n - i) + 1 - 1 - t = (n - i) - t := by omega
      rw [e3, Nat.choose_symm (by omega)]
    rw [hr2, Int.alternating_sum_range_choose]
    by_cases hni : n = i
    . subst hni
      simp
    . have hne : Ne (n - i) 0 := by omega
      simp [hne, hni]
  . have hz : forall k, k < n + 1 -> Nat.choose k i = 0 := fun k hk => Nat.choose_eq_zero_of_lt (by
      omega)
    rw [Finset.sum_eq_zero (fun k hk => by rw [hz k (Finset.mem_range.mp hk)]; simp)]
    have hne : Ne n i := by omega
    simp [hne]

/-- the same sum in any commutative ring: (-1)^(n - k) C(n, k) C(k, i) over k is 1 at i = n, else 0 -/
theorem all_alt_choose_R {R : Type*} [CommRing R] (n i : Nat) :
    (Finset.range (n + 1)).sum (fun k => (-1 : R) ^ (n - k) * ((Nat.choose n k : R) * (Nat.choose k
        i : R)))
      = if n = i then 1 else 0 := by
  have h := congrArg (Int.cast : Int -> R) (all_alt_choose n i)
  push_cast at h
  rw [h]

/-- binomial inversion in any commutative ring: the signed binomial transform undoes the binomial
    transform -/
theorem all_binv {R : Type*} [CommRing R] (a : Nat -> R) (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (-1 : R) ^ (n - k) * (Nat.choose n k : R)
      * (Finset.range (k + 1)).sum (fun i => (Nat.choose k i : R) * a i)) = a n := by
  have hext : forall k, k < n + 1 ->
      (Finset.range (k + 1)).sum (fun i => (Nat.choose k i : R) * a i)
        = (Finset.range (n + 1)).sum (fun i => (Nat.choose k i : R) * a i) := by
    intro k hk
    apply Finset.sum_subset
    . intro x hx
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range]
      omega
    . intro x hx hnx
      rw [Finset.mem_range] at hx hnx
      rw [Nat.choose_eq_zero_of_lt (by omega : k < x)]
      simp
  rw [Finset.sum_congr rfl (fun k hk => by rw [hext k (Finset.mem_range.mp hk)])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hin : forall i, (Finset.range (n + 1)).sum
      (fun k => (-1 : R) ^ (n - k) * (Nat.choose n k : R) * ((Nat.choose k i : R) * a i))
      = (if n = i then 1 else 0) * a i := by
    intro i
    rw [<- all_alt_choose_R n i, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [Finset.sum_congr rfl (fun i _ => hin i)]
  simp

/-- the sum over k of C(n, k) C(k, s) is C(n, s) 2^(n - s) -/
theorem all_choose_two_pow (n s : Nat) :
    (Finset.range (n + 1)).sum (fun k => Nat.choose n k * Nat.choose k s) = Nat.choose n s * 2 ^ (n
        - s) := by
  by_cases hs : s <= n
  . rw [<- Finset.sum_range_add_sum_Ico _ (show s <= n + 1 by omega)]
    have h1 : (Finset.range s).sum (fun k => Nat.choose n k * Nat.choose k s) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      simp [Nat.choose_eq_zero_of_lt hk]
    rw [h1, zero_add, Finset.sum_Ico_eq_sum_range]
    have h2 : forall t, t < n + 1 - s ->
        Nat.choose n (s + t) * Nat.choose (s + t) s = Nat.choose n s * Nat.choose (n - s) t := by
      intro t _
      have hc := Nat.choose_mul (n := n) (k := s + t) (s := s) (by omega)
      have e1 : s + t - s = t := by omega
      rw [e1] at hc
      exact hc
    rw [Finset.sum_congr rfl (fun t ht => h2 t (Finset.mem_range.mp ht)), <- Finset.mul_sum]
    have hN : n + 1 - s = (n - s) + 1 := by omega
    rw [hN, Nat.sum_range_choose]
  . have hz : forall k, k < n + 1 -> Nat.choose k s = 0 := fun k hk => Nat.choose_eq_zero_of_lt (by
      omega)
    rw [Finset.sum_eq_zero (fun k hk => by rw [hz k (Finset.mem_range.mp hk)]; simp)]
    rw [Nat.choose_eq_zero_of_lt (by omega : n < s)]
    simp

/-- M(n), the sum of C(n, 2j) C(j) over j -/
def motzkin (n : Nat) : Rat := (Finset.range (n + 1)).sum (fun j => (Nat.choose n (2 * j) : Rat) *
    (catalan j : Rat))

/-- the binomial transform of the Motzkin numbers is Touchard's sum -/
theorem all_binom_motzkin (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Rat) * motzkin k) = touchardSum n := by
  unfold motzkin touchardSum touchardTerm
  have hext : forall k, k < n + 1 ->
      (Finset.range (k + 1)).sum (fun j => (Nat.choose k (2 * j) : Rat) * (catalan j : Rat))
        = (Finset.range (n + 1)).sum (fun j => (Nat.choose k (2 * j) : Rat) * (catalan j : Rat)) := by
    intro k hk
    apply Finset.sum_subset
    . intro x hx
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range]
      omega
    . intro x hx hnx
      rw [Finset.mem_range] at hx hnx
      rw [Nat.choose_eq_zero_of_lt (by omega : k < 2 * x)]
      simp
  rw [Finset.sum_congr rfl (fun k hk => by rw [hext k (Finset.mem_range.mp hk)])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := all_choose_two_pow n (2 * j)
  have hq : (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Rat) * (Nat.choose k (2 * j) : Rat))
      = (Nat.choose n (2 * j) : Rat) * 2 ^ (n - 2 * j) := by exact_mod_cast h
  calc (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Rat) * ((Nat.choose k (2 * j) : Rat)
      * (catalan j : Rat)))
      = (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Rat) * (Nat.choose k (2 * j) : Rat))
          * (catalan j : Rat) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = (Nat.choose n (2 * j) : Rat) * 2 ^ (n - 2 * j) * (catalan j : Rat) := by rw [hq]

/-- step 32, for every n: the inverse binomial transform of C(k + 1) is M(n); the step's own theorem
    above takes the list A000108_1 to the list A001006, on 40 terms -/
theorem all_step32_binomialInverse (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * (catalan
        (k + 1) : Rat))
      = motzkin n := by
  have h : forall k, (catalan (k + 1) : Rat) = (Finset.range (k + 1)).sum (fun i => (Nat.choose k i
      : Rat) * motzkin i) := by
    intro k
    rw [all_binom_motzkin k, all_touchard k]
  simp_rw [h]
  exact all_binv motzkin n

/-- step 33, for every n: the inverse binomial transform of M is C(n / 2) at even n and 0 at odd n; the
    step's own theorem above takes the list A001006 to the list A126120, on 40 terms -/
theorem all_step33_binomialInverse (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * motzkin k)
      = if n % 2 = 0 then (catalan (n / 2) : Rat) else 0 := by
  unfold motzkin
  have hext : forall k, k < n + 1 ->
      (Finset.range (k + 1)).sum (fun j => (Nat.choose k (2 * j) : Rat) * (catalan j : Rat))
        = (Finset.range (n + 1)).sum (fun j => (Nat.choose k (2 * j) : Rat) * (catalan j : Rat)) := by
    intro k hk
    apply Finset.sum_subset
    . intro x hx
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range]
      omega
    . intro x hx hnx
      rw [Finset.mem_range] at hx hnx
      rw [Nat.choose_eq_zero_of_lt (by omega : k < 2 * x)]
      simp
  rw [Finset.sum_congr rfl (fun k hk => by rw [hext k (Finset.mem_range.mp hk)])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hin : forall j, (Finset.range (n + 1)).sum
      (fun k => (-1 : Rat) ^ (n - k) * (Nat.choose n k : Rat) * ((Nat.choose k (2 * j) : Rat) *
          (catalan j : Rat)))
      = (if n = 2 * j then 1 else 0) * (catalan j : Rat) := by
    intro j
    rw [<- all_alt_choose_R n (2 * j), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [Finset.sum_congr rfl (fun j _ => hin j)]
  by_cases he : n % 2 = 0
  . have hn2 : n = 2 * (n / 2) := by omega
    simp only [he, ite_true]
    rw [Finset.sum_eq_single (n / 2)]
    . simp [hn2.symm]
    . intro b _ hb
      have hne : Ne n (2 * b) := by omega
      simp [hne]
    . intro hn
      rw [Finset.mem_range] at hn
      omega
  . simp only [he, ite_false]
    apply Finset.sum_eq_zero
    intro j _
    have hne : Ne n (2 * j) := by omega
    simp [hne]

/-! ### 5. Algebraic Atoms over an Arbitrary Field
`e_k = [1; z^k - 1]`, `l_k = [0; (z^k - 1)/k] = k (e_k - 1)`, `m_k = [0; z^k/k] = l_k / e_k`. -/

section Atoms
variable {K : Type*} [Field K]

/-- the atom e_k = [1; z^k - 1]: 1 + 1/(z^k - 1) = z^k/(z^k - 1), in any field, where z^k is not 1 -/
theorem atom_e (z : K) (k : Nat) (h : Ne (z ^ k - 1) 0) :
    1 + 1 / (z ^ k - 1) = z ^ k / (z ^ k - 1) := by
  field_simp
  ring

/-- the atom l_k = [0; (z^k - 1)/k] = k (e_k - 1), where k is not 0 and z^k is not 1 -/
theorem atom_l (z : K) (k : Nat) (hk : Ne (k : K) 0) (h : Ne (z ^ k - 1) 0) :
    1 / ((z ^ k - 1) / k) = k * (z ^ k / (z ^ k - 1) - 1) := by
  field_simp
  ring

/-- the atom m_k = [0; z^k/k] = l_k / e_k, where k and z are not 0 and z^k is not 1 -/
theorem atom_m (z : K) (k : Nat) (hk : Ne (k : K) 0) (hz : Ne z 0) (h : Ne (z ^ k - 1) 0) :
    1 / (z ^ k / k) = (k / (z ^ k - 1)) / (z ^ k / (z ^ k - 1)) := by
  have hzk : Ne (z ^ k) 0 := pow_ne_zero k hz
  field_simp

end Atoms

end Origami

/-! # The elements -/

namespace PeriodicTable

/-! ## G. Carbon's address among the elements: the closures' address, then 2, 4 -/

/-- subshells (n, l) sorted by (n + l, n), Madelung's rule: runs n + l = k, k < K; run N + 1 corresponds to the
partitions of N into parts 1 and 2 (run_is_partitions) -/
def madelungTo (K : Nat) : List (Nat × Nat) :=
  (List.range K).flatMap fun k => (List.range (k + 1)).filterMap fun n => if k < 2 * n then some (n, k - n) else none

/-- its first nine runs, 1s to 8s: the subshells the table's places read -/
def madelung : List (Nat × Nat) := madelungTo 9

def fill : List (Nat × Nat) → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | (n, l) :: rest, z => (n, l, min z (2 * (2 * l + 1))) :: fill rest (z - min z (2 * (2 * l + 1)))

/-- the shell closures, restated from Electrons.el_closures -/
def closes : List Nat := [2, 10, 18, 36, 54, 86, 118]

def valence (z : Nat) : Nat := min (z - (closes.filter fun c => decide (c < z)).foldl max 0) ((closes.filter fun c => decide (z ≤ c)).foldl min 1000 - z)

/-- period N's length 2 a(N)², a(N) = ⌊N/2⌋ + 1 the number of partitions of N into parts at most 2 (1, 1, 2, 2, 3,
3, …); Madelung's runs regrouped -/
def periodLen (N : Nat) : Nat := 2 * (N / 2 + 1) ^ 2

/-- the closures are the running sums of the periods' lengths -/
theorem closes_are_period_sums :
    (List.range 7).map (fun k => ((List.range (k + 1)).map fun i => periodLen (i + 1)).sum) = closes := by decide

/-- an element's period and position: the closures below it, plus one; its distance past the last of them -/
def seat (z : Nat) : Nat × Nat :=
  ((closes.filter fun c => decide (c < z)).length + 1, z - (closes.filter fun c => decide (c < z)).foldl max 0)

/-- carbon: period 2, position 4; silicon: period 3, position 4; both valence 4 -/
theorem carbon_seat : seat 6 = (2, 4) ∧ seat 14 = (3, 4) ∧ valence 6 = 4 ∧ valence 14 = 4 := by decide

/-- every element's valence, the distance to the nearest closure, is read off its position j: min(j, L − j), L the
period's length, Z = 1 … 118 -/
theorem valence_from_seat : (List.range 118).all (fun i =>
    valence (i + 1) == min (seat (i + 1)).2 (periodLen (seat (i + 1)).1 - (seat (i + 1)).2)) = true := by decide +kernel

/-- 118 elements, 118 distinct (period, position) pairs -/
theorem seats_distinct : ((List.range 118).map fun i => seat (i + 1)).Nodup := by decide +kernel

/-! ## M. The periodic table's places, computed

* Madelung's order in blocks: block k holds the subshells (n, l) with n + l = k and l < n, by n; its s subshell last.
* Laws, every n, by induction: a shell's subshells hold 2n² states; block k, 2⌈k/2⌉²; period N (the s subshell of
  shell N, then block N + 1 up to its s), 2 a(N)². Every period from the second ends on its shell's p subshell. The
  states before each s subshell are the closures; their closed form continues them past 118.
* Place, from the last subshell (n, l, e), e its electrons, and the period N: f on row N + 2, column 2 + e; s in
  column e, a period's last element in 18; p in column 12 + e; d in column 2 + e. This 18-column frame holds while
  l ≤ 3, the order's first nine blocks.
* Range: to Z = 118, the largest Z with γ₁ = √(1 − (Zα)²) ≥ 1/2 at 1/α = 662194096285/4832263787, where the named
  elements also end. Compared last: the measured valences, inputs. -/

/-- Madelung's block k: the subshells (k − l, l) with l < k − l, by n, the s subshell last -/
def block (k : Nat) : List (Nat × Nat) := ((List.range ((k + 1) / 2)).map fun l => (k - l, l)).reverse

/-- Madelung's run n + l = k is block k, every k: its subshells, k < 2n, n rising, are (k − l, l), l falling to 0 -/
theorem madelung_run (k : Nat) : ((List.range (k + 1)).filterMap fun n => if k < 2 * n then some (n, k - n) else none) = block k := by
  have hs : k + 1 = (k / 2 + 1) + (k + 1) / 2 := by omega
  have h0 : (List.range (k / 2 + 1)).filterMap (fun n => if k < 2 * n then some (n, k - n) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro n hn
    rw [List.mem_range] at hn
    simp [show ¬k < 2 * n by omega]
  have key : ∀ l : List ℕ, ((l.map (k / 2 + 1 + ·)).filterMap fun n => if k < 2 * n then some (n, k - n) else none) =
      l.map fun i => (k / 2 + 1 + i, k - (k / 2 + 1 + i)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih, show k < 2 * (k / 2 + 1 + a) by omega]
  rw [hs, List.range_add, List.filterMap_append, h0, List.nil_append, key, block]
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_map, List.length_range, List.length_reverse] at hi1 hi2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_map, List.length_range, Prod.mk.injEq]
    constructor <;> omega

/-- section G's order is the blocks, every number of runs K: its first nine are 1s to 8s, and it continues block by
block past them (the periodic table page's "the (n + l, n) order, generated") -/
theorem madelung_is_blocks (K : Nat) : madelungTo K = (List.range K).flatMap block := by
  simp only [madelungTo, madelung_run]

/-- run n + l = N + 1 corresponds to the partitions of N into parts 1 and 2: subshell (n, l) ↦ (n − l − 1 ones,
l twos), l rising 0 … ⌊N/2⌋, every N -/
theorem run_is_partitions (N : Nat) :
    (block (N + 1)).reverse.map (fun p => (p.1 - p.2 - 1, p.2)) = (List.range (N / 2 + 1)).map (fun l => (N - 2 * l, l)) ∧
    ((List.range (N / 2 + 1)).map fun l => (N - 2 * l, l)).all (fun p => p.1 + 2 * p.2 = N) := by
  have h : (N + 1 + 1) / 2 = N / 2 + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [block, h, List.reverse_reverse, List.map_map]
    apply List.map_congr_left
    intro l hl
    rw [List.mem_range] at hl
    show (N + 1 - l - l - 1, l) = (N - 2 * l, l)
    congr 1
    omega
  · rw [List.all_eq_true]
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range] at hl
    show decide (N - 2 * l + 2 * l = N) = true
    simp only [decide_eq_true_eq]
    omega

/-- a subshell's states, 2(2l + 1) -/
def cap (p : Nat × Nat) : Nat := 2 * (2 * p.2 + 1)

/-- the odd numbers sum to squares: the subshells l = 0 … m − 1 hold 2m² states, every m; at m = n, a shell's 2n² -/
theorem odd_seats_square (m : Nat) : ((List.range m).map fun l => 2 * (2 * l + 1)).sum = 2 * m ^ 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- block k holds 2⌈k/2⌉² states, every k -/
theorem block_seats (k : Nat) : ((block k).map cap).sum = 2 * ((k + 1) / 2) ^ 2 := by
  simpa [block, cap, Function.comp_def] using odd_seats_square ((k + 1) / 2)

/-- block k + 1 before its s subshell: (k − l, l + 1) for l from ⌊k/2⌋ − 1 down to 0 -/
def nonS (k : Nat) : List (Nat × Nat) := ((List.range (k / 2)).map fun l => (k - l, l + 1)).reverse

/-- every block ends on its s subshell, for every k -/
theorem block_ends_on_s (k : Nat) : block (k + 1) = nonS k ++ [(k + 1, 0)] := by
  have h : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
  rw [block, h, List.range_succ_eq_map]
  simp [nonS, Function.comp_def]

/-- period N: the s subshell of shell N, then block N + 1 up to its s -/
def period (N : Nat) : List (Nat × Nat) := (N, 0) :: nonS N

/-- period N holds 2 a(N)² states, a(N) = ⌊N/2⌋ + 1, every N: section G's period length -/
theorem period_seats (N : Nat) : ((period N).map cap).sum = periodLen N := by
  have h1 := block_seats (N + 1)
  have h2 : (N + 1 + 1) / 2 = N / 2 + 1 := by omega
  rw [block_ends_on_s, h2, List.map_append, List.sum_append] at h1
  have h3 : (([(N + 1, 0)] : List (Nat × Nat)).map cap).sum = 2 := rfl
  rw [h3] at h1
  show cap (N, 0) + ((nonS N).map cap).sum = periodLen N
  rw [show cap (N, 0) = 2 from rfl, periodLen]
  omega

/-- from the second period on, every period ends on its own shell's p subshell (N, 1), every N ≥ 2: its last element
completes that subshell, column 12 + 6 = 18 -/
theorem period_ends_on_p (N : Nat) (h : 2 ≤ N) : (period N).getLast? = some (N, 1) := by
  obtain ⟨m, hm⟩ : ∃ m, N / 2 = m + 1 := ⟨N / 2 - 1, by omega⟩
  simp [period, nonS, hm, List.range_succ_eq_map, List.getLast?_cons]

/-- the states before the s subshell of shell N + 1 are the N-th closure, the running sum of the periods' lengths,
every N: the order and the closures count the same periods -/
theorem s_opens_every_period (N : Nat) :
    (((List.range (N + 1)).flatMap block ++ (block (N + 1)).dropLast).map cap).sum =
      ((List.range N).map fun i => periodLen (i + 1)).sum := by
  induction N with
  | zero => decide
  | succ N ih =>
    have e1 : (List.range (N + 1 + 1)).flatMap block = (List.range (N + 1)).flatMap block ++ block (N + 1) := by
      rw [List.range_succ, List.flatMap_append]
      simp
    have e2 : ∀ k, (block (k + 1)).dropLast = nonS k := fun k => by rw [block_ends_on_s, List.dropLast_concat]
    have e3 : ((block (N + 1)).map cap).sum = ((nonS N).map cap).sum + 2 := by
      rw [block_ends_on_s, List.map_append, List.sum_append]
      rfl
    have e4 : 2 + ((nonS (N + 1)).map cap).sum = periodLen (N + 1) := period_seats (N + 1)
    have e5 : ((List.range (N + 1)).map fun i => periodLen (i + 1)).sum =
        ((List.range N).map fun i => periodLen (i + 1)).sum + periodLen (N + 1) := by
      rw [List.range_succ, List.map_append, List.sum_append]
      simp
    rw [e2, List.map_append, List.sum_append] at ih
    rw [e1, e2, List.append_assoc, List.map_append, List.sum_append, List.map_append, List.sum_append, e3, e5, ← e4]
    omega

/-- the N-th closure, the running sum of the first N periods' lengths -/
def closing (N : Nat) : Nat := ((List.range N).map fun i => periodLen (i + 1)).sum

/-- the closures for every period, in closed form: 3 c(2k) + 6 = 2k(k + 1)(2k + 1) + 6(k + 1)², and c(2k + 1) = c(2k) + 2(k + 1)² -/
theorem closures_closed_form (k : Nat) :
    3 * closing (2 * k) + 6 = 2 * k * (k + 1) * (2 * k + 1) + 6 * (k + 1) ^ 2 ∧
      closing (2 * k + 1) = closing (2 * k) + 2 * (k + 1) ^ 2 := by
  have step : ∀ n, closing (n + 1) = closing n + periodLen (n + 1) := fun n => by
    simp [closing, List.range_succ]
  have p1 : ∀ k, periodLen (2 * k + 1) = 2 * (k + 1) ^ 2 := fun k => by
    rw [periodLen, show (2 * k + 1) / 2 = k by omega]
  have p2 : ∀ k, periodLen (2 * k + 1 + 1) = 2 * (k + 2) ^ 2 := fun k => by
    rw [periodLen, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  refine ⟨?_, by rw [step, p1]⟩
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, step, p2, step, p1]
    nlinarith [ih]

/-- the closures continue for every period N, in one closed form: 3 c(N) = 4k³ + 12k² + 14k + 6r(k + 1)²,
k = ⌊N/2⌋, r = N mod 2 (the periodic table page's closures, the running sums of 2 a(N)², a(N) = ⌊N/2⌋ + 1) -/
theorem closures_continue (N : Nat) :
    3 * closing N = 4 * (N / 2) ^ 3 + 12 * (N / 2) ^ 2 + 14 * (N / 2) + 6 * (N % 2) * (N / 2 + 1) ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · obtain ⟨h1, -⟩ := closures_closed_form k
    rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
    nlinarith [h1]
  · obtain ⟨h1, h2⟩ := closures_closed_form k
    rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega, h2]
    nlinarith [h1]

/-- the closed form's first instances: the periods hold 2, 8, 8, 18, 18, 32, 32, then 50, 50 states; the closures
continue past oganesson, the eighth and ninth 168 and 218 -/
theorem closures_first_nine : (List.range 9).map (fun i => periodLen (i + 1)) = [2, 8, 8, 18, 18, 32, 32, 50, 50] ∧
    (List.range 9).map (fun k => closing (k + 1)) = closes ++ [168, 218] := by decide

/-- the frame's reach: the order's first nine blocks hold 120 states, every subshell s, p, d or f; block 9 opens on
(5, 4), the first g subshell, past the table's edge and past 8s, its 18 states more than the 16 columns from 3 to 18:
the place rule is the frame to the edge, not a law past it -/
theorem frame_ends_at_g : (((List.range 9).flatMap block).map cap).sum = 120 ∧
    ((List.range 9).flatMap block).all (fun p => decide (p.2 ≤ 3)) = true ∧ (block 9).head? = some (5, 4) ∧ cap (5, 4) = 18 := by decide

/-- 1/α = p/q in lowest terms, (m² + n²)/(2mn) at (m, n) = (1150813, 4199), from the fine-structure file; this p -/
def alphaInvP : Nat := (1150813 ^ 2 + 4199 ^ 2) / 2

/-- and this denominator q, mn -/
def alphaInvQ : Nat := 1150813 * 4199

/-- the largest z below hi with 4z²q² ≤ 3p², by bisection between lo, where it holds, and hi, where it fails; fuel:
the halvings allowed -/
def edgeAux (p q : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if 4 * ((lo + hi) / 2) ^ 2 * q ^ 2 ≤ 3 * p ^ 2 then edgeAux p q f ((lo + hi) / 2) hi else edgeAux p q f lo ((lo + hi) / 2)

/-- the largest Z with γ₁ = √(1 − (Zα)²) ≥ 1/2, that is 4Z²q² ≤ 3p², at 1/α = p/q; the bisection starts
between 0 and p + 1, where it fails, and p halvings are more than it takes -/
def zEdge : Nat := edgeAux alphaInvP alphaInvQ alphaInvP 0 (alphaInvP + 1)

/-- the edge is Z = 118: γ₁ ≥ 1/2 there, not at 119; γ₁ is real, Zα < 1 (the point-Coulomb Dirac 1s bound), through
Z = 137, not at 138; 1/α = 662194096285/4832263787 -/
theorem table_edge : zEdge = 118 ∧ 4 * 118 ^ 2 * alphaInvQ ^ 2 ≤ 3 * alphaInvP ^ 2 ∧ 3 * alphaInvP ^ 2 < 4 * 119 ^ 2 * alphaInvQ ^ 2 ∧
    137 * alphaInvQ < alphaInvP ∧ alphaInvP < 138 * alphaInvQ ∧ alphaInvP = 662194096285 ∧ alphaInvQ = 4832263787 := by decide +kernel

/-- an element's subshells in the (n + l, n) order, each (n, l, e) with e its electrons, the empty ones dropped -/
def subshells (z : Nat) : List (Nat × Nat × Nat) := (fill madelung z).filter fun (_, _, t) => decide (0 < t)

/-- the electrons in the subshells begun at or past the closure before z -/
def pastClosure (z : Nat) : Nat :=
  ((subshells z).foldl (fun (s : Nat × Nat) (c : Nat × Nat × Nat) =>
    (s.1 + c.2.2, if z - (seat z).2 ≤ s.1 then s.2 + c.2.2 else s.2)) (0, 0)).2

/-- each element to the edge places all its electrons; those past the closure before it number its position j -/
theorem electrons_seated : (List.range zEdge).all (fun i =>
    ((subshells (i + 1)).map fun c => c.2.2).sum == i + 1 && pastClosure (i + 1) == (seat (i + 1)).2) = true := by decide +kernel

/-- an element's place, (row, column), from its last subshell (n, l, e) and its period N -/
def place (z : Nat) : Nat × Nat :=
  match (subshells z).getLastD (0, 0, 0) with
  | (_, l, e) =>
    if l = 3 then ((seat z).1 + 2, 2 + e)
    else ((seat z).1, if l = 0 then (if z = closes.getD ((seat z).1 - 1) 0 then 18 else e) else if l = 1 then 12 + e else 2 + e)

/-- the elements to the edge take distinct places, every column from 1 to 18 used and none past it -/
theorem places_distinct : ((List.range zEdge).map fun i => place (i + 1)).Nodup ∧
    (List.range zEdge).all (fun i => decide (1 ≤ (place (i + 1)).2 ∧ (place (i + 1)).2 ≤ 18)) = true ∧
    (List.range 18).all (fun c => (List.range zEdge).any fun i => (place (i + 1)).2 == c + 1) = true := by decide +kernel

/-- each closure to the edge, helium 2 to oganesson 118, ends its row in column 18 -/
theorem closures_in_column_18 : closes.all (fun c => (place c).2 == 18) = true := by decide +kernel

/-- column 3 of the fourth to seventh rows holds exactly Z = 21, 39, 71, 103: the order puts lutetium and lawrencium, not lanthanum and
actinium, under yttrium -/
theorem group_three : ((List.range zEdge).map (· + 1)).filter (fun z => (place z).2 == 3 && decide (4 ≤ (place z).1 ∧ (place z).1 ≤ 7)) =
    [21, 39, 71, 103] := by decide +kernel

/-- the f rows: the eighth holds exactly Z = 57 … 70, lanthanum first, the ninth exactly Z = 89 … 102, actinium first, and none lies
below them -/
theorem f_rows : ((List.range zEdge).map (· + 1)).filter (fun z => (place z).1 == 8) = List.range' 57 14 ∧
    ((List.range zEdge).map (· + 1)).filter (fun z => (place z).1 == 9) = List.range' 89 14 ∧
    (List.range zEdge).all (fun i => decide ((place (i + 1)).1 ≤ 9)) = true := by decide +kernel

/-- carbon at (2, 14), silicon under it at (3, 14) -/
theorem carbon_silicon_place : place 6 = (2, 14) ∧ place 14 = (3, 14) := by decide +kernel

/-- input, compared last: the measured valences of hydrogen to carbon -/
def input_valences_H_to_C : List Nat := [1, 0, 1, 2, 3, 4]

/-- input, compared last: iron's measured valences -/
def input_iron_valences : List Nat := [2, 3]

/-- the distance to the nearest closure reads hydrogen to carbon as measured, and departs at iron, period 4,
position 8: 8 against 2 and 3, the transition block -/
theorem valence_compared_last : (List.range 6).map (fun i => valence (i + 1)) = input_valences_H_to_C ∧
    seat 26 = (4, 8) ∧ valence 26 = 8 ∧ valence 26 ∉ input_iron_valences := by decide

/-! ## O. Sizes and lines: the one-electron ion at nuclear charge Z, exact over ℚ -/

/-- its level n, in hartree: −Z²/(2n²) -/
def ionLevel (Z : ℚ) (n : ℕ) : ℚ := -Z ^ 2 / (2 * (n : ℚ) ^ 2)

/-- the line from level i down to level j, in hartree: Z² (1/j² − 1/i²)/2 -/
def ionLine (Z : ℚ) (i j : ℕ) : ℚ := Z ^ 2 * (1 / (j : ℚ) ^ 2 - 1 / (i : ℚ) ^ 2) / 2

/-- a line is the difference of its two levels, for every Z and every pair of levels -/
theorem line_is_level_difference (Z : ℚ) (i j : ℕ) : ionLine Z i j = ionLevel Z i - ionLevel Z j := by
  unfold ionLine ionLevel
  ring

/-- 0 < n < n', Z ≠ 0: −Z²/(2n²) < −Z²/(2n'²); in a run's tie, smaller n is the lower level -/
theorem ionLevel_rises (Z : ℚ) (hZ : Z ≠ 0) (n n' : ℕ) (h0 : 0 < n) (h : n < n') : ionLevel Z n < ionLevel Z n' := by
  unfold ionLevel
  have hZ2 : 0 < Z ^ 2 := by positivity
  have hn : (0 : ℚ) < n := by exact_mod_cast h0
  have hnn : (n : ℚ) < n' := by exact_mod_cast h
  have hd : 2 * (n : ℚ) ^ 2 < 2 * (n' : ℚ) ^ 2 := by nlinarith
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hZ2 (by positivity) hd

/-- every ion's lines are hydrogen's times Z²: one pattern, scaled, so each tile's strip shows the same series -/
theorem lines_scale_Z_squared (Z : ℚ) (i j : ℕ) : ionLine Z i j = Z ^ 2 * ionLine 1 i j := by
  unfold ionLine
  ring

/-- so Balmer-α over Lyman-α is 5/27, at every Z ≠ 0 -/
theorem balmer_over_lyman (Z : ℚ) (hZ : Z ≠ 0) : ionLine Z 3 2 / ionLine Z 2 1 = 5 / 27 := by
  unfold ionLine
  field_simp
  ring

/-- a cut's true size: the shape (n, l), read in R = 2Zr/n, has radius c there, so n c/(2Z) in r -/
def trueSize (n : ℕ) (c Z : ℚ) : ℚ := n * c / (2 * Z)

/-- helium's 1s is hydrogen's at exactly half the size, for every radius c ≠ 0 the shape is read at -/
theorem helium_half_hydrogen (c : ℚ) (hc : c ≠ 0) : trueSize 1 c 2 / trueSize 1 c 1 = 1 / 2 := by
  unfold trueSize
  field_simp

/-! ## P. The address map: each element at its address, the closures' address then N, j

* The page's second picture draws element Z = 1 … 137 from its address's last two labels alone: N, its period, the
  first whose closure reaches Z; j, its position, Z less the closure before; L = 2 a(N)², the period's length.
* Spiral: Z at radius N − 1 + j/L and turn j/L mod 1, two rationals. Valence: the turn's distance from the closures'
  ray. Hyperedges: read off N.j. Stair: the spiral lifted to height N − 1 + j/L.
* The closures are section M's `closing`, every period, so the map runs past 118 to 137:
  the last Z with Zα < 1 at that (m, n). -/

/-- element z's period N, the first whose closure reaches z -/
def periodOf (z : Nat) : Nat := ((List.range (z + 1)).find? fun N => decide (z ≤ closing N)).getD 0

/-- its position j, z less the closure before -/
def seatOf (z : Nat) : Nat := z - closing (periodOf z - 1)

/-- its period's length L, 2 a(N)² -/
def lenOf (z : Nat) : Nat := periodLen (periodOf z)

/-- the closures' address past the root mark ॐ: their J-fraction word alone, since it terminates (the fold list's
addresses since 2026-11-13); copied from the fold list, whose check holds this line to it -/
def closuresAt : List String := ["2×5,-16,-53/16,135/256,-397/2160,-4624/18225…"]

/-- an element's address past ॐ: the closures' address, then its period N and its position j -/
def address (z : Nat) : List String := closuresAt ++ [toString (periodOf z), toString (seatOf z)]

/-- the spiral's radius, N − 1 + j/L, exact -/
def radius (z : Nat) : ℚ := (periodOf z : ℚ) - 1 + (seatOf z : ℚ) / (lenOf z : ℚ)

/-- the spiral's turn, j/L mod 1, exact -/
def turn (z : Nat) : ℚ := Int.fract ((seatOf z : ℚ) / (lenOf z : ℚ))

/-- the map's last element ⌊p/q⌋ = ⌊1/α⌋: the last Z with Zα < 1 (section M's edge: real through 137, not at 138) -/
def zLast : Nat := alphaInvP / alphaInvQ

/-- the turn is the position's remainder mod the period's length, over that length, every z -/
theorem turn_is_remainder (z : Nat) : turn z = ((seatOf z % lenOf z : ℕ) : ℚ) / (lenOf z : ℚ) :=
  Int.fract_div_natCast_eq_div_natCast_mod

/-- a statement decided on 1 … n holds for each z from 1 to n -/
theorem of_all_range {P : Nat → Prop} [DecidablePred P] (n : Nat) (h : (List.range n).all (fun i => decide (P (i + 1))) = true) :
    ∀ z, 1 ≤ z → z ≤ n → P z := by
  intro z h1 h2
  have := List.all_eq_true.mp h (z - 1) (List.mem_range.mpr (by omega))
  rw [show z - 1 + 1 = z by omega] at this
  exact of_decide_eq_true this

/-- every element to 137 has its address, its position j from 1 to L: carbon at the closures' address then
2, 4; silicon then 3, 4; Z = 137 then 8, 19, in a period of 50. To 118 its (N, j) is section G's (the page's
"element Z at its ID") -/
theorem address_map_places : zLast = 137 ∧ address 6 = closuresAt ++ ["2", "4"] ∧ address 14 = closuresAt ++ ["3", "4"] ∧
    address 137 = closuresAt ++ ["8", "19"] ∧
    lenOf 137 = 50 ∧ (List.range 137).all (fun i => decide (1 ≤ seatOf (i + 1) ∧ seatOf (i + 1) ≤ lenOf (i + 1))) = true ∧
    (List.range 118).all (fun i => (periodOf (i + 1), seatOf (i + 1)) == seat (i + 1)) = true := by decide +kernel

/-- the radius rises at every step, Z = 1 … 137 -/
theorem spiral_steps : (List.range 136).all (fun i => decide (radius (i + 1) < radius (i + 1 + 1))) = true := by decide +kernel

/-- Z grows with the radius: Z < Z′ gives radius Z < radius Z′ for all 1 ≤ Z < Z′ ≤ 137, hydrogen innermost at 1/2
(the page's "Z increases with the radius" and the stair's "hydrogen lowest") -/
theorem spiral_rises (a b : Nat) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 137) : radius a < radius b := by
  have st := of_all_range (P := fun z => radius z < radius (z + 1)) 136 spiral_steps
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact lt_trans (ih h (by omega)) (st b (by omega) (by omega))
    · subst h
      exact st a ha (by omega)

/-- turn 0 holds exactly the closures to 137, helium to oganesson, each at radius N, its period (the page's "every
noble-gas closure on turn 0 at radius N, and no other element on turn 0") -/
theorem turn_zero_at_closures : (∀ z, 1 ≤ z → z ≤ 137 → (turn z = 0 ↔ z ∈ closes)) ∧ closes.all (fun c => radius c == (periodOf c : ℚ)) = true := by
  refine ⟨fun z h1 h2 => ?_, by decide +kernel⟩
  rw [turn_is_remainder]
  revert z
  exact of_all_range (P := fun z => ((seatOf z % lenOf z : ℕ) : ℚ) / (lenOf z : ℚ) = 0 ↔ z ∈ closes) 137 (by decide +kernel)

/-- valence is the turn's distance from the closures' ray: L · min(turn, 1 − turn) = min(j, L − j) for Z = 1 … 137
(the page's "valence as the turn distance from the closure ray") -/
theorem valence_is_turn_distance : ∀ z, 1 ≤ z → z ≤ 137 →
    (lenOf z : ℚ) * min (turn z) (1 - turn z) = ((min (seatOf z) (lenOf z - seatOf z) : ℕ) : ℚ) := by
  intro z h1 h2
  rw [turn_is_remainder]
  revert z
  exact of_all_range (P := fun z => (lenOf z : ℚ) * min (((seatOf z % lenOf z : ℕ) : ℚ) / (lenOf z : ℚ))
    (1 - ((seatOf z % lenOf z : ℕ) : ℚ) / (lenOf z : ℚ)) = ((min (seatOf z) (lenOf z - seatOf z) : ℕ) : ℚ)) 137 (by decide +kernel)

/-- the mid-period positions j = L − j to 137 are Z = 1, 6, 14, 27, 45, 70, 102, each at turn 1/2; carbon at radius
3/2 and silicon at 5/2, both at turn 1/2 (the page's "carbon and silicon sit at turn ½") -/
theorem mid_period_seats : ((List.range 137).map (· + 1)).filter (fun z => 2 * seatOf z == lenOf z) = [1, 6, 14, 27, 45, 70, 102] ∧
    ((List.range 137).map (· + 1)).all (fun z => 2 * seatOf z != lenOf z || turn z == 1 / 2) = true ∧
    radius 6 = 3 / 2 ∧ radius 14 = 5 / 2 ∧ turn 6 = 1 / 2 ∧ turn 14 = 1 / 2 := by
  simp only [turn_is_remainder]
  decide +kernel

/-- element z's hyperedges, (kind, value): its period (0, N); its nearest closure (1, c), both at a mid-period
position; its valence (2, min(j, L − j)); its position (3, j) -/
def hyperOf (z : Nat) : List (Nat × Nat) :=
  [(0, periodOf z)] ++
    (if 2 * seatOf z < lenOf z then [(1, closing (periodOf z - 1))] else if lenOf z < 2 * seatOf z then [(1, closing (periodOf z))]
      else [(1, closing (periodOf z - 1)), (1, closing (periodOf z))]) ++
    [(2, min (seatOf z) (lenOf z - seatOf z)), (3, seatOf z)]

/-- every element's hyperedges to the map's last, each as often as it has members -/
def allHyper : List (Nat × Nat) := (List.range zLast).flatMap fun i => hyperOf (i + 1)

/-- the hyperedges of two elements or more, each once -/
def hyperedges : List (Nat × Nat) := allHyper.dedup.filter fun k => decide (2 ≤ allHyper.count k)

/-- 8 periods, 7 nearest closures, 17 valences and 32 positions join two elements or more: 64 hyperedges
(the page's "64 read off N.j") -/
theorem hyperedge_counts : [0, 1, 2, 3].map (fun t => (hyperedges.filter fun k => k.1 == t).length) = [8, 7, 17, 32] ∧
    hyperedges.length = 64 := by decide +kernel

/-- an element's degree on the map, its hyperedges of two elements or more -/
def degOf (z : Nat) : Nat := ((hyperOf z).filter hyperedges.contains).length

/-- each incidence of the map, a hyperedge e of two elements or more with a member v, as the pair (|e| · deg v, the element) -/
def incidences : List (Nat × Nat) :=
  (List.range zLast).flatMap fun i => ((hyperOf (i + 1)).filter hyperedges.contains).map fun k => (allHyper.count k * degOf (i + 1), i + 1)

/-- the walk's scale K, the least common multiple of |e| · deg v over the incidences -/
def walkK : Nat := (incidences.map Prod.fst).foldl Nat.lcm 1

/-- K = 1643241600 clears every denominator of the map's walk, so K·M is an integer matrix, (K·M)_ef the sum of K/(|e| · deg v) over v in
e and f; there are 551 incidences, and the trace of K·M, the sum of K/(|e| · deg v) over them, is 26142201486 (the page's "K = 1643241600"
and the x⁶³ coefficient of det(x − K·M), −trace) -/
theorem walk_scale : walkK = 1643241600 ∧ incidences.length = 551 ∧ incidences.all (fun c => walkK % c.1 == 0) = true ∧
    (incidences.map fun c => walkK / c.1).sum = 26142201486 := by decide +kernel

section Walk

variable {V E : Type} [Fintype V] [Fintype E] (mem : E → V → Prop) [∀ e v, Decidable (mem e v)]

/-- a hyperedge's size, its members -/
def hsize (e : E) : ℕ := (Finset.univ.filter (mem e)).card

/-- an element's degree, the hyperedges holding it -/
def hdeg (v : V) : ℕ := (Finset.univ.filter fun e => mem e v).card

/-- the walk M = D_e⁻¹ Hᵀ D_v⁻¹ H: from hyperedge e to a member v, each with weight 1/|e|, then to a hyperedge f holding v, each with
weight 1/deg v -/
def hwalk (e f : E) : ℚ := ∑ v, if mem e v ∧ mem f v then 1 / ((hsize mem e : ℚ) * hdeg mem v) else 0

/-- every row of the walk sums to 1, on every hypergraph, the map's 64 hyperedges among them: K·M's rows sum to K
(the page's "every row of K·M sums to K") -/
theorem walk_rows (e : E) (he : 0 < hsize mem e) : ∑ f, hwalk mem e f = 1 := by
  have hs : (hsize mem e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  unfold hwalk
  rw [Finset.sum_comm]
  have inner : ∀ v, (∑ f, if mem e v ∧ mem f v then 1 / ((hsize mem e : ℚ) * hdeg mem v) else 0) =
      if mem e v then 1 / (hsize mem e : ℚ) else 0 := by
    intro v
    by_cases hv : mem e v
    · have hd : (hdeg mem v : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩).ne'
      simp only [hv, true_and, ite_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      change (hdeg mem v : ℚ) * _ = _
      field_simp
    · simp [hv]
  rw [Finset.sum_congr rfl fun v _ => inner v, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change (hsize mem e : ℚ) * _ = 1
  field_simp

/-- |e| · M_ef = |f| · M_fe, on every hypergraph: D_e·M is symmetric, so M is similar to a symmetric matrix (the
page's "D_e·K·M is symmetric, |e|·(K·M)_ef = |f|·(K·M)_fe") -/
theorem walk_balance (e f : E) : (hsize mem e : ℚ) * hwalk mem e f = hsize mem f * hwalk mem f e := by
  unfold hwalk
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : mem e v ∧ mem f v
  · have pos : ∀ g, mem g v → (hsize mem g : ℚ) ≠ 0 := fun g hg =>
      Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩⟩).ne'
    have hd : (hdeg mem v : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩⟩).ne'
    have he := pos e h.1
    have hf := pos f h.2
    simp only [h.1, h.2, and_self, ite_true]
    field_simp
  · have h' : ¬(mem f v ∧ mem e v) := fun h' => h ⟨h'.2, h'.1⟩
    simp [h, h']

end Walk

/-- insertion into a sorted list -/
def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

/-- a list sorted by insertion, a multiset's one listing -/
def isort : List Nat → List Nat
  | [] => []
  | a :: l => ins a (isort l)

/-- colours as classes: each item's signature replaced by its place among the distinct signatures -/
def relabel (sigs : List (Nat × List Nat)) : List Nat := sigs.map fun x => sigs.dedup.idxOf x

/-- the hyperedges of the given kinds -/
def edgesOf (kinds : List Nat) : List (Nat × Nat) := hyperedges.filter fun k => kinds.contains k.1

/-- each element's hyperedges of those kinds, by their place in `edgesOf` -/
def incOf (kinds : List Nat) : List (List Nat) :=
  (List.range zLast).map fun i => (List.range (edgesOf kinds).length).filter fun e => (hyperOf (i + 1)).contains ((edgesOf kinds).getD e (0, 0))

/-- each hyperedge's members, by element place -/
def memOf (kinds : List Nat) : List (List Nat) :=
  (List.range (edgesOf kinds).length).map fun e => (List.range zLast).filter fun i => ((incOf kinds).getD i []).contains e

/-- one round of colour refinement: an element's new colour is its colour with its hyperedges' colours, a hyperedge's its colour with its
members' new colours -/
def refineStep (I M : List (List Nat)) (st : List Nat × List Nat) : List Nat × List Nat :=
  let nz := relabel ((List.range st.1.length).map fun i => (st.1.getD i 0, isort ((I.getD i []).map fun e => st.2.getD e 0)))
  (nz, relabel ((List.range st.2.length).map fun e => (st.2.getD e 0, isort ((M.getD e []).map fun i => nz.getD i 0))))

/-- refined until neither count of classes grows, then the elements' classes (fuel: the rounds allowed) -/
def refine (I M : List (List Nat)) : Nat → List Nat × List Nat → Nat
  | 0, st => st.1.dedup.length
  | f + 1, st =>
    if (refineStep I M st).1.dedup.length = st.1.dedup.length ∧ (refineStep I M st).2.dedup.length = st.2.dedup.length then st.1.dedup.length
    else refine I M f (refineStep I M st)

/-- the classes colour refinement leaves among the elements on the hyperedges of the given kinds, the elements starting alike and each
hyperedge as its kind -/
def twins (kinds : List Nat) : Nat :=
  refine (incOf kinds) (memOf kinds) (zLast + 64) (List.replicate zLast 0, (edgesOf kinds).map Prod.fst)

/-- without the position hyperedges, colour refinement leaves 70 classes of the 137 elements; with them, 137: the
positions separate every element (the page's 70 and 137) -/
theorem seats_part_the_elements : twins [0, 1, 2] = 70 ∧ twins [0, 1, 2, 3] = 137 := by decide +kernel

/-- the stair's screen point of (x, y) at height h under the lift's spinor pair (s, c), from the flat view (1, 0) at lift 0: (x, y s + h c) -/
def proj (x y h s c : ℤ) : ℤ × ℤ := (x, y * s + h * c)

/-- the lift keeps x for every lift and every camera, and at the flat spinor (1, 0) the stair is the flat spiral (x, y), whatever the
height (the page's "the lift v runs φ from 90 degrees, the flat spiral, every point as before") -/
theorem stair_flat_at_zero (x y h s c : ℤ) : (proj x y h s c).1 = x ∧ proj x y h 1 0 = (x, y) := by
  exact ⟨rfl, by simp [proj]⟩

/-! ## Q. The explored table: a press opens a period

* The page opens unexplored. A press on an unexplored element z opens its crease: the hyperedge holding it, its period
  N = periodOf z (address: the closures' address, then N), every element of it.
* The explored elements: the union of the opened creases (2026-11-09). -/

/-- the elements' periods, Z = 1 … 137 -/
def periods : List Nat := (List.range zLast).map fun i => periodOf (i + 1)

/-- the crease of period N: the elements whose period is N -/
def crease (N : Nat) : List Nat := ((List.range zLast).map (· + 1)).filter fun z => periodOf z == N

/-- the elements explored once the creases of the periods Ns are open -/
def explored (Ns : List Nat) : List Nat := ((List.range zLast).map (· + 1)).filter fun z => Ns.contains (periodOf z)

/-- the periods in bit mask m, N = 1 … 8 -/
def periodsIn (m : Nat) : List Nat := (List.range 8).filterMap fun i => if m / 2 ^ i % 2 == 1 then some (i + 1) else none

/-- crease N holds 2 a(N)² elements to period 7 and 137 − 118 = 19 in period 8; for every set of periods (all 256), the explored count is
the sum of their creases' counts; Fe's crease 18, with H's 20, with C's 28, all eight 137 -/
theorem crease_counts : (List.range 7).all (fun i => (crease (i + 1)).length == periodLen (i + 1)) = true ∧ (crease 8).length = zLast - closing 7 ∧
    (crease 8).length = 19 ∧ (List.range 256).all (fun m => (periods.filter (periodsIn m).contains).length == ((periodsIn m).map fun N => (crease N).length).sum) = true ∧
    (explored [4]).length = 18 ∧ (explored [4, 1]).length = 20 ∧ (explored [4, 1, 2]).length = 28 ∧ (explored [1, 2, 3, 4, 5, 6, 7, 8]).length = 137 := by decide +kernel

/-! ## R. The gnomon squares: one square each period, one cell each orbital

* Period N holds 2 a(N)² states, a(N) = ⌊N/2⌋ + 1, and a(N)² = 1 + 3 + … + (2a(N) − 1): a square of side a(N). Its
  subshell l is the gnomon at ring l, 2l + 1 cells with max(col, row) = l from the bottom-left corner; each cell an
  orbital (n, l, m) of two states.
* A gnomon's path: the top row left to right, (p, l) for p ≤ l, then the right column down, (l, 2l − p);
  position p carries m = l − p.
* Element z, last subshell (n, l, e): at p = (e − 1) mod (2l + 1), half ⌊(e − 1)/(2l + 1)⌋; the first electron, then
  its partner z + 2l + 1 (Hund's order, a convention). The page computes the same squares (2026-11-09). -/

/-- the gnomons 1, 3, …, 2k − 1 fill the k × k square, for every k -/
theorem gnomons_square (k : Nat) : ((List.range k).map fun l => 2 * l + 1).sum = k ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- period N's states are twice its gnomons' cells, 2 a(N)² = 2 · Σ_{l < a(N)} (2l + 1), every N -/
theorem period_is_gnomons (N : Nat) : periodLen N = 2 * ((List.range (N / 2 + 1)).map fun l => 2 * l + 1).sum := by
  rw [gnomons_square, periodLen]

/-- the cell at path position p of gnomon l, (col, row) from the bottom-left corner -/
def cellAt (l p : Nat) : Nat × Nat := if p ≤ l then (p, l) else (l, 2 * l - p)

/-- the cells of gnomons l < k in path order -/
def gnomonCells (k : Nat) : List (Nat × Nat) := (List.range k).flatMap fun l => (List.range (2 * l + 1)).map (cellAt l)

/-- the gnomons' paths tile the k × k square, each cell once, gnomon l on the cells max(col, row) = l, for k = 1 … 5 (the squares to period 8) -/
theorem gnomon_tiles : (List.range 5).all (fun i => decide (gnomonCells (i + 1)).Nodup && (gnomonCells (i + 1)).length == (i + 1) ^ 2 &&
      (gnomonCells (i + 1)).all fun c => decide (c.1 < i + 1 ∧ c.2 < i + 1)) = true ∧
    (List.range 5).all (fun l => (List.range (2 * l + 1)).all fun p => max (cellAt l p).1 (cellAt l p).2 == l) = true := by decide

/-- an element's subshells to the eighth closure (runs n + l ≤ 9, 5g included), each (n, l, e), the empty ones dropped -/
def subshellsTo (z : Nat) : List (Nat × Nat × Nat) := (fill (madelungTo 10) z).filter fun (_, _, t) => decide (0 < t)

/-- element z's orbital cell (period, l, path position p, half s) from its last subshell (n, l, e) -/
def orbitalOf (z : Nat) : Nat × Nat × Nat × Nat :=
  match (subshellsTo z).getLastD (0, 0, 0) with
  | (_, l, e) => (periodOf z, l, (e - 1) % (2 * l + 1), (e - 1) / (2 * l + 1))

/-- the elements Z = 1 … 137 with their orbital cells -/
def orbitals : List (Nat × Nat × Nat × Nat × Nat) := (List.range zLast).map fun i => (i + 1, orbitalOf (i + 1))

/-- the elements in square N's cell of gnomon l at path position p, ascending: the first electron, then its partner -/
def cellPair (N l p : Nat) : List Nat := (orbitals.filter fun o => o.2.1 == N && o.2.2.1 == l && o.2.2.2.1 == p).map Prod.fst

/-- square N's rows top to bottom: the cell (col, row) is gnomon l = max(col, row)'s, at path position col on the top row, 2l − row on the right column -/
def squareOf (N : Nat) : List (List (List Nat)) :=
  (List.range (N / 2 + 1)).reverse.map fun r => (List.range (N / 2 + 1)).map fun c => cellPair N (max c r) (if r = max c r then c else 2 * max c r - r)

/-- every element sits in its period's square, inside its gnomon (l < a(N), p < 2l + 1, half 0 or 1); each cell holds at most two, the second
the first's partner z + 2l + 1; the squares hold 2, 8, 8, 18, 18, 32, 32 elements and 19 to Z = 137 -/
theorem orbital_cells : orbitals.all (fun o => decide (o.2.2.1 < o.2.1 / 2 + 1 ∧ o.2.2.2.1 < 2 * o.2.2.1 + 1 ∧ o.2.2.2.2 < 2)) = true ∧
    (List.range 8).all (fun i => (List.range ((i + 1) / 2 + 1)).all fun l => (List.range (2 * l + 1)).all fun p =>
      match cellPair (i + 1) l p with
      | [] => true
      | [_] => true
      | [a, b] => b == a + 2 * l + 1
      | _ => false) = true ∧
    (List.range 8).map (fun i => ((squareOf (i + 1)).map fun r => (r.map List.length).sum).sum) = [2, 8, 8, 18, 18, 32, 32, 19] := by decide +kernel

/-- the worked squares: period 4 (3 × 3) Sc/Fe Ti/Co V/Ni, Ga/Se Ge/Br Cr/Cu, K/Ca As/Kr Mn/Zn; period 6 (4 × 4) from La/Gd to Eu/Yb; period 8
(5 × 5) to Z = 137, its corner 119/120 and gnomon 4 filled (129 alone), gnomons 1, 2, 3 empty -/
theorem worked_squares :
    squareOf 4 = [[[21, 26], [22, 27], [23, 28]], [[31, 34], [32, 35], [24, 29]], [[19, 20], [33, 36], [25, 30]]] ∧
    squareOf 6 = [[[57, 64], [58, 65], [59, 66], [60, 67]], [[71, 76], [72, 77], [73, 78], [61, 68]], [[81, 84], [82, 85], [74, 79], [62, 69]],
      [[55, 56], [83, 86], [75, 80], [63, 70]]] ∧
    squareOf 8 = [[[121, 130], [122, 131], [123, 132], [124, 133], [125, 134]], [[], [], [], [], [126, 135]], [[], [], [], [], [127, 136]],
      [[], [], [], [], [128, 137]], [[119, 120], [], [], [], [129]]] := by decide +kernel

end PeriodicTable

/-! # Axiom Verification Report
Every theorem's axioms lie within `propext`, `Classical.choice` and `Quot.sound`; the kernel's
report follows, one line a theorem. -/

#print axioms Origami.step01_binomialTransform
#print axioms Origami.step02_partialSums
#print axioms Origami.step03_eulerTransform
#print axioms Origami.step04_logDerivative
#print axioms Origami.step05_moebiusInversion
#print axioms Origami.step06_partialSums
#print axioms Origami.step07_partialSums
#print axioms Origami.step08_partialSums
#print axioms Origami.step09_timesEulerFactors
#print axioms Origami.step10_timesEulerFactors
#print axioms Origami.step11_timesEulerFactors
#print axioms Origami.step12_timesEulerFactors
#print axioms Origami.step13_eulerTransform
#print axioms Origami.step14_logDerivative
#print axioms Origami.step15_moebiusInversion
#print axioms Origami.step16_binomialTransform
#print axioms Origami.step17_antidiagonalSums
#print axioms Origami.step18_centralDiagonal
#print axioms Origami.step19_divideByNPlusOne
#print axioms Origami.step20_partialProducts
#print axioms Origami.step21_jacobiAlphas
#print axioms Origami.step22_partialProducts
#print axioms Origami.step23_jacobiBetas
#print axioms Origami.step24_sfractionMoments
#print axioms Origami.step25_sfractionMoments
#print axioms Origami.step26_sfractionMoments
#print axioms Origami.step27_charpolyRowsAre
#print axioms Origami.step28_divideByNPlusOne
#print axioms Origami.step29_sfractionMoments
#print axioms Origami.step30_binomialInverse
#print axioms Origami.step31_charpolyRowsAre
#print axioms Origami.step32_binomialInverse
#print axioms Origami.step33_binomialInverse
#print axioms Origami.step34_divideByTwoPow
#print axioms Origami.step35_adjacentSums
#print axioms Origami.step36_partialSums
#print axioms Origami.step37_partialSums
#print axioms Origami.step38_partialSums
#print axioms Origami.step39_divideByTwoPow
#print axioms Origami.step40_poleAtTwo
#print axioms Origami.step41_divideByTwoPow
#print axioms Origami.step42_poleAtTwo
#print axioms Origami.step43_alternateBetaRows
#print axioms Origami.step44_rowSums
#print axioms Origami.step45_dressedLoops
#print axioms Origami.cf_A000007
#print axioms Origami.cf_A000012
#print axioms Origami.cf_A000027
#print axioms Origami.cf_A000041
#print axioms Origami.cf_A000203
#print axioms Origami.cf_A000217_1
#print axioms Origami.cf_A000292_1
#print axioms Origami.cf_A000332_4
#print axioms Origami.cf_A008619
#print axioms Origami.cf_A001399
#print axioms Origami.cf_A008638
#print axioms Origami.cf_oddM
#print axioms Origami.cf_A000009
#print axioms Origami.cf_A000593
#print axioms Origami.cf_A000079
#print axioms Origami.cf_A000045_1
#print axioms Origami.cf_A000984
#print axioms Origami.cf_A000108
#print axioms Origami.cf_A000142
#print axioms Origami.cf_A005408
#print axioms Origami.cf_A001147
#print axioms Origami.cf_A000290_1
#print axioms Origami.cf_nu
#print axioms Origami.cf_nu0
#print axioms Origami.cf_A000108_1
#print axioms Origami.cf_A001006
#print axioms Origami.cf_A126120
#print axioms Origami.cf_omegaS
#print axioms Origami.cf_A040000
#print axioms Origami.cf_A000330_1
#print axioms Origami.cf_G1
#print axioms Origami.cf_G3
#print axioms Origami.cf_A000041_bent
#print axioms Origami.rel_beta_nu0
#print axioms Origami.rel_pole_nu
#print axioms Origami.all_step01_binomialTransform
#print axioms Origami.all_step02_partialSums
#print axioms Origami.all_columns_partialSums
#print axioms Origami.all_step06_partialSums
#print axioms Origami.all_step07_partialSums
#print axioms Origami.all_step08_partialSums
#print axioms Origami.all_step09_timesEulerFactors
#print axioms Origami.all_step10_timesEulerFactors
#print axioms Origami.all_step05_moebiusInversion
#print axioms Origami.all_step15_moebiusInversion
#print axioms Origami.all_step16_binomialTransform
#print axioms Origami.all_step17_antidiagonalSums
#print axioms Origami.all_step18_centralDiagonal
#print axioms Origami.all_step19_divideByNPlusOne
#print axioms Origami.all_step20_partialProducts
#print axioms Origami.all_step22_partialProducts
#print axioms Origami.all_step30_binomialInverse
#print axioms Origami.all_step35_adjacentSums
#print axioms Origami.all_step36_partialSums
#print axioms Origami.all_step37_partialSums
#print axioms Origami.all_step38_partialSums
#print axioms Origami.all_rec1
#print axioms Origami.all_catalan_rec
#print axioms Origami.all_touchard_term_shape
#print axioms Origami.all_catalan_ratio
#print axioms Origami.all_touchard_partner_shape
#print axioms Origami.all_touchard_telescope
#print axioms Origami.all_touchard_rec
#print axioms Origami.all_touchard
#print axioms Origami.all_alt_choose
#print axioms Origami.all_alt_choose_R
#print axioms Origami.all_binv
#print axioms Origami.all_choose_two_pow
#print axioms Origami.all_binom_motzkin
#print axioms Origami.all_step32_binomialInverse
#print axioms Origami.all_step33_binomialInverse
#print axioms Origami.atom_e
#print axioms Origami.atom_l
#print axioms Origami.atom_m
#print axioms PeriodicTable.closes_are_period_sums
#print axioms PeriodicTable.carbon_seat
#print axioms PeriodicTable.valence_from_seat
#print axioms PeriodicTable.seats_distinct
#print axioms PeriodicTable.madelung_run
#print axioms PeriodicTable.madelung_is_blocks
#print axioms PeriodicTable.run_is_partitions
#print axioms PeriodicTable.odd_seats_square
#print axioms PeriodicTable.block_seats
#print axioms PeriodicTable.block_ends_on_s
#print axioms PeriodicTable.period_seats
#print axioms PeriodicTable.period_ends_on_p
#print axioms PeriodicTable.s_opens_every_period
#print axioms PeriodicTable.closures_closed_form
#print axioms PeriodicTable.closures_continue
#print axioms PeriodicTable.closures_first_nine
#print axioms PeriodicTable.frame_ends_at_g
#print axioms PeriodicTable.table_edge
#print axioms PeriodicTable.electrons_seated
#print axioms PeriodicTable.places_distinct
#print axioms PeriodicTable.closures_in_column_18
#print axioms PeriodicTable.group_three
#print axioms PeriodicTable.f_rows
#print axioms PeriodicTable.carbon_silicon_place
#print axioms PeriodicTable.valence_compared_last
#print axioms PeriodicTable.line_is_level_difference
#print axioms PeriodicTable.ionLevel_rises
#print axioms PeriodicTable.lines_scale_Z_squared
#print axioms PeriodicTable.balmer_over_lyman
#print axioms PeriodicTable.helium_half_hydrogen
#print axioms PeriodicTable.turn_is_remainder
#print axioms PeriodicTable.of_all_range
#print axioms PeriodicTable.address_map_places
#print axioms PeriodicTable.spiral_steps
#print axioms PeriodicTable.spiral_rises
#print axioms PeriodicTable.turn_zero_at_closures
#print axioms PeriodicTable.valence_is_turn_distance
#print axioms PeriodicTable.mid_period_seats
#print axioms PeriodicTable.hyperedge_counts
#print axioms PeriodicTable.walk_scale
#print axioms PeriodicTable.walk_rows
#print axioms PeriodicTable.walk_balance
#print axioms PeriodicTable.seats_part_the_elements
#print axioms PeriodicTable.stair_flat_at_zero
#print axioms PeriodicTable.crease_counts
#print axioms PeriodicTable.gnomons_square
#print axioms PeriodicTable.period_is_gnomons
#print axioms PeriodicTable.gnomon_tiles
#print axioms PeriodicTable.orbital_cells
#print axioms PeriodicTable.worked_squares
