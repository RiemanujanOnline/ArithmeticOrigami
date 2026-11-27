/-
Copyright (c) 2026 Sambuddha Sarkar. All rights reserved.
Author: Sambuddha Sarkar
-/
/-
Origami Arithmetica, page 1, Śūnya: the Śūnya conjecture, Axiom Ś and the page's notices, Lean 4 theorems; the proof
that accompanies the Gazette's page 1, in the order of its notices.
Lean 4.34.1, Mathlib v4.34.1. Check: lake build OrigamiArithmetica.Sunya (a project requiring Mathlib v4.34.1).
Output: the axiom report alone; an error is a false statement.
Terms: crease, the inversion J, x ↦ 1/x; shift, the translation T, x ↦ x + 1; word, a string of the letters J and T,
the reduced word T^a_0 J ⋯ T^a_n J being [a_0; a_1, ..., a_n], its partial quotients; J-fraction, a series' continued fraction.
Śūnya conjecture and Axiom Ś
P  The Śūnya conjecture's points 1–5.
A  The readings of Axiom Ś: the given, the crease, the shift, the numerals.
Continued fraction
C  The limit: every infinite regular word with a 0 >= 0 converges; the continuants, their unit determinant, the
   denominators' growth, Cauchy in ℚ.
N  Positional notation beside the continued fraction.
R  The two periodicities.
H  The wheel (chakravāla), Ś5: a cycle's fixed point is a root of its integer quadratic; Bhaskara's 67 and 61.
Letter
G  The words' geometry.
V  Fixed points and orders: fixed points, the numerals' trailing identification, Peano's remaining axioms, which
   quotients are reflections, the orders by trace.
X  The tensor's steps; the binomial transform on a matrix.
Word
M  The model's faithfulness: every nonnegative unimodular matrix is exactly one reduced word.
K  The pair and reduction: points 1 and 2 on the pair, the trailing zero, the determinant of a word, Ś2 in the model,
   the stabiliser of the given, the one involution; every word reduces.
L  The exact form of the Śūnya conjecture, the two shifts R = T and L = J T J: a T/J word is an L/R word followed by J
   or by nothing; the run-lengths are the quotients; the L/R word of a matrix is unique; J swaps the two shifts; as
   Stern-Brocot's letters the two shifts reach every positive rational, and never zero.
O  The finite orders, complete: the Chebyshev powers of a determinant-1 matrix; trace at most -3; trace 2 and -2; a
   crease word of nonzero trace; the crystallographic restriction, every case in the kernel.
U  The unimodular group: every integer matrix of determinant 1 or -1 a word in T, T^-1 and J, by Euclid on the first
   column, with Euclid's canonical word as a function; every matrix of determinant 1 a word in S, T and T^-1.
W  The numerals on the letters alone: Peano with no integer; the exact fixed points of the crease and the shift; each
   nonnegative rational once, in Euclid's normal form.
E  Euclid's measurement: Euclid's division read as its quotients, the word, ending at the remainder 0.
Y  The presentation of the unimodular group: three relations; in any group that holds them a word of the identity is
   the identity, and the group on the sheet is the group they present; each element has one reduced state; the place
   D_b is a word only at b = 1 and -1.
Z  Reduction modulo a prime: a word keeps every cross determinant up to sign, so its convergents are never one point
   modulo a prime; the place reads positions to the left; the J-fraction's letter, its step
   x ↦ 1/(z - al - be x), is the crease, a shift and a place.
The J-fraction's step
S  The J-fraction's step; its three kinds by trace: elliptic, parabolic, hyperbolic.
B  The atoms' multipliers: units, and one non-unit.
I  The radial step.
D  The Dirac cone; the large trace.
F  Every Dirac level a rational curve.
Spinor lock (m, n)
   Gaussian multiplication; the coupling's rule at every lock; Hermite–Serret's stop.
Unit, edge, self-recoil
   The units 1 and i, the quarter turn; the edge lock (1, 1) and the self-recoil lock (2, 1).
Candidate
   1/α = 662194096285/4832263787 read off the lock (1150813, 4199), its word of 20 partial quotients; the flagpole's
   legs.
Selection rule
   Euclid's division of the lock, ending at the remainder 0; the lock's prime spinors, Hermite–Serret's from its norm.
Namespaces: SunyaAxiom, the conjecture to section Z; AlphaRoutes, Euclid's division (section E) and the J-fraction's
step to the selection rule.
Proofs: `decide`, the kernel evaluating a closed integer statement.
Variables: a theorem in a, b, c, d, k, n, ... holds for every value.

## Workflow Delineation
* Author: Sambuddha Sarkar.
  Computation, Śūnya conjecture and axiom, and the methodology. Definitions, theorems and kernel
  checks formulated, reviewed and validated.
* AI assistance:
  Principal investigation within bounded searches.
  Text, code and computation runs drafted and executed under the author's review.
-/
import Mathlib

namespace SunyaAxiom

/-! # Śūnya conjecture and Axiom Ś -/

/-! ## The sheet: integer 2 x 2 matrices acting on the projective line -/

/-- a 2 x 2 integer matrix by its entries -/
@[ext]
structure M2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

namespace M2

def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def one : M2 := ⟨1, 0, 0, 1⟩

def pow (x : M2) : ℕ → M2
  | 0 => one
  | n + 1 => mul (pow x n) x

def det (x : M2) : ℤ := x.a * x.d - x.b * x.c

def tr (x : M2) : ℤ := x.a + x.d

/-- the action on a point of the projective line, a pair (numerator, denominator) -/
def act (x : M2) (v : ℤ × ℤ) : ℤ × ℤ := (x.a * v.1 + x.b * v.2, x.c * v.1 + x.d * v.2)

/-- acting by a product is acting by each factor in turn: act (x y) v = act x (act y v) -/
theorem act_mul (x y : M2) (v : ℤ × ℤ) : act (mul x y) v = act x (act y v) := by
  simp only [act, mul, Prod.mk.injEq]
  constructor <;> ring

/-- matrix multiplication is associative -/
theorem mul_assoc (x y z : M2) : mul (mul x y) z = mul x (mul y z) := by
  simp only [mul, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- the identity is a left unit -/
theorem one_mul (x : M2) : mul one x = x := by
  ext <;> simp [mul, one]

/-- and a right unit -/
theorem mul_one (x : M2) : mul x one = x := by
  ext <;> simp [mul, one]

/-- the determinant is multiplicative -/
theorem det_mul (x y : M2) : (mul x y).det = x.det * y.det := by
  simp only [mul, det]; ring

/-- Cayley-Hamilton on the sheet: x² = (tr x) x - (det x) I -/
theorem cayley_hamilton (x : M2) :
    mul x x = ⟨x.tr * x.a - x.det, x.tr * x.b, x.tr * x.c, x.tr * x.d - x.det⟩ := by
  simp only [mul, tr, det, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- the trace of a square: tr² - 2 det; a crease word (det -1) squares to trace tr² + 2 -/
theorem tr_sq (x : M2) : (mul x x).tr = x.tr ^ 2 - 2 * x.det := by
  simp only [mul, tr, det]; ring

/-- x^(m + n) = x^m x^n -/
theorem pow_add (x : M2) (m n : ℕ) : pow x (m + n) = mul (pow x m) (pow x n) := by
  induction n with
  | zero => simp [pow, M2.mul_one]
  | succ n ih =>
    show mul (pow x (m + n)) x = mul (pow x m) (mul (pow x n) x)
    rw [ih, M2.mul_assoc]

end M2

/-! ## P. The Śūnya conjecture's points 1–5 -/

/-- the empty tail 1/0: the one given -/
def inf : ℤ × ℤ := (1, 0)

/-- the crease J, x ↦ 1/x: the zero quotient -/
def J : M2 := ⟨0, 1, 1, 0⟩

/-- the shift T, x ↦ x + 1 -/
def T : M2 := ⟨1, 1, 0, 1⟩

/-- the partial quotient a: T^a J = [[a, 1], [1, 0]] -/
def Q (a : ℤ) : M2 := ⟨a, 1, 1, 0⟩

/-- the word of [a_0; a_1, ..., a_n]: Q a_0 · Q a_1 ⋯ Q a_n -/
def word : List ℤ → M2
  | [] => M2.one
  | a :: r => M2.mul (Q a) (word r)

/-- the value in ℚ: the word applied to 1/0 under Lean's total division p/0 = 0 (for the pair without convention, see Section K) -/
def val (w : List ℤ) : ℚ := ((M2.act (word w) inf).1 : ℚ) / ((M2.act (word w) inf).2 : ℚ)

/-- point 3: every quotient is a crease, determinant -1 -/
theorem point3_det (a : ℤ) : (Q a).det = -1 := by simp [Q, M2.det]

/-- point 3: J J = I -/
theorem point3_JJ : M2.mul J J = M2.one := by decide

/-- point 4, the crease limit: an interior zero merges its neighbours, [.., a, 0, b, ..] = [.., a + b, ..] -/
theorem point4_crease_limit (a b : ℤ) : M2.mul (Q a) (M2.mul J (Q b)) = Q (a + b) := by
  ext <;> simp [M2.mul, Q, J]

/-- point 4 on a word: [0; 1, 0, 2, 0, 3] = [0; 6] -/
theorem point4_instance : word [0, 1, 0, 2, 0, 3] = word [0, 6] := by decide

/-- point 5: J exchanges 1/0 and 0; both come from the one quotient -/
theorem point5_swap : M2.act J inf = (0, 1) ∧ M2.act J (0, 1) = inf := by decide

/-- point 1, position on ℚ (under p/0 = 0; see `point1_pair` on ℤ × ℤ): [0; a_1, ...] = 1 / [a_1; ...] -/
theorem point1_position (r : List ℤ) : val (0 :: r) = 1 / val r := by
  have hJ : ∀ v : ℤ × ℤ, M2.act (Q 0) v = (v.2, v.1) := by
    intro v; simp [M2.act, Q]
  simp only [val, word, M2.act_mul, hJ, one_div_div]

/-- point 2, the unit on ℚ (under p/0 = 0 at n = 0; see `point2_pair` on ℤ × ℤ): [0; n] = 1/n -/
theorem point2_unit (n : ℤ) : val [0, n] = 1 / n := by
  simp [val, word, Q, M2.mul, M2.one, M2.act, inf]

/-! ## A. The readings of Axiom Ś: the given, the crease, the shift, the numerals -/

/-- zero is made: one crease of the given, 0 = J(1/0) -/
theorem zero_from_inf : M2.act J inf = (0, 1) := by decide

/-- one is made: one shift of zero -/
theorem one_from_zero : M2.act T (0, 1) = (1, 1) := by decide

/-- the shift's n-th power is [[1, n], [0, 1]] -/
theorem T_pow (n : ℕ) : M2.pow T n = ⟨1, n, 0, 1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show M2.mul (M2.pow T n) T = _
    rw [ih]; (ext <;> simp [M2.mul, T]); ring

/-- every natural quotient is a word in the shift and the crease: Q n = T^n J -/
theorem quotient_word (n : ℕ) : Q n = M2.mul (M2.pow T n) J := by
  rw [T_pow]; ext <;> simp [M2.mul, Q, J]

/-- Peano's n is the word T^n J applied to the given: n = T^n(0) -/
theorem nat_from_inf (n : ℕ) : M2.act (M2.mul (M2.pow T n) J) inf = ((n : ℤ), 1) := by
  rw [T_pow]; simp [M2.mul, M2.act, J, inf]

/-- the successor is the shift -/
theorem succ_is_shift (n : ℤ) : M2.act T (n, 1) = (n + 1, 1) := by
  simp [M2.act, T]

/-- the numeral [n] reads n -/
theorem val_nat (n : ℤ) : val [n] = n := by
  simp [val, word, Q, M2.mul, M2.one, M2.act, inf]

/-! # Continued fraction -/

/-! ## C. The limit: every infinite regular word converges. The continuants p_n, q_n of the
word's prefixes, their unit determinant, the denominators' growth, the prefix words as the convergents, and Cauchy in ℚ -/

/-- the word of a concatenation is the product of the words -/
theorem word_append (r s : List ℤ) : word (r ++ s) = M2.mul (word r) (word s) := by
  induction r with
  | nil => simp [word, M2.one_mul]
  | cons a r ih => simp [word, ih, M2.mul_assoc]

/-- the continuants of a regular word a 0, a 1, a 2, ...: `cnum a (n + 1)` and `cden a (n + 1)` are the numerator and the
denominator of its n-th convergent [a 0; a 1, ..., a n], and index 0 holds the empty tail 1/0 -/
def cnum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 0
  | n + 2 => a (n + 1) * cnum a (n + 1) + cnum a n

def cden (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) * cden a (n + 1) + cden a n

/-- consecutive convergents differ by a unit: p_n q_(n-1) - p_(n-1) q_n = (-1)^(n+1), in cnum's indexing (p_(-1) = 1,
q_(-1) = 0, the empty tail) -/
theorem cont_det (a : ℕ → ℕ) (n : ℕ) :
    (cnum a (n + 1) : ℤ) * cden a n - cnum a n * cden a (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [cnum, cden]
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, cnum, cden]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-- for a regular word every denominator q_n is at least 1 -/
theorem cden_pos (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : 1 ≤ cden a (n + 1) := by
  induction n with
  | zero => simp [cden]
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, cden]
    nlinarith [ha k, Nat.zero_le (cden a k)]

/-- the denominators never decrease -/
theorem cden_mono (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : cden a (n + 1) ≤ cden a (n + 2) := by
  rw [cden]
  nlinarith [ha n, Nat.zero_le (cden a n)]

/-- they at least double every two steps: 2 q_n is at most q_(n+2) -/
theorem cden_double (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : 2 * cden a (n + 1) ≤ cden a (n + 3) := by
  rw [show n + 3 = (n + 1) + 2 from rfl, cden]
  nlinarith [ha (n + 1), cden_mono a ha n, Nat.zero_le (cden a (n + 2))]

/-- the denominators at least double every two steps, so q_n ≥ 2^(n/2), in cnum's indexing -/
theorem cden_pow (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : 2 ^ (n / 2) ≤ cden a (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [cden]
    | 1 => simpa using cden_pos a ha 1
    | m + 2 =>
      have h := ih m (by omega)
      have h2 := cden_double a ha m
      have : (m + 2) / 2 = m / 2 + 1 := by omega
      rw [this, pow_succ]
      calc 2 ^ (m / 2) * 2 ≤ cden a (m + 1) * 2 := Nat.mul_le_mul_right 2 h
        _ = 2 * cden a (m + 1) := Nat.mul_comm _ _
        _ ≤ cden a (m + 3) := h2

/-- 2^n is at most 2 q_n q_(n+1) -/
theorem cden_prod (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : 2 ^ n ≤ 2 * (cden a (n + 1) * cden a (n + 2)) := by
  have h1 := cden_pow a ha n
  have hm := cden_mono a ha n
  have hsq : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ cden a (n + 1) * cden a (n + 2) :=
    Nat.mul_le_mul h1 (le_trans h1 hm)
  have he : 2 ^ n ≤ 2 * (2 ^ (n / 2) * 2 ^ (n / 2)) := by
    rw [← pow_add, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- the prefix words are the convergents: the word of a 0, ..., a n is [[p_n, p_(n-1)], [q_n, q_(n-1)]] -/
theorem word_prefix (a : ℕ → ℕ) (n : ℕ) :
    word ((List.range (n + 1)).map fun k => (a k : ℤ)) = ⟨cnum a (n + 1), cnum a n, cden a (n + 1), cden a n⟩ := by
  induction n with
  | zero => simp [word, Q, M2.mul, M2.one, cnum, cden]
  | succ k ih =>
    rw [List.range_succ, List.map_append, word_append, ih]
    simp [word, Q, M2.mul, M2.one, cnum, cden]
    constructor <;> ring

/-- the word of a_0, ..., a_n applied to the given 1/0 reads (p_n, q_n) -/
theorem prefix_reads (a : ℕ → ℕ) (n : ℕ) :
    M2.act (word ((List.range (n + 1)).map fun k => (a k : ℤ))) inf = ((cnum a (n + 1) : ℤ), (cden a (n + 1) : ℤ)) := by
  rw [word_prefix]
  simp [M2.act, inf]

/-- consecutive convergents lie within 2 (1/2)^n (the proof bounds their distance in ℚ, 1 / (q_n q_(n+1)) by `cont_det`) -/
theorem conv_step (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) :
    |((cnum a (n + 1) : ℚ) / cden a (n + 1)) - ((cnum a (n + 2) : ℚ) / cden a (n + 2))| ≤ 2 * (1 / 2 : ℚ) ^ n := by
  have h1 : (0 : ℚ) < cden a (n + 1) := by exact_mod_cast cden_pos a ha n
  have h2 : (0 : ℚ) < cden a (n + 2) := by exact_mod_cast cden_pos a ha (n + 1)
  have hd := cont_det a (n + 1)
  have hdQ : ((cnum a (n + 2) : ℚ) * cden a (n + 1) - cnum a (n + 1) * cden a (n + 2)) = (-1) ^ (n + 2) := by
    exact_mod_cast hd
  have hg : (2 : ℚ) ^ n ≤ 2 * (cden a (n + 1) * cden a (n + 2)) := by exact_mod_cast cden_prod a ha n
  rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
  have hnum : (cnum a (n + 1) : ℚ) * cden a (n + 2) - cden a (n + 1) * cnum a (n + 2) = -(-1) ^ (n + 2) := by
    linarith
  rw [hnum, abs_div, abs_neg, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (mul_pos h1 h2)]
  rw [one_div_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (mul_pos h1 h2) (by positivity)]
  linarith

/-- every infinite regular word is Cauchy in ℚ: a 0 any natural and every later partial quotient at least 1, for every
rational tolerance ε > 0 the words of its prefixes, applied to the given 1/0, stay within ε of one another
* Hardy and Wright, Theorem 166; proved here in pure ℚ from the continuants' geometric step bound. -/
theorem regular_word_converges (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a (n + 1)) (ε : ℚ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m k : ℕ, N ≤ m → N ≤ k →
      |((M2.act (word ((List.range (m + 1)).map fun i => (a i : ℤ))) inf).1 : ℚ) /
        (M2.act (word ((List.range (m + 1)).map fun i => (a i : ℤ))) inf).2 -
       ((M2.act (word ((List.range (k + 1)).map fun i => (a i : ℤ))) inf).1 : ℚ) /
        (M2.act (word ((List.range (k + 1)).map fun i => (a i : ℤ))) inf).2| < ε := by
  let f : ℕ → ℚ := fun n => (cnum a (n + 1) : ℚ) / cden a (n + 1)
  have htel : ∀ n d : ℕ, |f n - f (n + d)| ≤ 4 * (1 / 2 : ℚ) ^ n - 4 * (1 / 2 : ℚ) ^ (n + d) := by
    intro n d
    induction d with
    | zero => simp
    | succ d ih =>
      have hstep : |f (n + d) - f (n + (d + 1))| ≤ 2 * (1 / 2 : ℚ) ^ (n + d) := conv_step a ha (n + d)
      have htri := abs_sub_le (f n) (f (n + d)) (f (n + (d + 1)))
      have halg : (4 * (1 / 2 : ℚ) ^ n - 4 * (1 / 2 : ℚ) ^ (n + d)) + 2 * (1 / 2 : ℚ) ^ (n + d) =
          4 * (1 / 2 : ℚ) ^ n - 4 * (1 / 2 : ℚ) ^ (n + (d + 1)) := by
        rw [show n + (d + 1) = (n + d) + 1 by omega, pow_succ]
        ring
      linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (8 / ε)
  refine ⟨N, fun m k hm hk => ?_⟩
  have hm' : |f N - f m| ≤ 4 * (1 / 2 : ℚ) ^ N := by
    have h1 := htel N (m - N)
    rw [Nat.add_sub_of_le hm] at h1
    have hp : (0 : ℚ) ≤ 4 * (1 / 2 : ℚ) ^ m := by positivity
    linarith
  have hk' : |f N - f k| ≤ 4 * (1 / 2 : ℚ) ^ N := by
    have h1 := htel N (k - N)
    rw [Nat.add_sub_of_le hk] at h1
    have hp : (0 : ℚ) ≤ 4 * (1 / 2 : ℚ) ^ k := by positivity
    linarith
  have hmk : |f m - f k| ≤ 8 * (1 / 2 : ℚ) ^ N := by
    have htri := abs_sub_le (f m) (f N) (f k)
    rw [abs_sub_comm (f m) (f N)] at htri
    linarith
  have hpow_nat : ∀ n : ℕ, n < 2 ^ n := fun n => by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  have hpow : (N : ℚ) < (2 : ℚ) ^ N := by exact_mod_cast hpow_nat N
  have h2pos : (0 : ℚ) < (2 : ℚ) ^ N := by positivity
  have h8 : (8 : ℚ) < ε * (2 : ℚ) ^ N := by
    have hN' : 8 < (N : ℚ) * ε := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hbound : 8 * (1 / 2 : ℚ) ^ N < ε := by
    rw [one_div_pow, ← div_eq_mul_one_div, div_lt_iff₀ h2pos]
    linarith
  have hgoal : |f m - f k| < ε := lt_of_le_of_lt hmk hbound
  simpa [f, prefix_reads] using hgoal

/-! ## N. Positional notation beside the continued fraction: the place D_b, determinant b -/

/-- the place: x ↦ b x -/
def D (b : ℤ) : M2 := ⟨b, 0, 0, 1⟩

/-- a digit d at a new place: x ↦ b x + d, the product T^d D_b (a word only at b = ±1, `place_word_iff`) -/
theorem digit_word (b d : ℤ) : M2.mul ⟨1, d, 0, 1⟩ (D b) = ⟨b, d, 0, 1⟩ := by
  ext <;> simp [M2.mul, D]

/-- the digit's word T^d D_b = [[b, d], [0, 1]] has determinant b, the base: for b ≠ -1 it is not a crease -/
theorem place_det (b d : ℤ) : (⟨b, d, 0, 1⟩ : M2).det = b := by simp [M2.det]

/-- Horner's reading of the digits d_0 d_1 ... (most significant first) -/
def horner (b : ℤ) (ds : List ℤ) : ℤ := ds.foldl (fun x d => b * x + d) 0

/-- the positional word of the digits: each digit's matrix applied after the previous -/
def posword (b : ℤ) (ds : List ℤ) : M2 := ds.foldl (fun m d => M2.mul ⟨b, d, 0, 1⟩ m) M2.one

/-- the place matrices [[b, d], [0, 1]] read digits in base b: if m sends (0, 1) to (x, 1), folding the digits ds onto m sends it to (x followed by ds in base b, 1) -/
theorem posword_act_aux (b : ℤ) (ds : List ℤ) (m : M2) (x : ℤ) (h : M2.act m (0, 1) = (x, 1)) :
    M2.act (ds.foldl (fun m d => M2.mul ⟨b, d, 0, 1⟩ m) m) (0, 1) = (ds.foldl (fun x d => b * x + d) x, 1) := by
  induction ds generalizing m x with
  | nil => simpa using h
  | cons d ds ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [M2.act_mul, h]
    simp [M2.act]

/-- positional notation acts on the same line from the same zero: the word applied to 0 reads Horner's value -/
theorem posword_act (b : ℤ) (ds : List ℤ) : M2.act (posword b ds) (0, 1) = (horner b ds, 1) :=
  posword_act_aux b ds M2.one 0 (by decide)

/-- the zero digit holds a place: it multiplies by the base and adds nothing -/
theorem zero_digit_holds (b : ℤ) (ds : List ℤ) : horner b (ds ++ [0]) = b * horner b ds := by
  simp [horner, List.foldl_append]

/-- the zero digit's matrix is the bare place -/
theorem zero_digit_is_place (b : ℤ) : (⟨b, 0, 0, 1⟩ : M2) = D b := rfl

/-! ## R. The two periodicities: with integer entries a period in the place is rational, a period in the crease quadratic -/

/-- a block H repeating at the place, base B > 1: x = (H + x)/B gives x = H/(B - 1), degree one -/
theorem periodic_place (H B x : ℚ) (hB : 1 < B) (hx : x = (H + x) / B) : x = H / (B - 1) := by
  have hB0 : B ≠ 0 := by linarith
  have hB1 : B - 1 ≠ 0 := by linarith
  rw [eq_div_iff hB0] at hx
  rw [eq_div_iff hB1]
  linarith

/-- a block P = [[a, b], [c, d]] repeating in the crease: where c x + d ≠ 0, x = P x gives c x^2 + (d - a) x - b = 0,
    degree two when c ≠ 0 -/
theorem periodic_crease {K : Type*} [Field K] (a b c d x : K) (h : c * x + d ≠ 0) (hx : x = (a * x + b) / (c * x + d)) :
    c * x ^ 2 + (d - a) * x - b = 0 := by
  rw [eq_div_iff h] at hx
  linear_combination hx

/-! ## H. The wheel (chakravāla), Ś5 in integers: a cycle's fixed point is a root of its integer quadratic -/

/-- Ś5, the wheel (chakravāla), in integers: a point the cycle's matrix fixes, x = (a x + b) / (c x + d) written
without division, is a root of the cycle's integer quadratic c x^2 + (d - a) x - b
* The word is that fixed point; no limit is taken. -/
theorem wheel_fixed_point_quadratic {K : Type*} [CommRing K] (M : M2) (x : K)
    (h : (M.a : K) * x + M.b = x * ((M.c : K) * x + M.d)) :
    (M.c : K) * x ^ 2 + ((M.d : K) - M.a) * x - M.b = 0 := by
  linear_combination -h

/-- Ś5 on the golden word [1; 1, 1, ...]: its cycle is the one partial quotient Q 1, and the point it fixes is a root
of x^2 - x - 1. -/
theorem wheel_golden {K : Type*} [CommRing K] (x : K)
    (h : ((Q 1).a : K) * x + (Q 1).b = x * (((Q 1).c : K) * x + (Q 1).d)) :
    x ^ 2 - x - 1 = 0 := by
  have hq := wheel_fixed_point_quadratic (Q 1) x h
  simp only [Q, Int.cast_one, Int.cast_zero] at hq
  linear_combination hq

/-- Bhaskara II, Bijaganita 76, after the cakra-vala of verse 75: which square times 67, plus one, is a square
* The word of sqrt 67's first cycle, its partial quotients those of the root of x^2 - 67, answers in its own
  matrix. -/
theorem wheel_bhaskara_67 :
    (word [8, 5, 2, 1, 1, 7, 1, 1, 2, 5]).a ^ 2 - 67 * (word [8, 5, 2, 1, 1, 7, 1, 1, 2, 5]).c ^ 2 = 1 := by
  decide

/-- The same verse's second question, 61: one turn of sqrt 61's wheel, its first cycle of eleven partial quotients,
leaves the additive -1, the sign changed. -/
theorem wheel_bhaskara_61_one_turn :
    (word [7, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1]).a ^ 2 - 61 * (word [7, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1]).c ^ 2 = -1 := by
  decide

/-- Two turns of sqrt 61's wheel give the additive +1: the square times 61, plus one, is a square. -/
theorem wheel_bhaskara_61 :
    (word [7, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1, 14, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1]).a ^ 2
      - 61 * (word [7, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1, 14, 1, 4, 3, 1, 2, 2, 1, 3, 4, 1]).c ^ 2 = 1 := by
  decide

/-! # Letter -/

/-! ## G. The words' geometry: a reflection and a translation; with T^-1 they generate GL(2, Z) (section U) -/

/-- the crease reverses orientation -/
theorem J_det : J.det = -1 := by decide

/-- the shift is a translation: determinant 1, trace 2 -/
theorem T_det_tr : T.det = 1 ∧ T.tr = 2 := by decide

def Tinv : M2 := ⟨1, -1, 0, 1⟩

def S : M2 := ⟨0, -1, 1, 0⟩

/-- T^-1 T is the identity -/
theorem Tinv_T : M2.mul Tinv T = M2.one := by decide

/-- S = T⁻¹ J T J T⁻¹: the modular group's second generator, a word in the shift, its inverse and the crease -/
theorem S_word : M2.mul (M2.mul (M2.mul (M2.mul Tinv J) T) J) Tinv = S := by decide

/-- S^2 = -I and S^4 = I -/
theorem S_order : M2.pow S 2 = ⟨-1, 0, 0, -1⟩ ∧ M2.pow S 4 = M2.one := by decide

/-- J T J is the transpose of T: the crease exchanges the lattice's two shifts -/
theorem JTJ : M2.mul (M2.mul J T) J = ⟨1, 0, 1, 1⟩ := by decide

/-- the J-fraction's step on Catalan's tail (2, 1), elliptic at z = 1, 2, 3: their third, fourth and sixth powers are I
* Orders exactly 3, 4, 6, by their traces -1, 0, 1 (`trace_neg1_ne_one`, `trace0_sq`, `trace1_cube`,
  `trace1_sq_ne_one`). -/
theorem clocks_catalan :
    M2.pow ⟨0, 1, -1, -1⟩ 3 = M2.one ∧ M2.pow ⟨0, 1, -1, 0⟩ 4 = M2.one ∧ M2.pow ⟨0, 1, -1, 1⟩ 6 = M2.one := by
  decide

/-! ## V. Fixed points, Peano's remaining axioms, the one involutory quotient, and the orders by trace -/

/-- the given 1/0 is fixed by the shift: T(1/0) = 1/0, and so every power (`inf_fixed_Tpow`): a word's trailing shifts read nothing -/
theorem inf_fixed_T : M2.act T inf = inf := by decide

/-- the crease fixes 1: J(1) = 1 -/
theorem one_fixed_J : M2.act J (1, 1) = (1, 1) := by decide

/-- an identification of numerals, [...; a] = [...; a - 1, 1], keeps the value: the crease fixes 1 (`one_fixed_J`) -/
theorem trailing_one (r : List ℤ) (a : ℤ) : val (r ++ [a]) = val (r ++ [a - 1, 1]) := by
  have h1 : M2.act (word [a]) inf = (a, 1) := by simp [word, Q, M2.mul, M2.one, M2.act, inf]
  have h2 : M2.act (word [a - 1, 1]) inf = (a, 1) := by simp [word, Q, M2.mul, M2.one, M2.act, inf]
  simp only [val, word_append, M2.act_mul, h1, h2]

/-- Peano: zero is no successor -/
theorem succ_ne_zero (n : ℕ) : M2.act T ((n : ℤ), 1) ≠ (0, 1) := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only [M2.act, T] at h1
  omega

/-- Peano: the successor is injective (the shift is invertible) -/
theorem succ_inj (m n : ℤ) (h : M2.act T (m, 1) = M2.act T (n, 1)) : m = n := by
  simpa [M2.act, T] using h

/-- a quotient's square: Q(a)² = [[a² + 1, a], [a, 1]], trace a² + 2 -/
theorem quotient_square (a : ℤ) : M2.mul (Q a) (Q a) = ⟨a * a + 1, a, a, 1⟩ := by
  ext <;> simp [M2.mul, Q]

/-- a quotient is an involution (a reflection) only at a = 0: every other quotient reverses orientation without
being a reflection -/
theorem quotient_involution_iff (a : ℤ) : M2.mul (Q a) (Q a) = M2.one ↔ a = 0 := by
  rw [quotient_square]
  constructor
  · intro h
    have hb := congrArg M2.b h
    simpa [M2.one] using hb
  · rintro rfl
    decide

/-- the shift's powers, for any shift [[1, k], [0, 1]] -/
theorem shift_pow (k : ℤ) (n : ℕ) : M2.pow ⟨1, k, 0, 1⟩ n = ⟨1, k * n, 0, 1⟩ := by
  induction n with
  | zero => ext <;> simp [M2.pow, M2.one]
  | succ n ih =>
    show M2.mul (M2.pow ⟨1, k, 0, 1⟩ n) ⟨1, k, 0, 1⟩ = _
    rw [ih]
    ext <;> simp [M2.mul]
    all_goals ring

/-- multiplication of naturals is repetition of the word: (T^m)^n applied to 0 reads m n -/
theorem mul_is_repeat (m n : ℕ) : M2.act (M2.pow (M2.pow T m) n) (0, 1) = (((m * n : ℕ) : ℤ), 1) := by
  rw [T_pow, shift_pow]
  simp [M2.act]

/-- the place D_n and the n-fold repetition agree on every natural numeral -/
theorem place_is_repetition (m n : ℕ) :
    M2.act (D n) ((m : ℤ), 1) = M2.act (M2.pow (M2.pow T m) n) (0, 1) := by
  rw [mul_is_repeat]
  simp [M2.act, D, mul_comm]

/-- det 1, trace 0: the fourth power is I; with `trace0_sq` (x² = -I) the order is exactly 4 -/
theorem trace0_order4 (x : M2) (h1 : x.det = 1) (h0 : x.tr = 0) : M2.pow x 4 = M2.one := by
  have h2 : M2.pow x 2 = ⟨-1, 0, 0, -1⟩ := by
    show M2.mul (M2.mul M2.one x) x = _
    rw [M2.one_mul, M2.cayley_hamilton, h0, h1]
    ext <;> simp
  show M2.pow x (2 + 2) = M2.one
  rw [M2.pow_add, h2]
  decide

/-- det 1, trace 0: the square is -I, so no power below the fourth is I (the order is exactly 4, `trace0_order4`) -/
theorem trace0_sq (x : M2) (h1 : x.det = 1) (h0 : x.tr = 0) : M2.pow x 2 = ⟨-1, 0, 0, -1⟩ := by
  show M2.mul (M2.mul M2.one x) x = _
  rw [M2.one_mul, M2.cayley_hamilton, h0, h1]
  ext <;> simp

/-- det 1, trace -1: the cube is I, and x ≠ I (`trace_neg1_ne_one`), so the order is exactly 3 -/
theorem trace_neg1_order3 (x : M2) (h1 : x.det = 1) (h0 : x.tr = -1) : M2.pow x 3 = M2.one := by
  have h2 : M2.mul x x = ⟨-x.a - 1, -x.b, -x.c, -x.d - 1⟩ := by
    rw [M2.cayley_hamilton, h0, h1]
    ext <;> simp
  simp only [M2.det] at h1
  simp only [M2.tr] at h0
  show M2.mul (M2.mul (M2.mul M2.one x) x) x = M2.one
  rw [M2.one_mul, h2]
  ext <;> simp only [M2.mul, M2.one]
  · linear_combination h1 - x.a * h0
  · linear_combination -x.b * h0
  · linear_combination -x.c * h0
  · linear_combination h1 - x.d * h0

/-- det 1, trace 1: the sixth power is I; with `trace1_cube` (x^3 = -I) the order is exactly 6 -/
theorem trace1_order6 (x : M2) (h1 : x.det = 1) (h0 : x.tr = 1) : M2.pow x 6 = M2.one := by
  have h2 : M2.mul x x = ⟨x.a - 1, x.b, x.c, x.d - 1⟩ := by
    rw [M2.cayley_hamilton, h0, h1]
    ext <;> simp
  simp only [M2.det] at h1
  simp only [M2.tr] at h0
  have h3 : M2.pow x 3 = ⟨-1, 0, 0, -1⟩ := by
    show M2.mul (M2.mul (M2.mul M2.one x) x) x = _
    rw [M2.one_mul, h2]
    ext <;> simp only [M2.mul]
    · linear_combination -h1 + x.a * h0
    · linear_combination x.b * h0
    · linear_combination x.c * h0
    · linear_combination -h1 + x.d * h0
  show M2.pow x (3 + 3) = M2.one
  rw [M2.pow_add, h3]
  decide

/-- det 1, trace 1: the cube is -I, so the order is exactly 6 (`trace1_order6`, and x² ≠ I by `trace1_sq_ne_one`) -/
theorem trace1_cube (x : M2) (h1 : x.det = 1) (h0 : x.tr = 1) : M2.pow x 3 = ⟨-1, 0, 0, -1⟩ := by
  have h2 : M2.mul x x = ⟨x.a - 1, x.b, x.c, x.d - 1⟩ := by
    rw [M2.cayley_hamilton, h0, h1]
    ext <;> simp
  simp only [M2.det] at h1
  simp only [M2.tr] at h0
  show M2.mul (M2.mul (M2.mul M2.one x) x) x = _
  rw [M2.one_mul, h2]
  ext <;> simp only [M2.mul]
  · linear_combination -h1 + x.a * h0
  · linear_combination x.b * h0
  · linear_combination x.c * h0
  · linear_combination -h1 + x.d * h0


/-- trace -1: not the identity, whose trace is 2 -/
theorem trace_neg1_ne_one (x : M2) (h0 : x.tr = -1) : x ≠ M2.one := by
  rintro rfl
  simp [M2.tr, M2.one] at h0

/-- det 1, trace 1: the square is not I, since x² = I with x^3 = -I would make x = -I, of trace -2 -/
theorem trace1_sq_ne_one (x : M2) (h1 : x.det = 1) (h0 : x.tr = 1) : M2.pow x 2 ≠ M2.one := by
  intro h2
  have h3 := trace1_cube x h1 h0
  have hx : M2.pow x 3 = x := by
    show M2.mul (M2.pow x 2) x = x
    rw [h2, M2.one_mul]
  rw [hx] at h3
  rw [h3] at h0
  simp [M2.tr] at h0
/-- det -1, trace 0: a reflection, x² = I; every other crease word squares to a hyperbolic word (tr_sq) -/
theorem reflection_sq (x : M2) (h1 : x.det = -1) (h0 : x.tr = 0) : M2.mul x x = M2.one := by
  rw [M2.cayley_hamilton, h0, h1]
  ext <;> simp [M2.one]

/-! ## X. Two numbers and the binomial: the tensor's steps, the binomial transform on a matrix -/

/-- a tensor z(x, y) = (a x y + b x + c y + d) / (e x y + f x + g y + h) -/
structure Tensor where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ

namespace Tensor

/-- the tensor on two pairs -/
def eval (t : Tensor) (x y : ℤ × ℤ) : ℤ × ℤ :=
  (t.a * x.1 * y.1 + t.b * x.1 * y.2 + t.c * x.2 * y.1 + t.d * x.2 * y.2,
   t.e * x.1 * y.1 + t.f * x.1 * y.2 + t.g * x.2 * y.1 + t.h * x.2 * y.2)

/-- the tensor after it consumes a quotient q of x -/
def inX (t : Tensor) (q : ℤ) : Tensor :=
  ⟨q * t.a + t.c, q * t.b + t.d, t.a, t.b, q * t.e + t.g, q * t.f + t.h, t.e, t.f⟩

/-- the tensor after it consumes a quotient q of y -/
def inY (t : Tensor) (q : ℤ) : Tensor :=
  ⟨q * t.a + t.b, t.a, q * t.c + t.d, t.c, q * t.e + t.f, t.e, q * t.g + t.h, t.g⟩

/-- the tensor after it emits a quotient q -/
def out (t : Tensor) (q : ℤ) : Tensor :=
  ⟨t.e, t.f, t.g, t.h, t.a - q * t.e, t.b - q * t.f, t.c - q * t.g, t.d - q * t.h⟩

end Tensor

/-- the sum is a tensor: (0, 1, 1, 0, 0, 0, 0, 1) -/
theorem tensor_add (x y : ℤ × ℤ) :
    (⟨0, 1, 1, 0, 0, 0, 0, 1⟩ : Tensor).eval x y = (x.1 * y.2 + x.2 * y.1, x.2 * y.2) := by
  simp only [Tensor.eval, Prod.mk.injEq]
  constructor <;> ring

/-- the product is a tensor: (1, 0, 0, 0, 0, 0, 0, 1) -/
theorem tensor_mul (x y : ℤ × ℤ) : (⟨1, 0, 0, 0, 0, 0, 0, 1⟩ : Tensor).eval x y = (x.1 * y.1, x.2 * y.2) := by
  simp only [Tensor.eval, Prod.mk.injEq]
  constructor <;> ring

/-- consuming a quotient of x leaves the value: z(Q(q) x, y) = z'(x, y) -/
theorem tensor_in_x (t : Tensor) (q : ℤ) (x y : ℤ × ℤ) : t.eval (M2.act (Q q) x) y = (t.inX q).eval x y := by
  simp only [Tensor.eval, Tensor.inX, M2.act, Q, Prod.mk.injEq]
  constructor <;> ring

/-- consuming a quotient of y leaves the value: z(x, Q(q) y) = z'(x, y) -/
theorem tensor_in_y (t : Tensor) (q : ℤ) (x y : ℤ × ℤ) : t.eval x (M2.act (Q q) y) = (t.inY q).eval x y := by
  simp only [Tensor.eval, Tensor.inY, M2.act, Q, Prod.mk.injEq]
  constructor <;> ring

/-- emitting a quotient leaves the value: z(x, y) = Q(q) z'(x, y) -/
theorem tensor_out (t : Tensor) (q : ℤ) (x y : ℤ × ℤ) : M2.act (Q q) ((t.out q).eval x y) = t.eval x y := by
  simp only [Tensor.eval, Tensor.out, M2.act, Q, Prod.mk.injEq]
  constructor <;> ring

/-- BINOMIAL on a matrix: the binomial transform of the moments A^k is the moments of A + 1, entry by entry, over any
commutative ring, so rational J-fraction coefficients too -/
theorem binomial_is_shift {R : Type*} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (n : ℕ) (i j : Fin m) :
    ((A + 1) ^ n) i j = (Finset.range (n + 1)).sum fun k => (n.choose k : R) * (A ^ k) i j := by
  rw [(Commute.one_right A).add_pow n, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]

/-- A + 1 moves every diagonal entry (alpha) by 1 and no other entry (beta), over any commutative ring -/
theorem binomial_moves_alpha {R : Type*} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (A + 1) i i = A i i + 1 ∧ (i ≠ j → (A + 1) i j = A i j) := by
  constructor
  · simp [Matrix.add_apply]
  · intro h
    simp [Matrix.add_apply, h]

/-! # Word -/

/-! ## M. The model is faithful: every nonnegative unimodular matrix is exactly one reduced word in T and J -/

/-- the two letters -/
inductive Letter
  | t
  | j
  deriving DecidableEq, Repr

/-- the matrix of a word, the first letter outermost -/
def ev : List Letter → M2
  | [] => M2.one
  | Letter.t :: w => M2.mul T (ev w)
  | Letter.j :: w => M2.mul J (ev w)

/-- reduced, no two creases in a row (J J = ε): the empty word, a shift before a reduced word, the crease alone, a
crease and a shift before a reduced word -/
inductive Red : List Letter → Prop
  | nil : Red []
  | t (w : List Letter) : Red w → Red (Letter.t :: w)
  | j_nil : Red [Letter.j]
  | jt (w : List Letter) : Red w → Red (Letter.j :: Letter.t :: w)

/-- nonnegative entries -/
abbrev Nn (x : M2) : Prop := 0 ≤ x.a ∧ 0 ≤ x.b ∧ 0 ≤ x.c ∧ 0 ≤ x.d

/-- unimodular: determinant ±1 -/
abbrev Uni (x : M2) : Prop := x.det = 1 ∨ x.det = -1

/-- prefixing the shift t adds the second row to the first -/
theorem ev_t (w : List Letter) :
    ev (Letter.t :: w) = ⟨(ev w).a + (ev w).c, (ev w).b + (ev w).d, (ev w).c, (ev w).d⟩ := by
  show M2.mul T (ev w) = _
  ext <;> simp [M2.mul, T]

/-- prefixing the crease j swaps the two rows -/
theorem ev_j (w : List Letter) : ev (Letter.j :: w) = ⟨(ev w).c, (ev w).d, (ev w).a, (ev w).b⟩ := by
  show M2.mul J (ev w) = _
  ext <;> simp [M2.mul, J]

/-- every word's matrix has nonnegative entries -/
theorem ev_nn (w : List Letter) : Nn (ev w) := by
  induction w with
  | nil => exact ⟨by decide, by decide, by decide, by decide⟩
  | cons a w ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    cases a
    · rw [ev_t]
      exact ⟨by show 0 ≤ (ev w).a + (ev w).c; linarith, by show 0 ≤ (ev w).b + (ev w).d; linarith, h3, h4⟩
    · rw [ev_j]
      exact ⟨h3, h4, h1, h2⟩

/-- and determinant 1 or -1 -/
theorem ev_uni (w : List Letter) : Uni (ev w) := by
  induction w with
  | nil => left; decide
  | cons a w ih =>
    have hT : T.det = 1 := by decide
    have hJ : J.det = -1 := by decide
    cases a
    · show (M2.mul T (ev w)).det = 1 ∨ (M2.mul T (ev w)).det = -1
      rw [M2.det_mul, hT, one_mul]
      exact ih
    · show (M2.mul J (ev w)).det = 1 ∨ (M2.mul J (ev w)).det = -1
      rw [M2.det_mul, hJ]
      rcases ih with h | h <;> rw [h] <;> decide

/-- the tail of a reduced word is reduced -/
theorem red_tail (a : Letter) (w : List Letter) (h : Red (a :: w)) : Red w := by
  cases h with
  | t _ h' => exact h'
  | j_nil => exact Red.nil
  | jt _ h' => exact Red.t _ h'

/-- after a crease, a reduced word ends or continues with a shift -/
theorem red_j_cases (v : List Letter) (h : Red (Letter.j :: v)) : v = [] ∨ ∃ u, v = Letter.t :: u := by
  cases h with
  | j_nil => exact Or.inl rfl
  | jt u _ => exact Or.inr ⟨u, rfl⟩

/-- peeling a shift, the second row taken from the first, keeps the determinant -/
theorem det_peel_t (x : M2) : (⟨x.a - x.c, x.b - x.d, x.c, x.d⟩ : M2).det = x.det := by
  simp only [M2.det]; ring

/-- peeling j t negates it -/
theorem det_peel_jt (x : M2) : (⟨x.c - x.a, x.d - x.b, x.a, x.b⟩ : M2).det = -x.det := by
  simp only [M2.det]; ring

/-- off I and J, one row of a nonnegative unimodular matrix dominates the other: the first letter is forced -/
theorem rows_comparable (x : M2) (hn : Nn x) (hu : Uni x) (h1 : x ≠ M2.one) (hJ : x ≠ J) :
    (x.c ≤ x.a ∧ x.d ≤ x.b) ∨ (x.a ≤ x.c ∧ x.b ≤ x.d) := by
  obtain ⟨ha, hb, hc, hd⟩ := hn
  unfold Uni M2.det at hu
  rcases le_or_gt x.c x.a with hca | hca
  · rcases le_or_gt x.d x.b with hdb | hdb
    · exact Or.inl ⟨hca, hdb⟩
    rcases le_or_gt x.a x.c with hac | hac
    · exact Or.inr ⟨hac, le_of_lt hdb⟩
    exfalso
    have hp : (x.c + 1) * (x.b + 1) ≤ x.a * x.d := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    have hsum : x.b + x.c ≤ 0 := by rcases hu with h | h <;> nlinarith
    have hb0 : x.b = 0 := by omega
    have hc0 : x.c = 0 := by omega
    rw [hb0, hc0] at hu hp
    norm_num at hp
    have had : x.a * x.d = 1 := by rcases hu with h | h <;> linarith
    have ha1 : x.a = 1 := Int.eq_one_of_mul_eq_one_right ha had
    have hd1 : x.d = 1 := Int.eq_one_of_mul_eq_one_left hd had
    exact h1 (by ext <;> simp [M2.one, ha1, hb0, hc0, hd1])
  · rcases le_or_gt x.b x.d with hbd | hbd
    · exact Or.inr ⟨le_of_lt hca, hbd⟩
    exfalso
    have hp : (x.a + 1) * (x.d + 1) ≤ x.c * x.b := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    have hsum : x.a + x.d ≤ 0 := by rcases hu with h | h <;> nlinarith
    have ha0 : x.a = 0 := by omega
    have hd0 : x.d = 0 := by omega
    rw [ha0, hd0] at hu hp
    norm_num at hp hu
    have hbc : x.b * x.c = 1 := by rcases hu with h | h <;> nlinarith
    have hb1 : x.b = 1 := Int.eq_one_of_mul_eq_one_right hb hbc
    have hc1 : x.c = 1 := Int.eq_one_of_mul_eq_one_left hc hbc
    exact hJ (by ext <;> simp [J, ha0, hd0, hb1, hc1])

/-- and never both: rows dominating each other both ways are equal, and a matrix with equal rows has determinant 0, not ±1 -/
theorem rows_not_both (x : M2) (hu : Uni x) (h : (x.c ≤ x.a ∧ x.d ≤ x.b) ∧ (x.a ≤ x.c ∧ x.b ≤ x.d)) : False := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have hc : x.c = x.a := le_antisymm h1 h3
  have hd : x.d = x.b := le_antisymm h2 h4
  rcases hu with hu | hu <;> simp only [M2.det, hc, hd] at hu <;> nlinarith [hu]

/-- existence: Euclid on the rows, the entry sum falling at every letter -/
theorem exists_word_aux (n : ℕ) :
    ∀ x : M2, Nn x → Uni x → x.a + x.b + x.c + x.d ≤ n → ∃ w, Red w ∧ ev w = x := by
  induction n with
  | zero =>
    intro x hn hu hs
    obtain ⟨ha, hb, hc, hd⟩ := hn
    exfalso
    have ha0 : x.a = 0 := by omega
    have hb0 : x.b = 0 := by omega
    have hc0 : x.c = 0 := by omega
    have hd0 : x.d = 0 := by omega
    unfold Uni M2.det at hu
    rw [ha0, hb0, hc0, hd0] at hu
    simp at hu
  | succ n ih =>
    intro x hn hu hs
    obtain ⟨ha, hb, hc, hd⟩ := hn
    by_cases h1 : x = M2.one
    · exact ⟨[], Red.nil, by rw [h1]; rfl⟩
    by_cases hJ : x = J
    · exact ⟨[Letter.j], Red.j_nil, by rw [hJ]; decide⟩
    rcases rows_comparable x ⟨ha, hb, hc, hd⟩ hu h1 hJ with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · have hcd : 0 < x.c + x.d := by
        by_contra hz
        have hc0 : x.c = 0 := by omega
        have hd0 : x.d = 0 := by omega
        unfold Uni M2.det at hu
        rw [hc0, hd0] at hu
        simp at hu
      obtain ⟨w, hw, hev⟩ := ih ⟨x.a - x.c, x.b - x.d, x.c, x.d⟩
        ⟨by show 0 ≤ x.a - x.c; omega, by show 0 ≤ x.b - x.d; omega, hc, hd⟩
        (by unfold Uni; rw [det_peel_t]; exact hu)
        (by show x.a - x.c + (x.b - x.d) + x.c + x.d ≤ (n : ℤ); omega)
      refine ⟨Letter.t :: w, Red.t w hw, ?_⟩
      rw [ev_t, hev]
      ext <;> simp
    · have hab : 0 < x.a + x.b := by
        by_contra hz
        have ha0 : x.a = 0 := by omega
        have hb0 : x.b = 0 := by omega
        unfold Uni M2.det at hu
        rw [ha0, hb0] at hu
        simp at hu
      obtain ⟨w, hw, hev⟩ := ih ⟨x.c - x.a, x.d - x.b, x.a, x.b⟩
        ⟨by show 0 ≤ x.c - x.a; omega, by show 0 ≤ x.d - x.b; omega, ha, hb⟩
        (by unfold Uni; rw [det_peel_jt]; rcases hu with h | h <;> simp [h])
        (by show x.c - x.a + (x.d - x.b) + x.a + x.b ≤ (n : ℤ); omega)
      refine ⟨Letter.j :: Letter.t :: w, Red.jt w hw, ?_⟩
      rw [ev_j, ev_t, hev]
      ext <;> simp

/-- every nonnegative matrix of determinant 1 or -1 is the matrix of some reduced word -/
theorem exists_word (x : M2) (hn : Nn x) (hu : Uni x) : ∃ w, Red w ∧ ev w = x :=
  exists_word_aux (x.a + x.b + x.c + x.d).toNat x hn hu (Int.self_le_toNat _)

/-- T cancels on the left -/
theorem T_cancel (x y : M2) (h : M2.mul T x = M2.mul T y) : x = y := by
  have h' := congrArg (M2.mul Tinv) h
  rwa [← M2.mul_assoc, ← M2.mul_assoc, Tinv_T, M2.one_mul, M2.one_mul] at h'

/-- J cancels on the left -/
theorem J_cancel (x y : M2) (h : M2.mul J x = M2.mul J y) : x = y := by
  have h' := congrArg (M2.mul J) h
  rwa [← M2.mul_assoc, ← M2.mul_assoc, point3_JJ, M2.one_mul, M2.one_mul] at h'

/-- no word that begins with a shift reads the identity -/
theorem ev_t_ne_one (v : List Letter) (h : ev (Letter.t :: v) = M2.one) : False := by
  rw [ev_t] at h
  obtain ⟨_, h2, _, _⟩ := ev_nn v
  simp only [M2.one, M2.mk.injEq] at h
  omega

/-- nor one that begins with j t -/
theorem ev_jt_ne_one (u : List Letter) (h : ev (Letter.j :: Letter.t :: u) = M2.one) : False := by
  rw [ev_j, ev_t] at h
  obtain ⟨h1, _, _, _⟩ := ev_nn u
  simp only [M2.one, M2.mk.injEq] at h
  omega

/-- no word that begins with a shift reads J -/
theorem ev_t_ne_J (v : List Letter) (h : ev (Letter.t :: v) = J) : False := by
  rw [ev_t] at h
  obtain ⟨h1, _, _, _⟩ := ev_nn v
  simp only [J, M2.mk.injEq] at h
  omega

/-- the single crease does not read the identity -/
theorem ev_j_ne_one : ev [Letter.j] ≠ M2.one := by decide

/-- a word opening with the shift and one opening with the crease and then a shift are never the same matrix: the one has its
first row dominant, the other its second -/
theorem ev_t_ne_ev_jt (v u : List Letter) (h : ev (Letter.t :: v) = ev (Letter.j :: Letter.t :: u)) : False := by
  rw [ev_t, ev_j, ev_t] at h
  obtain ⟨hv1, hv2, hv3, hv4⟩ := ev_nn v
  obtain ⟨hu1, hu2, hu3, hu4⟩ := ev_nn u
  have hd := ev_uni v
  unfold Uni M2.det at hd
  simp only [M2.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  have ha0 : (ev v).a = 0 := by omega
  have hb0 : (ev v).b = 0 := by omega
  rw [ha0, hb0] at hd
  simp at hd

/-- uniqueness: two reduced words with one matrix are one word -/
theorem unique_word (w : List Letter) : ∀ w', Red w → Red w' → ev w = ev w' → w = w' := by
  induction w with
  | nil =>
    intro w' _ hr' h
    cases w' with
    | nil => rfl
    | cons b u =>
      cases b
      · exact (ev_t_ne_one u h.symm).elim
      · rcases red_j_cases u hr' with rfl | ⟨u', rfl⟩
        · exact absurd h.symm ev_j_ne_one
        · exact (ev_jt_ne_one u' h.symm).elim
  | cons a v ih =>
    intro w' hr hr' h
    cases w' with
    | nil =>
      cases a
      · exact (ev_t_ne_one v h).elim
      · rcases red_j_cases v hr with rfl | ⟨v', rfl⟩
        · exact absurd h ev_j_ne_one
        · exact (ev_jt_ne_one v' h).elim
    | cons b u =>
      cases a <;> cases b
      · simp only [ev] at h
        rw [ih u (red_tail _ _ hr) (red_tail _ _ hr') (T_cancel _ _ h)]
      · rcases red_j_cases u hr' with rfl | ⟨u', rfl⟩
        · exact (ev_t_ne_J v h).elim
        · exact (ev_t_ne_ev_jt v u' h).elim
      · rcases red_j_cases v hr with rfl | ⟨v', rfl⟩
        · exact (ev_t_ne_J u h.symm).elim
        · exact (ev_t_ne_ev_jt u v' h.symm).elim
      · simp only [ev] at h
        rw [ih u (red_tail _ _ hr) (red_tail _ _ hr') (J_cancel _ _ h)]

/-- the model is faithful: every nonnegative unimodular matrix is exactly one reduced word, so the words of
Axiom Ś (the free product of the shift's monoid and the crease's Z/2) are the matrices, with no relation beyond J J = ε -/
theorem faithful (x : M2) (hn : Nn x) (hu : Uni x) : ∃! w, Red w ∧ ev w = x := by
  obtain ⟨w, hw, he⟩ := exists_word x hn hu
  exact ⟨w, ⟨hw, he⟩, fun w' ⟨hw', he'⟩ => unique_word w' w hw' hw (he'.trans he.symm)⟩

/-! ## K. The points on the pair, the trailing zero, Ś2 in the model, the stabiliser, and reduction -/

/-- point 1 on the pair, with no convention about division by zero: [0; r] applied to 1/0 is [r]'s pair swapped -/
theorem point1_pair (r : List ℤ) :
    M2.act (word (0 :: r)) inf = ((M2.act (word r) inf).2, (M2.act (word r) inf).1) := by
  simp only [word, M2.act_mul]
  simp [M2.act, Q]

/-- point 2 on the pair: [0; n] applied to 1/0 is (1, n), for every n, 0 included (where it is 1/0 again) -/
theorem point2_pair (n : ℤ) : M2.act (word [0, n]) inf = (1, n) := by
  simp [word, Q, M2.mul, M2.one, M2.act, inf]

/-- point 4, the trailing zero: [..., a, b, 0] = [..., a], since Q(b) J (1/0) = Q(b)(0) = 1/0 -/
theorem point4_trailing (r : List ℤ) (a b : ℤ) :
    M2.act (word (r ++ [a, b, 0])) inf = M2.act (word (r ++ [a])) inf := by
  have h : M2.act (word [a, b, 0]) inf = M2.act (word [a]) inf := by
    simp [word, Q, M2.mul, M2.one, M2.act, inf]
  simp only [word_append, M2.act_mul, h]

/-- a word of k quotients has determinant (-1)^k: each quotient is one crease -/
theorem word_det (as : List ℤ) : (word as).det = (-1) ^ as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    show (M2.mul (Q a) (word as)).det = (-1) ^ (as.length + 1)
    rw [M2.det_mul, point3_det, ih, pow_succ]
    ring

/-- Ś2 in the model: no nonempty string of shifts is the empty word (the empty string is: T^0 = I) -/
theorem T_pow_ne_one (n : ℕ) (hn : 0 < n) : M2.pow T n ≠ M2.one := by
  rw [T_pow]
  intro h
  have hb : (n : ℤ) = 0 := congrArg M2.b h
  omega

/-- the given, applied to: a word sends 1/0 to its first column -/
theorem act_inf (x : M2) : M2.act x inf = (x.a, x.c) := by
  simp [M2.act, inf]

/-- Bhaskara's khahara, one way: a word that leaves the given 1/0 where it is is a shift (every shift does, `inf_fixed_Tpow`) -/
theorem stab_inf (x : M2) (hn : Nn x) (hu : Uni x) (hfix : (M2.act x inf).2 = 0) : ∃ n : ℕ, x = M2.pow T n := by
  obtain ⟨ha, hb, _, hd⟩ := hn
  have hc : x.c = 0 := by simpa [act_inf] using hfix
  unfold Uni M2.det at hu
  rw [hc] at hu
  simp only [mul_zero, sub_zero] at hu
  have had : x.a * x.d = 1 := by
    rcases hu with h | h
    · exact h
    · exact absurd h (by nlinarith [mul_nonneg ha hd])
  have ha1 : x.a = 1 := Int.eq_one_of_mul_eq_one_right ha had
  have hd1 : x.d = 1 := Int.eq_one_of_mul_eq_one_left hd had
  refine ⟨x.b.toNat, ?_⟩
  rw [T_pow]
  ext
  · exact ha1
  · exact (Int.toNat_of_nonneg hb).symm
  · exact hc
  · exact hd1

/-- Bhaskara's khahara, the other way: every shift leaves the given 1/0 where it is, T^n (1/0) = 1/0 -/
theorem inf_fixed_Tpow (n : ℕ) : M2.act (M2.pow T n) inf = inf := by
  induction n with
  | zero => decide
  | succ n ih =>
    show M2.act (M2.mul (M2.pow T n) T) inf = inf
    rw [M2.act_mul, inf_fixed_T, ih]

/-- the crease is the one word that undoes itself: in the monoid, x x = I only for I and J -/
theorem involution_iff (x : M2) (hn : Nn x) (hu : Uni x) : M2.mul x x = M2.one ↔ x = M2.one ∨ x = J := by
  constructor
  · intro h
    obtain ⟨ha, hb, hc, hd⟩ := hn
    rw [M2.cayley_hamilton] at h
    simp only [M2.one, M2.mk.injEq, M2.tr, M2.det] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    unfold Uni M2.det at hu
    rcases hu with hu | hu
    · left
      have hs : 0 < x.a + x.d := by nlinarith
      have had : x.a = x.d := by nlinarith
      have ha1 : x.a = 1 := by nlinarith
      have hd1 : x.d = 1 := by omega
      have hb0 : x.b = 0 := by nlinarith
      have hc0 : x.c = 0 := by nlinarith
      ext
      · exact ha1
      · exact hb0
      · exact hc0
      · exact hd1
    · right
      have ht : x.a + x.d = 0 := by nlinarith
      have ha0 : x.a = 0 := by omega
      have hd0 : x.d = 0 := by omega
      have hbc : x.b * x.c = 1 := by rw [ha0, hd0] at hu; linarith
      have hb1 : x.b = 1 := Int.eq_one_of_mul_eq_one_right hb hbc
      have hc1 : x.c = 1 := Int.eq_one_of_mul_eq_one_left hc hbc
      ext
      · exact ha0
      · exact hb1
      · exact hc1
      · exact hd0
  · rintro (rfl | rfl)
    · decide
    · exact point3_JJ

/-- the matrix of one letter -/
def letter : Letter → M2
  | Letter.t => T
  | Letter.j => J

/-- ev (a :: w) is the letter's matrix times ev w -/
theorem ev_cons (a : Letter) (w : List Letter) : ev (a :: w) = M2.mul (letter a) (ev w) := by
  cases a <;> rfl

/-- a letter put before a reduced word, the creases cancelling: the one step of reduction -/
def push : Letter → List Letter → List Letter
  | Letter.t, u => Letter.t :: u
  | Letter.j, Letter.j :: u => u
  | Letter.j, u => Letter.j :: u

/-- every word reduced: each letter pushed onto the reduced rest -/
def reduce : List Letter → List Letter
  | [] => []
  | a :: w => push a (reduce w)

/-- pushing a letter onto a reduced word keeps it reduced -/
theorem red_push (a : Letter) (u : List Letter) (h : Red u) : Red (push a u) := by
  cases a with
  | t => exact Red.t u h
  | j =>
    rcases u with _ | ⟨_ | _, u⟩
    · exact Red.j_nil
    · exact Red.jt u (red_tail _ _ h)
    · exact red_tail _ _ h

/-- push a u reads the same matrix as a :: u -/
theorem ev_push (a : Letter) (u : List Letter) : ev (push a u) = ev (a :: u) := by
  cases a with
  | t => rfl
  | j =>
    rcases u with _ | ⟨_ | _, u⟩
    · rfl
    · rfl
    · show ev u = M2.mul J (M2.mul J (ev u))
      rw [← M2.mul_assoc, point3_JJ, M2.one_mul]

/-- reduce w is reduced -/
theorem red_reduce (w : List Letter) : Red (reduce w) := by
  induction w with
  | nil => exact Red.nil
  | cons a w ih => exact red_push a _ ih

/-- and reads the same matrix as w -/
theorem ev_reduce (w : List Letter) : ev (reduce w) = ev w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show ev (push a (reduce w)) = ev (a :: w)
    rw [ev_push, ev_cons, ev_cons, ih]

/-- Ś3 as a theorem of the model: two words are the same matrix exactly when they agree after every J J is deleted -/
theorem same_word_iff (w w' : List Letter) : ev w = ev w' ↔ reduce w = reduce w' := by
  constructor
  · intro h
    exact unique_word (reduce w) (reduce w') (red_reduce w) (red_reduce w') (by rw [ev_reduce, ev_reduce, h])
  · intro h
    rw [← ev_reduce w, ← ev_reduce w', h]

/-! ## L. The exact form of the Śūnya conjecture: the two shifts R = T and L = J T J -/

/-!
* A word in T and J is a word in R and L, followed by J when its creases are odd.
* The run-lengths of the L/R word are the quotients of the T/J word.
* The L/R word of a matrix is unique.
* The crease exchanges the two shifts.
* The two shifts, as Stern-Brocot's letters, reach every positive rational from the given and never reach zero; in
  Axiom Ś's letters each L = J T J carries the crease twice. -/

/-- the second shift, x ↦ x/(x + 1): J T J (the theorem `JTJ`) -/
def L : M2 := ⟨1, 0, 1, 1⟩

/-- L = J T J -/
theorem L_is_JTJ : M2.mul (M2.mul J T) J = L := by rw [JTJ]; rfl

/-- the crease carries one shift to the other: J T = L J (the reverse, J L = T J, is `JL_TJ`) -/
theorem JT_LJ : M2.mul J T = M2.mul L J := by decide

/-- J L = T J: the crease swaps the two shifts -/
theorem JL_TJ : M2.mul J L = M2.mul T J := by decide

/-- the two shifts as letters -/
inductive Side
  | r
  | l
  deriving DecidableEq, Repr

/-- the matrix of a word in the two shifts, the first letter outermost -/
def evLR : List Side → M2
  | [] => M2.one
  | Side.r :: w => M2.mul T (evLR w)
  | Side.l :: w => M2.mul L (evLR w)

/-- prefixing R adds the second row to the first -/
theorem evLR_r (w : List Side) :
    evLR (Side.r :: w) = ⟨(evLR w).a + (evLR w).c, (evLR w).b + (evLR w).d, (evLR w).c, (evLR w).d⟩ := by
  show M2.mul T (evLR w) = _
  ext <;> simp [M2.mul, T]

/-- prefixing L adds the first row to the second -/
theorem evLR_l (w : List Side) :
    evLR (Side.l :: w) = ⟨(evLR w).a, (evLR w).b, (evLR w).a + (evLR w).c, (evLR w).b + (evLR w).d⟩ := by
  show M2.mul L (evLR w) = _
  ext <;> simp [M2.mul, L]

/-- every L/R word's matrix has nonnegative entries -/
theorem evLR_nn (w : List Side) : Nn (evLR w) := by
  induction w with
  | nil => exact ⟨by decide, by decide, by decide, by decide⟩
  | cons a w ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    cases a
    · rw [evLR_r]
      exact ⟨by show 0 ≤ (evLR w).a + (evLR w).c; linarith, by show 0 ≤ (evLR w).b + (evLR w).d; linarith, h3, h4⟩
    · rw [evLR_l]
      exact ⟨h1, h2, by show 0 ≤ (evLR w).a + (evLR w).c; linarith, by show 0 ≤ (evLR w).b + (evLR w).d; linarith⟩

/-- and determinant 1 -/
theorem evLR_det (w : List Side) : (evLR w).det = 1 := by
  induction w with
  | nil => decide
  | cons a w ih =>
    cases a
    · show (M2.mul T (evLR w)).det = 1
      rw [M2.det_mul, ih]; decide
    · show (M2.mul L (evLR w)).det = 1
      rw [M2.det_mul, ih]; decide

/-- a T/J word read in the two shifts: a shift is R, or L once an odd number of creases has been read; a crease flips -/
def toLR : Bool → List Letter → List Side
  | _, [] => []
  | b, Letter.t :: w => (cond b Side.l Side.r) :: toLR b w
  | b, Letter.j :: w => toLR (!b) w

/-- whether a word's creases are odd in number -/
def creasesOdd : List Letter → Bool
  | [] => false
  | Letter.t :: w => creasesOdd w
  | Letter.j :: w => !creasesOdd w

/-- a T/J word reads as its L/R word followed by J when its creases are odd and by nothing otherwise; J times it reads the other way, with J and nothing exchanged -/
theorem ev_lr (w : List Letter) :
    ev w = M2.mul (evLR (toLR false w)) (cond (creasesOdd w) J M2.one) ∧
    M2.mul J (ev w) = M2.mul (evLR (toLR true w)) (cond (creasesOdd w) M2.one J) := by
  induction w with
  | nil => exact ⟨by simp [ev, evLR, toLR, creasesOdd, M2.mul_one], by simp [ev, evLR, toLR, creasesOdd, M2.mul_one, M2.one_mul]⟩
  | cons a w ih =>
    obtain ⟨h0, h1⟩ := ih
    cases a with
    | t =>
      constructor
      · show M2.mul T (ev w) = M2.mul (M2.mul T (evLR (toLR false w))) (cond (creasesOdd w) J M2.one)
        rw [M2.mul_assoc, ← h0]
      · show M2.mul J (M2.mul T (ev w)) = M2.mul (M2.mul L (evLR (toLR true w))) (cond (creasesOdd w) M2.one J)
        rw [← M2.mul_assoc, JT_LJ, M2.mul_assoc, h1, M2.mul_assoc]
    | j =>
      constructor
      · show M2.mul J (ev w) = M2.mul (evLR (toLR true w)) (cond (!creasesOdd w) J M2.one)
        rw [h1]
        cases creasesOdd w <;> rfl
      · show M2.mul J (M2.mul J (ev w)) = M2.mul (evLR (toLR false w)) (cond (!creasesOdd w) M2.one J)
        rw [← M2.mul_assoc, point3_JJ, M2.one_mul, h0]
        cases creasesOdd w <;> rfl

/-- a word of the crease and the shift is a word of the two shifts, followed by the crease when its creases are odd -/
theorem ev_eq_lr (w : List Letter) : ev w = M2.mul (evLR (toLR false w)) (cond (creasesOdd w) J M2.one) :=
  (ev_lr w).1

/-- every nonnegative unimodular word is an L/R word or an L/R word followed by one crease -/
theorem two_shifts_and_crease (x : M2) (hn : Nn x) (hu : Uni x) :
    ∃ w : List Side, x = evLR w ∨ x = M2.mul (evLR w) J := by
  obtain ⟨w, _, hw⟩ := exists_word x hn hu
  refine ⟨toLR false w, ?_⟩
  rw [← hw, ev_eq_lr w]
  cases creasesOdd w
  · left; exact M2.mul_one _
  · right; rfl

/-- the second shift undone -/
def Linv : M2 := ⟨1, 0, -1, 1⟩

/-- L^-1 L is the identity -/
theorem Linv_L : M2.mul Linv L = M2.one := by decide

/-- L cancels on the left -/
theorem L_cancel (x y : M2) (h : M2.mul L x = M2.mul L y) : x = y := by
  have h' := congrArg (M2.mul Linv) h
  rwa [← M2.mul_assoc, ← M2.mul_assoc, Linv_L, M2.one_mul, M2.one_mul] at h'

/-- no L/R word that begins with R reads the identity -/
theorem evLR_r_ne_one (w : List Side) (h : evLR (Side.r :: w) = M2.one) : False := by
  rw [evLR_r] at h
  obtain ⟨_, hb, _, _⟩ := evLR_nn w
  simp only [M2.one, M2.mk.injEq] at h
  omega

/-- nor one that begins with L -/
theorem evLR_l_ne_one (w : List Side) (h : evLR (Side.l :: w) = M2.one) : False := by
  rw [evLR_l] at h
  obtain ⟨_, _, hc, _⟩ := evLR_nn w
  simp only [M2.one, M2.mk.injEq] at h
  omega

/-- a word opening with R and one opening with L are never the same matrix: the one has its first row dominant, the
other its second, and a matrix with both rows dominant has equal rows and determinant 0 -/
theorem evLR_r_ne_l (v u : List Side) (h : evLR (Side.r :: v) = evLR (Side.l :: u)) : False := by
  rw [evLR_r, evLR_l] at h
  obtain ⟨hv1, hv2, hv3, hv4⟩ := evLR_nn v
  obtain ⟨hu1, hu2, hu3, hu4⟩ := evLR_nn u
  have hd := evLR_det v
  unfold M2.det at hd
  simp only [M2.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  have ha0 : (evLR v).a = 0 := by omega
  have hb0 : (evLR v).b = 0 := by omega
  rw [ha0, hb0] at hd
  simp at hd

/-- the L/R word of a matrix is unique: the two shifts generate a free monoid (Stern-Brocot) -/
theorem unique_lr (w : List Side) : ∀ w', evLR w = evLR w' → w = w' := by
  induction w with
  | nil =>
    intro w' h
    cases w' with
    | nil => rfl
    | cons b u =>
      cases b
      · exact (evLR_r_ne_one u h.symm).elim
      · exact (evLR_l_ne_one u h.symm).elim
  | cons a v ih =>
    intro w' h
    cases w' with
    | nil =>
      cases a
      · exact (evLR_r_ne_one v h).elim
      · exact (evLR_l_ne_one v h).elim
    | cons b u =>
      cases a <;> cases b
      · simp only [evLR] at h
        rw [ih u (T_cancel _ _ h)]
      · exact (evLR_r_ne_l v u h).elim
      · exact (evLR_r_ne_l u v h.symm).elim
      · simp only [evLR] at h
        rw [ih u (L_cancel _ _ h)]

/-- every nonnegative matrix of determinant 1 is an L/R word: the crease count of its T/J word is even -/
theorem exists_lr (x : M2) (hn : Nn x) (hd : x.det = 1) : ∃ w : List Side, evLR w = x := by
  obtain ⟨w, _, hw⟩ := exists_word x hn (Or.inl hd)
  have h := ev_eq_lr w
  rw [hw] at h
  cases hodd : creasesOdd w
  · rw [hodd] at h
    exact ⟨toLR false w, by rw [h]; exact (M2.mul_one _).symm⟩
  · exfalso
    rw [hodd] at h
    have hdet := congrArg M2.det h
    rw [M2.det_mul, evLR_det, hd] at hdet
    exact absurd hdet (by decide)

/-- the mirror of an L/R word: R and L exchanged -/
def mirror : List Side → List Side
  | [] => []
  | Side.r :: w => Side.l :: mirror w
  | Side.l :: w => Side.r :: mirror w

/-- the crease exchanges the two shifts along a whole word: J w = (mirror w) J
* With `JT_LJ`: the nonnegative unimodular monoid is the free monoid on R and L, extended by the swap J. -/
theorem J_mirror (w : List Side) : M2.mul J (evLR w) = M2.mul (evLR (mirror w)) J := by
  induction w with
  | nil => simp [evLR, mirror, M2.mul_one, M2.one_mul]
  | cons a w ih =>
    cases a
    · show M2.mul J (M2.mul T (evLR w)) = M2.mul (M2.mul L (evLR (mirror w))) J
      rw [← M2.mul_assoc, JT_LJ, M2.mul_assoc, ih, M2.mul_assoc]
    · show M2.mul J (M2.mul L (evLR w)) = M2.mul (M2.mul T (evLR (mirror w))) J
      rw [← M2.mul_assoc, JL_TJ, M2.mul_assoc, ih, M2.mul_assoc]

/-- the T/J word of the quotients a_0, ..., a_n: T^a_0 J T^a_1 J ⋯ T^a_n J -/
def tj : List ℕ → List Letter
  | [] => []
  | a :: as => List.replicate a Letter.t ++ Letter.j :: tj as

/-- the L/R word with the run-lengths a_0, ..., a_n: R^a_0 L^a_1 R^a_2 ⋯ (from L when b is true) -/
def lr : Bool → List ℕ → List Side
  | _, [] => []
  | b, a :: as => List.replicate a (cond b Side.l Side.r) ++ lr (!b) as

/-- whether the number of quotients is odd -/
def oddLen : List ℕ → Bool
  | [] => false
  | _ :: as => !oddLen as

/-- a run of a shifts becomes a run of a letters, L or R by the flag -/
theorem toLR_rep (b : Bool) (a : ℕ) (w : List Letter) :
    toLR b (List.replicate a Letter.t ++ w) = List.replicate a (cond b Side.l Side.r) ++ toLR b w := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [List.replicate_succ, List.cons_append, toLR, ih]

/-- a run of shifts leaves the creases' parity unchanged -/
theorem creasesOdd_rep (a : ℕ) (w : List Letter) : creasesOdd (List.replicate a Letter.t ++ w) = creasesOdd w := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [List.replicate_succ, List.cons_append, creasesOdd, ih]

/-- the T/J word of the quotients as reads as the L/R word lr b as -/
theorem toLR_tj (b : Bool) (as : List ℕ) : toLR b (tj as) = lr b as := by
  induction as generalizing b with
  | nil => rfl
  | cons a as ih => simp only [tj, lr, toLR_rep, toLR, ih]

/-- the T/J word of as has an odd number of creases exactly when as has odd length -/
theorem creasesOdd_tj (as : List ℕ) : creasesOdd (tj as) = oddLen as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [tj, oddLen, creasesOdd_rep, creasesOdd, ih]

/-- reading (c), the identity: the T/J word with the quotients a_0, ..., a_n is the L/R word with those run-lengths,
followed by the crease when n + 1 is odd
* The crease is what makes the two shifts one letter. -/
theorem quotients_are_runs (as : List ℕ) :
    ev (tj as) = M2.mul (evLR (lr false as)) (cond (oddLen as) J M2.one) := by
  rw [ev_eq_lr, toLR_tj, creasesOdd_tj]

/-- a run of a shifts before w reads T^a times w's matrix -/
theorem ev_rep (a : ℕ) (w : List Letter) : ev (List.replicate a Letter.t ++ w) = M2.mul (M2.pow T a) (ev w) := by
  induction a with
  | zero => simp [M2.pow, M2.one_mul]
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append, ev, ih]
    rw [← M2.mul_assoc, T_pow, T_pow]
    congr 1
    ext <;> simp [M2.mul, T]

/-- the word of quotients of section P is the word of letters of section M: Q a_0 ⋯ Q a_n = T^a_0 J ⋯ T^a_n J -/
theorem word_tj (as : List ℕ) : word (as.map (fun a : ℕ => (a : ℤ))) = ev (tj as) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, word, tj, ev_rep, ev, ih]
    rw [← M2.mul_assoc, quotient_word]

/-- reading (a): no word of the two shifts sends the given to zero; zero needs the crease -/
theorem zero_needs_crease (w : List Side) : (M2.act (evLR w) inf).1 ≠ 0 := by
  have hd := evLR_det w
  obtain ⟨_, hb, hc, _⟩ := evLR_nn w
  rw [act_inf]
  intro ha
  have ha' : (evLR w).a = 0 := ha
  unfold M2.det at hd
  rw [ha'] at hd
  nlinarith [mul_nonneg hb hc]

/-- for positive p and q with p + q at most n, some L/R word's first column is proportional to (p, q) -/
theorem reach_aux (n : ℕ) : ∀ p q : ℤ, 0 < p → 0 < q → p + q ≤ n →
    ∃ w : List Side, (evLR w).a * q = (evLR w).c * p := by
  induction n with
  | zero =>
    intro p q hp hq hs
    exact absurd hs (by omega)
  | succ n ih =>
    intro p q hp hq hs
    rcases lt_trichotomy p q with hlt | heq | hgt
    · obtain ⟨w, hw⟩ := ih p (q - p) hp (by omega) (by omega)
      refine ⟨Side.l :: w, ?_⟩
      rw [evLR_l]
      show (evLR w).a * q = ((evLR w).a + (evLR w).c) * p
      linear_combination hw
    · subst heq
      exact ⟨[Side.l], by simp [evLR, L, M2.mul, M2.one]⟩
    · obtain ⟨w, hw⟩ := ih (p - q) q (by omega) hq (by omega)
      refine ⟨Side.r :: w, ?_⟩
      rw [evLR_r]
      show ((evLR w).a + (evLR w).c) * q = (evLR w).c * p
      linear_combination hw

/-- reading (b), in Stern-Brocot's alphabet, where L = J T J (`L_is_JTJ`) is a letter of its own: the two shifts reach
every positive rational from the given
* Every such word holds an L, since R fixes the given: in Axiom Ś's letters it carries the crease twice, and there the
  crease-free words T^n leave 1/0 where it is (`inf_fixed_Tpow`).
* The word's first column (a, c) is p/q as a point: a q = c p. -/
theorem reach (p q : ℤ) (hp : 0 < p) (hq : 0 < q) : ∃ w : List Side, (evLR w).a * q = (evLR w).c * p :=
  reach_aux (p + q).toNat p q hp hq (Int.self_le_toNat _)

/-! ## O. The finite orders, complete: orders 1, 2, 3, 4 and 6, and no other -/

/-!
* A unimodular word with a power equal to the identity has order 1, 2, 3, 4 or 6, and no other.
* The cases: the powers of a determinant-1 matrix by the Chebyshev recursion; trace at most -3, by the negative; trace
  2 and -2, I and -I only; a crease word of nonzero trace, its square hyperbolic. -/

namespace M2

/-- the negative of a matrix -/
def negate (x : M2) : M2 := ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- negating both factors leaves the product unchanged -/
theorem negs_mul (x y : M2) : mul (negate x) (negate y) = mul x y := by
  simp only [mul, negate, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- negating twice is the identity -/
theorem negate_negate (x : M2) : negate (negate x) = x := by
  ext <;> simp [negate]

/-- negation keeps the determinant -/
theorem det_negs (x : M2) : (negate x).det = x.det := by
  simp only [det, negate]; ring

/-- and negates the trace -/
theorem tr_negs (x : M2) : (negate x).tr = -x.tr := by
  simp only [tr, negate]; ring

/-- x^2 = x x -/
theorem pow_two_eq (x : M2) : pow x 2 = mul x x := by
  show mul (mul one x) x = mul x x
  rw [M2.one_mul]

/-- even powers forget the sign: (-x)^(2m) = x^(2m) -/
theorem pow_negs_even (x : M2) (m : ℕ) : pow (negate x) (2 * m) = pow x (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, M2.pow_add, M2.pow_add, ih, pow_two_eq, pow_two_eq, negs_mul]

/-- the power of a square is the double power -/
theorem pow_square (x : M2) (m : ℕ) : pow (mul x x) m = pow x (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show mul (pow (mul x x) m) (mul x x) = pow x (2 * (m + 1))
    rw [ih, Nat.mul_succ, M2.pow_add, pow_two_eq]

/-- the Chebyshev numbers of the trace: p_0 = 0, p_1 = 1, p_(n+2) = t p_(n+1) - p_n -/
def cheb (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * cheb t (n + 1) - cheb t n

/-- cheb t satisfies Chebyshev's recurrence U(n + 2) = t U(n + 1) - U(n) -/
theorem cheb_succ_succ (t : ℤ) (n : ℕ) : cheb t (n + 1 + 1) = t * cheb t (n + 1) - cheb t n := rfl

/-- the powers of a determinant-1 matrix: M^(n+1) = p_(n+1) M - p_n I, Cayley-Hamilton iterated -/
theorem pow_cheb (x : M2) (h1 : x.det = 1) (n : ℕ) :
    pow x (n + 1) = ⟨cheb x.tr (n + 1) * x.a - cheb x.tr n, cheb x.tr (n + 1) * x.b,
                     cheb x.tr (n + 1) * x.c, cheb x.tr (n + 1) * x.d - cheb x.tr n⟩ := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [det] at h1
  simp only [tr]
  induction n with
  | zero => simp [pow, mul, one, cheb]
  | succ n ih =>
    rw [pow, ih, cheb_succ_succ]
    simp only [mul, M2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-(cheb (a + d) (n + 1))) * h1
    · ring
    · ring
    · linear_combination (-(cheb (a + d) (n + 1))) * h1

/-- for t at least 3, cheb t is nonnegative and strictly increasing -/
theorem cheb_pos (t : ℤ) (ht : 3 ≤ t) (n : ℕ) : 0 ≤ cheb t n ∧ cheb t n < cheb t (n + 1) := by
  induction n with
  | zero => simp [cheb]
  | succ n ih =>
    rw [cheb_succ_succ]
    constructor
    · linarith [ih.1, ih.2]
    · nlinarith [ih.1, ih.2, mul_le_mul_of_nonneg_right ht (by linarith [ih.1, ih.2] : (0 : ℤ) ≤ cheb t (n + 1))]

/-- at trace 2 the Chebyshev numbers are the naturals: p_n = n -/
theorem cheb_two_aux (n : ℕ) : cheb 2 n = (n : ℤ) ∧ cheb 2 (n + 1) = (n : ℤ) + 1 := by
  induction n with
  | zero => exact ⟨by simp [cheb], by simp [cheb]⟩
  | succ n ih =>
    exact ⟨by rw [ih.2, Nat.cast_succ], by rw [cheb_succ_succ, ih.2, ih.1, Nat.cast_succ]; ring⟩

/-- trace at least 3, determinant 1: no power is the identity (every integer matrix) -/
theorem hyperbolic_no_clock (x : M2) (h1 : x.det = 1) (ht : 3 ≤ x.tr) (n : ℕ) : pow x (n + 1) ≠ one := by
  intro h
  rw [pow_cheb x h1 n] at h
  obtain ⟨a, b, c, d⟩ := x
  simp only [det, tr] at h1 ht h
  simp only [one, M2.mk.injEq] at h
  obtain ⟨_, hb, hc, _⟩ := h
  have hp := cheb_pos (a + d) ht n
  have hp1 : 0 < cheb (a + d) (n + 1) := by linarith [hp.1, hp.2]
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · linarith
    · exact h
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · linarith
    · exact h
  subst hb0 hc0
  have had : a * d = 1 := by linarith
  by_cases ha : a ≤ 0 <;> by_cases hd : d ≤ 0
  · linarith
  · push Not at hd
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -a) (by linarith : (0 : ℤ) ≤ d)]
  · push Not at ha
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a) (by linarith : (0 : ℤ) ≤ -d)]
  · push Not at ha hd
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1)]

/-- trace 2, determinant 1: only the identity has a power equal to the identity -/
theorem parabolic_pos (x : M2) (h1 : x.det = 1) (ht : x.tr = 2) (n : ℕ) (h : pow x (n + 1) = one) : x = one := by
  rw [pow_cheb x h1 n] at h
  obtain ⟨a, b, c, d⟩ := x
  simp only [det, tr] at h1 ht h
  simp only [one, M2.mk.injEq] at h
  rw [ht, (cheb_two_aux (n + 1)).1, (cheb_two_aux n).1] at h
  obtain ⟨ha, hb, hc, hd⟩ := h
  push_cast at ha hb hc hd
  have hn : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · linarith
    · exact h
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · linarith
    · exact h
  have ha1 : a = 1 := by
    have e : ((n : ℤ) + 1) * (a - 1) = 0 := by linarith
    rcases mul_eq_zero.mp e with h | h
    · linarith
    · linarith
  have hd1 : d = 1 := by
    have e : ((n : ℤ) + 1) * (d - 1) = 0 := by linarith
    rcases mul_eq_zero.mp e with h | h
    · linarith
    · linarith
  ext <;> simp [one, ha1, hb0, hc0, hd1]

/-- trace -2, determinant 1: only -I has a power equal to the identity -/
theorem parabolic_neg (x : M2) (h1 : x.det = 1) (ht : x.tr = -2) (n : ℕ) (h : pow x (n + 1) = one) :
    x = negate one := by
  have h2 : pow (negate x) (2 * n + 1 + 1) = one := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_negs_even, two_mul, M2.pow_add, h, M2.one_mul]
  have hx : negate x = one :=
    parabolic_pos (negate x) (by rw [det_negs, h1]) (by rw [tr_negs, ht]; norm_num) (2 * n + 1) h2
  have h3 := congrArg negate hx
  rwa [negate_negate] at h3

/-- trace at most -3, determinant 1: no power is the identity, by the negative -/
theorem hyperbolic_neg (x : M2) (h1 : x.det = 1) (ht : x.tr ≤ -3) (n : ℕ) : pow x (n + 1) ≠ one := by
  intro h
  have h2 : pow (negate x) (2 * n + 1 + 1) = one := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_negs_even, two_mul, M2.pow_add, h, M2.one_mul]
  exact hyperbolic_no_clock (negate x) (by rw [det_negs, h1]) (by rw [tr_negs]; linarith) (2 * n + 1) h2

/-- a crease word of nonzero trace: its square has determinant 1 and trace at least 3, so no power is the identity -/
theorem crease_no_clock (x : M2) (h1 : x.det = -1) (ht : x.tr ≠ 0) (n : ℕ) : pow x (n + 1) ≠ one := by
  intro h
  have hsq : pow (mul x x) (n + 1) = one := by
    rw [pow_square, two_mul, M2.pow_add, h, M2.one_mul]
  have hd : (mul x x).det = 1 := by rw [M2.det_mul, h1]; norm_num
  have h3 : 1 ≤ x.tr * x.tr := by
    rcases lt_or_gt_of_ne ht with hlt | hgt <;> nlinarith
  have htr : 3 ≤ (mul x x).tr := by
    rw [M2.tr_sq, h1]
    nlinarith [h3]
  exact hyperbolic_no_clock (mul x x) hd htr n hsq

end M2

/-- the crystallographic restriction, complete: a unimodular word with some power equal to the identity has its first,
second, third, fourth or sixth power equal to the identity, so the finite orders are 1, 2, 3, 4, 6 and no other -/
theorem crystallographic (x : M2) (hu : Uni x) (n : ℕ) (h : M2.pow x (n + 1) = M2.one) :
    M2.pow x 1 = M2.one ∨ M2.pow x 2 = M2.one ∨ M2.pow x 3 = M2.one ∨ M2.pow x 4 = M2.one ∨ M2.pow x 6 = M2.one := by
  rcases hu with h1 | h1
  · have hcases : x.tr ≤ -3 ∨ x.tr = -2 ∨ x.tr = -1 ∨ x.tr = 0 ∨ x.tr = 1 ∨ x.tr = 2 ∨ 3 ≤ x.tr := by omega
    rcases hcases with ht | ht | ht | ht | ht | ht | ht
    · exact absurd h (M2.hyperbolic_neg x h1 ht n)
    · right; left
      rw [M2.parabolic_neg x h1 ht n h]
      decide
    · right; right; left
      exact trace_neg1_order3 x h1 ht
    · right; right; right; left
      exact trace0_order4 x h1 ht
    · right; right; right; right
      exact trace1_order6 x h1 ht
    · left
      rw [M2.parabolic_pos x h1 ht n h]
      decide
    · exact absurd h (M2.hyperbolic_no_clock x h1 ht n)
  · by_cases ht : x.tr = 0
    · right; left
      rw [M2.pow_two_eq]
      exact reflection_sq x h1 ht
    · exact absurd h (M2.crease_no_clock x h1 ht n)

/-- the orders 3, 4 and 6 need subtraction: a nonnegative unimodular matrix, exactly a word in T and J (`faithful`), with a power
equal to the identity is I or the crease J
* So the words in T and J alone have the orders 1 and 2; 3, 4, 6 need T⁻¹ (`crystallographic`). -/
theorem monoid_orders (x : M2) (hn : Nn x) (hu : Uni x) (n : ℕ) (h : M2.pow x (n + 1) = M2.one) : x = M2.one ∨ x = J := by
  obtain ⟨ha, hb, hc, hd⟩ := hn
  rcases hu with h1 | h1
  · left
    have h1' : x.a * x.d - x.b * x.c = 1 := h1
    have hbc : 0 ≤ x.b * x.c := mul_nonneg hb hc
    have ha1 : 1 ≤ x.a := by
      rcases (show x.a = 0 ∨ 1 ≤ x.a by omega) with h0 | h0
      · rw [h0] at h1'
        nlinarith
      · exact h0
    have hd1 : 1 ≤ x.d := by
      rcases (show x.d = 0 ∨ 1 ≤ x.d by omega) with h0 | h0
      · rw [h0] at h1'
        nlinarith
      · exact h0
    have ht : 2 ≤ x.tr := by
      show 2 ≤ x.a + x.d
      omega
    rcases (show x.tr = 2 ∨ 3 ≤ x.tr by omega) with ht2 | ht3
    · exact M2.parabolic_pos x h1 ht2 n h
    · exact absurd h (M2.hyperbolic_no_clock x h1 ht3 n)
  · right
    by_cases ht : x.tr = 0
    · have hs : x.a + x.d = 0 := ht
      have ha0 : x.a = 0 := by omega
      have hd0 : x.d = 0 := by omega
      have h1' : x.a * x.d - x.b * x.c = -1 := h1
      rw [ha0, hd0] at h1'
      have hbc : x.b * x.c = 1 := by linarith
      have hb1 : x.b = 1 := Int.eq_one_of_mul_eq_one_right hb hbc
      have hc1 : x.c = 1 := Int.eq_one_of_mul_eq_one_left hc hbc
      ext <;> simp [J, ha0, hd0, hb1, hc1]
    · exact absurd h (M2.crease_no_clock x h1 ht n)

/-! ## U. The unimodular group: GL_2(Z) from T, T^-1 and J, and SL_2(Z) from S and T -/

/-!
* Every integer matrix of determinant 1 or -1 is a word in T, T^-1 and J, by Euclid on the first column.
* Every matrix of determinant 1 is a word in S, T and T^-1: the modular group generated by S and T, a theorem of the
  words.
* Euclid's canonical word: below. Every relation among the words, a consequence of three: section Y. -/

/-- the group's three letters: the shift, its inverse, the crease -/
inductive Gen
  | t
  | u
  | j
  deriving DecidableEq, Repr

/-- the matrix of a word of the group, the first letter outermost -/
def evG : List Gen → M2
  | [] => M2.one
  | Gen.t :: w => M2.mul T (evG w)
  | Gen.u :: w => M2.mul Tinv (evG w)
  | Gen.j :: w => M2.mul J (evG w)

/-- the matrix of a concatenation of generator words is the product of their matrices -/
theorem evG_append (v w : List Gen) : evG (v ++ w) = M2.mul (evG v) (evG w) := by
  induction v with
  | nil => simp [evG, M2.one_mul]
  | cons a v ih => cases a <;> simp [evG, ih, M2.mul_assoc]

/-- T^-1's n-th power is [[1, -n], [0, 1]] -/
theorem Tinv_pow (n : ℕ) : M2.pow Tinv n = ⟨1, -(n : ℤ), 0, 1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show M2.mul (M2.pow Tinv n) Tinv = _
    rw [ih]
    ext <;> simp [M2.mul, Tinv]

/-- a run of n letters t before w reads T^n times w's matrix -/
theorem evG_rep_t (n : ℕ) (w : List Gen) : evG (List.replicate n Gen.t ++ w) = M2.mul (M2.pow T n) (evG w) := by
  induction n with
  | zero => simp [M2.pow, M2.one_mul]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evG, ih]
    rw [← M2.mul_assoc, T_pow, T_pow]
    congr 1
    ext <;> simp [M2.mul, T]

/-- a run of n letters u before w reads (T^-1)^n times w's matrix -/
theorem evG_rep_u (n : ℕ) (w : List Gen) : evG (List.replicate n Gen.u ++ w) = M2.mul (M2.pow Tinv n) (evG w) := by
  induction n with
  | zero => simp [M2.pow, M2.one_mul]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, evG, ih]
    rw [← M2.mul_assoc, Tinv_pow, Tinv_pow]
    congr 1
    ext <;> simp [M2.mul, Tinv]
    ring

/-- the shift to an integer power, as a word: k shifts, or -k inverse shifts -/
def tpow (k : ℤ) : List Gen := if 0 ≤ k then List.replicate k.toNat Gen.t else List.replicate (-k).toNat Gen.u

/-- the word tpow k reads [[1, k], [0, 1]], for every integer k -/
theorem evG_tpow (k : ℤ) : evG (tpow k) = ⟨1, k, 0, 1⟩ := by
  unfold tpow
  split_ifs with hk
  · have h := evG_rep_t k.toNat []
    rw [List.append_nil] at h
    rw [h, T_pow, Int.toNat_of_nonneg hk]
    ext <;> simp [M2.mul, evG, M2.one]
  · have h := evG_rep_u (-k).toNat []
    rw [List.append_nil] at h
    rw [h, Tinv_pow, Int.toNat_of_nonneg (by omega)]
    ext <;> simp [M2.mul, evG, M2.one]

/-- the word of S: T^-1 J T J T^-1 (the theorem `S_word`) -/
def sword : List Gen := [Gen.u, Gen.j, Gen.t, Gen.j, Gen.u]

/-- the word sword reads S -/
theorem evG_sword : evG sword = S := by decide

/-- S S = -I as a word -/
theorem evG_negone : evG (sword ++ sword) = M2.negate M2.one := by decide

/-- a unimodular matrix with 0 below the diagonal is a word: a shift, or -I, or J S = diag(1, -1), times shifts -/
theorem word_c_zero (x : M2) (hu : Uni x) (hc : x.c = 0) : ∃ w : List Gen, evG w = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only at hc
  subst hc
  unfold Uni M2.det at hu
  simp only [mul_zero, sub_zero] at hu
  rcases hu with h | h
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one h with ha | ha
    · subst ha
      have hd : d = 1 := by linarith
      refine ⟨tpow b, ?_⟩
      rw [evG_tpow]
      ext <;> simp [hd]
    · subst ha
      have hd : d = -1 := by linarith
      refine ⟨sword ++ sword ++ tpow (-b), ?_⟩
      rw [evG_append, evG_negone, evG_tpow]
      ext <;> simp [M2.mul, M2.negate, M2.one, hd]
  · rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h with ha | ha
    · subst ha
      have hd : d = -1 := by linarith
      refine ⟨tpow (-b) ++ Gen.j :: sword, ?_⟩
      rw [evG_append, evG_tpow]
      simp only [evG, evG_sword]
      ext <;> simp [M2.mul, S, J, hd]
    · subst ha
      have hd : d = 1 := by linarith
      refine ⟨sword ++ sword ++ tpow b ++ Gen.j :: sword, ?_⟩
      rw [evG_append, evG_append, evG_negone, evG_tpow]
      simp only [evG, evG_sword]
      ext <;> simp [M2.mul, M2.negate, M2.one, S, J, hd]

/-- Euclid on the first column: a shift takes a below (c), then the crease swaps the rows, and |c| falls -/
theorem gl2_aux (n : ℕ) : ∀ x : M2, Uni x → x.c.natAbs ≤ n → ∃ w : List Gen, evG w = x := by
  induction n with
  | zero =>
    intro x hu hn
    exact word_c_zero x hu (by omega)
  | succ n ih =>
    intro x hu hn
    by_cases hc : x.c = 0
    · exact word_c_zero x hu hc
    · obtain ⟨q, r, hdiv, hr0, hrc⟩ : ∃ q r : ℤ, x.c * q + r = x.a ∧ 0 ≤ r ∧ r < (x.c.natAbs : ℤ) :=
        ⟨x.a / x.c, x.a % x.c, Int.mul_ediv_add_emod _ _, Int.emod_nonneg _ hc, Int.emod_lt _ hc⟩
      have hy : Uni (⟨x.c, x.d, r, x.b - q * x.d⟩ : M2) := by
        unfold Uni M2.det at hu
        unfold Uni M2.det
        rcases hu with h | h
        · right
          linear_combination (-1 : ℤ) * h - x.d * hdiv
        · left
          linear_combination (-1 : ℤ) * h - x.d * hdiv
      have hsz : (⟨x.c, x.d, r, x.b - q * x.d⟩ : M2).c.natAbs ≤ n := by
        show r.natAbs ≤ n
        have hn' : (x.c.natAbs : ℤ) ≤ n + 1 := by exact_mod_cast hn
        omega
      obtain ⟨w, hw⟩ := ih _ hy hsz
      refine ⟨tpow q ++ Gen.j :: w, ?_⟩
      rw [evG_append, evG_tpow]
      simp only [evG, hw]
      ext <;> simp [M2.mul, J]
      linarith [hdiv]

/-- every integer matrix of determinant 1 or -1 is a word in the shift, its inverse and the crease -/
theorem gl2_word (x : M2) (hu : Uni x) : ∃ w : List Gen, evG w = x :=
  gl2_aux x.c.natAbs x hu le_rfl

/-- the modular group's letters: S, the shift and its inverse -/
inductive SGen
  | s
  | t
  | u
  deriving DecidableEq, Repr

def evS : List SGen → M2
  | [] => M2.one
  | SGen.s :: w => M2.mul S (evS w)
  | SGen.t :: w => M2.mul T (evS w)
  | SGen.u :: w => M2.mul Tinv (evS w)

/-- every word in S, T and T^-1 has determinant 1 -/
theorem evS_det (w : List SGen) : (evS w).det = 1 := by
  induction w with
  | nil => decide
  | cons a w ih => cases a <;> simp only [evS, M2.det_mul, ih] <;> decide

/-- the crease pushed past a shift: J T = (T S T) J (past T^-1 it is `JTinv_word`) -/
theorem JT_TST : M2.mul J T = M2.mul (M2.mul T (M2.mul S T)) J := by decide

/-- J T^-1 = T^-1 S S S T^-1 J -/
theorem JTinv_word : M2.mul J Tinv = M2.mul (M2.mul Tinv (M2.mul S (M2.mul S (M2.mul S Tinv)))) J := by decide

/-- a word of the group read in S and the shifts: past an odd number of creases a shift becomes T S T -/
def toS : Bool → List Gen → List SGen
  | _, [] => []
  | false, Gen.t :: w => SGen.t :: toS false w
  | true, Gen.t :: w => SGen.t :: SGen.s :: SGen.t :: toS true w
  | false, Gen.u :: w => SGen.u :: toS false w
  | true, Gen.u :: w => SGen.u :: SGen.s :: SGen.s :: SGen.s :: SGen.u :: toS true w
  | b, Gen.j :: w => toS (!b) w

/-- whether a word of the group has an odd number of creases -/
def oddJ : List Gen → Bool
  | [] => false
  | Gen.t :: w => oddJ w
  | Gen.u :: w => oddJ w
  | Gen.j :: w => !oddJ w

/-- a word in t, u and j reads as its S/T word followed by J when its j's are odd and by nothing otherwise; J times it reads the other way -/
theorem evG_evS (w : List Gen) :
    evG w = M2.mul (evS (toS false w)) (cond (oddJ w) J M2.one) ∧
    M2.mul J (evG w) = M2.mul (evS (toS true w)) (cond (oddJ w) M2.one J) := by
  induction w with
  | nil => exact ⟨by simp [evG, evS, toS, oddJ, M2.mul_one], by simp [evG, evS, toS, oddJ, M2.mul_one, M2.one_mul]⟩
  | cons a w ih =>
    obtain ⟨h0, h1⟩ := ih
    cases a with
    | t =>
      constructor
      · show M2.mul T (evG w) = M2.mul (M2.mul T (evS (toS false w))) (cond (oddJ w) J M2.one)
        rw [M2.mul_assoc, ← h0]
      · show M2.mul J (M2.mul T (evG w)) =
            M2.mul (M2.mul T (M2.mul S (M2.mul T (evS (toS true w))))) (cond (oddJ w) M2.one J)
        rw [← M2.mul_assoc, JT_TST]
        simp only [M2.mul_assoc]
        rw [h1]
    | u =>
      constructor
      · show M2.mul Tinv (evG w) = M2.mul (M2.mul Tinv (evS (toS false w))) (cond (oddJ w) J M2.one)
        rw [M2.mul_assoc, ← h0]
      · show M2.mul J (M2.mul Tinv (evG w)) =
            M2.mul (M2.mul Tinv (M2.mul S (M2.mul S (M2.mul S (M2.mul Tinv (evS (toS true w))))))) (cond (oddJ w) M2.one J)
        rw [← M2.mul_assoc, JTinv_word]
        simp only [M2.mul_assoc]
        rw [h1]
    | j =>
      constructor
      · show M2.mul J (evG w) = M2.mul (evS (toS true w)) (cond (!oddJ w) J M2.one)
        rw [h1]
        cases oddJ w <;> rfl
      · show M2.mul J (M2.mul J (evG w)) = M2.mul (evS (toS false w)) (cond (!oddJ w) M2.one J)
        rw [← M2.mul_assoc, point3_JJ, M2.one_mul, h0]
        cases oddJ w <;> rfl

/-- SL(2, Z) = <S, T>: every integer matrix of determinant 1 is a word in S, T and T^-1 -/
theorem sl2_generated (x : M2) (hd : x.det = 1) : ∃ w : List SGen, evS w = x := by
  obtain ⟨w, hw⟩ := gl2_word x (Or.inl hd)
  have h := (evG_evS w).1
  rw [hw] at h
  cases hodd : oddJ w
  · rw [hodd] at h
    exact ⟨toS false w, by rw [h]; exact (M2.mul_one _).symm⟩
  · exfalso
    rw [hodd] at h
    have hdet := congrArg M2.det h
    rw [M2.det_mul, evS_det, hd] at hdet
    exact absurd hdet (by decide)

/-! ### Euclid's canonical word in the group
* The word `gl2_aux` builds, as a function `nf` of the matrix; `nf_eval` proves `evG (nf x) = x`.
* A canonical section, one word per unimodular matrix; the group's reduced form and its uniqueness: section Y's
  `gl2_normal_form`. -/

/-- the word of a unimodular matrix with 0 below the diagonal: a shift; or J S = diag(1, -1) and a shift; or -I and a
shift; or -I, a shift and J S -/
def nf0 (x : M2) : List Gen :=
  if x.a = 1 then (if x.d = 1 then tpow x.b else tpow (-x.b) ++ Gen.j :: sword)
  else (if x.d = -1 then sword ++ sword ++ tpow (-x.b) else sword ++ sword ++ tpow x.b ++ Gen.j :: sword)

/-- a matrix of determinant 1 or -1 with c = 0 is read by its normal form nf0 -/
theorem nf0_eval (x : M2) (hu : Uni x) (hc : x.c = 0) : evG (nf0 x) = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only at hc
  subst hc
  unfold Uni M2.det at hu
  simp only [mul_zero, sub_zero] at hu
  rcases hu with h | h
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one h with ha | ha
    · subst ha
      have hd : d = 1 := by linarith
      subst hd
      show evG (tpow b) = _
      rw [evG_tpow]
    · subst ha
      have hd : d = -1 := by linarith
      subst hd
      show evG (sword ++ sword ++ tpow (-b)) = _
      rw [evG_append, evG_negone, evG_tpow]
      ext <;> simp [M2.mul, M2.negate, M2.one]
  · rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h with ha | ha
    · subst ha
      have hd : d = -1 := by linarith
      subst hd
      show evG (tpow (-b) ++ Gen.j :: sword) = _
      rw [evG_append, evG_tpow]
      simp only [evG, evG_sword]
      ext <;> simp [M2.mul, S, J]
    · subst ha
      have hd : d = 1 := by linarith
      subst hd
      show evG (sword ++ sword ++ tpow b ++ Gen.j :: sword) = _
      rw [evG_append, evG_append, evG_negone, evG_tpow]
      simp only [evG, evG_sword]
      ext <;> simp [M2.mul, M2.negate, M2.one, S, J]

/-- Euclid's canonical word: shifts by the quotient of the first column, the crease, and the rest on the smaller column -/
def nf (x : M2) : List Gen :=
  if _hc : x.c = 0 then nf0 x
  else tpow (x.a / x.c) ++ Gen.j :: nf ⟨x.c, x.d, x.a % x.c, x.b - x.a / x.c * x.d⟩
termination_by x.c.natAbs
decreasing_by
  show (x.a % x.c).natAbs < x.c.natAbs
  have h1 := Int.emod_nonneg x.a _hc
  have h2 := Int.emod_lt x.a _hc
  omega

/-- every matrix of determinant 1 or -1 with |c| at most n is read by its normal form nf -/
theorem nf_eval_aux (n : ℕ) : ∀ x : M2, Uni x → x.c.natAbs ≤ n → evG (nf x) = x := by
  induction n with
  | zero =>
    intro x hu hn
    have hc : x.c = 0 := by omega
    unfold nf
    split
    · exact nf0_eval x hu hc
    · rename_i h
      exact absurd hc h
  | succ n ih =>
    intro x hu hn
    by_cases hc : x.c = 0
    · unfold nf
      split
      · exact nf0_eval x hu hc
      · rename_i h
        exact absurd hc h
    · unfold nf
      split
      · rename_i h
        exact absurd h hc
      obtain ⟨q, r, hq, hr, hdiv, hr0, hrc⟩ :
          ∃ q r : ℤ, q = x.a / x.c ∧ r = x.a % x.c ∧ x.c * q + r = x.a ∧ 0 ≤ r ∧ r < (x.c.natAbs : ℤ) :=
        ⟨_, _, rfl, rfl, Int.mul_ediv_add_emod _ _, Int.emod_nonneg _ hc, Int.emod_lt _ hc⟩
      rw [← hq, ← hr]
      have hy : Uni (⟨x.c, x.d, r, x.b - q * x.d⟩ : M2) := by
        unfold Uni M2.det at hu
        unfold Uni M2.det
        rcases hu with h | h
        · right
          linear_combination (-1 : ℤ) * h - x.d * hdiv
        · left
          linear_combination (-1 : ℤ) * h - x.d * hdiv
      have hsz : (⟨x.c, x.d, r, x.b - q * x.d⟩ : M2).c.natAbs ≤ n := by
        show r.natAbs ≤ n
        have hn' : (x.c.natAbs : ℤ) ≤ n + 1 := by exact_mod_cast hn
        omega
      have hev := ih _ hy hsz
      rw [evG_append, evG_tpow]
      simp only [evG, hev]
      ext <;> simp [M2.mul, J]
      linarith [hdiv]

/-- every unimodular matrix evaluates its own canonical word in T, T^-1, J (a right inverse to evG on GL_2(Z)) -/
theorem nf_eval (x : M2) (hu : Uni x) : evG (nf x) = x :=
  nf_eval_aux x.c.natAbs x hu le_rfl

/-! ## W. The numerals on the letters alone: Peano with no integer, the exact fixed points, each nonnegative rational once -/

/-- a natural, on the letters alone: the crease (zero), or a shift before a natural -/
inductive NatWord : List Letter → Prop
  | zero : NatWord [Letter.j]
  | succ (w : List Letter) : NatWord w → NatWord (Letter.t :: w)

/-- Peano with no integer in the statement: the successor is injective -/
theorem peano_succ_inj (v w : List Letter) (h : Letter.t :: v = Letter.t :: w) : v = w :=
  (List.cons.inj h).2

/-- Peano with no integer in the statement: zero is no successor, their first letters differ -/
theorem peano_succ_ne_zero (w : List Letter) : Letter.t :: w ≠ [Letter.j] := by
  intro h
  cases h

/-- Peano with no integer in the statement: induction on the letters -/
theorem peano_induction (C : List Letter → Prop) (h0 : C [Letter.j])
    (hs : ∀ w, NatWord w → C w → C (Letter.t :: w)) (w : List Letter) (h : NatWord w) : C w := by
  induction h with
  | zero => exact h0
  | succ w hw ih => exact hs w hw ih

/-- the model reads each of the letters' naturals as a natural over 1 (T^n J reads n, `nat_from_inf`) -/
theorem natWord_reads (w : List Letter) (h : NatWord w) : ∃ n : ℕ, M2.act (ev w) inf = ((n : ℤ), 1) := by
  induction h with
  | zero => exact ⟨0, by simp [ev, M2.mul, M2.one, J, M2.act, inf]⟩
  | succ w _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    show M2.act (M2.mul T (ev w)) inf = _
    rw [M2.act_mul, hn]
    simp [M2.act, T]

/-- the crease's fixed points on the line, exactly: p/q with p = q or p = -q, that is, for every pair but (0, 0), 1 and -1, and no
other -/
theorem J_fixed_iff (p q : ℤ) : (M2.act J (p, q)).1 * q = (M2.act J (p, q)).2 * p ↔ p = q ∨ p = -q := by
  show (0 * p + 1 * q) * q = (1 * p + 0 * q) * p ↔ _
  constructor
  · intro h
    have h' : (p - q) * (p + q) = 0 := by linear_combination (-1 : ℤ) * h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- the shift's fixed point on the line, exactly: q = 0, that is, for every pair but (0, 0), the given 1/0, and no other -/
theorem T_fixed_iff (p q : ℤ) : (M2.act T (p, q)).1 * q = (M2.act T (p, q)).2 * p ↔ q = 0 := by
  show (1 * p + 1 * q) * q = (0 * p + 1 * q) * p ↔ q = 0
  constructor
  · intro h
    have h' : q * q = 0 := by linear_combination h
    exact mul_self_eq_zero.mp h'
  · rintro rfl
    ring

/-- the pair a word of quotients in ℕ sends 1/0 to -/
def pair : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | a :: r => (a * (pair r).1 + (pair r).2, (pair r).1)

/-- the pair is the model's: the word applied to 1/0 -/
theorem pair_word (w : List ℕ) :
    M2.act (word (w.map fun a : ℕ => (a : ℤ))) inf = (((pair w).1 : ℤ), ((pair w).2 : ℤ)) := by
  induction w with
  | nil => simp [word, M2.act, M2.one, inf, pair]
  | cons a r ih =>
    simp only [List.map_cons, word, M2.act_mul, ih, pair]
    simp [M2.act, Q]

/-- the pair is in lowest terms: Euclid runs back through the word -/
theorem pair_coprime (w : List ℕ) : Nat.Coprime (pair w).1 (pair w).2 := by
  induction w with
  | nil => simp [pair]
  | cons a r ih =>
    show Nat.Coprime (a * (pair r).1 + (pair r).2) (pair r).1
    rw [Nat.coprime_mul_right_add_left]
    exact ih.symm

/-- the tail of a normal form: every quotient at least 1, the last at least 2 -/
inductive TailNF : List ℕ → Prop
  | last (a : ℕ) : 2 ≤ a → TailNF [a]
  | cons (a b : ℕ) (r : List ℕ) : 1 ≤ a → TailNF (b :: r) → TailNF (a :: b :: r)

/-- Euclid's normal form [a_0; a_1, ..., a_n]: one quotient, or a quotient before a tail -/
def IsNF (w : List ℕ) : Prop := (∃ a, w = [a]) ∨ ∃ a r, w = a :: r ∧ TailNF r

/-- a tail reads above 1, with a positive denominator -/
theorem tail_pair (r : List ℕ) (h : TailNF r) : (pair r).2 < (pair r).1 ∧ 1 ≤ (pair r).2 := by
  induction h with
  | last a ha =>
    have e : pair [a] = (a, 1) := by simp [pair]
    rw [e]
    exact ⟨ha, le_rfl⟩
  | cons a b r ha _ ih =>
    obtain ⟨h1, h2⟩ := ih
    show (pair (b :: r)).1 < a * (pair (b :: r)).1 + (pair (b :: r)).2 ∧ 1 ≤ (pair (b :: r)).1
    have hle : (pair (b :: r)).1 ≤ a * (pair (b :: r)).1 := Nat.le_mul_of_pos_left _ ha
    omega

/-- Euclid's step is forced: quotient and remainder below the divisor are unique -/
theorem euclid_unique (a a' d m m' : ℕ) (hm : m < d) (hm' : m' < d) (h : a * d + m = a' * d + m') :
    a = a' ∧ m = m' := by
  have key : a = a' := by
    rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
    · exfalso
      have : (a + 1) * d ≤ a' * d := Nat.mul_le_mul_right d hlt
      nlinarith
    · exact heq
    · exfalso
      have : (a' + 1) * d ≤ a * d := Nat.mul_le_mul_right d hgt
      nlinarith
  subst key
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- a single quotient [a] and a quotient before a tail never share a pair -/
theorem tail_ne_single (a a' : ℕ) (r : List ℕ) (ht : TailNF r) (h : pair [a] = pair (a' :: r)) : False := by
  have h2 := tail_pair _ ht
  have e2 : (pair [a]).2 = (pair (a' :: r)).2 := congrArg Prod.snd h
  have e3 : (pair [a]).2 = 1 := by simp [pair]
  have e4 : (pair (a' :: r)).2 = (pair r).1 := rfl
  omega

/-- two tails with one pair are one tail -/
theorem tail_inj (r : List ℕ) (hr : TailNF r) : ∀ r', TailNF r' → pair r = pair r' → r = r' := by
  induction hr with
  | last a _ =>
    intro r' hr' h
    cases hr' with
    | last a' _ =>
      have h1 : a = a' := by simpa [pair] using h
      rw [h1]
    | cons a' b s _ ht => exact (tail_ne_single a a' _ ht h).elim
  | cons a b r _ ht ih =>
    intro r' hr' h
    cases hr' with
    | last a' _ => exact (tail_ne_single a' a _ ht h.symm).elim
    | cons a' b' s _ ht' =>
      have hd : (pair (b :: r)).1 = (pair (b' :: s)).1 := congrArg Prod.snd h
      have hn : a * (pair (b :: r)).1 + (pair (b :: r)).2 = a' * (pair (b' :: s)).1 + (pair (b' :: s)).2 :=
        congrArg Prod.fst h
      have h1 := tail_pair _ ht
      have h2 := tail_pair _ ht'
      rw [← hd] at hn h2
      obtain ⟨e1, e2⟩ := euclid_unique a a' _ _ _ h1.1 h2.1 hn
      rw [e1, ih _ ht' (Prod.ext hd e2)]

/-- two normal forms with one pair are one word -/
theorem nf_pair_inj (w w' : List ℕ) (h : IsNF w) (h' : IsNF w') (e : pair w = pair w') : w = w' := by
  rcases h with ⟨a, rfl⟩ | ⟨a, r, rfl, ht⟩ <;> rcases h' with ⟨a', rfl⟩ | ⟨a', r', rfl, ht'⟩
  · have h1 : a = a' := by simpa [pair] using e
    rw [h1]
  · exact (tail_ne_single a a' _ ht' e).elim
  · exact (tail_ne_single a' a _ ht e.symm).elim
  · have hd : (pair r).1 = (pair r').1 := congrArg Prod.snd e
    have hn : a * (pair r).1 + (pair r).2 = a' * (pair r').1 + (pair r').2 := congrArg Prod.fst e
    have h1 := tail_pair _ ht
    have h2 := tail_pair _ ht'
    rw [← hd] at hn h2
    obtain ⟨e1, e2⟩ := euclid_unique a a' _ _ _ h1.1 h2.1 hn
    rw [e1, tail_inj r ht r' ht' (Prod.ext hd e2)]

/-- if p and q are coprime, so are q and p mod q -/
theorem coprime_mod (p q : ℕ) (hc : Nat.Coprime p q) : Nat.Coprime q (p % q) := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, ← Nat.gcd_rec]
  exact hc.symm

/-- Euclid builds the tail of a pair above 1 in lowest terms -/
theorem tail_exists (n : ℕ) :
    ∀ p q : ℕ, q ≤ n → 1 ≤ q → q < p → Nat.Coprime p q → ∃ r, TailNF r ∧ pair r = (p, q) := by
  induction n with
  | zero =>
    intro p q h0 h1
    omega
  | succ n ih =>
    intro p q hn h1 hlt hc
    by_cases hz : p % q = 0
    · have hq1 : q = 1 := hc.symm.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hz)
      subst hq1
      exact ⟨[p], TailNF.last p (by omega), by simp [pair]⟩
    · have hm := Nat.mod_lt p h1
      have hm1 : 1 ≤ p % q := Nat.pos_of_ne_zero hz
      have ha : 1 ≤ p / q := Nat.div_pos (le_of_lt hlt) h1
      obtain ⟨r, hr, e⟩ := ih q (p % q) (by omega) hm1 hm (coprime_mod p q hc)
      rcases r with _ | ⟨b, s⟩
      · cases hr
      · refine ⟨p / q :: b :: s, TailNF.cons _ _ _ ha hr, ?_⟩
        show (p / q * (pair (b :: s)).1 + (pair (b :: s)).2, (pair (b :: s)).1) = (p, q)
        rw [e]
        show (p / q * q + p % q, q) = (p, q)
        rw [Nat.div_add_mod']

/-- every nonnegative rational p/q in lowest terms has a word in Euclid's normal form -/
theorem normal_form_exists (p q : ℕ) (hq : 0 < q) (hc : Nat.Coprime p q) : ∃ w, IsNF w ∧ pair w = (p, q) := by
  by_cases hz : p % q = 0
  · have hq1 : q = 1 := hc.symm.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hz)
    subst hq1
    exact ⟨[p], Or.inl ⟨p, rfl⟩, by simp [pair]⟩
  · have hm := Nat.mod_lt p hq
    have hm1 : 1 ≤ p % q := Nat.pos_of_ne_zero hz
    obtain ⟨r, hr, e⟩ := tail_exists q q (p % q) (le_of_lt hm) hm1 hm (coprime_mod p q hc)
    refine ⟨p / q :: r, Or.inr ⟨_, _, rfl, hr⟩, ?_⟩
    show (p / q * (pair r).1 + (pair r).2, (pair r).1) = (p, q)
    rw [e]
    show (p / q * q + p % q, q) = (p, q)
    rw [Nat.div_add_mod']

/-- each nonnegative rational exactly once: p/q in lowest terms is one word in Euclid's normal form -/
theorem rational_once (p q : ℕ) (hq : 0 < q) (hc : Nat.Coprime p q) : ∃! w, IsNF w ∧ pair w = (p, q) := by
  obtain ⟨w, hw, e⟩ := normal_form_exists p q hq hc
  exact ⟨w, ⟨hw, e⟩, fun w' h' => nf_pair_inj w' w h'.1 hw (h'.2.trans e.symm)⟩

end SunyaAxiom

namespace AlphaRoutes

/-! ## E. Euclid's measurement
* Euclid's division (Elements VII.2; Āryabhaṭa's kuṭṭaka) measures one count by another: its quotients are the
  partial quotients, the word; it ends at remainder 0 exactly when the pair is commensurable. -/

/-- Euclid's division read as its quotients, with fuel: the word of a/b -/
def euclidWord : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | f + 1, a, b + 1 => a / (b + 1) :: euclidWord f (b + 1) (a % (b + 1))

end AlphaRoutes

namespace SunyaAxiom

/-! ## Y. The presentation of the unimodular group: the shift, the crease and three relations -/

/-- the value of a word of the group in any group, given a shift and a crease -/
def evGrp {G : Type*} [Group G] (t j : G) : List Gen → G
  | [] => 1
  | Gen.t :: w => t * evGrp t j w
  | Gen.u :: w => t⁻¹ * evGrp t j w
  | Gen.j :: w => j * evGrp t j w

/-- in any group, the word map sends a concatenation to the product -/
theorem evGrp_append {G : Type*} [Group G] (t j : G) (v w : List Gen) :
    evGrp t j (v ++ w) = evGrp t j v * evGrp t j w := by
  induction v with
  | nil => simp [evGrp]
  | cons a v ih => cases a <;> simp [evGrp, ih, mul_assoc]

/-- S in any group, as `S_word` reads it: T⁻¹ J T J T⁻¹ -/
def sG {G : Type*} [Group G] (t j : G) : G := t⁻¹ * (j * t * j) * t⁻¹

/-- the word in the two shifts, in any group: R is t and L is j t j -/
def pvG {G : Type*} [Group G] (t j : G) : List Side → G
  | [] => 1
  | Side.r :: w => t * pvG t j w
  | Side.l :: w => j * t * j * pvG t j w

/-- the three relations: the crease squares to one, the shift t and y = j t⁻¹ j braid, and S^4 = 1 -/
structure Rels {G : Type*} [Group G] (t j : G) : Prop where
  sq : j * j = 1
  braid : t * (j * t⁻¹ * j) * t = j * t⁻¹ * j * t * (j * t⁻¹ * j)
  four : (t⁻¹ * (j * t * j) * t⁻¹) ^ 4 = 1

/-- a state of the reduction: S^k, then a word in the two shifts, then S^i, then the crease e times -/
abbrev St := ℕ × List Side × ℕ × ℕ

/-- the state's value in a group -/
def stG {G : Type*} [Group G] (t j : G) : St → G
  | (k, P, i, e) => sG t j ^ k * (pvG t j P * (sG t j ^ i * j ^ e))

/-- the shift read at an odd power of S -/
def stepT (k i e : ℕ) : List Side → St
  | Side.r :: P => (k - 1, Side.l :: P, i, e)
  | Side.l :: P => (k, P, i, e)
  | [] => (k - 1, [Side.r], i + 1, e)

/-- the inverse shift read at an even power of S -/
def stepU (k e : ℕ) : List Side → ℕ → St
  | Side.r :: P, i => (k, P, i, e)
  | Side.l :: P, i => (k + 1, Side.r :: P, i, e)
  | [], i + 1 => (k + 1, [Side.l], i, e)
  | [], 0 => (k + 1, [Side.l], 3, e)

/-- one letter read into a state -/
def stepG : Gen → St → St
  | Gen.t, (k, P, i, e) => if k % 2 = 0 then (k, Side.r :: P, i, e) else stepT k i e P
  | Gen.u, (k, P, i, e) => if k % 2 = 0 then stepU k e P i else (k, Side.l :: P, i, e)
  | Gen.j, (k, P, i, e) => (3 * k, mirror P, 3 * i, e + 1)

/-- the state a word reaches, the last letter read first -/
def stateOf : List Gen → St
  | [] => (0, [], 0, 0)
  | a :: w => stepG a (stateOf w)

/-- under the three relations, j t j t^-1 (j t j) is the group's S -/
theorem rels_L_S {G : Type*} [Group G] {t j : G} (h : Rels t j) : j * t * j * t⁻¹ * (j * t * j) = sG t j := by
  have hj : j⁻¹ = j := inv_eq_of_mul_eq_one_left h.sq
  have hb := congrArg (·⁻¹) h.braid
  simp only [mul_inv_rev, inv_inv, hj] at hb
  simp only [sG]
  rw [show t⁻¹ * (j * t * j) * t⁻¹ = t⁻¹ * (j * (t * j) * t⁻¹) by group, hb]
  group

/-- S² commutes with the shift -/
theorem rels_central {G : Type*} [Group G] {t j : G} (h : Rels t j) : Commute (sG t j * sG t j) t := by
  have key : t * sG t j * t * sG t j * t = sG t j := by
    calc t * sG t j * t * sG t j * t = j * t * j * t⁻¹ * (j * t * j) := by simp only [sG]; group
      _ = sG t j := rels_L_S h
  show sG t j * sG t j * t = t * (sG t j * sG t j)
  generalize sG t j = s at key
  calc s * s * t = (t * s * t * s * t) * s * t := by rw [key]
    _ = t * s * (t * s * t * s * t) := by group
    _ = t * (s * s) := by rw [key, mul_assoc]

/-- under the relations, every even power of S commutes with t -/
theorem rels_even {G : Type*} [Group G] {t j : G} (h : Rels t j) (q : ℕ) : Commute (sG t j ^ (2 * q)) t := by
  rw [pow_mul, sq]; exact (rels_central h).pow_left q

/-- under the relations, t S j t j X = S X for every X -/
theorem rels_tsl {G : Type*} [Group G] {t j : G} (h : Rels t j) (X : G) :
    t * (sG t j * (j * (t * (j * X)))) = sG t j * X := by
  calc t * (sG t j * (j * (t * (j * X)))) = j * t * j * t⁻¹ * (j * t * j) * X := by simp only [sG]; group
    _ = sG t j * X := by rw [rels_L_S h]

/-- j S = S^3 j -/
theorem rels_j_S {G : Type*} [Group G] {t j : G} (h : Rels t j) : j * sG t j = sG t j ^ 3 * j := by
  have hj : j⁻¹ = j := inv_eq_of_mul_eq_one_left h.sq
  have h4 : sG t j ^ 4 = 1 := h.four
  have h3 : sG t j ^ 3 = (sG t j)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h4)
  have hb : (sG t j)⁻¹ = j * sG t j * j := by
    simp only [sG, mul_inv_rev, inv_inv, hj]
    calc t * (j * (t⁻¹ * j) * t) = t * (j * t⁻¹ * j) * t := by group
      _ = j * t⁻¹ * j * t * (j * t⁻¹ * j) := h.braid
      _ = _ := by group
  rw [h3, hb, mul_assoc, mul_assoc, h.sq, mul_one]

/-- under the relations, j moves past an L/R word as its mirror: j (P X) = (mirror P) (j X) -/
theorem rels_j_pv {G : Type*} [Group G] {t j : G} (h : Rels t j) (P : List Side) (X : G) :
    j * (pvG t j P * X) = pvG t j (mirror P) * (j * X) := by
  have hjj : ∀ Y : G, j * (j * Y) = Y := fun Y => by rw [← mul_assoc, h.sq, one_mul]
  induction P with
  | nil => simp [pvG, mirror]
  | cons a P ih =>
    cases a
    · simp only [pvG, mirror, mul_assoc]
      rw [← ih, hjj]
    · simp only [pvG, mirror, mul_assoc]
      rw [hjj, ih]

/-- under the relations, a step by t multiplies the state's value by t on the left -/
theorem stG_t {G : Type*} [Group G] {t j : G} (h : Rels t j) (s : St) : stG t j (stepG Gen.t s) = t * stG t j s := by
  obtain ⟨k, P, i, e⟩ := s
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hk : 2 * q % 2 = 0 := by omega
    simp only [stepG, hk, ↓reduceIte, stG, pvG, mul_assoc]
    exact (rels_even h q).left_comm _
  · have hk : (2 * q + 1) % 2 ≠ 0 := by omega
    have hc := (rels_even h q).left_comm
    have hp : sG t j ^ (2 * q + 1) = sG t j ^ (2 * q) * sG t j := pow_succ _ _
    simp only [stepG, hk, ↓reduceIte]
    cases P with
    | nil =>
      simp only [stepT, stG, pvG, Nat.add_sub_cancel, mul_one, one_mul, hp, pow_succ' (sG t j) i, mul_assoc]
      rw [← hc]
    | cons a P =>
      cases a
      · simp only [stepT, stG, pvG, Nat.add_sub_cancel, hp, mul_assoc]
        rw [← hc]
        congr 1
        generalize pvG t j P * (sG t j ^ i * j ^ e) = X
        simp only [sG]; group
      · simp only [stepT, stG, pvG, hp, mul_assoc]
        rw [← hc, rels_tsl h]

/-- a step by u multiplies it by t^-1 -/
theorem stG_u {G : Type*} [Group G] {t j : G} (h : Rels t j) (s : St) : stG t j (stepG Gen.u s) = t⁻¹ * stG t j s := by
  obtain ⟨k, P, i, e⟩ := s
  have hus : ∀ X : G, t⁻¹ * (sG t j * X) = sG t j * (j * (t * (j * X))) := fun X => by
    rw [← rels_tsl h X, inv_mul_cancel_left]
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hk : 2 * q % 2 = 0 := by omega
    have hc := (rels_even h q).inv_right.left_comm
    have hp : sG t j ^ (2 * q + 1) = sG t j ^ (2 * q) * sG t j := pow_succ _ _
    simp only [stepG, hk, ↓reduceIte]
    cases P with
    | nil =>
      cases i with
      | zero =>
        have h4 : ∀ Y : G, sG t j * (sG t j ^ 3 * Y) = Y := fun Y => by
          rw [← mul_assoc, ← pow_succ', show sG t j ^ (3 + 1) = 1 from h.four, one_mul]
        simp only [stepU, stG, pvG, pow_zero, mul_one, one_mul, hp, mul_assoc]
        rw [← hc, ← hus, h4]
      | succ i =>
        simp only [stepU, stG, pvG, one_mul, mul_one, hp, pow_succ' (sG t j) i, mul_assoc]
        rw [← hc, hus]
    | cons a P =>
      cases a
      · simp only [stepU, stG, pvG, mul_assoc]
        rw [← hc, inv_mul_cancel_left]
      · simp only [stepU, stG, pvG, hp, mul_assoc]
        rw [← hc]
        congr 1
        generalize pvG t j P * (sG t j ^ i * j ^ e) = X
        simp only [sG]; group
  · have hk : (2 * q + 1) % 2 ≠ 0 := by omega
    have hc := (rels_even h q).inv_right.left_comm
    have hp : sG t j ^ (2 * q + 1) = sG t j ^ (2 * q) * sG t j := pow_succ _ _
    simp only [stepG, hk, ↓reduceIte, stG, pvG, hp, mul_assoc]
    rw [← hc, hus]

/-- a step by j multiplies it by j -/
theorem stG_j {G : Type*} [Group G] {t j : G} (h : Rels t j) (s : St) : stG t j (stepG Gen.j s) = j * stG t j s := by
  obtain ⟨k, P, i, e⟩ := s
  have hS : ∀ (n : ℕ) (X : G), j * (sG t j ^ n * X) = sG t j ^ (3 * n) * (j * X) := fun n X => by
    have hs : SemiconjBy j (sG t j) (sG t j ^ 3) := rels_j_S h
    rw [pow_mul, ← mul_assoc, (hs.pow_right n).eq, mul_assoc]
  simp only [stepG, stG]
  rw [hS, rels_j_pv h, hS, pow_succ']

/-- a word's value is the value of the state it reaches -/
theorem evGrp_state {G : Type*} [Group G] {t j : G} (h : Rels t j) (w : List Gen) : evGrp t j w = stG t j (stateOf w) := by
  induction w with
  | nil => simp [evGrp, stateOf, stG, pvG]
  | cons a w ih =>
    cases a
    · simp only [evGrp, stateOf, stG_t h, ih]
    · simp only [evGrp, stateOf, stG_u h, ih]
    · simp only [evGrp, stateOf, stG_j h, ih]

/-- the unimodular group on the sheet: the integer matrices of determinant 1 or -1 -/
def GL2Z : Type := {x : M2 // Uni x}

instance : Mul GL2Z :=
  ⟨fun x y => ⟨M2.mul x.1 y.1, by
    rcases x.2 with h | h <;> rcases y.2 with h' | h' <;> simp [Uni, M2.det_mul, h, h']⟩⟩

instance : One GL2Z := ⟨⟨M2.one, Or.inl (by decide)⟩⟩

instance : Inv GL2Z :=
  ⟨fun x => ⟨⟨x.1.det * x.1.d, -x.1.det * x.1.b, -x.1.det * x.1.c, x.1.det * x.1.a⟩, by
    rcases x with ⟨⟨a, b, c, d⟩, hu⟩
    simp only [Uni, M2.det] at hu ⊢
    rcases hu with h | h
    · left; rw [h]; linear_combination h
    · right; rw [h]; linear_combination h⟩⟩

instance : Group GL2Z := Group.ofLeftAxioms
  (fun x y z => Subtype.ext (M2.mul_assoc x.1 y.1 z.1))
  (fun x => Subtype.ext (M2.one_mul x.1))
  (fun x => Subtype.ext (by
    have hd : x.1.det * (x.1.a * x.1.d - x.1.b * x.1.c) = 1 := by
      show x.1.det * x.1.det = 1
      rcases x.2 with h | h <;> rw [h] <;> norm_num
    show M2.mul ⟨x.1.det * x.1.d, -x.1.det * x.1.b, -x.1.det * x.1.c, x.1.det * x.1.a⟩ x.1 = M2.one
    simp only [M2.mul, M2.one, M2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination hd
    · ring
    · ring
    · linear_combination hd))

/-- the shift and the crease in the group on the sheet -/
def Tg : GL2Z := ⟨T, Or.inl (by decide)⟩
def Jg : GL2Z := ⟨J, Or.inr (by decide)⟩

/-- the three relations hold on the sheet -/
theorem rels_model : Rels Tg Jg := ⟨Subtype.ext (by decide), Subtype.ext (by decide), Subtype.ext (by decide)⟩

/-- on the sheet, a generator word's group element has the word's matrix -/
theorem evGrp_val (w : List Gen) : (evGrp Tg Jg w).1 = evG w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a
    · show M2.mul T (evGrp Tg Jg w).1 = M2.mul T (evG w)
      rw [ih]
    · show M2.mul (Tg⁻¹).1 (evGrp Tg Jg w).1 = M2.mul Tinv (evG w)
      rw [ih, show (Tg⁻¹).1 = Tinv by decide]
    · show M2.mul J (evGrp Tg Jg w).1 = M2.mul J (evG w)
      rw [ih]

/-- on the sheet, an L/R word's group element has the word's matrix -/
theorem pvG_val (P : List Side) : (pvG Tg Jg P).1 = evLR P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    cases a
    · show M2.mul T (pvG Tg Jg P).1 = M2.mul T (evLR P)
      rw [ih]
    · show M2.mul (Jg * Tg * Jg).1 (pvG Tg Jg P).1 = M2.mul L (evLR P)
      rw [ih, show (Jg * Tg * Jg).1 = L by decide]

/-- the determinant as a homomorphism on the group on the sheet -/
def detG : GL2Z →* ℤ where
  toFun x := x.1.det
  map_one' := by decide
  map_mul' x y := M2.det_mul x.1 y.1

/-- a word of the identity reaches the state S^k S^i with k + i divisible by four, no shift left, and an even number of creases -/
theorem state_kernel (w : List Gen) (hw : evG w = M2.one) :
    (stateOf w).2.1 = [] ∧ ((stateOf w).1 + (stateOf w).2.2.1) % 4 = 0 ∧ Even (stateOf w).2.2.2 := by
  have hm : stG Tg Jg (stateOf w) = 1 := by
    rw [← evGrp_state rels_model]; exact Subtype.ext ((evGrp_val w).trans hw)
  generalize stateOf w = s at hm ⊢
  obtain ⟨k, P, i, e⟩ := s
  show P = [] ∧ (k + i) % 4 = 0 ∧ Even e
  simp only [stG] at hm
  have hP : detG (pvG Tg Jg P) = 1 := by
    show (pvG Tg Jg P).1.det = 1
    rw [pvG_val, evLR_det]
  have hd := congrArg detG hm
  simp only [map_mul, map_pow, hP, show detG (sG Tg Jg) = 1 by decide, show detG Jg = -1 by decide, one_pow, one_mul,
    map_one] at hd
  have he : Even e := (neg_one_pow_eq_one_iff_even (by decide)).mp hd
  obtain ⟨c, hc⟩ := he
  have hj : Jg ^ e = 1 := by
    rw [hc, ← two_mul, pow_mul, sq, rels_model.sq, one_pow]
  rw [hj, mul_one] at hm
  have hp : pvG Tg Jg P = (sG Tg Jg ^ ((i + k) % 4))⁻¹ := by
    rw [← pow_eq_pow_mod (i + k) (show sG Tg Jg ^ 4 = 1 from rels_model.four), pow_add, mul_inv_rev]
    exact eq_mul_inv_of_mul_eq (eq_inv_of_mul_eq_one_right hm)
  have hlt : (i + k) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hnn := evLR_nn P
  rw [← pvG_val, hp] at hnn
  generalize hr : (i + k) % 4 = r at hp hnn hlt
  interval_cases r
  · have hP1 : evLR P = evLR [] := by
      rw [← pvG_val, hp]; rfl
    exact ⟨unique_lr P [] hP1, by omega, ⟨c, hc⟩⟩
  · exact absurd hnn (by decide)
  · exact absurd hnn (by decide)
  · exact absurd hnn (by decide)

/-- the presentation: in any group, a shift and a crease with the three relations send every word of the identity to the
identity, so every relation among the words on the sheet follows from the three -/
theorem gl2_presentation {G : Type*} [Group G] {t j : G} (h : Rels t j) (w : List Gen) (hw : evG w = M2.one) :
    evGrp t j w = 1 := by
  obtain ⟨hP, h4, he⟩ := state_kernel w hw
  rw [evGrp_state h]
  generalize stateOf w = s at hP h4 he
  obtain ⟨k, P, i, e⟩ := s
  simp only at hP h4 he
  subst hP
  obtain ⟨c, hc⟩ := he
  obtain ⟨d, hd⟩ := Nat.dvd_of_mod_eq_zero h4
  have hS : sG t j ^ k * sG t j ^ i = 1 := by
    rw [← pow_add, hd, pow_mul, show sG t j ^ 4 = 1 from h.four, one_pow]
  have hJ : j ^ e = 1 := by
    rw [hc, ← two_mul, pow_mul, sq, h.sq, one_pow]
  simp [stG, pvG, hJ, hS]

/-- the inverse of a word: read backwards, with the shift and its inverse exchanged -/
def invW : List Gen → List Gen
  | [] => []
  | Gen.t :: w => invW w ++ [Gen.u]
  | Gen.u :: w => invW w ++ [Gen.t]
  | Gen.j :: w => invW w ++ [Gen.j]

/-- when j^2 = 1, the inverse word reads the inverse element -/
theorem evGrp_inv {G : Type*} [Group G] {t j : G} (hj : j * j = 1) (w : List Gen) :
    evGrp t j (invW w) = (evGrp t j w)⁻¹ := by
  have hi : j⁻¹ = j := inv_eq_of_mul_eq_one_left hj
  induction w with
  | nil => simp [invW, evGrp]
  | cons a w ih => cases a <;> simp [invW, evGrp, evGrp_append, ih, hi]

/-- two words of one matrix have one value in every group with the three relations -/
theorem gl2_same {G : Type*} [Group G] {t j : G} (h : Rels t j) (v w : List Gen) (hw : evG v = evG w) :
    evGrp t j v = evGrp t j w := by
  have hm : evG (v ++ invW w) = M2.one := by
    have hv : evGrp Tg Jg v = evGrp Tg Jg w := Subtype.ext (by rw [evGrp_val, evGrp_val, hw])
    rw [← evGrp_val, evGrp_append, evGrp_inv rels_model.sq, hv, mul_inv_cancel]
    rfl
  have h1 := gl2_presentation h _ hm
  rwa [evGrp_append, evGrp_inv h.sq, mul_inv_eq_one] at h1

/-- a group homomorphism from the sheet sends each word's value to the same word's value at the images of T and J -/
theorem evGrp_map {G : Type*} [Group G] (f : GL2Z →* G) (w : List Gen) :
    f (evGrp Tg Jg w) = evGrp (f Tg) (f Jg) w := by
  induction w with
  | nil => simp [evGrp]
  | cons a w ih => cases a <;> simp [evGrp, ih]

/-- the universal property: the group on the sheet is the group presented by the shift, the crease and the three
relations
* In any group, a shift and a crease with the three relations are the image of T and J under exactly one
  homomorphism. -/
theorem gl2_universal {G : Type*} [Group G] {t j : G} (h : Rels t j) : ∃! f : GL2Z →* G, f Tg = t ∧ f Jg = j := by
  have hone : ∀ (g : Gen) (x : GL2Z), x.1 = evG [g] → evGrp t j (nf x.1) = evGrp t j [g] := fun g x hx =>
    gl2_same h _ _ (by rw [nf_eval x.1 x.2, hx])
  refine ⟨MonoidHom.mk' (fun x => evGrp t j (nf x.1)) (fun x y => ?_), ⟨?_, ?_⟩, ?_⟩
  · rw [← evGrp_append]
    apply gl2_same h
    rw [evG_append, nf_eval _ (x * y).2, nf_eval _ x.2, nf_eval _ y.2]
    rfl
  · simpa [evGrp] using hone Gen.t Tg (by decide)
  · simpa [evGrp] using hone Gen.j Jg (by decide)
  · rintro f ⟨h1, h2⟩
    refine MonoidHom.ext fun x => ?_
    have hx : x = evGrp Tg Jg (nf x.1) := Subtype.ext ((evGrp_val _).trans (nf_eval x.1 x.2)).symm
    show f x = evGrp t j (nf x.1)
    conv_lhs => rw [hx]
    rw [evGrp_map, h1, h2]

/-- a word's determinant is 1 or -1 -/
theorem evG_det (w : List Gen) : Uni (evG w) := by
  rw [← evGrp_val]; exact (evGrp Tg Jg w).2

/-- the place D_b is a word of the group exactly when b is 1 or -1: positional notation adds an operand the two letters do not reach -/
theorem place_word_iff (b : ℤ) : (∃ w, evG w = D b) ↔ b = 1 ∨ b = -1 := by
  constructor
  · rintro ⟨w, hw⟩
    have h := evG_det w
    rw [hw] at h
    simpa [Uni, M2.det, D] using h
  · rintro (rfl | rfl)
    · exact gl2_word _ (Or.inl (by decide))
    · exact gl2_word _ (Or.inr (by decide))


/-- a state in reduced form: S^k with k below four, a word in the two shifts, S^i with i below two, the crease at most once;
with no shift left, i is zero -/
def IsNormal (s : St) : Prop := s.1 < 4 ∧ s.2.2.1 < 2 ∧ s.2.2.2 < 2 ∧ (s.2.1 = [] → s.2.2.1 = 0)

/-- S² is -I on the sheet, so it commutes with everything -/
theorem sg_central (x : GL2Z) : Commute (sG Tg Jg * sG Tg Jg) x := by
  have h : (sG Tg Jg * sG Tg Jg).1 = ⟨-1, 0, 0, -1⟩ := by decide
  refine Subtype.ext ?_
  show M2.mul (sG Tg Jg * sG Tg Jg).1 x.1 = M2.mul x.1 (sG Tg Jg * sG Tg Jg).1
  rw [h]
  ext <;> simp [M2.mul]

/-- every state has a normal state with the same value on the sheet -/
theorem exists_normal (s : St) : ∃ s' : St, IsNormal s' ∧ stG Tg Jg s' = stG Tg Jg s := by
  obtain ⟨k, P, i, e⟩ := s
  have hS4 : sG Tg Jg ^ 4 = 1 := rels_model.four
  have hJ2 : Jg ^ 2 = 1 := by rw [sq]; exact rels_model.sq
  cases P with
  | nil =>
    refine ⟨((k + i) % 4, [], 0, e % 2), ⟨Nat.mod_lt _ (by norm_num), by norm_num, Nat.mod_lt _ (by norm_num), fun _ => rfl⟩, ?_⟩
    simp only [stG, pvG, pow_zero, one_mul]
    rw [← pow_eq_pow_mod _ hS4, ← pow_eq_pow_mod _ hJ2, pow_add, mul_assoc]
  | cons a P =>
    refine ⟨((k + 2 * (i / 2)) % 4, a :: P, i % 2, e % 2),
      ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), by simp⟩, ?_⟩
    have hc : Commute (sG Tg Jg ^ (2 * (i / 2))) (pvG Tg Jg (a :: P)) := by
      rw [pow_mul, sq]; exact (sg_central _).pow_left _
    simp only [stG]
    rw [← pow_eq_pow_mod _ hS4, ← pow_eq_pow_mod _ hJ2, pow_add]
    conv_rhs => rw [← Nat.div_add_mod i 2, pow_add]
    simp only [mul_assoc]
    rw [hc.left_comm]

/-- the sign analysis: if m and m' = S^a m S^c are nonnegative, m of determinant 1, a < 4, c < 4 and c ≠ 2, then a = c = 0,
    or c is odd and m = m' = the identity -/
theorem nn_sign (m m' : M2) (hn : Nn m) (hn' : Nn m') (hd : m.det = 1) (a c : ℕ) (ha : a < 4) (hc : c < 4) (hc2 : c ≠ 2)
    (h : m' = M2.mul (M2.mul (M2.pow S a) m) (M2.pow S c)) :
    (a = 0 ∧ c = 0) ∨ (c % 2 = 1 ∧ m = M2.one ∧ m' = M2.one) := by
  obtain ⟨p, q, r, s⟩ := m
  obtain ⟨h1, h2, h3, h4⟩ := hn
  simp only [M2.det] at hd h1 h2 h3 h4
  subst h
  obtain ⟨n1, n2, n3, n4⟩ := hn'
  have hid : q = 0 → r = 0 → p = 1 ∧ s = 1 := fun hq hr => by
    subst hq hr
    have hps : p * s = 1 := by simpa using hd
    have hp : p = 1 := Int.eq_one_of_mul_eq_one_right h1 hps
    subst hp
    exact ⟨rfl, by simpa using hps⟩
  interval_cases a <;> interval_cases c <;> simp [M2.mul, M2.pow, M2.one, S] at n1 n2 n3 n4 hc2 ⊢
  · exfalso; nlinarith
  · exfalso; nlinarith
  · exfalso; nlinarith
  · exfalso; nlinarith
  · obtain ⟨rfl, rfl⟩ := hid (by omega) (by omega)
    have hq : q = 0 := by omega
    have hr : r = 0 := by omega
    subst hq hr
    simp
  · exfalso; nlinarith
  · exfalso; nlinarith
  · exfalso; nlinarith
  · exfalso; nlinarith
  · obtain ⟨rfl, rfl⟩ := hid (by omega) (by omega)
    have hq : q = 0 := by omega
    have hr : r = 0 := by omega
    subst hq hr
    simp
  · exfalso; nlinarith

/-- two reduced states of one element are one state -/
theorem normal_unique (s s' : St) (hs : IsNormal s) (hs' : IsNormal s') (h : stG Tg Jg s = stG Tg Jg s') : s = s' := by
  obtain ⟨k, P, i, e⟩ := s
  obtain ⟨k', P', i', e'⟩ := s'
  obtain ⟨hk, hi, he, h0⟩ := hs
  obtain ⟨hk', hi', he', h0'⟩ := hs'
  simp only at hk hi he h0 hk' hi' he' h0'
  simp only [stG] at h
  have hP : ∀ Q : List Side, detG (pvG Tg Jg Q) = 1 := fun Q => by
    show (pvG Tg Jg Q).1.det = 1
    rw [pvG_val, evLR_det]
  have hd := congrArg detG h
  simp only [map_mul, map_pow, hP, show detG (sG Tg Jg) = 1 by decide, show detG Jg = -1 by decide, one_pow, one_mul] at hd
  have hee : e = e' := by
    interval_cases e <;> interval_cases e' <;> first | rfl | (norm_num at hd)
  subst hee
  have h1 : sG Tg Jg ^ k * (pvG Tg Jg P * sG Tg Jg ^ i) = sG Tg Jg ^ k' * (pvG Tg Jg P' * sG Tg Jg ^ i') := by
    apply mul_right_cancel (b := Jg ^ e)
    simpa only [mul_assoc] using h
  have hS4 : sG Tg Jg ^ 4 = 1 := rels_model.four
  have hinv : ∀ n : ℕ, (sG Tg Jg ^ n)⁻¹ = sG Tg Jg ^ (3 * n) := fun n => by
    rw [pow_mul, ← inv_pow, show (sG Tg Jg)⁻¹ = sG Tg Jg ^ 3 from Subtype.ext (by decide)]
  have h2 : pvG Tg Jg P' = sG Tg Jg ^ ((3 * k' + k) % 4) * pvG Tg Jg P * sG Tg Jg ^ ((i + 3 * i') % 4) := by
    rw [← pow_eq_pow_mod _ hS4, ← pow_eq_pow_mod _ hS4, pow_add, pow_add, ← hinv, ← hinv]
    calc pvG Tg Jg P' = (sG Tg Jg ^ k')⁻¹ * (sG Tg Jg ^ k' * (pvG Tg Jg P' * sG Tg Jg ^ i')) * (sG Tg Jg ^ i')⁻¹ := by group
      _ = _ := by rw [← h1]; group
  have h3 : (pvG Tg Jg P').1 = M2.mul (M2.mul (M2.pow S ((3 * k' + k) % 4)) (pvG Tg Jg P).1) (M2.pow S ((i + 3 * i') % 4)) := by
    have hpow : ∀ n : ℕ, (sG Tg Jg ^ n).1 = M2.pow S n := fun n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ]
        show M2.mul (sG Tg Jg ^ n).1 (sG Tg Jg).1 = M2.mul (M2.pow S n) S
        rw [ih, show (sG Tg Jg).1 = S by decide]
    rw [h2]
    show M2.mul (M2.mul (sG Tg Jg ^ _).1 (pvG Tg Jg P).1) (sG Tg Jg ^ _).1 = _
    rw [hpow, hpow]
  rw [pvG_val, pvG_val] at h3
  have hc2 : (i + 3 * i') % 4 ≠ 2 := by interval_cases i <;> interval_cases i' <;> decide
  rcases nn_sign _ _ (evLR_nn P) (evLR_nn P') (evLR_det P) _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hc2 h3 with
    ⟨ha, hc⟩ | ⟨hc, hm, hm'⟩
  · rw [ha, hc] at h3
    have hPP : P' = P := unique_lr P' P (by rw [h3]; ext <;> simp [M2.mul, M2.pow, M2.one])
    subst hPP
    have hkk : k = k' := by omega
    have hii : i = i' := by omega
    subst hkk hii
    rfl
  · have hPe : P = [] := unique_lr P [] hm
    have hPe' : P' = [] := unique_lr P' [] hm'
    have hi0 := h0 hPe
    have hi0' := h0' hPe'
    omega

/-- the normal form of the group: every element is exactly one reduced state, S^k, a word in the two shifts, S^i, the
crease at most once
* Beside `gl2_presentation`, the word problem: the matrix decides it, and each element has one reduced state. -/
theorem gl2_normal_form (x : GL2Z) : ∃! s : St, IsNormal s ∧ stG Tg Jg s = x := by
  have hx : stG Tg Jg (stateOf (nf x.1)) = x := by
    rw [← evGrp_state rels_model]
    exact Subtype.ext ((evGrp_val _).trans (nf_eval x.1 x.2))
  obtain ⟨s, hs, he⟩ := exists_normal (stateOf (nf x.1))
  exact ⟨s, ⟨hs, he.trans hx⟩, fun s' h' => normal_unique _ _ h'.1 hs (h'.2.trans (he.trans hx).symm)⟩

/-! ## Z. Reduction modulo a prime: the cross determinant, positions to the left, the J-fraction's letter -/

/-- the cross determinant of two points of the line, as pairs -/
def cross (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- for v in lowest terms, any pair u and every p: p divides their cross determinant exactly when u is a multiple of v
up to multiples of p in both coordinates
* With u in lowest terms too: they are one point at p, so the power of a prime dividing it is how near they are at
  that prime. -/
theorem cross_dvd_iff (p : ℤ) (u v : ℤ × ℤ) (hv : IsCoprime v.1 v.2) :
    p ∣ cross u v ↔ ∃ l : ℤ, p ∣ u.1 - l * v.1 ∧ p ∣ u.2 - l * v.2 := by
  obtain ⟨r, s, hrs⟩ := hv
  constructor
  · rintro ⟨c, hc⟩
    simp only [cross] at hc
    exact ⟨r * u.1 + s * u.2, ⟨s * c, by linear_combination s * hc - u.1 * hrs⟩, ⟨-r * c, by linear_combination -r * hc - u.2 * hrs⟩⟩
  · rintro ⟨l, ⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨c * v.2 - d * v.1, by simp only [cross]; linear_combination v.2 * hc - v.1 * hd⟩

/-- a matrix multiplies every cross determinant by its determinant -/
theorem cross_act (x : M2) (u v : ℤ × ℤ) : cross (M2.act x u) (M2.act x v) = x.det * cross u v := by
  simp only [cross, M2.act, M2.det]; ring

/-- a word of the group keeps every cross determinant up to sign: it moves no two points nearer at any prime -/
theorem word_cross (w : List Gen) (u v : ℤ × ℤ) :
    cross (M2.act (evG w) u) (M2.act (evG w) v) = cross u v ∨ cross (M2.act (evG w) u) (M2.act (evG w) v) = -cross u v := by
  rw [cross_act]
  rcases evG_det w with h | h <;> simp [h]

/-- a word of the group sends a point in lowest terms to a point in lowest terms -/
theorem word_coprime (w : List Gen) (u : ℤ × ℤ) (h : IsCoprime u.1 u.2) : IsCoprime (M2.act (evG w) u).1 (M2.act (evG w) u).2 := by
  induction w with
  | nil => simpa [evG, M2.act, M2.one] using h
  | cons a w ih =>
    obtain ⟨r, s, hrs⟩ := ih
    cases a
    · refine ⟨r, s - r, ?_⟩
      simp only [evG, M2.act_mul]
      simp only [M2.act, T] at hrs ⊢
      linear_combination hrs
    · refine ⟨r, s + r, ?_⟩
      simp only [evG, M2.act_mul]
      simp only [M2.act, Tinv] at hrs ⊢
      linear_combination hrs
    · refine ⟨s, r, ?_⟩
      simp only [evG, M2.act_mul]
      simp only [M2.act, J] at hrs ⊢
      linear_combination hrs

/-- the two columns of a word are consecutive convergents, and no non-unit divides their cross determinant: they are
never one point modulo any prime
* Read p-adically, not stated here: they stay at distance at least 1, so the words converge at no prime. -/
theorem convergents_apart (w : List Gen) (p : ℤ) (hp : p ∣ cross (M2.act (evG w) (1, 0)) (M2.act (evG w) (0, 1))) : IsUnit p := by
  rw [cross_act, show cross (1, 0) (0, 1) = 1 by decide, mul_one] at hp
  rcases evG_det w with h | h <;> rw [h] at hp
  · exact isUnit_of_dvd_one hp
  · exact isUnit_of_dvd_one (by simpa using hp)

/-- the digit's matrix multiplies every cross determinant by the base: the base's primes see the place, and they see no word -/
theorem digit_cross (b d : ℤ) (u v : ℤ × ℤ) :
    cross (M2.act ⟨b, d, 0, 1⟩ u) (M2.act ⟨b, d, 0, 1⟩ v) = b * cross u v := by
  rw [cross_act, place_det]

/-- positions to the left: the digits d_0 d_1 ... with the units outermost and the tail innermost -/
def leftword (b : ℤ) : List ℤ → M2
  | [] => M2.one
  | d :: ds => M2.mul ⟨b, d, 0, 1⟩ (leftword b ds)

/-- the value of the digits read to the left -/
def leftval (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => d + b * leftval b ds

/-- the place word of the digits ds in base b is [[b^len, leftval b ds], [0, 1]] -/
theorem leftword_eq (b : ℤ) (ds : List ℤ) : leftword b ds = ⟨b ^ ds.length, leftval b ds, 0, 1⟩ := by
  induction ds with
  | nil => simp [leftword, leftval, M2.one]
  | cons d ds ih =>
    rw [leftword, ih]
    ext <;> simp [M2.mul, leftval, pow_succ] <;> ring

/-- k digits forget the tail modulo b^k: the images of two tails differ by exactly b^k (x - y) -/
theorem left_tail (b : ℤ) (ds : List ℤ) (x y : ℤ) :
    (M2.act (leftword b ds) (x, 1)).1 - (M2.act (leftword b ds) (y, 1)).1 = b ^ ds.length * (x - y) := by
  rw [leftword_eq]
  simp only [M2.act]
  ring

/-- reading a concatenation: leftval b (u ++ v) = leftval b u + b^|u| leftval b v -/
theorem leftval_append (b : ℤ) (u v : List ℤ) : leftval b (u ++ v) = leftval b u + b ^ u.length * leftval b v := by
  induction u with
  | nil => simp [leftval]
  | cons d u ih =>
    simp only [List.cons_append, leftval, ih, List.length_cons, pow_succ]
    ring

/-- a period at the left: m copies of a block of value H and length n satisfy (1 - b^n) x = H (1 - b^(n m)), so x is
H/(1 - b^n) modulo b^(n m)
* Read to the right, the same block is H/(b^n - 1), the opposite rational. -/
theorem left_period (b : ℤ) (ds : List ℤ) (m : ℕ) :
    (1 - b ^ ds.length) * leftval b (List.replicate m ds).flatten = leftval b ds * (1 - b ^ (ds.length * m)) := by
  induction m with
  | zero => simp [leftval]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, leftval_append, Nat.mul_succ, pow_add]
    linear_combination b ^ ds.length * ih

/-- the left period's value is the fixed point of its matrix, the pair (H, 1 - B) -/
theorem left_fixed (H B : ℤ) : M2.act ⟨B, H, 0, 1⟩ (H, 1 - B) = (H, 1 - B) := by
  simp only [M2.act, Prod.mk.injEq]
  constructor <;> ring

/-- k nines in base ten are 10^k - 1, so -1 modulo 10^k for every k (...999 = -1 in the 10-adic integers, a completion Ś4
does not adjoin) -/
theorem left_nines (k : ℕ) : (1 - (10 : ℤ)) * leftval 10 (List.replicate k 9) = 9 * (1 - 10 ^ k) := by
  simpa [leftval] using left_period 10 [9] k

/-- the axle's ends 1 and -1, the crease's fixed points, have cross determinant 2: with `cross_dvd_iff` they agree
modulo 2 and differ modulo every odd prime -/
theorem axle_ends : cross (1, 1) (-1, 1) = 2 := by decide

/-- the J-fraction's letter acts as x ↦ 1/(z - al - be x) -/
theorem fold_letter_act (al be z x : ℤ) : M2.act ⟨0, 1, -be, z - al⟩ (x, 1) = (1, z - al - be * x) := by
  simp only [M2.act, Prod.mk.injEq]
  constructor <;> ring

/-- the J-fraction's letter is the crease, a shift and a place: J T^(z - al) D_(-be) (its determinant, be, is `fold_letter_det`) -/
theorem fold_letter (al be z : ℤ) : (⟨0, 1, -be, z - al⟩ : M2) = M2.mul (M2.mul J ⟨1, z - al, 0, 1⟩) (D (-be)) := by
  ext <;> simp [M2.mul, J, D]

/-- the J-fraction's letter [[0, 1], [-beta, z - alpha]] has determinant beta -/
theorem fold_letter_det (al be z : ℤ) : (⟨0, 1, -be, z - al⟩ : M2).det = be := by simp [M2.det]

/-- the J-fraction's letter is a word of the group exactly when be is 1 or -1: every other be needs the place -/
theorem fold_letter_word_iff (al be z : ℤ) : (∃ w, evG w = ⟨0, 1, -be, z - al⟩) ↔ be = 1 ∨ be = -1 := by
  constructor
  · rintro ⟨w, hw⟩
    have h := evG_det w
    rw [hw] at h
    simpa [Uni, M2.det] using h
  · rintro (rfl | rfl)
    · exact gl2_word _ (Or.inl (by simp [M2.det]))
    · exact gl2_word _ (Or.inr (by simp [M2.det]))

end SunyaAxiom

/-! # The J-fraction's step -/

namespace AlphaRoutes

/-! ## S. The J-fraction's step at a spectral point
* A J-fraction whose coefficients end in the constant tail alpha = a, beta = b: off the band, where one fixed point
  attracts, its Stieltjes transform is read from the fixed point of w ↦ b / (z - a - w).
* The step: the integer matrix [[0, b], [-1, z - a]], determinant b, trace z - a. -/

/-- a 2 x 2 integer matrix by its entries -/
structure M2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

namespace M2

def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def one : M2 := ⟨1, 0, 0, 1⟩

def pow (x : M2) : ℕ → M2
  | 0 => one
  | n + 1 => mul (pow x n) x

def det (x : M2) : ℤ := x.a * x.d - x.b * x.c

def tr (x : M2) : ℤ := x.a + x.d

end M2

/-- the J-fraction's step at z on the tail (a, b) -/
def sunya (a b z : ℤ) : M2 := ⟨0, b, -1, z - a⟩

/-- the step's matrix [[0, b], [-1, z - a]] has determinant b -/
theorem sunya_det (a b z : ℤ) : (sunya a b z).det = b := by
  simp [sunya, M2.det]

/-- and trace z - a -/
theorem sunya_tr (a b z : ℤ) : (sunya a b z).tr = z - a := by
  simp [sunya, M2.tr]

/-- the step's fixed points are the roots of the tail's quadratic: w = b/(z - a - w) iff w^2 - (z - a) w + b = 0,
where z - a - w ≠ 0 -/
theorem sunya_fixed_point (a b z w : ℚ) (h : z - a - w ≠ 0) :
    w = b / (z - a - w) ↔ w ^ 2 - (z - a) * w + b = 0 := by
  rw [eq_div_iff h]
  constructor <;> intro h' <;> linear_combination (-1 : ℚ) * h'

/-- Catalan's tail (2, 1): the discriminant (z - 2)^2 - 4 vanishes at the band's edges z = 4 and z = 0, where the
fixed point is double, w = 1 and w = -1 -/
theorem catalan_edges : ((1 : ℚ) ^ 2 - (4 - 2) * 1 + 1 = 0) ∧ ((-1 : ℚ) ^ 2 - (0 - 2) * (-1) + 1 = 0)
    ∧ ((4 : ℚ) - 2) ^ 2 - 4 = 0 ∧ ((0 : ℚ) - 2) ^ 2 - 4 = 0 := by
  norm_num

/-! ### Elliptic: determinant 1 and trace -1, 0, 1 give M^3 = I, M^2 = -I, M^3 = -I, every integer matrix M
* The orders 3, 4, 6, with section V's `trace_neg1_ne_one` (M ≠ I at trace -1) and `trace1_sq_ne_one`
  (M^2 ≠ I at trace 1). -/

/-- determinant 1, trace -1: M^3 = I, order 3 -/
theorem clock3 (a b c d : ℤ) (h1 : a * d - b * c = 1) (h2 : a + d = -1) :
    M2.mul (M2.mul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩) ⟨a, b, c, d⟩ = M2.one := by
  have hd : d = -1 - a := by linarith
  subst hd
  simp only [M2.mul, M2.one, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 - a) * h1
  · linear_combination (-b) * h1
  · linear_combination (-c) * h1
  · linear_combination (a + 2) * h1

/-- trace 0: M^2 = -I, so the order is 4 -/
theorem clock4 (a b c d : ℤ) (h1 : a * d - b * c = 1) (h2 : a + d = 0) :
    M2.mul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩ = ⟨-1, 0, 0, -1⟩ := by
  have hd : d = -a := by linarith
  subst hd
  simp only [M2.mul, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1 : ℤ) * h1
  · ring
  · ring
  · linear_combination (-1 : ℤ) * h1

/-- trace 1: M^3 = -I, so the order is 6 -/
theorem clock6 (a b c d : ℤ) (h1 : a * d - b * c = 1) (h2 : a + d = 1) :
    M2.mul (M2.mul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩) ⟨a, b, c, d⟩ = ⟨-1, 0, 0, -1⟩ := by
  have hd : d = 1 - a := by linarith
  subst hd
  simp only [M2.mul, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a - 1) * h1
  · linear_combination (-b) * h1
  · linear_combination (-c) * h1
  · linear_combination (a - 2) * h1

/-- -I squares to the identity -/
theorem neg_one_sq : M2.mul ⟨-1, 0, 0, -1⟩ ⟨-1, 0, 0, -1⟩ = M2.one := by
  decide

/-- Catalan's band at its integer points z = 1, 2, 3, evaluated by the kernel: matrix orders exactly 3, 4, 6; the
    square at z = 2 and the cube at z = 3 are -I, so on the Stieltjes variable the orders are 3, 2, 3 -/
theorem catalan_clocks :
    (sunya 2 1 1).pow 3 = M2.one ∧ (sunya 2 1 1).pow 1 ≠ M2.one ∧ (sunya 2 1 1).pow 2 ≠ M2.one ∧
    (sunya 2 1 2).pow 4 = M2.one ∧ (sunya 2 1 2).pow 2 = ⟨-1, 0, 0, -1⟩ ∧ (sunya 2 1 2).pow 1 ≠ M2.one ∧
    (sunya 2 1 2).pow 3 ≠ M2.one ∧
    (sunya 2 1 3).pow 6 = M2.one ∧ (sunya 2 1 3).pow 3 = ⟨-1, 0, 0, -1⟩ ∧ (sunya 2 1 3).pow 1 ≠ M2.one ∧
    (sunya 2 1 3).pow 2 ≠ M2.one := by
  decide

/-! ### Parabolic: trace 2 at z = 4 and -2 at z = 0; no positive power is the identity -/

/-- at the edge z = 4 (a = 2, b = 1) the step's n-th power is [[1 - n, n], [-n, 1 + n]] -/
theorem edge4_pow (n : ℕ) : (sunya 2 1 4).pow n = ⟨1 - (n : ℤ), n, -(n : ℤ), 1 + n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [M2.pow, ih]
    simp only [sunya, M2.mul, M2.mk.injEq]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- at the edge z = 0 (a = 2, b = 1) the step's n-th power is (-1)^n [[1 - n, -n], [n, 1 + n]] -/
theorem edge0_pow (n : ℕ) :
    (sunya 2 1 0).pow n = ⟨(-1) ^ n * (1 - (n : ℤ)), (-1) ^ n * (-(n : ℤ)), (-1) ^ n * n, (-1) ^ n * (1 + n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [M2.pow, ih]
    simp only [sunya, M2.mul, M2.mk.injEq]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- at the band's edge z = 4 no positive power of the step is the identity: parabolic, no finite order -/
theorem edge4_never_one (n : ℕ) (hn : 0 < n) : (sunya 2 1 4).pow n ≠ M2.one := by
  rw [edge4_pow]
  intro h
  simp only [M2.one, M2.mk.injEq] at h
  omega

/-- nor at the edge z = 0 -/
theorem edge0_never_one (n : ℕ) (hn : 0 < n) : (sunya 2 1 0).pow n ≠ M2.one := by
  rw [edge0_pow]
  intro h
  simp only [M2.one, M2.mk.injEq] at h
  have h2 := h.2.1
  rcases neg_one_pow_eq_or ℤ n with h' | h' <;> rw [h'] at h2 <;> omega

/-! ### Hyperbolic: determinant 1 and trace at least 3, of infinite order, every integer matrix
* M^n = p_n M - p_(n-1), p_0 = 0, p_1 = 1, p_(n+2) = t p_(n+1) - p_n (Chebyshev's recurrence), t the trace.
* p_n increases for t ≥ 3. -/

def cheb (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * cheb t (n + 1) - cheb t n

/-- cheb t satisfies Chebyshev's recurrence U(n + 2) = t U(n + 1) - U(n) -/
theorem cheb_succ_succ (t : ℤ) (n : ℕ) : cheb t (n + 1 + 1) = t * cheb t (n + 1) - cheb t n := rfl

/-- a matrix of determinant 1 has (n + 1)-th power U(n + 1) M - U(n) I, with U = cheb at its trace -/
theorem pow_cheb (M : M2) (h1 : M.det = 1) (n : ℕ) :
    M.pow (n + 1) = ⟨cheb M.tr (n + 1) * M.a - cheb M.tr n, cheb M.tr (n + 1) * M.b,
                     cheb M.tr (n + 1) * M.c, cheb M.tr (n + 1) * M.d - cheb M.tr n⟩ := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [M2.det, M2.tr] at h1 ⊢
  induction n with
  | zero => simp [M2.pow, M2.mul, M2.one, cheb]
  | succ n ih =>
    rw [M2.pow, ih, cheb_succ_succ]
    simp only [M2.mul, M2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-(cheb (a + d) (n + 1))) * h1
    · ring
    · ring
    · linear_combination (-(cheb (a + d) (n + 1))) * h1

/-- for t at least 3, cheb t is nonnegative and strictly increasing -/
theorem cheb_pos (t : ℤ) (ht : 3 ≤ t) (n : ℕ) : 0 ≤ cheb t n ∧ cheb t n < cheb t (n + 1) := by
  induction n with
  | zero => simp [cheb]
  | succ n ih =>
    rw [cheb_succ_succ]
    constructor
    · linarith [ih.1, ih.2]
    · nlinarith [ih.1, ih.2, mul_le_mul_of_nonneg_right ht (by linarith [ih.1, ih.2] : (0 : ℤ) ≤ cheb t (n + 1))]

/-- a matrix of determinant 1 and trace at least 3 has no positive power equal to the identity: hyperbolic, no finite order -/
theorem hyperbolic_no_clock (M : M2) (h1 : M.det = 1) (ht : 3 ≤ M.tr) (n : ℕ) :
    M.pow (n + 1) ≠ M2.one := by
  intro h
  rw [pow_cheb M h1 n] at h
  obtain ⟨a, b, c, d⟩ := M
  simp only [M2.det, M2.tr] at h1 ht h
  simp only [M2.one, M2.mk.injEq] at h
  obtain ⟨_, hb, hc, _⟩ := h
  have hp := cheb_pos (a + d) ht n
  have hp1 : 0 < cheb (a + d) (n + 1) := by linarith [hp.1, hp.2]
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · linarith
    · exact h
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · linarith
    · exact h
  subst hb0 hc0
  have had : a * d = 1 := by linarith
  by_cases ha : a ≤ 0 <;> by_cases hd : d ≤ 0
  · linarith
  · push Not at hd
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -a) (by linarith : (0 : ℤ) ≤ d)]
  · push Not at ha
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a) (by linarith : (0 : ℤ) ≤ -d)]
  · push Not at ha hd
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1)]

/-- a hyperbolic step's multiplier: for t ≥ 3 and s ≥ 0 with s^2 = t^2 - 4, u = (t - s)/2 is the root of u^2 - t u + 1 = 0 with 0 < u < 1 -/
theorem multiplier (t s : ℚ) (ht : 3 ≤ t) (hs0 : 0 ≤ s) (hs : s ^ 2 = t ^ 2 - 4) :
    let u := (t - s) / 2
    u ^ 2 - t * u + 1 = 0 ∧ 0 < u ∧ u < 1 := by
  intro u
  have h1 : (t - s) * (t + s) = 4 := by linear_combination -hs
  have h2 : (s - (t - 2)) * (s + (t - 2)) = 4 * t - 8 := by linear_combination hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [u]; linear_combination (1 / 4 : ℚ) * hs
  · simp only [u]; nlinarith
  · simp only [u]; nlinarith

/-! ## B. The atoms' multipliers: the plastic and the golden are units; Fine's is not -/

/-- the plastic atom z = -1/ρ, ρ^3 = ρ + 1, is a root of z^3 - z^2 + 1 -/
theorem plastic_atom {K : Type*} [Field K] (ρ : K) (hρ : ρ ≠ 0) (h : ρ ^ 3 = ρ + 1) :
    (-ρ⁻¹) ^ 3 - (-ρ⁻¹) ^ 2 + 1 = 0 := by
  field_simp
  linear_combination h

/-- its multiplier is u = -ρ^-3: u^2 - (z - 2) u + 1 = 0 at z = -1/ρ on the tail (2, 1) -/
theorem plastic_multiplier {K : Type*} [Field K] (ρ : K) (hρ : ρ ≠ 0) (h : ρ ^ 3 = ρ + 1) :
    (-(ρ ^ 3)⁻¹) ^ 2 - (-ρ⁻¹ - 2) * (-(ρ ^ 3)⁻¹) + 1 = 0 := by
  field_simp
  linear_combination (ρ ^ 3 + ρ - 1) * h

/-- the multiplier is a unit: a root of the palindromic u^6 + 5u^5 + 11u^4 + 15u^3 + 11u^2 + 5u + 1 -/
theorem plastic_unit {K : Type*} [Field K] (ρ : K) (hρ : ρ ≠ 0) (h : ρ ^ 3 = ρ + 1) :
    let u := -(ρ ^ 3)⁻¹
    u ^ 6 + 5 * u ^ 5 + 11 * u ^ 4 + 15 * u ^ 3 + 11 * u ^ 2 + 5 * u + 1 = 0 := by
  intro u
  have h18 : ρ ^ 18 * (u ^ 6 + 5 * u ^ 5 + 11 * u ^ 4 + 15 * u ^ 3 + 11 * u ^ 2 + 5 * u + 1)
      = 1 - 5 * ρ ^ 3 + 11 * ρ ^ 6 - 15 * ρ ^ 9 + 11 * ρ ^ 12 - 5 * ρ ^ 15 + ρ ^ 18 := by
    simp only [u]
    field_simp
    ring
  have hP : 1 - 5 * ρ ^ 3 + 11 * ρ ^ 6 - 15 * ρ ^ 9 + 11 * ρ ^ 12 - 5 * ρ ^ 15 + ρ ^ 18 = 0 := by
    linear_combination (-1 + ρ - ρ ^ 2 + 5 * ρ ^ 3 - 4 * ρ ^ 4 + 3 * ρ ^ 5 - 9 * ρ ^ 6 + 5 * ρ ^ 7 - 2 * ρ ^ 8
      + 8 * ρ ^ 9 - 3 * ρ ^ 10 + ρ ^ 11 - 4 * ρ ^ 12 + ρ ^ 13 + ρ ^ 15) * h
  have h18' : ρ ^ 18 ≠ 0 := pow_ne_zero _ hρ
  exact (mul_eq_zero.mp (h18.trans hP)).resolve_left h18'

/-- the golden atom 2 + √5 = φ^3 on the tail (2, 1): 1/φ is a root of the multiplier's equation u^2 - (z - 2) u + 1 = 0 at
z = φ^3, and of u^4 - 3u^2 + 1 -/
theorem golden_unit {K : Type*} [Field K] (φ : K) (hφ : φ ≠ 0) (h : φ ^ 2 = φ + 1) :
    (φ⁻¹) ^ 4 - 3 * (φ⁻¹) ^ 2 + 1 = 0 ∧ (φ⁻¹) ^ 2 - (φ ^ 3 - 2) * φ⁻¹ + 1 = 0 := by
  constructor
  · field_simp
    linear_combination (φ ^ 2 + φ - 1) * h
  · field_simp
    linear_combination (-(φ ^ 2 + φ + 1)) * h

/-- and its trace u + 1/u squares to 5 -/
theorem golden_trace {K : Type*} [Field K] (φ : K) (hφ : φ ≠ 0) (h : φ ^ 2 = φ + 1) : (φ⁻¹ + φ) ^ 2 = 5 := by
  field_simp
  linear_combination (φ ^ 2 + φ - 1) * h

/-- Fine's atom -1/2 on the tail (2, 1): the multiplier -1/2 is a root of 2u^2 + 5u + 2 = (2u + 1)(u + 2); its minimal
polynomial 2u + 1 is not monic, so -1/2 is no algebraic integer and no unit -/
theorem fine_multiplier : (2 : ℚ) * (-1 / 2) ^ 2 + 5 * (-1 / 2) + 2 = 0 := by
  norm_num

/-! ## I. The radial step: the Laguerre J-fraction, alpha_k = 2k + a + 1, beta_k = k (k + a) -/

/-- at the band's bottom z = 0 the discriminant is 4k + (a + 1)^2, positive for every k > 0: hyperbolic -/
theorem radial_disc (k a : ℚ) : (2 * k + a + 1) ^ 2 - 4 * k * (k + a) = 4 * k + (a + 1) ^ 2
    ∧ (0 < k → 0 < 4 * k + (a + 1) ^ 2) := by
  exact ⟨by ring, fun hk => by positivity⟩

/-- the numerator of the derivative of cosh l_k in the coupling a (taken by hand) is k (a - 1 + z): the integer
    case a = 1 is stationary at z = 0 -/
theorem radial_stationary (k a z : ℚ) : 2 * k * (k + a) - k * (2 * k + a + 1 - z) = k * (a - 1 + z) := by
  ring

/-- at a = 1 the multiplier u = (s - 1)/r, s^2 = k + 1, r^2 = k, has trace 2s/r: (s - 1)^2 + r^2 = 2 s (s - 1)
* By hand: u is a unit only at k = 1, 2, 4, since u^2 + u^-2 = (2k + 4)/k would be a rational algebraic integer, an
  integer only when k divides 4. -/
theorem radial_trace {R : Type*} [CommRing R] (k s r : R) (hs : s ^ 2 = k + 1) (hr : r ^ 2 = k) :
    (s - 1) ^ 2 + r ^ 2 = 2 * s * (s - 1) := by
  linear_combination hr - hs

/-! ## D. The cone kappa^2 = gamma^2 + w^2, read as Dirac's (w = Z alpha), and the boost across it -/

/-- the boost eps = (kappa + gamma)/w has trace 2 kappa / w: the large trace -/
theorem cone_trace {K : Type*} [Field K] (κ γ w : K) (hw : w ≠ 0) (hk : κ + γ ≠ 0) (h : κ ^ 2 = γ ^ 2 + w ^ 2) :
    (κ + γ) / w + w / (κ + γ) = 2 * κ / w := by
  field_simp
  linear_combination (-1 : K) * h

/-- the gap ratio (kappa + gamma)/(kappa - gamma) is the square of the boost -/
theorem cone_gap {K : Type*} [Field K] (κ γ w : K) (hw : w ≠ 0) (hm : κ - γ ≠ 0) (h : κ ^ 2 = γ ^ 2 + w ^ 2) :
    (κ + γ) / (κ - γ) = ((κ + γ) / w) ^ 2 := by
  field_simp
  linear_combination (-(κ + γ)) * h

/-- the square's trace: eps + eps^-1 = T gives eps^2 + eps^-2 = T^2 - 2 -/
theorem trace_sq {K : Type*} [Field K] (ε T : K) (hε : ε ≠ 0) (h : ε + ε⁻¹ = T) : ε ^ 2 + (ε ^ 2)⁻¹ = T ^ 2 - 2 := by
  rw [← h]
  field_simp
  ring

/-- the trace is twice the algebraic hyperbolic cosine (ε + ε⁻¹)/2, whose duplication law is 2 c^2 - 1 = (ε^2 + ε^-2)/2 -/
theorem cosh_log {K : Type*} [Field K] [CharZero K] (ε : K) (hε : ε ≠ 0) :
    let c := (ε + ε⁻¹) / 2
    ε + ε⁻¹ = 2 * c ∧ 2 * c ^ 2 - 1 = (ε ^ 2 + (ε ^ 2)⁻¹) / 2 := by
  intro c
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_⟩
  · simp only [c]; field_simp
  · simp only [c]; field_simp; ring

/-- the partial quotient a as a matrix: T^a J = [[a, 1], [1, 0]], determinant -1 -/
def TJ (a : ℤ) : M2 := ⟨a, 1, 1, 0⟩

/-- the period matrix T^1 J T^m J of [m + 1; (1, m)], period (1, m), has trace m + 2 and determinant 1 -/
theorem period_matrix (m : ℤ) : (M2.mul (TJ 1) (TJ m)).tr = m + 2 ∧ (M2.mul (TJ 1) (TJ m)).det = 1 := by
  constructor
  · simp only [TJ, M2.mul, M2.tr]; ring
  · simp only [TJ, M2.mul, M2.det]; ring

/-- at kappa = 1, w = 1/N the gap ratio's trace (2N)^2 - 2 is the trace of the period matrix T^1 J T^(4N^2 - 4) J
of [4N^2 - 3; (1, 4N^2 - 4)] -/
theorem large_trace (N : ℤ) : (M2.mul (TJ 1) (TJ (4 * N ^ 2 - 4))).tr = (2 * N) ^ 2 - 2 := by
  rw [(period_matrix _).1]
  ring

/-! ## F. Every Dirac level (n_r, kappa) is a rational curve -/

/-- with gamma = (u^2 - n_r^2 - kappa^2)/(2 n_r): (n_r + gamma)^2 + (kappa^2 - gamma^2) = u^2 -/
theorem level_rational (nr κ u : ℚ) (h : nr ≠ 0) :
    (nr + (u ^ 2 - nr ^ 2 - κ ^ 2) / (2 * nr)) ^ 2
      + (κ ^ 2 - ((u ^ 2 - nr ^ 2 - κ ^ 2) / (2 * nr)) ^ 2) = u ^ 2 := by
  field_simp
  ring

/-- so s = (n_r + gamma)/u satisfies s^2 (1 + t/(n_r + gamma)^2) = 1, t = kappa^2 - gamma^2: read as Dirac's level -/
theorem level_s (nr κ u γ : ℚ) (hu : u ≠ 0) (hg : nr + γ ≠ 0) (key : (nr + γ) ^ 2 + (κ ^ 2 - γ ^ 2) = u ^ 2) :
    ((nr + γ) / u) ^ 2 * (1 + (κ ^ 2 - γ ^ 2) / (nr + γ) ^ 2) = 1 := by
  field_simp
  linear_combination key

/-! # Spinor lock (m, n)
* spinor (a, b), a^2 + b^2 = p: Penrose's spin-vector, real components; group SL(2, R), not SL(2, C)
* square (a^2 - b^2, 2ab; p): flagpole, plane's null vector; Euclid's triple
* +-(a, b): one flagpole; sign = turn 2 pi
* lock: Clifford product, prime spinors (Cartan 1913; Kocik 2007; Penrose, Rindler 1984)
* The coupling's rule 1/α = (m² + n²)/(2mn): Catalan's at t = 1, where the loop through Narayana's triangle closes. -/

/-- Gaussian integers as pairs: angles add, norms multiply -/
def gmul (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- at t = 1 the loop's rule y = (α/2)(1 + y²) holds at every lock (m, n), with y = n/m and α/2 = mn/(m² + n²) -/
theorem loop_rule (m n : ℚ) (hm : m ≠ 0) (hs : m ^ 2 + n ^ 2 ≠ 0) :
    n / m = m * n / (m ^ 2 + n ^ 2) * (1 + (n / m) ^ 2) := by
  field_simp

/-- Euclid's remainders until the first whose square is at most p, with the next one: Hermite–Serret's stop -/
def descend : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b, _ => (b, a % b)
  | f + 1, a, b, p => if p < b * b then descend f b (a % b) p else (b, a % b)

/-! # Unit, edge, self-recoil
* units: 1 = (1, 0), the given 1/0; i = (0, 1), one crease of it; i times (m, n) = (-n, m), a quarter turn -/

/-- the unit i as a pair: i times (m, n) is (-n, m), a quarter turn, every m and n -/
theorem quarter_turn (m n : ℤ) : gmul (0, 1) (m, n) = (-n, m) := by simp [gmul]

/-- the units: i times the unit lock (1, 0) is (0, 1); i squared is -1; four quarter turns return (1, 0) -/
theorem unit_i : gmul (0, 1) (1, 0) = (0, 1) ∧ gmul (0, 1) (0, 1) = (-1, 0) ∧
    gmul (0, 1) (gmul (0, 1) (gmul (0, 1) (gmul (0, 1) (1, 0)))) = (1, 0) := by decide

/-- the edge lock (1, 1): α = 1, where the tail step's discriminant (z − 2)² − 4 vanishes at z = 4/α² = 4 -/
theorem edge_lock : (2 * 1 * 1 : ℚ) / (1 ^ 2 + 1 ^ 2) = 1 ∧ ((4 : ℚ) / 1 ^ 2 - 2) ^ 2 - 4 = 0 := by norm_num

/-- the self-recoil lock (2, 1): α = 4/5, and s·C(s²/4) = 1 with C = 5/4 = 1 + u·C², u = s²/4 -/
theorem recoil_lock : (2 * 2 * 1 : ℚ) / (2 ^ 2 + 1 ^ 2) = 4 / 5 ∧ (5 / 4 : ℚ) = 1 + (4 / 5) ^ 2 / 4 * (5 / 4) ^ 2 ∧
    (4 / 5 : ℚ) * (5 / 4) = 1 := by norm_num

/-! # Candidate -/

/-- the coupling read downstream of the word: 1/α = (m² + n²)/(2mn) = 662194096285/4832263787, cross-multiplied -/
theorem node_inv_frac : (1150813 ^ 2 + 4199 ^ 2) * 4832263787 = 2 * 1150813 * 4199 * 662194096285 := by decide

/-- and its word, 20 partial quotients -/
theorem node_inv_word : euclidWord 30 662194096285 4832263787 =
    [137, 27, 1, 3, 1, 1, 18, 1, 1, 1, 2, 5, 1, 2, 247, 1, 4, 1, 1, 2] := by decide

/-- the node squared in Z[i]: (m + ni)² = (m² − n²) + 2mn·i, twice the flagpole's legs (662176464684, 4832263787), the Pythagorean triple's -/
theorem tri_square : gmul (1150813, 4199) (1150813, 4199) = (2 * 662176464684, 2 * 4832263787) := by decide

/-- the flagpole's legs and the numerator of 1/α: 1 − α² = (662176464684/662194096285)², so the root of (1 − t)·y² = 1 at t = α², the
    central binomials' equation, is 662194096285/662176464684 -/
theorem lor_pythagoras : (662194096285 : ℕ) ^ 2 = 662176464684 ^ 2 + 4832263787 ^ 2 := by decide

/-- the binding and the inverse of the Lorentz factor add to 1: 17631601 + 662176464684 = 662194096285, with 17631601 = 4199² -/
theorem bind_sum : 17631601 + 662176464684 = 662194096285 ∧ (4199 : ℕ) ^ 2 = 17631601 := by decide

/-! # Selection rule
* On the lock (m, n) = (1150813, 4199): the word [274; 14, 1, 1, 1, 2, 2, 2, 1, 1, 2].
* Brahmagupta's identity: the lock is (1, 1)·(2, 1)·(116341, −344824).
* Hermite–Serret: Euclid on (P, r), r² ≡ −1 (P), stopped below √P, returns the prime spinor (a Gaussian prime) from
  its norm P = 132438819257 alone. -/

/-- the lock (1150813, 4199) measured by Euclid's division: the 274 word, ending at the remainder 0 -/
theorem node_word : euclidWord 20 1150813 4199 = [274, 14, 1, 1, 1, 2, 2, 2, 1, 1, 2] := by decide

/-- Brahmagupta: the lock is the edge (1, 1) times the self-recoil (2, 1) times one prime spinor -/
theorem node_factors : gmul (gmul (1, 1) (2, 1)) (116341, -344824) = (1150813, 4199) := by decide

/-- spinor dividing spinor: the lock times the conjugate of (1, 3) is 10 times the prime spinor, so the division leaves 0 -/
theorem node_divides : gmul (1150813, 4199) (1, -3) = (10 * 116341, 10 * -344824) := by decide

/-- the norms: 2 · 5 · P for the lock -/
theorem node_norm : (1150813 : ℕ) ^ 2 + 4199 ^ 2 = 2 * 5 * 132438819257 := by decide

/-- and P for the prime spinor -/
theorem spinor_norm : (344824 : ℕ) ^ 2 + 116341 ^ 2 = 132438819257 := by decide

/-- r = 17536552121 satisfies r² + 1 ≡ 0 (P) -/
theorem sqrt_neg_one : (17536552121 ^ 2 + 1) % 132438819257 = 0 := by decide

/-- Euclid on (P, r), stopped below √P, returns the prime spinor from its norm alone -/
theorem hermite_serret : descend 40 132438819257 17536552121 132438819257 = (344824, 116341) := by decide

end AlphaRoutes

/-! # Axiom Verification Report
Every theorem's axioms lie within `propext`, `Classical.choice` and `Quot.sound`; the kernel's
report follows, one line a theorem. -/

#print axioms SunyaAxiom.M2.act_mul
#print axioms SunyaAxiom.M2.mul_assoc
#print axioms SunyaAxiom.M2.one_mul
#print axioms SunyaAxiom.M2.mul_one
#print axioms SunyaAxiom.M2.det_mul
#print axioms SunyaAxiom.M2.cayley_hamilton
#print axioms SunyaAxiom.M2.tr_sq
#print axioms SunyaAxiom.M2.pow_add
#print axioms SunyaAxiom.point3_det
#print axioms SunyaAxiom.point3_JJ
#print axioms SunyaAxiom.point4_crease_limit
#print axioms SunyaAxiom.point4_instance
#print axioms SunyaAxiom.point5_swap
#print axioms SunyaAxiom.point1_position
#print axioms SunyaAxiom.point2_unit
#print axioms SunyaAxiom.zero_from_inf
#print axioms SunyaAxiom.one_from_zero
#print axioms SunyaAxiom.T_pow
#print axioms SunyaAxiom.quotient_word
#print axioms SunyaAxiom.nat_from_inf
#print axioms SunyaAxiom.succ_is_shift
#print axioms SunyaAxiom.val_nat
#print axioms SunyaAxiom.word_append
#print axioms SunyaAxiom.cont_det
#print axioms SunyaAxiom.cden_pos
#print axioms SunyaAxiom.cden_mono
#print axioms SunyaAxiom.cden_double
#print axioms SunyaAxiom.cden_pow
#print axioms SunyaAxiom.cden_prod
#print axioms SunyaAxiom.word_prefix
#print axioms SunyaAxiom.prefix_reads
#print axioms SunyaAxiom.conv_step
#print axioms SunyaAxiom.regular_word_converges
#print axioms SunyaAxiom.digit_word
#print axioms SunyaAxiom.place_det
#print axioms SunyaAxiom.posword_act_aux
#print axioms SunyaAxiom.posword_act
#print axioms SunyaAxiom.zero_digit_holds
#print axioms SunyaAxiom.zero_digit_is_place
#print axioms SunyaAxiom.periodic_place
#print axioms SunyaAxiom.periodic_crease
#print axioms SunyaAxiom.wheel_fixed_point_quadratic
#print axioms SunyaAxiom.wheel_golden
#print axioms SunyaAxiom.wheel_bhaskara_67
#print axioms SunyaAxiom.wheel_bhaskara_61_one_turn
#print axioms SunyaAxiom.wheel_bhaskara_61
#print axioms SunyaAxiom.J_det
#print axioms SunyaAxiom.T_det_tr
#print axioms SunyaAxiom.Tinv_T
#print axioms SunyaAxiom.S_word
#print axioms SunyaAxiom.S_order
#print axioms SunyaAxiom.JTJ
#print axioms SunyaAxiom.clocks_catalan
#print axioms SunyaAxiom.inf_fixed_T
#print axioms SunyaAxiom.one_fixed_J
#print axioms SunyaAxiom.trailing_one
#print axioms SunyaAxiom.succ_ne_zero
#print axioms SunyaAxiom.succ_inj
#print axioms SunyaAxiom.quotient_square
#print axioms SunyaAxiom.quotient_involution_iff
#print axioms SunyaAxiom.shift_pow
#print axioms SunyaAxiom.mul_is_repeat
#print axioms SunyaAxiom.place_is_repetition
#print axioms SunyaAxiom.trace0_order4
#print axioms SunyaAxiom.trace0_sq
#print axioms SunyaAxiom.trace_neg1_order3
#print axioms SunyaAxiom.trace1_order6
#print axioms SunyaAxiom.trace1_cube
#print axioms SunyaAxiom.trace_neg1_ne_one
#print axioms SunyaAxiom.trace1_sq_ne_one
#print axioms SunyaAxiom.reflection_sq
#print axioms SunyaAxiom.tensor_add
#print axioms SunyaAxiom.tensor_mul
#print axioms SunyaAxiom.tensor_in_x
#print axioms SunyaAxiom.tensor_in_y
#print axioms SunyaAxiom.tensor_out
#print axioms SunyaAxiom.binomial_is_shift
#print axioms SunyaAxiom.binomial_moves_alpha
#print axioms SunyaAxiom.ev_t
#print axioms SunyaAxiom.ev_j
#print axioms SunyaAxiom.ev_nn
#print axioms SunyaAxiom.ev_uni
#print axioms SunyaAxiom.red_tail
#print axioms SunyaAxiom.red_j_cases
#print axioms SunyaAxiom.det_peel_t
#print axioms SunyaAxiom.det_peel_jt
#print axioms SunyaAxiom.rows_comparable
#print axioms SunyaAxiom.rows_not_both
#print axioms SunyaAxiom.exists_word_aux
#print axioms SunyaAxiom.exists_word
#print axioms SunyaAxiom.T_cancel
#print axioms SunyaAxiom.J_cancel
#print axioms SunyaAxiom.ev_t_ne_one
#print axioms SunyaAxiom.ev_jt_ne_one
#print axioms SunyaAxiom.ev_t_ne_J
#print axioms SunyaAxiom.ev_j_ne_one
#print axioms SunyaAxiom.ev_t_ne_ev_jt
#print axioms SunyaAxiom.unique_word
#print axioms SunyaAxiom.faithful
#print axioms SunyaAxiom.point1_pair
#print axioms SunyaAxiom.point2_pair
#print axioms SunyaAxiom.point4_trailing
#print axioms SunyaAxiom.word_det
#print axioms SunyaAxiom.T_pow_ne_one
#print axioms SunyaAxiom.act_inf
#print axioms SunyaAxiom.stab_inf
#print axioms SunyaAxiom.inf_fixed_Tpow
#print axioms SunyaAxiom.involution_iff
#print axioms SunyaAxiom.ev_cons
#print axioms SunyaAxiom.red_push
#print axioms SunyaAxiom.ev_push
#print axioms SunyaAxiom.red_reduce
#print axioms SunyaAxiom.ev_reduce
#print axioms SunyaAxiom.same_word_iff
#print axioms SunyaAxiom.L_is_JTJ
#print axioms SunyaAxiom.JT_LJ
#print axioms SunyaAxiom.JL_TJ
#print axioms SunyaAxiom.evLR_r
#print axioms SunyaAxiom.evLR_l
#print axioms SunyaAxiom.evLR_nn
#print axioms SunyaAxiom.evLR_det
#print axioms SunyaAxiom.ev_lr
#print axioms SunyaAxiom.ev_eq_lr
#print axioms SunyaAxiom.two_shifts_and_crease
#print axioms SunyaAxiom.Linv_L
#print axioms SunyaAxiom.L_cancel
#print axioms SunyaAxiom.evLR_r_ne_one
#print axioms SunyaAxiom.evLR_l_ne_one
#print axioms SunyaAxiom.evLR_r_ne_l
#print axioms SunyaAxiom.unique_lr
#print axioms SunyaAxiom.exists_lr
#print axioms SunyaAxiom.J_mirror
#print axioms SunyaAxiom.toLR_rep
#print axioms SunyaAxiom.creasesOdd_rep
#print axioms SunyaAxiom.toLR_tj
#print axioms SunyaAxiom.creasesOdd_tj
#print axioms SunyaAxiom.quotients_are_runs
#print axioms SunyaAxiom.ev_rep
#print axioms SunyaAxiom.word_tj
#print axioms SunyaAxiom.zero_needs_crease
#print axioms SunyaAxiom.reach_aux
#print axioms SunyaAxiom.reach
#print axioms SunyaAxiom.M2.negs_mul
#print axioms SunyaAxiom.M2.negate_negate
#print axioms SunyaAxiom.M2.det_negs
#print axioms SunyaAxiom.M2.tr_negs
#print axioms SunyaAxiom.M2.pow_two_eq
#print axioms SunyaAxiom.M2.pow_negs_even
#print axioms SunyaAxiom.M2.pow_square
#print axioms SunyaAxiom.M2.cheb_succ_succ
#print axioms SunyaAxiom.M2.pow_cheb
#print axioms SunyaAxiom.M2.cheb_pos
#print axioms SunyaAxiom.M2.cheb_two_aux
#print axioms SunyaAxiom.M2.hyperbolic_no_clock
#print axioms SunyaAxiom.M2.parabolic_pos
#print axioms SunyaAxiom.M2.parabolic_neg
#print axioms SunyaAxiom.M2.hyperbolic_neg
#print axioms SunyaAxiom.M2.crease_no_clock
#print axioms SunyaAxiom.crystallographic
#print axioms SunyaAxiom.monoid_orders
#print axioms SunyaAxiom.evG_append
#print axioms SunyaAxiom.Tinv_pow
#print axioms SunyaAxiom.evG_rep_t
#print axioms SunyaAxiom.evG_rep_u
#print axioms SunyaAxiom.evG_tpow
#print axioms SunyaAxiom.evG_sword
#print axioms SunyaAxiom.evG_negone
#print axioms SunyaAxiom.word_c_zero
#print axioms SunyaAxiom.gl2_aux
#print axioms SunyaAxiom.gl2_word
#print axioms SunyaAxiom.evS_det
#print axioms SunyaAxiom.JT_TST
#print axioms SunyaAxiom.JTinv_word
#print axioms SunyaAxiom.evG_evS
#print axioms SunyaAxiom.sl2_generated
#print axioms SunyaAxiom.nf0_eval
#print axioms SunyaAxiom.nf_eval_aux
#print axioms SunyaAxiom.nf_eval
#print axioms SunyaAxiom.peano_succ_inj
#print axioms SunyaAxiom.peano_succ_ne_zero
#print axioms SunyaAxiom.peano_induction
#print axioms SunyaAxiom.natWord_reads
#print axioms SunyaAxiom.J_fixed_iff
#print axioms SunyaAxiom.T_fixed_iff
#print axioms SunyaAxiom.pair_word
#print axioms SunyaAxiom.pair_coprime
#print axioms SunyaAxiom.tail_pair
#print axioms SunyaAxiom.euclid_unique
#print axioms SunyaAxiom.tail_ne_single
#print axioms SunyaAxiom.tail_inj
#print axioms SunyaAxiom.nf_pair_inj
#print axioms SunyaAxiom.coprime_mod
#print axioms SunyaAxiom.tail_exists
#print axioms SunyaAxiom.normal_form_exists
#print axioms SunyaAxiom.rational_once
#print axioms SunyaAxiom.evGrp_append
#print axioms SunyaAxiom.rels_L_S
#print axioms SunyaAxiom.rels_central
#print axioms SunyaAxiom.rels_even
#print axioms SunyaAxiom.rels_tsl
#print axioms SunyaAxiom.rels_j_S
#print axioms SunyaAxiom.rels_j_pv
#print axioms SunyaAxiom.stG_t
#print axioms SunyaAxiom.stG_u
#print axioms SunyaAxiom.stG_j
#print axioms SunyaAxiom.evGrp_state
#print axioms SunyaAxiom.rels_model
#print axioms SunyaAxiom.evGrp_val
#print axioms SunyaAxiom.pvG_val
#print axioms SunyaAxiom.state_kernel
#print axioms SunyaAxiom.gl2_presentation
#print axioms SunyaAxiom.evGrp_inv
#print axioms SunyaAxiom.gl2_same
#print axioms SunyaAxiom.evGrp_map
#print axioms SunyaAxiom.gl2_universal
#print axioms SunyaAxiom.evG_det
#print axioms SunyaAxiom.place_word_iff
#print axioms SunyaAxiom.sg_central
#print axioms SunyaAxiom.exists_normal
#print axioms SunyaAxiom.nn_sign
#print axioms SunyaAxiom.normal_unique
#print axioms SunyaAxiom.gl2_normal_form
#print axioms SunyaAxiom.cross_dvd_iff
#print axioms SunyaAxiom.cross_act
#print axioms SunyaAxiom.word_cross
#print axioms SunyaAxiom.word_coprime
#print axioms SunyaAxiom.convergents_apart
#print axioms SunyaAxiom.digit_cross
#print axioms SunyaAxiom.leftword_eq
#print axioms SunyaAxiom.left_tail
#print axioms SunyaAxiom.leftval_append
#print axioms SunyaAxiom.left_period
#print axioms SunyaAxiom.left_fixed
#print axioms SunyaAxiom.left_nines
#print axioms SunyaAxiom.axle_ends
#print axioms SunyaAxiom.fold_letter_act
#print axioms SunyaAxiom.fold_letter
#print axioms SunyaAxiom.fold_letter_det
#print axioms SunyaAxiom.fold_letter_word_iff
#print axioms AlphaRoutes.sunya_det
#print axioms AlphaRoutes.sunya_tr
#print axioms AlphaRoutes.sunya_fixed_point
#print axioms AlphaRoutes.catalan_edges
#print axioms AlphaRoutes.clock3
#print axioms AlphaRoutes.clock4
#print axioms AlphaRoutes.clock6
#print axioms AlphaRoutes.neg_one_sq
#print axioms AlphaRoutes.catalan_clocks
#print axioms AlphaRoutes.edge4_pow
#print axioms AlphaRoutes.edge0_pow
#print axioms AlphaRoutes.edge4_never_one
#print axioms AlphaRoutes.edge0_never_one
#print axioms AlphaRoutes.cheb_succ_succ
#print axioms AlphaRoutes.pow_cheb
#print axioms AlphaRoutes.cheb_pos
#print axioms AlphaRoutes.hyperbolic_no_clock
#print axioms AlphaRoutes.multiplier
#print axioms AlphaRoutes.plastic_atom
#print axioms AlphaRoutes.plastic_multiplier
#print axioms AlphaRoutes.plastic_unit
#print axioms AlphaRoutes.golden_unit
#print axioms AlphaRoutes.golden_trace
#print axioms AlphaRoutes.fine_multiplier
#print axioms AlphaRoutes.radial_disc
#print axioms AlphaRoutes.radial_stationary
#print axioms AlphaRoutes.radial_trace
#print axioms AlphaRoutes.cone_trace
#print axioms AlphaRoutes.cone_gap
#print axioms AlphaRoutes.trace_sq
#print axioms AlphaRoutes.cosh_log
#print axioms AlphaRoutes.period_matrix
#print axioms AlphaRoutes.large_trace
#print axioms AlphaRoutes.level_rational
#print axioms AlphaRoutes.level_s
#print axioms AlphaRoutes.loop_rule
#print axioms AlphaRoutes.quarter_turn
#print axioms AlphaRoutes.unit_i
#print axioms AlphaRoutes.edge_lock
#print axioms AlphaRoutes.recoil_lock
#print axioms AlphaRoutes.node_inv_frac
#print axioms AlphaRoutes.node_inv_word
#print axioms AlphaRoutes.tri_square
#print axioms AlphaRoutes.lor_pythagoras
#print axioms AlphaRoutes.bind_sum
#print axioms AlphaRoutes.node_word
#print axioms AlphaRoutes.node_factors
#print axioms AlphaRoutes.node_divides
#print axioms AlphaRoutes.node_norm
#print axioms AlphaRoutes.spinor_norm
#print axioms AlphaRoutes.sqrt_neg_one
#print axioms AlphaRoutes.hermite_serret
