/-
Copyright (c) 2026 Sambuddha Sarkar. All rights reserved.
Author: Sambuddha Sarkar
-/
/-
Arithmetic Origami, page 3: Big Bang / ΛCDM, Table 1 lines 38 to 48, the epochs, the shell closures and the first fold;
Lean 4 theorems, in the page's order, epoch by epoch.
Lean 4.34.1, Mathlib v4.34.1. Check: lake build OrigamiArithmetica.BigBang (a project requiring Mathlib v4.34.1).
Output: the axiom report alone; an error is a false statement.
Stated here, once: Table 1's ΛCDM lines (namespace FreeParameters, as page 2 states its lines); the shell closures read off
(n+1)!'s division as it runs, the onset at every odd N from 3 and a readout never 34 (EuclidSelection); the closures'
two branches set against the measured ones (Nucleons); the closures of the n + l order (Electrons); the helium fraction 8/33
inside its interval and the simplest fraction there (AgeClocks).
Restated on one line under namespace BigBang, each proved by its theorem on page 1, page 2 or in the Foldcyclopedia: the
transformation steps the epochs cite (Origami), the closures, seats and addresses of the elements (PeriodicTable), the
lock's square (AlphaRoutes), the spinor of 29 (page 2);
and, above the closures they hold for, three rules for every N: the onset, readout = closure, readout never 34
(EuclidSelection).
Proofs: `decide +kernel` and `decide`, the kernel evaluating a closed statement; `norm_num`; `omega` and `simp` with Mathlib.

## Workflow Delineation
* Author: Sambuddha Sarkar.
  Computation, Śūnya conjecture and axiom, and the methodology. Definitions, theorems and kernel
  checks formulated, reviewed and validated.
* AI assistance:
  Principal investigation within bounded searches.
  Text, code and computation runs drafted and executed under the author's review.
-/
import OrigamiArithmetica.FreeParameters

open AlphaRoutes (euclidWord gmul)

/-! # 01 Big Bang · t = 0 -/

/-! ## Foldcyclopedia -/

namespace BigBang

open Origami in
/-- Step 28: A000079 divided by n + 1 is nu, on the first 40 terms. -/
theorem step28_divideByNPlusOne : divideByNPlusOne A000079 = nu := Origami.step28_divideByNPlusOne

open Origami in
/-- Step 40: the J-fraction ones beta_G1 reproduces G1; `poleAtTwo` of its betas gives the first 20 terms of A040000, on the first 40 terms. -/
theorem step40_poleAtTwo : jacobiMoments ones beta_G1 40 = G1 /\ poleAtTwo beta_G1 20 = A040000.take 20 := Origami.step40_poleAtTwo

end BigBang

/-! # 02 Primordial fluctuations · Δ²R, ns -/

namespace FreeParameters

/-! ## cos_As: lock (1, 469815645), x = 1/469815645 -/

/-- the lock (1, 469815645) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_As_word : euclidWord 7 1 469815645 = [0, 469815645] := by decide

/-! ## cos_ns: lock (25, 26), x = 25/26 -/

/-- the lock (25, 26) is the row's fraction; Euclid's division gives its 3 letters and ends at remainder 0 -/
theorem cos_ns_word : euclidWord 8 25 26 = [0, 1, 25] := by decide

end FreeParameters

/-! # 03 Hot plasma · radiation era -/

/-! ## Foldcyclopedia -/

namespace BigBang

open Origami in
/-- Step 18: the diagonal T(2n, n) of the triangle A007318 is A000984, on the first 20 terms. -/
theorem step18_centralDiagonal : centralDiagonal A007318 20 = A000984.take 20 := Origami.step18_centralDiagonal

end BigBang

/-! # 04 Nucleosynthesis · BBN -/

/-! ## the shell closures, read off (n+1)!'s division as it runs -/

namespace EuclidSelection

/-! ## T1. States -/

/-- states, oscillator shell N -/
def shell (N : ℕ) : ℕ := (N + 1) * (N + 2)

/-- states, the j = N + 1/2 level: 2j + 1 -/
def top (N : ℕ) : ℕ := 2 * (N + 1)

/-- states, shell N less the j = N + 1/2 level -/
def rest (N : ℕ) : ℕ := N * (N + 1)

/-- shell = top + rest -/
theorem shell_split (N : ℕ) : shell N = top N + rest N := by
  unfold shell top rest; ring

/-! ## T3. Division rest / top -/

/-- N = 2k: quotient k, remainder 0 -/
theorem rest_top_even (k : ℕ) : rest (2 * k) / top (2 * k) = k ∧ rest (2 * k) % top (2 * k) = 0 := by
  have h : 0 < top (2 * k) := by unfold top; omega
  exact (Nat.div_mod_unique h).2 ⟨by unfold rest top; ring, h⟩

/-- N = 2k + 1: quotient k, remainder 2k + 2 -/
theorem rest_top_odd (k : ℕ) :
    rest (2 * k + 1) / top (2 * k + 1) = k ∧ rest (2 * k + 1) % top (2 * k + 1) = 2 * k + 2 := by
  have h : 0 < top (2 * k + 1) := by unfold top; omega
  exact (Nat.div_mod_unique h).2 ⟨by unfold rest top; ring, by unfold top; omega⟩

/-! ## T4. Onset -/

/-- 1 ≤ quotient and remainder ≠ 0 iff 3 ≤ N and N odd -/
theorem onset_euclid (N : ℕ) : (1 ≤ rest N / top N ∧ rest N % top N ≠ 0) ↔ (3 ≤ N ∧ N % 2 = 1) := by
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · rw [(rest_top_even k).1, (rest_top_even k).2]; omega
  · rw [(rest_top_odd k).1, (rest_top_odd k).2]; omega

/-- top < rest iff 3 ≤ N -/
theorem onset_seats (N : ℕ) : top N < rest N ↔ 3 ≤ N := by
  unfold top rest
  constructor
  · intro h
    by_contra hn
    have hlt : N < 3 := by omega
    interval_cases N <;> omega
  · intro h
    nlinarith [Nat.mul_le_mul_right (N + 1) h]

/-! ## T6. Shell closures, onset k -/

/-- states added at closure N, onset k -/
def group (k N : ℕ) : ℕ := if N < k then shell N else if N = k then top N else rest (N - 1) + top N

/-- closure N, onset k: group k 0 + ... + group k N -/
def closure (k N : ℕ) : ℕ := ((List.range (N + 1)).map (group k)).sum

/-- oscillator closure N: shell 0 + ... + shell N -/
def osc (N : ℕ) : ℕ := ((List.range (N + 1)).map shell).sum

theorem closure_succ (k N : ℕ) : closure k (N + 1) = closure k N + group k (N + 1) := by
  unfold closure
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem osc_succ (N : ℕ) : osc (N + 1) = osc N + shell (N + 1) := by
  unfold osc
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- 3 ≤ N: closure 3 N + rest N = osc N -/
theorem closure_osc (N : ℕ) (h : 3 ≤ N) : closure 3 N + rest N = osc N := by
  induction N, h using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have e1 := closure_succ 3 n
    have e2 := osc_succ n
    have e3 : group 3 (n + 1) = rest n + top (n + 1) := by
      have h1 : ¬ (n + 1 < 3) := by omega
      have h2 : ¬ (n + 1 = 3) := by omega
      simp [group, h1, h2]
    have e4 := shell_split (n + 1)
    omega

/-! ## T10. The coefficient stream -/

/-- the coefficients in order: alpha_0, beta_0, alpha_1, beta_1, ... -/
def stream (k : ℕ) : ℕ := if k % 2 = 0 then top (k / 2) else rest (k / 2)

/-- running sum: stream 0 + ... + stream k -/
def run : ℕ → ℕ
  | 0 => stream 0
  | k + 1 => run k + stream (k + 1)

theorem run_succ (k : ℕ) : run (k + 1) = run k + stream (k + 1) := rfl

theorem stream_even (N : ℕ) : stream (2 * N) = top N := by
  have h1 : (2 * N) % 2 = 0 := by omega
  have h2 : (2 * N) / 2 = N := by omega
  simp [stream, h1, h2]

theorem stream_odd (N : ℕ) : stream (2 * N + 1) = rest N := by
  have h1 : (2 * N + 1) % 2 = 1 := by omega
  have h2 : (2 * N + 1) / 2 = N := by omega
  simp [stream, h1, h2]

/-- the sum through beta_N is osc N -/
theorem run_odd (N : ℕ) : run (2 * N + 1) = osc N := by
  induction N with
  | zero => decide
  | succ n ih =>
    have e : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
    have s1 : stream (2 * n + 1 + 1) = top (n + 1) := by
      have h := stream_even (n + 1)
      rwa [show 2 * (n + 1) = 2 * n + 1 + 1 by ring] at h
    have s2 : stream (2 * n + 1 + 1 + 1) = rest (n + 1) := by
      have h := stream_odd (n + 1)
      rwa [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring] at h
    rw [e, run_succ, run_succ, ih, s1, s2, osc_succ, shell_split (n + 1)]
    ring

/-- 3 ≤ N: closure 3 N is the sum through alpha_N -/
theorem closure_cut (N : ℕ) (h : 3 ≤ N) : closure 3 N = run (2 * N) := by
  have e1 : run (2 * N + 1) = run (2 * N) + stream (2 * N + 1) := run_succ (2 * N)
  have e2 := stream_odd N
  have e3 := run_odd N
  have e4 := closure_osc N h
  omega

theorem run_mono (k : ℕ) : run k ≤ run (k + 1) := by
  rw [run_succ]; exact Nat.le_add_right _ _

/-- 34, the fourth closure of the j = l - 1/2 branch, is no running sum -/
theorem off_stream : ∀ k, run k ≠ 34 := by
  intro k
  by_cases h : k ≤ 6
  · interval_cases k <;> decide
  · have h7 : run 7 ≤ run k := monotone_nat_of_le_succ run_mono (by omega)
    have h40 : run 7 = 40 := by decide
    omega

/-! ## T12. Closures read off the J-fraction as it runs -/

/-- closure N: the running sum through beta_N if beta_N ≤ alpha_N, else through alpha_N -/
def readout (N : ℕ) : ℕ := if rest N ≤ top N then run (2 * N + 1) else run (2 * N)

/-- beta_N ≤ alpha_N iff N < 3 -/
theorem rest_le_top (N : ℕ) : rest N ≤ top N ↔ N < 3 := by
  rw [← not_lt, onset_seats]
  exact not_le

/-- readout N = closure 3 N, every N -/
theorem readout_closure (N : ℕ) : readout N = closure 3 N := by
  by_cases h : N < 3
  · have hle : rest N ≤ top N := (rest_le_top N).2 h
    simp only [readout, hle, ↓reduceIte]
    interval_cases N <;> decide
  · have hnle : ¬ rest N ≤ top N := fun h' => h ((rest_le_top N).1 h')
    simp only [readout, hnle, ↓reduceIte]
    exact (closure_cut N (by omega)).symm

/-- the first 7 readouts: the published closures, compared last -/
theorem readout_published : (List.range 7).map readout = [2, 8, 20, 28, 50, 82, 126] := by decide +kernel

/-- readout ≠ 34, every N -/
theorem readout_not_34 (N : ℕ) : readout N ≠ 34 := by
  unfold readout
  split
  · exact off_stream _
  · exact off_stream _

end EuclidSelection

namespace BigBang

/-! ## for every N: the onset, readout = closure, readout never 34; the closures below are their instances -/

open EuclidSelection in
/-- the onset, every N: quotient at least 1 and remainder not 0 iff N is odd and at least 3 -/
theorem onset_euclid (N : ℕ) : (1 ≤ rest N / top N ∧ rest N % top N ≠ 0) ↔ (3 ≤ N ∧ N % 2 = 1) := EuclidSelection.onset_euclid N

open EuclidSelection in
/-- readout = closure, every N -/
theorem readout_closure (N : ℕ) : readout N = closure 3 N := EuclidSelection.readout_closure N

open EuclidSelection in
/-- the readout is never 34, every N -/
theorem readout_not_34 (N : ℕ) : readout N ≠ 34 := EuclidSelection.readout_not_34 N

end BigBang

/-! ## the two branches, compared last with the measured closures -/

namespace Nucleons

/-! ### 2. The page's numbers
The page's lists, as printed; an input: stated, never derived. -/

/-- input, compared last: the 7 measured magic numbers, as printed; nuc_branches derives the same
    values -/
def input_nuc_closures : List Rat := [2, 8, 20, 28, 50, 82, 126]

/-- input, compared last: the closures the page's sources report past those -/
def input_nuc_sourced : List Rat := [184, 258, 350]

/-- onset shell: the first N with beta_N = N(N + 1) > alpha_N = 2(N + 1) -/
def nuc_crossing : Nat := 3

/-- closure at shell N, j = l + 1/2 branch: below the onset, every shell through N; from the onset,
    the shells below N plus N's j = N + 1/2 level -/
def closure (N : Nat) : Nat :=
  if N < nuc_crossing then 2 * Nat.choose (N + 3) 3 else 2 * Nat.choose (N + 2) 3 + 2 * (N + 1)

/-- j = l - 1/2 branch: from the onset, shell N's j = N - 1/2 level (2N states) drops from the full
    closure -/
def antiClosure (N : Nat) : Nat :=
  if N < nuc_crossing then 2 * Nat.choose (N + 3) 3 else 2 * Nat.choose (N + 3) 3 - 2 * N

/-- the rule's closures at those places, set against the inputs -/
def closures_sourced : List Rat := [2, 8, 20, 28, 50, 82, 126, 184, 258, 350]

/-! ### 4. The closures
Closed form; the j = l + 1/2 and j = l - 1/2 branches. -/

/-- {closure, antiClosure, nuc_crossing, input_nuc_closures, closures_sourced} -> onset: the first N
    with beta_N > alpha_N; the j = l + 1/2 branch gives the 7 measured magic numbers (compared
    last), then the sourced ones; the j = l - 1/2 branch does not -/
theorem nuc_branches :
    2 * (nuc_crossing + 1) < nuc_crossing * (nuc_crossing + 1) /\
    (List.range nuc_crossing).all (fun N => N * (N + 1) <= 2 * (N + 1)) = true /\
    (List.range 10).map (fun N => (closure N : Rat)) = closures_sourced /\
    closures_sourced.take 7 = input_nuc_closures /\ closures_sourced.drop 7 = input_nuc_sourced /\
    (List.range 7).map (fun N => (antiClosure N : Rat)) != input_nuc_closures := by
  decide +kernel

end Nucleons

/-! ## Foldcyclopedia: H, He, seats and closure 2 -/

namespace BigBang

open PeriodicTable in
/-- every element to 137 has its address, its position j from 1 to L: carbon at the closures' address then 2, 4; silicon then 3, 4; Z = 137 then 8, 19, in a period of 50. To 118 its (N, j) is section G's (the page's "element Z at its ID") -/
theorem address_map_places : zLast = 137 ∧ address 6 = closuresAt ++ ["2", "4"] ∧ address 14 = closuresAt ++ ["3", "4"] ∧ address 137 = closuresAt ++ ["8", "19"] ∧ lenOf 137 = 50 ∧ (List.range 137).all (fun i => decide (1 ≤ seatOf (i + 1) ∧ seatOf (i + 1) ≤ lenOf (i + 1))) = true ∧ (List.range 118).all (fun i => (periodOf (i + 1), seatOf (i + 1)) == seat (i + 1)) = true := PeriodicTable.address_map_places

open PeriodicTable in
/-- every element's valence, the distance to the nearest closure, is read off its position j: min(j, L − j), L the period's length, Z = 1 … 118 -/
theorem valence_from_seat : (List.range 118).all (fun i => valence (i + 1) == min (seat (i + 1)).2 (periodLen (seat (i + 1)).1 - (seat (i + 1)).2)) = true := PeriodicTable.valence_from_seat

end BigBang

namespace AgeClocks

/-! ## T4. Helium-4 mass fraction: 8/33, the window's simplest rational -/

/-- 8/33 is in the Y_p window [2415/10000, 2481/10000]: 2415 * 33 ≤ 10000 * 8, 10000 * 8 ≤ 2481 * 33 -/
theorem helium_lock : (2415 : ℕ) * 33 ≤ 10000 * 8 ∧ (10000 : ℕ) * 8 ≤ 2481 * 33 := by norm_num

/-- smallest denominator: no p/q with 0 < q < 33, p ≤ q, is in the window -/
theorem helium_simplest :
    ∀ q < 33, ∀ p ≤ q, 0 < q → ¬(2415 * q ≤ 10000 * p ∧ 10000 * p ≤ 2481 * q) := by
  decide

end AgeClocks

namespace FreeParameters

/-! ## cos_Yp: lock (8, 33), x = 8/33 -/

/-- the lock (8, 33) is the row's fraction; Euclid's division gives its 3 letters and ends at remainder 0 -/
theorem cos_Yp_word : euclidWord 8 8 33 = [0, 4, 8] := by decide

/-! ## cos_eta: lock (1, 1623376624), x = 1/1623376624 -/

/-- the lock (1, 1623376624) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_eta_word : euclidWord 7 1 1623376624 = [0, 1623376624] := by decide

end FreeParameters

/-! # 05 Matter–radiation equality · zeq -/

namespace FreeParameters

/-! ## cos_ob: lock (1, 45), x = 1/45 -/

/-- the lock (1, 45) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_ob_word : euclidWord 7 1 45 = [0, 45] := by decide

/-! ## cos_oc: lock (3, 25), x = 3/25 -/

/-- the lock (3, 25) is the row's fraction; Euclid's division gives its 3 letters and ends at remainder 0 -/
theorem cos_oc_word : euclidWord 8 3 25 = [0, 8, 3] := by decide

end FreeParameters

/-! # 06 Last scattering · z* -/

/-! ## Foldcyclopedia -/

namespace BigBang

open Origami in
/-- Step 26: the S-fraction with coefficients c_tt is A000142, on the first 40 terms. -/
theorem step26_sfractionMoments : sfractionMoments c_tt 40 = A000142 := Origami.step26_sfractionMoments

open Origami in
/-- Step 24: the S-fraction with coefficients c_a is A000108, on the first 40 terms. -/
theorem step24_sfractionMoments : sfractionMoments c_a 40 = A000108 := Origami.step24_sfractionMoments

open Origami in
/-- Step 31: the J-fraction zeros beta_nu0 reproduces nu0, and lc(row i) det(z - J_i) is row i of A100258, i = 0 .. 8, on the first 40 terms. -/
theorem step31_charpolyRowsAre : jacobiMoments zeros beta_nu0 40 = nu0 /\ charpolyRowsAre zeros beta_nu0 A100258 8 = true := Origami.step31_charpolyRowsAre

/-! ## page 2 -/

/-- the spinor (5, 2) of 29 -/
theorem spinor_29 : (5 : Nat) ^ 2 + 2 ^ 2 = 29 := FreeParameters.spinor_29

end BigBang

/-! # 07 Dark ages, first stars · zre -/

namespace FreeParameters

/-! ## cos_tau: lock (1, 17), x = 1/17 -/

/-- the lock (1, 17) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_tau_word : euclidWord 7 1 17 = [0, 17] := by decide

end FreeParameters

/-! # 08 Elements · stars forge -/

/-! ## the closures of the n + l order -/

namespace Electrons

/-! ### 2. The page's numbers
The page's lists, as printed; an input: stated, never derived. -/

/-- the closures of the n + l order, as printed -/
def closure_list : List Rat := [2, 10, 18, 36, 54, 86, 118]

/-! ### 4. The order by n + l
Subshells ordered by n + l, then n (Madelung's rule); a period closes before each s subshell. -/

/-- A008619: partitions of m into parts 1 and 2, floor(m/2) + 1 -/
def A008619 (m : Nat) : Nat := m / 2 + 1

/-- electrons in subshell (n, l): 2(2l + 1) -/
def seats (q : Prod Nat Nat) : Nat := 2 * (2 * q.2 + 1)

/-- group n + l = k, by n: subshells (k - l, l), l < A008619(k - 1) -/
def group (k : Nat) : List (Prod Nat Nat) :=
  ((List.range (A008619 (k - 1))).map (fun l => (k - l, l))).reverse

/-- order by n + l, then n: groups k = 1, ..., K -/
def order (K : Nat) : List (Prod Nat Nat) := (List.range K).flatMap (fun k => group (k + 1))

/-- closures of an order: electrons before each s subshell, past the first -/
def closures (o : List (Prod Nat Nat)) : List Nat :=
  ((List.range o.length).filter (fun j => 0 < j && (o.getD j (0, 0)).2 == 0)).map
    (fun j => ((o.take j).map seats).sum)

/-- {closure_list} -> order through n + l = 8: shell closures 2, 10, 18, 36, 54, 86, 118, running
    sums of the period lengths 2 A008619(i + 1)^2; read as the noble gases' atomic numbers -/
theorem el_closures :
    (closures (order 8)).map (fun z => (z : Rat)) = closure_list /\
      (List.range 7).map (fun i =>
        ((((List.range (i + 1)).map fun j => 2 * A008619 (j + 1) ^ 2).sum : Nat) : Rat))
          = closure_list := by
  decide +kernel

end Electrons

/-! ## Foldcyclopedia -/

namespace BigBang

open PeriodicTable in
/-- the closures are the running sums of the periods' lengths -/
theorem closes_are_period_sums : (List.range 7).map (fun k => ((List.range (k + 1)).map fun i => periodLen (i + 1)).sum) = closes := PeriodicTable.closes_are_period_sums

end BigBang

/-! # 09 Chemistry · lane C -/

/-! ## Foldcyclopedia -/

namespace BigBang

open Origami in
/-- Step 43: the J-fraction zeros ones reproduces A126120; with every other beta times t, its even moments' coefficients, read by rows, are the first 19 rows of A001263, on the first 40 terms. -/
theorem step43_alternateBetaRows : jacobiMoments zeros ones 40 = A126120 /\ alternateBetaRows ones 19 = A001263 := Origami.step43_alternateBetaRows

end BigBang

/-! # 11 Λ era, today · Ω, H₀, T₀ -/

namespace FreeParameters

/-! ## cos_h: lock (1, 8429203911621286861613845026784597785325762090048547658556865), x = 1/8429203911621286861613845026784597785325762090048547658556865 -/

/-- the lock (1, 8429203911621286861613845026784597785325762090048547658556865) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_h_word : euclidWord 7 1 8429203911621286861613845026784597785325762090048547658556865 = [0, 8429203911621286861613845026784597785325762090048547658556865] := by decide

/-! ## cos_ol: lock (16, 11), sin^2 theta = 121/377 -/

/-- Euclid's division of the lock (16, 11): its word, ending at remainder 0 -/
theorem cos_ol_lock : euclidWord 8 16 11 = [1, 2, 5] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 121/377, cross-multiplied -/
theorem cos_ol_reading : 121 * (16 ^ 2 + 11 ^ 2) = 377 * 11 ^ 2 := by decide

/-- Euclid's division of 121/377: the row's 7 printed letters -/
theorem cos_ol_word : euclidWord 12 121 377 = [0, 3, 8, 1, 1, 1, 4] := by decide

/-- Brahmagupta: the lock (16, 11) is the product of its spinors -/
theorem cos_ol_spinors : gmul (gmul (gmul (1, 0) (3, -2)) (5, -2)) (0, 1) = (16, 11) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem cos_ol_norm : (16 : Nat) ^ 2 + 11 ^ 2 = 13 * 29 := by decide

/-! ## cos_T0: lock (1, 51970498757072662968265955773072), x = 1/51970498757072662968265955773072 -/

/-- the lock (1, 51970498757072662968265955773072) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem cos_T0_word : euclidWord 7 1 51970498757072662968265955773072 = [0, 51970498757072662968265955773072] := by decide

end FreeParameters

/-! ## page 1 -/

namespace BigBang

/-- the node squared in Z[i]: (m + ni)² = (m² − n²) + 2mn·i, twice the flagpole's legs (662176464684, 4832263787), the Pythagorean triple's -/
theorem tri_square : gmul (1150813, 4199) (1150813, 4199) = (2 * 662176464684, 2 * 4832263787) := AlphaRoutes.tri_square

end BigBang

/-! # First fold -/

/-! ## Foldcyclopedia -/

namespace BigBang

open Origami in
/-- Step 1: the binomial transform of A000007 is A000012, on the first 40 terms. -/
theorem step01_binomialTransform : binomialTransform A000007 = A000012 := Origami.step01_binomialTransform

end BigBang

/-! ## checksum: the axioms of every theorem stated here -/

#print axioms BigBang.step28_divideByNPlusOne
#print axioms BigBang.step40_poleAtTwo
#print axioms FreeParameters.cos_As_word
#print axioms FreeParameters.cos_ns_word
#print axioms BigBang.step18_centralDiagonal
#print axioms EuclidSelection.shell_split
#print axioms EuclidSelection.rest_top_even
#print axioms EuclidSelection.rest_top_odd
#print axioms EuclidSelection.onset_euclid
#print axioms EuclidSelection.onset_seats
#print axioms EuclidSelection.closure_succ
#print axioms EuclidSelection.osc_succ
#print axioms EuclidSelection.closure_osc
#print axioms EuclidSelection.run_succ
#print axioms EuclidSelection.stream_even
#print axioms EuclidSelection.stream_odd
#print axioms EuclidSelection.run_odd
#print axioms EuclidSelection.closure_cut
#print axioms EuclidSelection.run_mono
#print axioms EuclidSelection.off_stream
#print axioms EuclidSelection.rest_le_top
#print axioms EuclidSelection.readout_closure
#print axioms EuclidSelection.readout_published
#print axioms EuclidSelection.readout_not_34
#print axioms BigBang.onset_euclid
#print axioms BigBang.readout_closure
#print axioms BigBang.readout_not_34
#print axioms Nucleons.nuc_branches
#print axioms BigBang.address_map_places
#print axioms BigBang.valence_from_seat
#print axioms AgeClocks.helium_lock
#print axioms AgeClocks.helium_simplest
#print axioms FreeParameters.cos_Yp_word
#print axioms FreeParameters.cos_eta_word
#print axioms FreeParameters.cos_ob_word
#print axioms FreeParameters.cos_oc_word
#print axioms BigBang.step26_sfractionMoments
#print axioms BigBang.step24_sfractionMoments
#print axioms BigBang.step31_charpolyRowsAre
#print axioms BigBang.spinor_29
#print axioms FreeParameters.cos_tau_word
#print axioms Electrons.el_closures
#print axioms BigBang.closes_are_period_sums
#print axioms BigBang.step43_alternateBetaRows
#print axioms FreeParameters.cos_h_word
#print axioms FreeParameters.cos_ol_lock
#print axioms FreeParameters.cos_ol_reading
#print axioms FreeParameters.cos_ol_word
#print axioms FreeParameters.cos_ol_spinors
#print axioms FreeParameters.cos_ol_norm
#print axioms FreeParameters.cos_T0_word
#print axioms BigBang.tri_square
#print axioms BigBang.step01_binomialTransform
