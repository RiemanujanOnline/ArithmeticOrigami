/-
Copyright (c) 2026 Sambuddha Sarkar. All rights reserved.
Author: Sambuddha Sarkar
-/
/-
Arithmetic Origami, page 2: the Standard Model, Table 1 lines 1 to 37, each line's arithmetic; Lean 4 theorems.
Lean 4.34.1, Mathlib v4.34.1. Check: lake build OrigamiArithmetica.FreeParameters (a project requiring Mathlib v4.34.1).
Output: the axiom report alone; an error is a false statement.
Terms: lock, a pair (m, n), the Gaussian integer m + ni; word, the quotients of Euclid's division, in order;
spinor, a pair (a, b) with a^2 + b^2 = p; reading, the rule that gives a row's fraction from its lock.
One block a line of the table, in Table 1's order:
* lock: Euclid's division of (m, n) gives the lock's word and ends at remainder 0.
* reading: the row's fraction p/q is the lock's value by the row's rule, cross-multiplied.
  ratio m/n; angle n^2/(m^2 + n^2); coupling 2mn/(m^2 + n^2), or its inverse for 1/alpha; Z pole (m - n)/(4m).
* word: Euclid's division of (p, q) gives the row's printed letters.
* spinors, norm: the lock is the product of its spinors; its norm is the product of the printed factors.
A ratio line's fraction is its lock, so it carries its word alone.
Then each spinor's norm, once a factor, and each factor's primality where it is stated: every factor is proved prime (35).
Not stated in this file: the comparison with measurement, and the control statistic.
Proofs: `decide`, the kernel evaluating a closed integer statement; `norm_num` for a prime.
Euclid's word and the Gaussian product are page 1's (AlphaRoutes.euclidWord, AlphaRoutes.gmul), defined once there.
Above the lines, the rule at every lock (page 1), of which each coupling line is one instance.
After the factors, the statements page 2 cites from page 1 and the Foldcyclopedia, each restated on one line and proved by
its theorem there: the lock's square the flagpole, the edge and self-recoil locks, the word and the factors of alpha's
lock, the central binomials (the arcsine line). Lines 38 to 48, ΛCDM, are page 3's (BigBang.lean).

## Workflow Delineation
* Author: Sambuddha Sarkar.
  Computation, Śūnya conjecture and axiom, and the methodology. Definitions, theorems and kernel
  checks formulated, reviewed and validated.
* AI assistance:
  Principal investigation within bounded searches.
  Text, code and computation runs drafted and executed under the author's review.
-/
import OrigamiArithmetica.Foldcyclopedia

namespace FreeParameters

open AlphaRoutes (euclidWord gmul)

/-! ## page 1: the rule at every lock; each coupling line below is one instance -/

/-- at t = 1 the loop's rule y = (α/2)(1 + y²) holds at every lock (m, n), with y = n/m and α/2 = mn/(m² + n²) -/
theorem loop_rule (m n : ℚ) (hm : m ≠ 0) (hs : m ^ 2 + n ^ 2 ≠ 0) : n / m = m * n / (m ^ 2 + n ^ 2) * (1 + (n / m) ^ 2) := AlphaRoutes.loop_rule m n hm hs

/-! ## alpha: lock (1150813, 4199), 1/alpha = 662194096285/4832263787 -/

/-- Euclid's division of the lock (1150813, 4199): its word, ending at remainder 0 -/
theorem alpha_lock : euclidWord 16 1150813 4199 = [274, 14, 1, 1, 1, 2, 2, 2, 1, 1, 2] := by decide

/-- the coupling's rule, inverted: (m^2 + n^2)/(2mn) = 662194096285/4832263787, cross-multiplied -/
theorem alpha_reading : 662194096285 * (2 * 1150813 * 4199) = 4832263787 * (1150813 ^ 2 + 4199 ^ 2) := by decide

/-- Euclid's division of 662194096285/4832263787: the row's 20 printed letters -/
theorem alpha_word : euclidWord 25 662194096285 4832263787 = [137, 27, 1, 3, 1, 1, 18, 1, 1, 1, 2, 5, 1, 2, 247, 1, 4, 1, 1, 2] := by decide

/-- Brahmagupta: the lock (1150813, 4199) is the product of its spinors -/
theorem alpha_spinors : gmul (gmul (gmul (1, 1) (2, 1)) (344824, 116341)) (0, -1) = (1150813, 4199) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem alpha_norm : (1150813 : Nat) ^ 2 + 4199 ^ 2 = 2 * 5 * 132438819257 := by decide

/-! ## alpha_mz: lock (1791, 7), 1/alpha = 1603865/12537 -/

/-- Euclid's division of the lock (1791, 7): its word, ending at remainder 0 -/
theorem alpha_mz_lock : euclidWord 8 1791 7 = [255, 1, 6] := by decide

/-- the coupling's rule, inverted: (m^2 + n^2)/(2mn) = 1603865/12537, cross-multiplied -/
theorem alpha_mz_reading : 1603865 * (2 * 1791 * 7) = 12537 * (1791 ^ 2 + 7 ^ 2) := by decide

/-- Euclid's division of 1603865/12537: the row's 11 printed letters -/
theorem alpha_mz_word : euclidWord 16 1603865 12537 = [127, 1, 13, 2, 1, 1, 5, 1, 5, 1, 3] := by decide

/-- Brahmagupta: the lock (1791, 7) is the product of its spinors -/
theorem alpha_mz_spinors : gmul (gmul (gmul (1, 1) (2, -1)) (4, -1)) (137, -10) = (1791, 7) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem alpha_mz_norm : (1791 : Nat) ^ 2 + 7 ^ 2 = 2 * 5 * 17 * 18869 := by decide

/-! ## alpha_mz_os: lock (2063, 8), 1/alpha = 4256033/33008 -/

/-- Euclid's division of the lock (2063, 8): its word, ending at remainder 0 -/
theorem alpha_mz_os_lock : euclidWord 8 2063 8 = [257, 1, 7] := by decide

/-- the coupling's rule, inverted: (m^2 + n^2)/(2mn) = 4256033/33008, cross-multiplied -/
theorem alpha_mz_os_reading : 4256033 * (2 * 2063 * 8) = 33008 * (2063 ^ 2 + 8 ^ 2) := by decide

/-- Euclid's division of 4256033/33008: the row's 10 printed letters -/
theorem alpha_mz_os_word : euclidWord 15 4256033 33008 = [128, 1, 15, 1, 1, 19, 1, 8, 1, 4] := by decide

/-- Brahmagupta: the lock (2063, 8) is the product of its spinors -/
theorem alpha_mz_os_spinors : gmul (gmul (1, 0) (40, 11)) (48, -13) = (2063, 8) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem alpha_mz_os_norm : (2063 : Nat) ^ 2 + 8 ^ 2 = 1721 * 2473 := by decide

/-! ## sw_onshell: lock (69, 37), sin^2 theta = 1369/6130 -/

/-- Euclid's division of the lock (69, 37): its word, ending at remainder 0 -/
theorem sw_onshell_lock : euclidWord 10 69 37 = [1, 1, 6, 2, 2] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 1369/6130, cross-multiplied -/
theorem sw_onshell_reading : 1369 * (69 ^ 2 + 37 ^ 2) = 6130 * 37 ^ 2 := by decide

/-- Euclid's division of 1369/6130: the row's 10 printed letters -/
theorem sw_onshell_word : euclidWord 15 1369 6130 = [0, 4, 2, 10, 1, 2, 1, 1, 2, 3] := by decide

/-- Brahmagupta: the lock (69, 37) is the product of its spinors -/
theorem sw_onshell_spinors : gmul (gmul (1, 1) (2, 1)) (18, -17) = (69, 37) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem sw_onshell_norm : (69 : Nat) ^ 2 + 37 ^ 2 = 2 * 5 * 613 := by decide

/-! ## sw_msbar: lock (31, 17), sin^2 theta = 289/1250 -/

/-- Euclid's division of the lock (31, 17): its word, ending at remainder 0 -/
theorem sw_msbar_lock : euclidWord 10 31 17 = [1, 1, 4, 1, 2] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 289/1250, cross-multiplied -/
theorem sw_msbar_reading : 289 * (31 ^ 2 + 17 ^ 2) = 1250 * 17 ^ 2 := by decide

/-- Euclid's division of 289/1250: the row's 6 printed letters -/
theorem sw_msbar_word : euclidWord 11 289 1250 = [0, 4, 3, 13, 2, 3] := by decide

/-- Brahmagupta: the lock (31, 17) is the product of its spinors -/
theorem sw_msbar_spinors : gmul (gmul (gmul (gmul (gmul (1, 1) (2, -1)) (2, -1)) (2, -1)) (2, -1)) (0, 1) = (31, 17) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem sw_msbar_norm : (31 : Nat) ^ 2 + 17 ^ 2 = 2 * 5 ^ 4 := by decide

/-! ## zpole: lock (230, 17), sin^2 theta_eff = 213/920 -/

/-- Euclid's division of the lock (230, 17): its word, ending at remainder 0 -/
theorem zpole_lock : euclidWord 9 230 17 = [13, 1, 1, 8] := by decide

/-- the Z pole's rule: (m - n)/(4m) = 213/920, cross-multiplied -/
theorem zpole_reading : 213 * (4 * 230) = 920 * (230 - 17) := by decide

/-- the same lock's coupling: 2mn/(m^2 + n^2) = 7820/53189, cross-multiplied -/
theorem zpole_asymmetry : 7820 * (230 ^ 2 + 17 ^ 2) = 53189 * (2 * 230 * 17) := by decide

/-- Euclid's division of 213/920: the row's 7 printed letters -/
theorem zpole_word : euclidWord 12 213 920 = [0, 4, 3, 7, 1, 1, 4] := by decide

/-- Brahmagupta: the lock (230, 17) is the product of its spinors -/
theorem zpole_spinors : gmul (1, 0) (230, 17) = (230, 17) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem zpole_norm : (230 : Nat) ^ 2 + 17 ^ 2 = 53189 := by decide

/-! ## alpha_s: lock (17, 1), alpha_s = 17/145 -/

/-- Euclid's division of the lock (17, 1): its word, ending at remainder 0 -/
theorem alpha_s_lock : euclidWord 6 17 1 = [17] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 17/145, cross-multiplied -/
theorem alpha_s_reading : 17 * (17 ^ 2 + 1 ^ 2) = 145 * (2 * 17 * 1) := by decide

/-- Euclid's division of 17/145: the row's 5 printed letters -/
theorem alpha_s_word : euclidWord 10 17 145 = [0, 8, 1, 1, 8] := by decide

/-- Brahmagupta: the lock (17, 1) is the product of its spinors -/
theorem alpha_s_spinors : gmul (gmul (gmul (1, 1) (2, 1)) (5, 2)) (0, -1) = (17, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem alpha_s_norm : (17 : Nat) ^ 2 + 1 ^ 2 = 2 * 5 * 29 := by decide

/-! ## lambda: lock (77, 5), lambda = 385/2977 -/

/-- Euclid's division of the lock (77, 5): its word, ending at remainder 0 -/
theorem lambda_lock : euclidWord 8 77 5 = [15, 2, 2] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 385/2977, cross-multiplied -/
theorem lambda_reading : 385 * (77 ^ 2 + 5 ^ 2) = 2977 * (2 * 77 * 5) := by decide

/-- Euclid's division of 385/2977: the row's 10 printed letters -/
theorem lambda_word : euclidWord 15 385 2977 = [0, 7, 1, 2, 1, 2, 1, 4, 2, 2] := by decide

/-- Brahmagupta: the lock (77, 5) is the product of its spinors -/
theorem lambda_spinors : gmul (gmul (1, 1) (3, -2)) (15, -2) = (77, 5) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem lambda_norm : (77 : Nat) ^ 2 + 5 ^ 2 = 2 * 13 * 229 := by decide

/-! ## y_e: lock (1362849, 2), y = 5451396/1857357396805 -/

/-- Euclid's division of the lock (1362849, 2): its word, ending at remainder 0 -/
theorem y_e_lock : euclidWord 7 1362849 2 = [681424, 2] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 5451396/1857357396805, cross-multiplied -/
theorem y_e_reading : 5451396 * (1362849 ^ 2 + 2 ^ 2) = 1857357396805 * (2 * 1362849 * 2) := by decide

/-- Euclid's division of 5451396/1857357396805: the row's 7 printed letters -/
theorem y_e_word : euclidWord 12 5451396 1857357396805 = [0, 340712, 3, 1, 85177, 3, 5] := by decide

/-- Brahmagupta: the lock (1362849, 2) is the product of its spinors -/
theorem y_e_spinors : gmul (gmul (gmul (gmul (gmul (gmul (1, 0) (2, 1)) (7, 2)) (17, 8)) (20, 7)) (210, 11)) (0, -1) = (1362849, 2) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_e_norm : (1362849 : Nat) ^ 2 + 2 ^ 2 = 5 * 53 * 353 * 449 * 44221 := by decide

/-! ## y_mu: lock (105459, 32), y = 6749376/11121601705 -/

/-- Euclid's division of the lock (105459, 32): its word, ending at remainder 0 -/
theorem y_mu_lock : euclidWord 10 105459 32 = [3295, 1, 1, 2, 6] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 6749376/11121601705, cross-multiplied -/
theorem y_mu_reading : 6749376 * (105459 ^ 2 + 32 ^ 2) = 11121601705 * (2 * 105459 * 32) := by decide

/-- Euclid's division of 6749376/11121601705: the row's 20 printed letters -/
theorem y_mu_word : euclidWord 25 6749376 11121601705 = [0, 1647, 1, 3, 1, 12, 1, 1, 1, 7, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2] := by decide

/-- Brahmagupta: the lock (105459, 32) is the product of its spinors -/
theorem y_mu_spinors : gmul (gmul (gmul (gmul (1, 0) (2, 1)) (4, -1)) (17, 2)) (631, -220) = (105459, 32) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_mu_norm : (105459 : Nat) ^ 2 + 32 ^ 2 = 5 * 17 * 293 * 446561 := by decide

/-! ## y_tau: lock (3723, 19), y = 70737/6930545 -/

/-- Euclid's division of the lock (3723, 19): its word, ending at remainder 0 -/
theorem y_tau_lock : euclidWord 8 3723 19 = [195, 1, 18] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 70737/6930545, cross-multiplied -/
theorem y_tau_reading : 70737 * (3723 ^ 2 + 19 ^ 2) = 6930545 * (2 * 3723 * 19) := by decide

/-- Euclid's division of 70737/6930545: the row's 10 printed letters -/
theorem y_tau_word : euclidWord 15 70737 6930545 = [0, 97, 1, 41, 12, 2, 4, 1, 2, 4] := by decide

/-- Brahmagupta: the lock (3723, 19) is the product of its spinors -/
theorem y_tau_spinors : gmul (gmul (gmul (gmul (1, 1) (2, 1)) (7, -2)) (133, 92)) (0, -1) = (3723, 19) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_tau_norm : (3723 : Nat) ^ 2 + 19 ^ 2 = 2 * 5 * 53 * 26153 := by decide

/-! ## y_u: lock (156147, 1), y = 156147/12190942805 -/

/-- Euclid's division of the lock (156147, 1): its word, ending at remainder 0 -/
theorem y_u_lock : euclidWord 6 156147 1 = [156147] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 156147/12190942805, cross-multiplied -/
theorem y_u_reading : 156147 * (156147 ^ 2 + 1 ^ 2) = 12190942805 * (2 * 156147 * 1) := by decide

/-- Euclid's division of 156147/12190942805: the row's 5 printed letters -/
theorem y_u_word : euclidWord 10 156147 12190942805 = [0, 78073, 1, 1, 78073] := by decide

/-- Brahmagupta: the lock (156147, 1) is the product of its spinors -/
theorem y_u_spinors : gmul (gmul (gmul (1, 1) (2, 1)) (46844, 15615)) (0, -1) = (156147, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_u_norm : (156147 : Nat) ^ 2 + 1 ^ 2 = 2 * 5 * 2438188561 := by decide

/-! ## y_d: lock (73000, 1), y = 146000/5329000001 -/

/-- Euclid's division of the lock (73000, 1): its word, ending at remainder 0 -/
theorem y_d_lock : euclidWord 6 73000 1 = [73000] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 146000/5329000001, cross-multiplied -/
theorem y_d_reading : 146000 * (73000 ^ 2 + 1 ^ 2) = 5329000001 * (2 * 73000 * 1) := by decide

/-- Euclid's division of 146000/5329000001: the row's 3 printed letters -/
theorem y_d_word : euclidWord 8 146000 5329000001 = [0, 36500, 146000] := by decide

/-- Brahmagupta: the lock (73000, 1) is the product of its spinors -/
theorem y_d_spinors : gmul (gmul (gmul (1, 0) (3, -2)) (19, 16)) (810, -91) = (73000, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_d_norm : (73000 : Nat) ^ 2 + 1 ^ 2 = 13 * 617 * 664381 := by decide

/-! ## y_s: lock (3721, 1), y = 3721/6922921 -/

/-- Euclid's division of the lock (3721, 1): its word, ending at remainder 0 -/
theorem y_s_lock : euclidWord 6 3721 1 = [3721] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 3721/6922921, cross-multiplied -/
theorem y_s_reading : 3721 * (3721 ^ 2 + 1 ^ 2) = 6922921 * (2 * 3721 * 1) := by decide

/-- Euclid's division of 3721/6922921: the row's 5 printed letters -/
theorem y_s_word : euclidWord 10 3721 6922921 = [0, 1860, 1, 1, 1860] := by decide

/-- Brahmagupta: the lock (3721, 1) is the product of its spinors -/
theorem y_s_spinors : gmul (1, 1) (1861, -1860) = (3721, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_s_norm : (3721 : Nat) ^ 2 + 1 ^ 2 = 2 * 6922921 := by decide

/-! ## y_c: lock (273, 1), y = 273/37265 -/

/-- Euclid's division of the lock (273, 1): its word, ending at remainder 0 -/
theorem y_c_lock : euclidWord 6 273 1 = [273] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 273/37265, cross-multiplied -/
theorem y_c_reading : 273 * (273 ^ 2 + 1 ^ 2) = 37265 * (2 * 273 * 1) := by decide

/-- Euclid's division of 273/37265: the row's 5 printed letters -/
theorem y_c_word : euclidWord 10 273 37265 = [0, 136, 1, 1, 136] := by decide

/-- Brahmagupta: the lock (273, 1) is the product of its spinors -/
theorem y_c_spinors : gmul (gmul (gmul (1, 1) (2, -1)) (5, -2)) (16, 1) = (273, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_c_norm : (273 : Nat) ^ 2 + 1 ^ 2 = 2 * 5 * 29 * 257 := by decide

/-! ## y_b: lock (333, 4), y = 2664/110905 -/

/-- Euclid's division of the lock (333, 4): its word, ending at remainder 0 -/
theorem y_b_lock : euclidWord 7 333 4 = [83, 4] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 2664/110905, cross-multiplied -/
theorem y_b_reading : 2664 * (333 ^ 2 + 4 ^ 2) = 110905 * (2 * 333 * 4) := by decide

/-- Euclid's division of 2664/110905: the row's 12 printed letters -/
theorem y_b_word : euclidWord 17 2664 110905 = [0, 41, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2] := by decide

/-- Brahmagupta: the lock (333, 4) is the product of its spinors -/
theorem y_b_spinors : gmul (gmul (gmul (gmul (1, 0) (2, 1)) (5, 4)) (21, 10)) (0, -1) = (333, 4) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_b_norm : (333 : Nat) ^ 2 + 4 ^ 2 = 5 * 41 * 541 := by decide

/-! ## y_t: lock (8, 7), y = 112/113 -/

/-- Euclid's division of the lock (8, 7): its word, ending at remainder 0 -/
theorem y_t_lock : euclidWord 7 8 7 = [1, 7] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 112/113, cross-multiplied -/
theorem y_t_reading : 112 * (8 ^ 2 + 7 ^ 2) = 113 * (2 * 8 * 7) := by decide

/-- Euclid's division of 112/113: the row's 3 printed letters -/
theorem y_t_word : euclidWord 8 112 113 = [0, 1, 112] := by decide

/-- Brahmagupta: the lock (8, 7) is the product of its spinors -/
theorem y_t_spinors : gmul (1, 0) (8, 7) = (8, 7) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem y_t_norm : (8 : Nat) ^ 2 + 7 ^ 2 = 113 := by decide

/-! ## ckm_12: lock (13, 3), sin^2 theta = 9/178 -/

/-- Euclid's division of the lock (13, 3): its word, ending at remainder 0 -/
theorem ckm_12_lock : euclidWord 7 13 3 = [4, 3] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 9/178, cross-multiplied -/
theorem ckm_12_reading : 9 * (13 ^ 2 + 3 ^ 2) = 178 * 3 ^ 2 := by decide

/-- Euclid's division of 9/178: the row's 5 printed letters -/
theorem ckm_12_word : euclidWord 10 9 178 = [0, 19, 1, 3, 2] := by decide

/-- Brahmagupta: the lock (13, 3) is the product of its spinors -/
theorem ckm_12_spinors : gmul (1, 1) (8, -5) = (13, 3) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem ckm_12_norm : (13 : Nat) ^ 2 + 3 ^ 2 = 2 * 89 := by decide

/-! ## ckm_23: lock (24, 1), sin^2 theta = 1/577 -/

/-- Euclid's division of the lock (24, 1): its word, ending at remainder 0 -/
theorem ckm_23_lock : euclidWord 6 24 1 = [24] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 1/577, cross-multiplied -/
theorem ckm_23_reading : 1 * (24 ^ 2 + 1 ^ 2) = 577 * 1 ^ 2 := by decide

/-- Euclid's division of 1/577: the row's 2 printed letters -/
theorem ckm_23_word : euclidWord 7 1 577 = [0, 577] := by decide

/-- Brahmagupta: the lock (24, 1) is the product of its spinors -/
theorem ckm_23_spinors : gmul (1, 0) (24, 1) = (24, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem ckm_23_norm : (24 : Nat) ^ 2 + 1 ^ 2 = 577 := by decide

/-! ## ckm_13: lock (266, 1), sin^2 theta = 1/70757 -/

/-- Euclid's division of the lock (266, 1): its word, ending at remainder 0 -/
theorem ckm_13_lock : euclidWord 6 266 1 = [266] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 1/70757, cross-multiplied -/
theorem ckm_13_reading : 1 * (266 ^ 2 + 1 ^ 2) = 70757 * 1 ^ 2 := by decide

/-- Euclid's division of 1/70757: the row's 2 printed letters -/
theorem ckm_13_word : euclidWord 7 1 70757 = [0, 70757] := by decide

/-- Brahmagupta: the lock (266, 1) is the product of its spinors -/
theorem ckm_13_spinors : gmul (gmul (1, 0) (13, 2)) (20, -3) = (266, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem ckm_13_norm : (266 : Nat) ^ 2 + 1 ^ 2 = 173 * 409 := by decide

/-! ## pmns_12: lock (3, 2), sin^2 theta = 4/13 -/

/-- Euclid's division of the lock (3, 2): its word, ending at remainder 0 -/
theorem pmns_12_lock : euclidWord 7 3 2 = [1, 2] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 4/13, cross-multiplied -/
theorem pmns_12_reading : 4 * (3 ^ 2 + 2 ^ 2) = 13 * 2 ^ 2 := by decide

/-- Euclid's division of 4/13: the row's 3 printed letters -/
theorem pmns_12_word : euclidWord 8 4 13 = [0, 3, 4] := by decide

/-- Brahmagupta: the lock (3, 2) is the product of its spinors -/
theorem pmns_12_spinors : gmul (1, 0) (3, 2) = (3, 2) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem pmns_12_norm : (3 : Nat) ^ 2 + 2 ^ 2 = 13 := by decide

/-! ## pmns_23: lock (10, 11), sin^2 theta = 121/221 -/

/-- Euclid's division of the lock (10, 11): its word, ending at remainder 0 -/
theorem pmns_23_lock : euclidWord 8 10 11 = [0, 1, 10] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 121/221, cross-multiplied -/
theorem pmns_23_reading : 121 * (10 ^ 2 + 11 ^ 2) = 221 * 11 ^ 2 := by decide

/-- Euclid's division of 121/221: the row's 7 printed letters -/
theorem pmns_23_word : euclidWord 12 121 221 = [0, 1, 1, 4, 1, 3, 5] := by decide

/-- Brahmagupta: the lock (10, 11) is the product of its spinors -/
theorem pmns_23_spinors : gmul (gmul (1, 0) (3, 2)) (4, 1) = (10, 11) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem pmns_23_norm : (10 : Nat) ^ 2 + 11 ^ 2 = 13 * 17 := by decide

/-! ## pmns_13: lock (20, 3), sin^2 theta = 9/409 -/

/-- Euclid's division of the lock (20, 3): its word, ending at remainder 0 -/
theorem pmns_13_lock : euclidWord 8 20 3 = [6, 1, 2] := by decide

/-- the angle's rule: n^2/(m^2 + n^2) = 9/409, cross-multiplied -/
theorem pmns_13_reading : 9 * (20 ^ 2 + 3 ^ 2) = 409 * 3 ^ 2 := by decide

/-- Euclid's division of 9/409: the row's 4 printed letters -/
theorem pmns_13_word : euclidWord 9 9 409 = [0, 45, 2, 4] := by decide

/-- Brahmagupta: the lock (20, 3) is the product of its spinors -/
theorem pmns_13_spinors : gmul (1, 0) (20, 3) = (20, 3) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem pmns_13_norm : (20 : Nat) ^ 2 + 3 ^ 2 = 409 := by decide

/-! ## dm2_ratio: lock (1, 32), x = 1/32 -/

/-- the lock (1, 32) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem dm2_ratio_word : euclidWord 7 1 32 = [0, 32] := by decide

/-! ## nu_scale: lock (7009145198050, 1), y = 14018290396100/49128116407347373723802501 -/

/-- Euclid's division of the lock (7009145198050, 1): its word, ending at remainder 0 -/
theorem nu_scale_lock : euclidWord 6 7009145198050 1 = [7009145198050] := by decide

/-- the coupling's rule: 2mn/(m^2 + n^2) = 14018290396100/49128116407347373723802501, cross-multiplied -/
theorem nu_scale_reading : 14018290396100 * (7009145198050 ^ 2 + 1 ^ 2) = 49128116407347373723802501 * (2 * 7009145198050 * 1) := by decide

/-- Euclid's division of 14018290396100/49128116407347373723802501: the row's 3 printed letters -/
theorem nu_scale_word : euclidWord 8 14018290396100 49128116407347373723802501 = [0, 3504572599025, 14018290396100] := by decide

/-- Brahmagupta: the lock (7009145198050, 1) is the product of its spinors -/
theorem nu_scale_spinors : gmul (gmul (gmul (gmul (gmul (gmul (1, 0) (3, 2)) (34, 9)) (361, 344)) (1464, 215)) (73657, -13638)) (0, -1) = (7009145198050, 1) := by decide

/-- the lock's norm as the product of its printed factors -/
theorem nu_scale_norm : (7009145198050 : Nat) ^ 2 + 1 ^ 2 = 13 * 1237 * 248657 * 2189521 * 5611348693 := by decide

/-! ## mu_e: lock (183817, 889), x = 183817/889 -/

/-- the lock (183817, 889) is the row's fraction; Euclid's division gives its 7 letters and ends at remainder 0 -/
theorem mu_e_word : euclidWord 12 183817 889 = [206, 1, 3, 3, 5, 1, 10] := by decide

/-! ## tau_e: lock (6955, 2), x = 6955/2 -/

/-- the lock (6955, 2) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem tau_e_word : euclidWord 7 6955 2 = [3477, 2] := by decide

/-! ## d_u: lock (9, 4), x = 9/4 -/

/-- the lock (9, 4) is the row's fraction; Euclid's division gives its 2 letters and ends at remainder 0 -/
theorem d_u_word : euclidWord 7 9 4 = [2, 4] := by decide

/-! ## proton: lock (8310427, 4526), x = 8310427/4526 -/

/-- the lock (8310427, 4526) is the row's fraction; Euclid's division gives its 8 letters and ends at remainder 0 -/
theorem proton_word : euclidWord 13 8310427 4526 = [1836, 6, 1, 1, 4, 1, 1, 34] := by decide

/-! ## the spinors' norms: a^2 + b^2 = p, once a factor -/

/-- the spinor (1, 1) of 2 -/
theorem spinor_2 : (1 : Nat) ^ 2 + 1 ^ 2 = 2 := by decide

/-- the spinor (2, 1) of 5 -/
theorem spinor_5 : (2 : Nat) ^ 2 + 1 ^ 2 = 5 := by decide

/-- the spinor (3, 2) of 13 -/
theorem spinor_13 : (3 : Nat) ^ 2 + 2 ^ 2 = 13 := by decide

/-- the spinor (4, 1) of 17 -/
theorem spinor_17 : (4 : Nat) ^ 2 + 1 ^ 2 = 17 := by decide

/-- the spinor (5, 2) of 29 -/
theorem spinor_29 : (5 : Nat) ^ 2 + 2 ^ 2 = 29 := by decide

/-- the spinor (5, 4) of 41 -/
theorem spinor_41 : (5 : Nat) ^ 2 + 4 ^ 2 = 41 := by decide

/-- the spinor (7, 2) of 53 -/
theorem spinor_53 : (7 : Nat) ^ 2 + 2 ^ 2 = 53 := by decide

/-- the spinor (8, 5) of 89 -/
theorem spinor_89 : (8 : Nat) ^ 2 + 5 ^ 2 = 89 := by decide

/-- the spinor (8, 7) of 113 -/
theorem spinor_113 : (8 : Nat) ^ 2 + 7 ^ 2 = 113 := by decide

/-- the spinor (13, 2) of 173 -/
theorem spinor_173 : (13 : Nat) ^ 2 + 2 ^ 2 = 173 := by decide

/-- the spinor (15, 2) of 229 -/
theorem spinor_229 : (15 : Nat) ^ 2 + 2 ^ 2 = 229 := by decide

/-- the spinor (16, 1) of 257 -/
theorem spinor_257 : (16 : Nat) ^ 2 + 1 ^ 2 = 257 := by decide

/-- the spinor (17, 2) of 293 -/
theorem spinor_293 : (17 : Nat) ^ 2 + 2 ^ 2 = 293 := by decide

/-- the spinor (17, 8) of 353 -/
theorem spinor_353 : (17 : Nat) ^ 2 + 8 ^ 2 = 353 := by decide

/-- the spinor (20, 3) of 409 -/
theorem spinor_409 : (20 : Nat) ^ 2 + 3 ^ 2 = 409 := by decide

/-- the spinor (20, 7) of 449 -/
theorem spinor_449 : (20 : Nat) ^ 2 + 7 ^ 2 = 449 := by decide

/-- the spinor (21, 10) of 541 -/
theorem spinor_541 : (21 : Nat) ^ 2 + 10 ^ 2 = 541 := by decide

/-- the spinor (24, 1) of 577 -/
theorem spinor_577 : (24 : Nat) ^ 2 + 1 ^ 2 = 577 := by decide

/-- the spinor (18, 17) of 613 -/
theorem spinor_613 : (18 : Nat) ^ 2 + 17 ^ 2 = 613 := by decide

/-- the spinor (19, 16) of 617 -/
theorem spinor_617 : (19 : Nat) ^ 2 + 16 ^ 2 = 617 := by decide

/-- the spinor (34, 9) of 1237 -/
theorem spinor_1237 : (34 : Nat) ^ 2 + 9 ^ 2 = 1237 := by decide

/-- the spinor (40, 11) of 1721 -/
theorem spinor_1721 : (40 : Nat) ^ 2 + 11 ^ 2 = 1721 := by decide

/-- the spinor (48, 13) of 2473 -/
theorem spinor_2473 : (48 : Nat) ^ 2 + 13 ^ 2 = 2473 := by decide

/-- the spinor (137, 10) of 18869 -/
theorem spinor_18869 : (137 : Nat) ^ 2 + 10 ^ 2 = 18869 := by decide

/-- the spinor (133, 92) of 26153 -/
theorem spinor_26153 : (133 : Nat) ^ 2 + 92 ^ 2 = 26153 := by decide

/-- the spinor (210, 11) of 44221 -/
theorem spinor_44221 : (210 : Nat) ^ 2 + 11 ^ 2 = 44221 := by decide

/-- the spinor (230, 17) of 53189 -/
theorem spinor_53189 : (230 : Nat) ^ 2 + 17 ^ 2 = 53189 := by decide

/-- the spinor (361, 344) of 248657 -/
theorem spinor_248657 : (361 : Nat) ^ 2 + 344 ^ 2 = 248657 := by decide

/-- the spinor (631, 220) of 446561 -/
theorem spinor_446561 : (631 : Nat) ^ 2 + 220 ^ 2 = 446561 := by decide

/-- the spinor (810, 91) of 664381 -/
theorem spinor_664381 : (810 : Nat) ^ 2 + 91 ^ 2 = 664381 := by decide

/-- the spinor (1464, 215) of 2189521 -/
theorem spinor_2189521 : (1464 : Nat) ^ 2 + 215 ^ 2 = 2189521 := by decide

/-- the spinor (1861, 1860) of 6922921 -/
theorem spinor_6922921 : (1861 : Nat) ^ 2 + 1860 ^ 2 = 6922921 := by decide

/-- the spinor (46844, 15615) of 2438188561 -/
theorem spinor_2438188561 : (46844 : Nat) ^ 2 + 15615 ^ 2 = 2438188561 := by decide

/-- the spinor (73657, 13638) of 5611348693 -/
theorem spinor_5611348693 : (73657 : Nat) ^ 2 + 13638 ^ 2 = 5611348693 := by decide

/-- the spinor (344824, 116341) of 132438819257 -/
theorem spinor_132438819257 : (344824 : Nat) ^ 2 + 116341 ^ 2 = 132438819257 := by decide

/-! ## the factors are prime -/

/-- 2 is prime -/
theorem prime_2 : Nat.Prime 2 := by norm_num

/-- 5 is prime -/
theorem prime_5 : Nat.Prime 5 := by norm_num

/-- 13 is prime -/
theorem prime_13 : Nat.Prime 13 := by norm_num

/-- 17 is prime -/
theorem prime_17 : Nat.Prime 17 := by norm_num

/-- 29 is prime -/
theorem prime_29 : Nat.Prime 29 := by norm_num

/-- 41 is prime -/
theorem prime_41 : Nat.Prime 41 := by norm_num

/-- 53 is prime -/
theorem prime_53 : Nat.Prime 53 := by norm_num

/-- 89 is prime -/
theorem prime_89 : Nat.Prime 89 := by norm_num

/-- 113 is prime -/
theorem prime_113 : Nat.Prime 113 := by norm_num

/-- 173 is prime -/
theorem prime_173 : Nat.Prime 173 := by norm_num

/-- 229 is prime -/
theorem prime_229 : Nat.Prime 229 := by norm_num

/-- 257 is prime -/
theorem prime_257 : Nat.Prime 257 := by norm_num

/-- 293 is prime -/
theorem prime_293 : Nat.Prime 293 := by norm_num

/-- 353 is prime -/
theorem prime_353 : Nat.Prime 353 := by norm_num

/-- 409 is prime -/
theorem prime_409 : Nat.Prime 409 := by norm_num

/-- 449 is prime -/
theorem prime_449 : Nat.Prime 449 := by norm_num

/-- 541 is prime -/
theorem prime_541 : Nat.Prime 541 := by norm_num

/-- 577 is prime -/
theorem prime_577 : Nat.Prime 577 := by norm_num

/-- 613 is prime -/
theorem prime_613 : Nat.Prime 613 := by norm_num

/-- 617 is prime -/
theorem prime_617 : Nat.Prime 617 := by norm_num

/-- 1237 is prime -/
theorem prime_1237 : Nat.Prime 1237 := by norm_num

/-- 1721 is prime -/
theorem prime_1721 : Nat.Prime 1721 := by norm_num

/-- 2473 is prime -/
theorem prime_2473 : Nat.Prime 2473 := by norm_num

/-- 18869 is prime -/
theorem prime_18869 : Nat.Prime 18869 := by norm_num

/-- 26153 is prime -/
theorem prime_26153 : Nat.Prime 26153 := by norm_num

/-- 44221 is prime -/
theorem prime_44221 : Nat.Prime 44221 := by norm_num

/-- 53189 is prime -/
theorem prime_53189 : Nat.Prime 53189 := by norm_num

/-- 248657 is prime -/
theorem prime_248657 : Nat.Prime 248657 := by norm_num

/-- 446561 is prime -/
theorem prime_446561 : Nat.Prime 446561 := by norm_num

/-- 664381 is prime -/
theorem prime_664381 : Nat.Prime 664381 := by norm_num

/-- 2189521 is prime -/
theorem prime_2189521 : Nat.Prime 2189521 := by norm_num

/-- 6922921 is prime -/
theorem prime_6922921 : Nat.Prime 6922921 := by norm_num

set_option maxRecDepth 1000000 in
/-- 2438188561 is prime -/
theorem prime_2438188561 : Nat.Prime 2438188561 := by norm_num

set_option maxRecDepth 1000000 in
/-- 5611348693 is prime -/
theorem prime_5611348693 : Nat.Prime 5611348693 := by norm_num

set_option maxRecDepth 1000000 in
/-- 132438819257 is prime -/
theorem prime_132438819257 : Nat.Prime 132438819257 := by norm_num

/-! ## page 1: the statements page 2 cites, each proved by its theorem there -/

open AlphaRoutes (descend)

/-- the node squared in Z[i]: (m + ni)² = (m² − n²) + 2mn·i, twice the flagpole's legs (662176464684, 4832263787), the Pythagorean triple's -/
theorem tri_square : gmul (1150813, 4199) (1150813, 4199) = (2 * 662176464684, 2 * 4832263787) := AlphaRoutes.tri_square

/-- the edge lock (1, 1): α = 1, where the tail step's discriminant (z − 2)² − 4 vanishes at z = 4/α² = 4 -/
theorem edge_lock : (2 * 1 * 1 : ℚ) / (1 ^ 2 + 1 ^ 2) = 1 ∧ ((4 : ℚ) / 1 ^ 2 - 2) ^ 2 - 4 = 0 := AlphaRoutes.edge_lock

/-- the lock (1150813, 4199) measured by Euclid's division: the 274 word, ending at the remainder 0 -/
theorem node_word : euclidWord 20 1150813 4199 = [274, 14, 1, 1, 1, 2, 2, 2, 1, 1, 2] := AlphaRoutes.node_word

/-- the coupling read downstream of the word: 1/α = (m² + n²)/(2mn) = 662194096285/4832263787, cross-multiplied -/
theorem node_inv_frac : (1150813 ^ 2 + 4199 ^ 2) * 4832263787 = 2 * 1150813 * 4199 * 662194096285 := AlphaRoutes.node_inv_frac

/-- Brahmagupta: the lock is the edge (1, 1) times the self-recoil (2, 1) times one prime spinor -/
theorem node_factors : gmul (gmul (1, 1) (2, 1)) (116341, -344824) = (1150813, 4199) := AlphaRoutes.node_factors

/-- Euclid on (P, r), stopped below √P, returns the prime spinor from its norm alone -/
theorem hermite_serret : descend 40 132438819257 17536552121 132438819257 = (344824, 116341) := AlphaRoutes.hermite_serret

/-- the self-recoil lock (2, 1): α = 4/5, and s·C(s²/4) = 1 with C = 5/4 = 1 + u·C², u = s²/4 -/
theorem recoil_lock : (2 * 2 * 1 : ℚ) / (2 ^ 2 + 1 ^ 2) = 4 / 5 ∧ (5 / 4 : ℚ) = 1 + (4 / 5) ^ 2 / 4 * (5 / 4) ^ 2 ∧ (4 / 5 : ℚ) * (5 / 4) = 1 := AlphaRoutes.recoil_lock

/-- the flagpole's legs and the numerator of 1/α: 1 − α² = (662176464684/662194096285)², so the root of (1 − t)·y² = 1 at t = α², the central binomials' equation, is 662194096285/662176464684 -/
theorem lor_pythagoras : (662194096285 : ℕ) ^ 2 = 662176464684 ^ 2 + 4832263787 ^ 2 := AlphaRoutes.lor_pythagoras

/-- the binding and the inverse of the Lorentz factor add to 1: 17631601 + 662176464684 = 662194096285, with 17631601 = 4199² -/
theorem bind_sum : 17631601 + 662176464684 = 662194096285 ∧ (4199 : ℕ) ^ 2 = 17631601 := AlphaRoutes.bind_sum

/-! ## Foldcyclopedia: the statement page 2 cites, proved by its theorem there -/

open Origami (centralDiagonal A007318 A000984) in
/-- Step 18: the diagonal T(2n, n) of the triangle A007318 is A000984, on the first 20 terms. -/
theorem step18_centralDiagonal : centralDiagonal A007318 20 = A000984.take 20 := Origami.step18_centralDiagonal

end FreeParameters

/-! ## checksum: the axioms of every theorem stated here -/

#print axioms FreeParameters.loop_rule
#print axioms FreeParameters.alpha_lock
#print axioms FreeParameters.alpha_reading
#print axioms FreeParameters.alpha_word
#print axioms FreeParameters.alpha_spinors
#print axioms FreeParameters.alpha_norm
#print axioms FreeParameters.alpha_mz_lock
#print axioms FreeParameters.alpha_mz_reading
#print axioms FreeParameters.alpha_mz_word
#print axioms FreeParameters.alpha_mz_spinors
#print axioms FreeParameters.alpha_mz_norm
#print axioms FreeParameters.alpha_mz_os_lock
#print axioms FreeParameters.alpha_mz_os_reading
#print axioms FreeParameters.alpha_mz_os_word
#print axioms FreeParameters.alpha_mz_os_spinors
#print axioms FreeParameters.alpha_mz_os_norm
#print axioms FreeParameters.sw_onshell_lock
#print axioms FreeParameters.sw_onshell_reading
#print axioms FreeParameters.sw_onshell_word
#print axioms FreeParameters.sw_onshell_spinors
#print axioms FreeParameters.sw_onshell_norm
#print axioms FreeParameters.sw_msbar_lock
#print axioms FreeParameters.sw_msbar_reading
#print axioms FreeParameters.sw_msbar_word
#print axioms FreeParameters.sw_msbar_spinors
#print axioms FreeParameters.sw_msbar_norm
#print axioms FreeParameters.zpole_lock
#print axioms FreeParameters.zpole_reading
#print axioms FreeParameters.zpole_asymmetry
#print axioms FreeParameters.zpole_word
#print axioms FreeParameters.zpole_spinors
#print axioms FreeParameters.zpole_norm
#print axioms FreeParameters.alpha_s_lock
#print axioms FreeParameters.alpha_s_reading
#print axioms FreeParameters.alpha_s_word
#print axioms FreeParameters.alpha_s_spinors
#print axioms FreeParameters.alpha_s_norm
#print axioms FreeParameters.lambda_lock
#print axioms FreeParameters.lambda_reading
#print axioms FreeParameters.lambda_word
#print axioms FreeParameters.lambda_spinors
#print axioms FreeParameters.lambda_norm
#print axioms FreeParameters.y_e_lock
#print axioms FreeParameters.y_e_reading
#print axioms FreeParameters.y_e_word
#print axioms FreeParameters.y_e_spinors
#print axioms FreeParameters.y_e_norm
#print axioms FreeParameters.y_mu_lock
#print axioms FreeParameters.y_mu_reading
#print axioms FreeParameters.y_mu_word
#print axioms FreeParameters.y_mu_spinors
#print axioms FreeParameters.y_mu_norm
#print axioms FreeParameters.y_tau_lock
#print axioms FreeParameters.y_tau_reading
#print axioms FreeParameters.y_tau_word
#print axioms FreeParameters.y_tau_spinors
#print axioms FreeParameters.y_tau_norm
#print axioms FreeParameters.y_u_lock
#print axioms FreeParameters.y_u_reading
#print axioms FreeParameters.y_u_word
#print axioms FreeParameters.y_u_spinors
#print axioms FreeParameters.y_u_norm
#print axioms FreeParameters.y_d_lock
#print axioms FreeParameters.y_d_reading
#print axioms FreeParameters.y_d_word
#print axioms FreeParameters.y_d_spinors
#print axioms FreeParameters.y_d_norm
#print axioms FreeParameters.y_s_lock
#print axioms FreeParameters.y_s_reading
#print axioms FreeParameters.y_s_word
#print axioms FreeParameters.y_s_spinors
#print axioms FreeParameters.y_s_norm
#print axioms FreeParameters.y_c_lock
#print axioms FreeParameters.y_c_reading
#print axioms FreeParameters.y_c_word
#print axioms FreeParameters.y_c_spinors
#print axioms FreeParameters.y_c_norm
#print axioms FreeParameters.y_b_lock
#print axioms FreeParameters.y_b_reading
#print axioms FreeParameters.y_b_word
#print axioms FreeParameters.y_b_spinors
#print axioms FreeParameters.y_b_norm
#print axioms FreeParameters.y_t_lock
#print axioms FreeParameters.y_t_reading
#print axioms FreeParameters.y_t_word
#print axioms FreeParameters.y_t_spinors
#print axioms FreeParameters.y_t_norm
#print axioms FreeParameters.ckm_12_lock
#print axioms FreeParameters.ckm_12_reading
#print axioms FreeParameters.ckm_12_word
#print axioms FreeParameters.ckm_12_spinors
#print axioms FreeParameters.ckm_12_norm
#print axioms FreeParameters.ckm_23_lock
#print axioms FreeParameters.ckm_23_reading
#print axioms FreeParameters.ckm_23_word
#print axioms FreeParameters.ckm_23_spinors
#print axioms FreeParameters.ckm_23_norm
#print axioms FreeParameters.ckm_13_lock
#print axioms FreeParameters.ckm_13_reading
#print axioms FreeParameters.ckm_13_word
#print axioms FreeParameters.ckm_13_spinors
#print axioms FreeParameters.ckm_13_norm
#print axioms FreeParameters.pmns_12_lock
#print axioms FreeParameters.pmns_12_reading
#print axioms FreeParameters.pmns_12_word
#print axioms FreeParameters.pmns_12_spinors
#print axioms FreeParameters.pmns_12_norm
#print axioms FreeParameters.pmns_23_lock
#print axioms FreeParameters.pmns_23_reading
#print axioms FreeParameters.pmns_23_word
#print axioms FreeParameters.pmns_23_spinors
#print axioms FreeParameters.pmns_23_norm
#print axioms FreeParameters.pmns_13_lock
#print axioms FreeParameters.pmns_13_reading
#print axioms FreeParameters.pmns_13_word
#print axioms FreeParameters.pmns_13_spinors
#print axioms FreeParameters.pmns_13_norm
#print axioms FreeParameters.dm2_ratio_word
#print axioms FreeParameters.nu_scale_lock
#print axioms FreeParameters.nu_scale_reading
#print axioms FreeParameters.nu_scale_word
#print axioms FreeParameters.nu_scale_spinors
#print axioms FreeParameters.nu_scale_norm
#print axioms FreeParameters.mu_e_word
#print axioms FreeParameters.tau_e_word
#print axioms FreeParameters.d_u_word
#print axioms FreeParameters.proton_word
#print axioms FreeParameters.spinor_2
#print axioms FreeParameters.spinor_5
#print axioms FreeParameters.spinor_13
#print axioms FreeParameters.spinor_17
#print axioms FreeParameters.spinor_29
#print axioms FreeParameters.spinor_41
#print axioms FreeParameters.spinor_53
#print axioms FreeParameters.spinor_89
#print axioms FreeParameters.spinor_113
#print axioms FreeParameters.spinor_173
#print axioms FreeParameters.spinor_229
#print axioms FreeParameters.spinor_257
#print axioms FreeParameters.spinor_293
#print axioms FreeParameters.spinor_353
#print axioms FreeParameters.spinor_409
#print axioms FreeParameters.spinor_449
#print axioms FreeParameters.spinor_541
#print axioms FreeParameters.spinor_577
#print axioms FreeParameters.spinor_613
#print axioms FreeParameters.spinor_617
#print axioms FreeParameters.spinor_1237
#print axioms FreeParameters.spinor_1721
#print axioms FreeParameters.spinor_2473
#print axioms FreeParameters.spinor_18869
#print axioms FreeParameters.spinor_26153
#print axioms FreeParameters.spinor_44221
#print axioms FreeParameters.spinor_53189
#print axioms FreeParameters.spinor_248657
#print axioms FreeParameters.spinor_446561
#print axioms FreeParameters.spinor_664381
#print axioms FreeParameters.spinor_2189521
#print axioms FreeParameters.spinor_6922921
#print axioms FreeParameters.spinor_2438188561
#print axioms FreeParameters.spinor_5611348693
#print axioms FreeParameters.spinor_132438819257
#print axioms FreeParameters.prime_2
#print axioms FreeParameters.prime_5
#print axioms FreeParameters.prime_13
#print axioms FreeParameters.prime_17
#print axioms FreeParameters.prime_29
#print axioms FreeParameters.prime_41
#print axioms FreeParameters.prime_53
#print axioms FreeParameters.prime_89
#print axioms FreeParameters.prime_113
#print axioms FreeParameters.prime_173
#print axioms FreeParameters.prime_229
#print axioms FreeParameters.prime_257
#print axioms FreeParameters.prime_293
#print axioms FreeParameters.prime_353
#print axioms FreeParameters.prime_409
#print axioms FreeParameters.prime_449
#print axioms FreeParameters.prime_541
#print axioms FreeParameters.prime_577
#print axioms FreeParameters.prime_613
#print axioms FreeParameters.prime_617
#print axioms FreeParameters.prime_1237
#print axioms FreeParameters.prime_1721
#print axioms FreeParameters.prime_2473
#print axioms FreeParameters.prime_18869
#print axioms FreeParameters.prime_26153
#print axioms FreeParameters.prime_44221
#print axioms FreeParameters.prime_53189
#print axioms FreeParameters.prime_248657
#print axioms FreeParameters.prime_446561
#print axioms FreeParameters.prime_664381
#print axioms FreeParameters.prime_2189521
#print axioms FreeParameters.prime_6922921
#print axioms FreeParameters.prime_2438188561
#print axioms FreeParameters.prime_5611348693
#print axioms FreeParameters.prime_132438819257
#print axioms FreeParameters.tri_square
#print axioms FreeParameters.edge_lock
#print axioms FreeParameters.node_word
#print axioms FreeParameters.node_inv_frac
#print axioms FreeParameters.node_factors
#print axioms FreeParameters.hermite_serret
#print axioms FreeParameters.recoil_lock
#print axioms FreeParameters.lor_pythagoras
#print axioms FreeParameters.bind_sum
#print axioms FreeParameters.step18_centralDiagonal
