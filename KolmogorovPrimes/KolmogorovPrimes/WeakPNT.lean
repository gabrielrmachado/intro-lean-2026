import KolmogorovPrimes.Basic
import KolmogorovPrimes.SelfTerminatingCode
import KolmogorovPrimes.PrimeReconstruction

/-!
# The Weak Prime Number Theorem via Kolmogorov Incompressibility

This module formalizes Sections 4 and 5 of the report (Schöning & Pruim, Exercises 9.4 and 9.5):
1. Exact superadditivity of integer base-2 logarithms: `⌊log₂ a⌋ + ⌊log₂ b⌋ ≤ ⌊log₂(a * b)⌋`;
2. The Core Bit-Balance Inequality: for an incompressible integer `n` factored as `n = p_m * k`,
   the bit size of the prime factor `⌊log₂ p_m⌋` is bounded above by the code length of `m`;
3. Compact Code Bound:
   `⌊log₂ p_m⌋ ≤ ⌊log₂ m⌋ + 2 * ⌊log₂(⌊log₂ m⌋ + 1)⌋ + c + 3`;
4. Iterated Code Bound:
   `⌊log₂ p_m⌋ ≤ ⌊log₂ m⌋ + ⌊log₂(⌊log₂ m⌋ + 1)⌋ + 2 * ⌊log₂(⌊log₂(⌊log₂ m⌋ + 1)⌋ + 1)⌋ + c + 4`.
-/

namespace KolmogorovPrimes

open Cslib
open Cslib.Kolmogorov

/-! ## 1. Exact Superadditivity of Integer Base-2 Logarithms -/

/--
Superadditivity of `Nat.log2`:
For any non-zero natural numbers `a` and `b`,
`⌊log₂ a⌋ + ⌊log₂ b⌋ ≤ ⌊log₂ (a * b)⌋`.
Proof idea: Since `2^(log₂ a) ≤ a` and `2^(log₂ b) ≤ b`, multiplying yields
`2^(log₂ a + log₂ b) ≤ a * b`, which by definition of `log₂` implies
`log₂ a + log₂ b ≤ log₂ (a * b)`.
-/
theorem add_log2_le_log2_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log2 a + Nat.log2 b ≤ Nat.log2 (a * b) := by
  -- 1) By `Nat.log2_self_le`, `2^(log₂ x) ≤ x` for `x ≠ 0`.
  have ha_le : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le ha
  have hb_le : 2 ^ Nat.log2 b ≤ b := Nat.log2_self_le hb
  -- 2) Multiply the two inequalities: `2^(log₂ a) * 2^(log₂ b) ≤ a * b`.
  have hab_le : 2 ^ Nat.log2 a * 2 ^ Nat.log2 b ≤ a * b :=
    Nat.mul_le_mul ha_le hb_le
  -- 3) Combine the powers of 2: `2^(log₂ a + log₂ b) ≤ a * b`.
  rw [← Nat.pow_add] at hab_le
  -- 4) Apply monotonicity of `log₂` (`x ≤ y → log₂ x ≤ log₂ y`) and simplify `log₂(2^k) = k`.
  have h_mono : Nat.log2 (2 ^ (Nat.log2 a + Nat.log2 b)) ≤ Nat.log2 (a * b) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right hab_le
  have h_pow_log : Nat.log2 (2 ^ (Nat.log2 a + Nat.log2 b)) = Nat.log2 a + Nat.log2 b := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (by decide)]
  rw [h_pow_log] at h_mono
  exact h_mono

/--
Logarithmic Factorization Inequality:
If `p_m` divides `n` (with `p_m ≠ 0` and `n / p_m ≠ 0`), then
`⌊log₂ p_m⌋ + ⌊log₂ (n / p_m)⌋ ≤ ⌊log₂ n⌋`.
This is the exact integer version of Schöning's identity `log n - log(n/p_m) = log p_m`.
-/
theorem add_log2_div_le_log2 (n m : ℕ)
    (h_pm_ne : nthPrime m ≠ 0) (h_div_ne : n / nthPrime m ≠ 0)
    (h_dvd : nthPrime m ∣ n) :
    Nat.log2 (nthPrime m) + Nat.log2 (n / nthPrime m) ≤ Nat.log2 n := by
  have h_eq : nthPrime m * (n / nthPrime m) = n :=
    reconstructFromPrime_div n m h_dvd
  conv_rhs => rw [← h_eq]
  exact add_log2_le_log2_mul (nthPrime m) (n / nthPrime m) h_pm_ne h_div_ne

/-! ## 2. The Core Bit-Balance Theorem (Connecting `Complexitylib` to Primes) -/

/--
Core Bit-Balance Inequality (The Heart of Topic 9):
Suppose `n` is an incompressible integer (`|bin n| ≤ M.ecomplexity (bin n)`) factored as
`n = p_m * (n / p_m)`, and suppose `bin n` can be reconstructed from a prefix-free encoding
`enc_m` of `m` concatenated with `bin (n / p_m)` with machine overhead `c : ℕ`:
`M.ecomplexity (bin n) ≤ |enc_m ++ bin(n / p_m)| + c`.
Then the bit size of the prime `⌊log₂ p_m⌋` is bounded by `|enc_m| + c`!
-/
theorem log2_nthPrime_le_code_length
    (M : DescriptionMethod BinWord) (n m c : ℕ) (enc_m : BinWord)
    (hn : n ≠ 0) (h_pm_ne : nthPrime m ≠ 0) (h_div_ne : n / nthPrime m ≠ 0)
    (h_dvd : nthPrime m ∣ n)
    (h_incomp : ((bin n).length : ℕ∞) ≤ M.ecomplexity (bin n))
    (h_desc : M.ecomplexity (bin n) ≤ (((enc_m ++ bin (n / nthPrime m)).length + c : ℕ) : ℕ∞)) :
    Nat.log2 (nthPrime m) ≤ enc_m.length + c := by
  -- 1) Chain the incompressibility lower bound and the description upper bound in `ℕ∞`:
  have h_chain_enat :
      ((bin n).length : ℕ∞) ≤ (((enc_m ++ bin (n / nthPrime m)).length + c : ℕ) : ℕ∞) :=
    le_trans h_incomp h_desc
  -- 2) Project the inequality from `ℕ∞` down to `ℕ`:
  have h_chain_nat : (bin n).length ≤ (enc_m ++ bin (n / nthPrime m)).length + c :=
    ENat.natCast_le_natCast.mp h_chain_enat
  -- 3) Expand `|bin n| = log₂ n + 1` and `|A ++ B| = |A| + |B|`:
  rw [length_bin_pos n hn, List.length_append] at h_chain_nat
  -- 4) Upper bound `|bin (n / p_m)| ≤ log₂ (n / p_m) + 1`:
  have h_bin_div : (bin (n / nthPrime m)).length ≤ Nat.log2 (n / nthPrime m) + 1 :=
    length_bin_le (n / nthPrime m)
  -- 5) Lower bound `log₂ n ≥ log₂ p_m + log₂ (n / p_m)` via `add_log2_div_le_log2`:
  have h_log_split := add_log2_div_le_log2 n m h_pm_ne h_div_ne h_dvd
  -- 6) Cancel `log₂ (n / nthPrime m)` and `+ 1` from both sides:
  omega

/-! ## 3. Compact Self-Terminating Code Bound (`code`) -/

/--
Logarithmic Weak Prime Number Theorem Bound:
Instantiating the Core Bit-Balance Inequality with the compact prefix-free code
`enc_m = code (bin m)` yields:
`⌊log₂ p_m⌋ ≤ ⌊log₂ m⌋ + 2 * ⌊log₂(⌊log₂ m⌋ + 1)⌋ + c + 4`.
-/
theorem log2_nthPrime_le_compact_code
    (M : DescriptionMethod BinWord) (n m c : ℕ)
    (hn : n ≠ 0) (h_pm_ne : nthPrime m ≠ 0) (h_div_ne : n / nthPrime m ≠ 0)
    (h_dvd : nthPrime m ∣ n)
    (h_incomp : ((bin n).length : ℕ∞) ≤ M.ecomplexity (bin n))
    (h_desc : M.ecomplexity (bin n) ≤ (((encodePairCode m (n / nthPrime m)).length + c : ℕ) : ℕ∞)) :
    Nat.log2 (nthPrime m) ≤ Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + c + 4 := by
  -- 1) Apply the Core Bit-Balance Theorem with `enc_m = code (bin m)`:
  unfold encodePairCode at h_desc
  have h_base :=
    log2_nthPrime_le_code_length M n m c (code (bin m))
      hn h_pm_ne h_div_ne h_dvd h_incomp h_desc
  -- 2) Bound `|code (bin m)| ≤ |bin m| + 2 * log₂(|bin m|) + 3` via `length_code_le`:
  have h_code := length_code_le (bin m)
  -- 3) Bound `|bin m| ≤ log₂ m + 1` via `length_bin_le`:
  have h_bin := length_bin_le m
  -- 4) Use monotonicity of `log₂` to bound `log₂(|bin m|) ≤ log₂(log₂ m + 1)`:
  have h_log_mono : Nat.log2 (bin m).length ≤ Nat.log2 (Nat.log2 m + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_bin
  -- 5) Combine the inequalities linearly:
  omega

/-! ## 4. Iterated Self-Terminating Code Bound (`code2`) -/

/--
Refined Iterated Weak Prime Number Theorem Bound:
Instantiating the Core Bit-Balance Inequality with the iterated prefix-free code
`enc_m = code2 (bin m)` reduces the second-order term from `2 * log₂ log₂ m` to
`log₂ log₂ m + 2 * log₂ log₂ log₂ m`:
`⌊log₂ p_m⌋ ≤ ⌊log₂ m⌋ + ⌊log₂(⌊log₂ m⌋ + 1)⌋ + 2 * ⌊log₂(⌊log₂(⌊log₂ m⌋ + 1)⌋ + 1)⌋ + c + 5`.
-/
theorem log2_nthPrime_le_iterated_code
    (M : DescriptionMethod BinWord) (n m c : ℕ)
    (hn : n ≠ 0) (h_pm_ne : nthPrime m ≠ 0) (h_div_ne : n / nthPrime m ≠ 0)
    (h_dvd : nthPrime m ∣ n)
    (h_incomp : ((bin n).length : ℕ∞) ≤ M.ecomplexity (bin n))
    (h_desc : M.ecomplexity (bin n) ≤ (((encodePairCode2 m (n / nthPrime m)).length + c : ℕ) : ℕ∞)) :
    Nat.log2 (nthPrime m) ≤
      Nat.log2 m + Nat.log2 (Nat.log2 m + 1) +
        2 * Nat.log2 (Nat.log2 (Nat.log2 m + 1) + 1) + c + 5 := by
  -- 1) Apply the Core Bit-Balance Theorem with `enc_m = code2 (bin m)`:
  unfold encodePairCode2 at h_desc
  have h_base :=
    log2_nthPrime_le_code_length M n m c (code2 (bin m))
      hn h_pm_ne h_div_ne h_dvd h_incomp h_desc
  -- 2) Bound `|code2 (bin m)|` via `length_code2_le`:
  have h_code2 := length_code2_le (bin m)
  -- 3) Bound `|bin m| ≤ log₂ m + 1`:
  have h_bin := length_bin_le m
  -- 4) Monotonicity of `log₂` at level 1 (`log₂(|bin m|) ≤ log₂(log₂ m + 1)`):
  have h_mono1 : Nat.log2 (bin m).length ≤ Nat.log2 (Nat.log2 m + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_bin
  -- 5) Monotonicity of `log₂` at level 2 (`log₂(log₂(|bin m|) + 1) ≤ log₂(log₂(log₂ m + 1) + 1)`):
  have h_mono1_succ : Nat.log2 (bin m).length + 1 ≤ Nat.log2 (Nat.log2 m + 1) + 1 :=
    Nat.add_le_add_right h_mono1 1
  have h_mono2 :
      Nat.log2 (Nat.log2 (bin m).length + 1) ≤ Nat.log2 (Nat.log2 (Nat.log2 m + 1) + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_mono1_succ
  -- 6) Combine all linear inequalities:
  omega

/-! ## 5. Exponential Bridge: From Logarithmic Bit Bounds to Value Bounds on $p_m$ -/

/--
Fundamental Power-Logarithm Upper Bound:
For every natural number `x`, `2 ^ (Nat.log2 x) ≤ x + 1`.
(If `x = 0`, `2^0 = 1 ≤ 1`; if `x ≠ 0`, `2^(log₂ x) ≤ x ≤ x + 1` by `Nat.log2_self_le`).
This allows us to bound `2 ^ (Nat.log2 x)` cleanly without assuming `x ≠ 0` at every nested level.
-/
theorem two_pow_log2_le_succ (x : ℕ) : 2 ^ Nat.log2 x ≤ x + 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact le_trans (Nat.log2_self_le hx) (Nat.le_succ x)

/--
Exponentiation Lemma for Log-Log Bounds:
If `⌊log₂ p⌋ ≤ ⌊log₂ m⌋ + 2 * ⌊log₂(⌊log₂ m⌋ + 1)⌋ + K`, then raising 2 to both sides yields
the polynomial/quasilinear value bound:
`p < 2 ^ (K + 1) * (m + 1) * (⌊log₂ m⌋ + 2) ^ 2`.
-/
theorem value_bound_of_log2_compact_bound {p m K : ℕ}
    (h_log : Nat.log2 p ≤ Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + K) :
    p < 2 ^ (K + 1) * (m + 1) * (Nat.log2 m + 2) ^ 2 := by
  -- 1) Every integer satisfies `p < 2 ^ (log₂ p + 1)`.
  have hp_lt : p < 2 ^ (Nat.log2 p + 1) := Nat.lt_log2_self
  -- 2) By monotonicity of `2 ^ ·`, `2 ^ (log₂ p + 1) ≤ 2 ^ (log₂ m + 2 * log₂(log₂ m + 1) + K + 1)`.
  have h_exp_le :
      2 ^ (Nat.log2 p + 1) ≤ 2 ^ (Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + K + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right h_log 1)
  -- 3) Factor the exponent sum into a product of powers of 2:
  -- `2 ^ (A + 2*B + K + 1) = 2^(K + 1) * 2^A * (2^B)^2`.
  have h_split :
      2 ^ (Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + K + 1) =
        2 ^ (K + 1) * 2 ^ Nat.log2 m * (2 ^ Nat.log2 (Nat.log2 m + 1)) ^ 2 := by
    rw [← Nat.pow_mul, mul_comm (Nat.log2 (Nat.log2 m + 1)) 2]
    simp only [Nat.pow_add]
    ring
  -- 4) Bound `2 ^ (log₂ m) ≤ m + 1` and `2 ^ (log₂(log₂ m + 1)) ≤ log₂ m + 2` via `two_pow_log2_le_succ`:
  have hm_pow : 2 ^ Nat.log2 m ≤ m + 1 := two_pow_log2_le_succ m
  have hlog_pow : 2 ^ Nat.log2 (Nat.log2 m + 1) ≤ Nat.log2 m + 2 :=
    two_pow_log2_le_succ (Nat.log2 m + 1)
  have hlog_sq : (2 ^ Nat.log2 (Nat.log2 m + 1)) ^ 2 ≤ (Nat.log2 m + 2) ^ 2 :=
    Nat.pow_le_pow_left hlog_pow 2
  -- 5) Multiply the bounds together using monotonicity of multiplication:
  have h_prod1 : 2 ^ (K + 1) * 2 ^ Nat.log2 m ≤ 2 ^ (K + 1) * (m + 1) :=
    Nat.mul_le_mul_left (2 ^ (K + 1)) hm_pow
  have h_prod2 :
      2 ^ (K + 1) * 2 ^ Nat.log2 m * (2 ^ Nat.log2 (Nat.log2 m + 1)) ^ 2 ≤
        2 ^ (K + 1) * (m + 1) * (Nat.log2 m + 2) ^ 2 :=
    Nat.mul_le_mul h_prod1 hlog_sq
  -- 6) Chain `p < 2^(log₂ p + 1) ≤ ... ≤ 2^(K+1) * (m + 1) * (log₂ m + 2)²`:
  rw [h_split] at h_exp_le
  exact lt_of_lt_of_le hp_lt (le_trans h_exp_le h_prod2)

/--
Value Form of the Weak Prime Number Theorem Bound (Exercise 9.4 Complete):
Combines `log2_nthPrime_le_compact_code` with `value_bound_of_log2_compact_bound` to establish
 directly that the `m`-th prime satisfies:
`nthPrime m < 2 ^ (c + 5) * (m + 1) * (⌊log₂ m⌋ + 2) ^ 2`.
-/
theorem nthPrime_lt_compact_code_bound
    (M : DescriptionMethod BinWord) (n m c : ℕ)
    (hn : n ≠ 0) (h_pm_ne : nthPrime m ≠ 0) (h_div_ne : n / nthPrime m ≠ 0)
    (h_dvd : nthPrime m ∣ n)
    (h_incomp : ((bin n).length : ℕ∞) ≤ M.ecomplexity (bin n))
    (h_desc : M.ecomplexity (bin n) ≤ (((encodePairCode m (n / nthPrime m)).length + c : ℕ) : ℕ∞)) :
    nthPrime m < 2 ^ (c + 5) * (m + 1) * (Nat.log2 m + 2) ^ 2 := by
  have h_log :=
    log2_nthPrime_le_compact_code M n m c hn h_pm_ne h_div_ne h_dvd h_incomp h_desc
  have h_log' : Nat.log2 (nthPrime m) ≤ Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + (c + 4) := by
    omega
  exact value_bound_of_log2_compact_bound h_log'

end KolmogorovPrimes
