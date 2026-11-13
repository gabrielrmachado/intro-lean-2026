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

end KolmogorovPrimes
