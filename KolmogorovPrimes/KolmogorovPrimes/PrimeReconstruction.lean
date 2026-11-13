import KolmogorovPrimes.Basic
import KolmogorovPrimes.SelfTerminatingCode
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime Factorization Reconstruction and Analytic Reduction

This module formalizes Section 2 (and the analytic bridge of Section 4) of the report:
1. Enumeration of prime numbers (`nthPrime`) and the prime-counting function (`pi`)
   via `Mathlib.NumberTheory.PrimeCounting`;
2. Algorithmic reconstruction of an integer `n` from the index `m` of a prime factor
   `p_m` and the quotient `k = n / p_m` (Schöning & Pruim, Exercise 9.3);
3. Prefix-free binary encoding of the pair `(m, k)` using `bar`, `code`, and `code2`,
   along with injectivity proofs;
4. Analytic reduction showing how an upper bound on the `m`-th prime (`p_m`) yields
   a lower bound on the prime-counting function `π(p_m)` (Schöning & Pruim, Exercise 9.2).
-/

namespace KolmogorovPrimes

/-! ## 1. Prime Enumeration and Reconstruction (Section 2) -/

/--
The `m`-th prime number (0-indexed, following `Mathlib` convention:
`nthPrime 0 = 2`, `nthPrime 1 = 3`, `nthPrime 2 = 5`, ...).
-/
noncomputable def nthPrime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime m

/--
Given the index `m` of a prime factor and the quotient `k = n / p_m`,
reconstructs `n` by multiplying `nthPrime m * k`.
-/
noncomputable def reconstructFromPrime (m k : ℕ) : ℕ :=
  nthPrime m * k

/--
Fundamental Reconstruction Lemma:
If the `m`-th prime `nthPrime m` divides `n`, then reconstructing from `m`
and the quotient `n / nthPrime m` recovers `n` exactly.
-/
theorem reconstructFromPrime_div (n m : ℕ) (h_dvd : nthPrime m ∣ n) :
    reconstructFromPrime m (n / nthPrime m) = n := by
  unfold reconstructFromPrime
  -- Direct application of exact division multiplication in `Mathlib`: `a ∣ b → a * (b / a) = b`.
  exact Nat.mul_div_cancel' h_dvd

/-! ## 2. Prefix-Free Pair Encodings for `(m, k)` -/

/--
Elementary pair encoding: $\overline{\text{bin}(m)}\text{bin}(k)$.
Concatenates the bit-doubled code of `m` with the raw binary representation of `k`.
-/
def encodePairBar (m k : ℕ) : BinWord :=
  bar (bin m) ++ bin k

/--
Compact pair encoding: $\text{code}(\text{bin}(m))\text{bin}(k)$.
Concatenates the length-prefixed code of `m` with the raw binary representation of `k`.
-/
def encodePairCode (m k : ℕ) : BinWord :=
  code (bin m) ++ bin k

/--
Iterated pair encoding: $\text{code}_2(\text{bin}(m))\text{bin}(k)$.
Concatenates the iterated length-prefixed code of `m` with the raw binary of `k`.
-/
def encodePairCode2 (m k : ℕ) : BinWord :=
  code2 (bin m) ++ bin k

/--
Unambiguous decoding (injectivity) of `encodePairBar`:
If two pairs `(m₁, k₁)` and `(m₂, k₂)` produce the same binary tape under `encodePairBar`,
then `m₁ = m₂` and `k₁ = k₂`.
-/
theorem encodePairBar_inj {m₁ k₁ m₂ k₂ : ℕ}
    (h : encodePairBar m₁ k₁ = encodePairBar m₂ k₂) : m₁ = m₂ ∧ k₁ = k₂ := by
  unfold encodePairBar at h
  -- 1) Use `bar_append_inj` to split the tape into `bin m₁ = bin m₂` and `bin k₁ = bin k₂`.
  have ⟨hm_bin, hk_bin⟩ := bar_append_inj (bin m₁) (bin m₂) (bin k₁) (bin k₂) h
  -- 2) Apply injectivity of `bin` to both components.
  exact ⟨bin_injective hm_bin, bin_injective hk_bin⟩

/--
Unambiguous decoding (injectivity) of `encodePairCode`:
If `encodePairCode m₁ k₁ = encodePairCode m₂ k₂`, then `m₁ = m₂` and `k₁ = k₂`.
-/
theorem encodePairCode_inj {m₁ k₁ m₂ k₂ : ℕ}
    (h : encodePairCode m₁ k₁ = encodePairCode m₂ k₂) : m₁ = m₂ ∧ k₁ = k₂ := by
  unfold encodePairCode at h
  have ⟨hm_bin, hk_bin⟩ := code_append_inj (bin m₁) (bin m₂) (bin k₁) (bin k₂) h
  exact ⟨bin_injective hm_bin, bin_injective hk_bin⟩

/--
Unambiguous decoding (injectivity) of `encodePairCode2`:
If `encodePairCode2 m₁ k₁ = encodePairCode2 m₂ k₂`, then `m₁ = m₂` and `k₁ = k₂`.
-/
theorem encodePairCode2_inj {m₁ k₁ m₂ k₂ : ℕ}
    (h : encodePairCode2 m₁ k₁ = encodePairCode2 m₂ k₂) : m₁ = m₂ ∧ k₁ = k₂ := by
  unfold encodePairCode2 at h
  have ⟨hm_bin, hk_bin⟩ := code2_append_inj (bin m₁) (bin m₂) (bin k₁) (bin k₂) h
  exact ⟨bin_injective hm_bin, bin_injective hk_bin⟩

/-! ## 3. Length Bounds for Pair Encodings -/

/--
Upper bound on the bit length of the compact pair encoding `encodePairCode m k`:
`|\text{encodePairCode}(m, k)| ≤ ⌊log₂ m⌋ + 2 * ⌊log₂(⌊log₂ m⌋ + 1)⌋ + ⌊log₂ k⌋ + 5`.
-/
theorem length_encodePairCode_le (m k : ℕ) :
    (encodePairCode m k).length ≤
      Nat.log2 m + 2 * Nat.log2 (Nat.log2 m + 1) + Nat.log2 k + 5 := by
  unfold encodePairCode
  rw [List.length_append]
  have h_code := length_code_le (bin m)
  have h_bin_m := length_bin_le m
  have h_bin_k := length_bin_le k
  have h_log_mono : Nat.log2 (bin m).length ≤ Nat.log2 (Nat.log2 m + 1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_bin_m
  omega

/-! ## 4. Analytic Reduction: From $p_m$ Upper Bound to $\pi(n)$ Lower Bound -/

/--
Number of primes strictly less than `nthPrime m`:
By `Mathlib`'s `Nat.count_nth_of_infinite`, since there are infinitely many primes
(`Nat.infinite_setOf_prime`), there are exactly `m` primes strictly below `nthPrime m`.
-/
theorem count_primes_lt_nthPrime (m : ℕ) :
    Nat.count Nat.Prime (nthPrime m) = m := by
  unfold nthPrime
  exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime m

/--
Analytic Inversion Lemma:
If the `m`-th prime satisfies `nthPrime m ≤ m * (Nat.log2 m) ^ 2`, then the number
of primes strictly below `nthPrime m` (which is `m`) satisfies the cross-multiplied
lower bound: `nthPrime m ≤ Nat.count Nat.Prime (nthPrime m) * (Nat.log2 (nthPrime m)) ^ 2`.
(Note: We state the bound in multiplicative form `N ≤ π(N) * log₂(N)²` to avoid
truncating integer division `/` in `ℕ`).
-/
theorem analytic_reduction_prime_bound (m : ℕ)
    (h_pm : nthPrime m ≤ m * (Nat.log2 m) ^ 2) :
    nthPrime m ≤ Nat.count Nat.Prime (nthPrime m) * (Nat.log2 (nthPrime m)) ^ 2 := by
  -- 1) Replace `Nat.count Nat.Prime (nthPrime m)` with `m`.
  rw [count_primes_lt_nthPrime m]
  -- 2) `nthPrime` is strictly monotone, hence `m ≤ nthPrime m` (`StrictMono.id_le`).
  have h_id_le : m ≤ nthPrime m :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le m
  -- 3) By monotonicity of `Nat.log2`, `log₂ m ≤ log₂ (nthPrime m)`.
  have h_log : Nat.log2 m ≤ Nat.log2 (nthPrime m) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_id_le
  -- 4) Since squaring and multiplication are monotone on `ℕ`, `m * (log₂ m)² ≤ m * (log₂ p_m)²`.
  have h_pow : (Nat.log2 m) ^ 2 ≤ (Nat.log2 (nthPrime m)) ^ 2 :=
    Nat.pow_le_pow_left h_log 2
  have h_mul : m * (Nat.log2 m) ^ 2 ≤ m * (Nat.log2 (nthPrime m)) ^ 2 :=
    Nat.mul_le_mul_left m h_pow
  -- 5) Chain `nthPrime m ≤ m * (log₂ m)²` and `m * (log₂ m)² ≤ m * (log₂ p_m)²` by transitivity.
  exact le_trans h_pm h_mul

end KolmogorovPrimes
