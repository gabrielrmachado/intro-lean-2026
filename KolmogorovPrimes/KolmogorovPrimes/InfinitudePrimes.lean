import KolmogorovPrimes.Basic
import KolmogorovPrimes.SelfTerminatingCode

/-!
# Infinitude of Primes via Exponent Tuple Compression

This module formalizes Section 1 of the report:
1. Arithmetic bound on prime factorization exponents: if $p^e \mid n$ with $p \ge 2$ and $n > 0$,
   then $e \le \lfloor\log_2 n\rfloor$, so `bin e` uses at most $\lfloor\log_2(\lfloor\log_2 n\rfloor)\rfloor + 1$ bits;
2. Prefix-free encoding of a tuple/list of $k$ exponents `(e₁, ..., eₖ)` by concatenating
   `bar (bin eᵢ)`, along with a mechanical proof of unique decodability (injectivity);
3. Upper bound on the total bit length of the encoded exponent tuple:
   $|\text{encodeExponents}(e_1, \dots, e_k)| \le k \cdot (2 \lfloor\log_2(\lfloor\log_2 n\rfloor)\rfloor + 3)$;
4. The Kolmogorov Contradiction Theorem for Finite Primes (Exercise 9.1):
   if `bin n` is incompressible and described by $k$ prime exponents bounded by $\lfloor\log_2 n\rfloor$,
   then $\lfloor\log_2 n\rfloor + 1 \le k \cdot (2 \lfloor\log_2(\lfloor\log_2 n\rfloor)\rfloor + 3) + c$,
   which is violated as soon as $\lfloor\log_2 n\rfloor$ grows large relative to $k$.
-/

namespace KolmogorovPrimes

open Cslib
open Cslib.Kolmogorov

/-! ## 1. Exponent Bound in Prime Factorizations ($e \le \lfloor\log_2 n\rfloor$) -/

/--
Exponent Bound Lemma:
If a prime (or any integer `p ≥ 2`) raised to the power `e` divides a non-zero integer `n`,
then the exponent satisfies `e ≤ ⌊log₂ n⌋`.
Proof idea: `2^e ≤ p^e ≤ n`, and taking `⌊log₂ ·⌋` on both sides yields `e ≤ ⌊log₂ n⌋`.
-/
theorem exponent_le_log2_of_pow_dvd {n p e : ℕ} (hn : n ≠ 0) (hp : 2 ≤ p) (h_dvd : p ^ e ∣ n) :
    e ≤ Nat.log2 n := by
  -- 1) Since `p^e ∣ n` and `n > 0`, we have `p^e ≤ n`.
  have h_pe_le_n : p ^ e ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h_dvd
  -- 2) Since `2 ≤ p`, monotonicity of exponentiation gives `2^e ≤ p^e`.
  have h_2e_le_pe : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp e
  -- 3) By transitivity, `2^e ≤ n`.
  have h_2e_le_n : 2 ^ e ≤ n := le_trans h_2e_le_pe h_pe_le_n
  -- 4) Apply monotonicity of `log₂` and simplify `log₂(2^e) = e`.
  have h_mono : Nat.log2 (2 ^ e) ≤ Nat.log2 n := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_2e_le_n
  have h_pow_log : Nat.log2 (2 ^ e) = e := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (by decide)]
  rw [h_pow_log] at h_mono
  exact h_mono

/--
Bit-length bound for a single encoded exponent `bar (bin e)`:
If `e ≤ ⌊log₂ n⌋`, then the self-terminating encoding `bar (bin e)` uses at most
`2 * ⌊log₂(⌊log₂ n⌋)⌋ + 3` bits.
-/
theorem length_bar_bin_exponent_le {n e : ℕ} (he : e ≤ Nat.log2 n) :
    (bar (bin e)).length ≤ 2 * Nat.log2 (Nat.log2 n) + 3 := by
  -- 1) By `length_bar`, `|bar (bin e)| = 2 * |bin e| + 1`.
  rw [length_bar]
  -- 2) By `length_bin_le`, `|bin e| ≤ log₂ e + 1`.
  have h_bin : (bin e).length ≤ Nat.log2 e + 1 := length_bin_le e
  -- 3) By monotonicity of `log₂`, `e ≤ log₂ n` implies `log₂ e ≤ log₂ (log₂ n)`.
  have h_log_mono : Nat.log2 e ≤ Nat.log2 (Nat.log2 n) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right he
  -- 4) Combine linear inequalities: `2 * (log₂(log₂ n) + 1) + 1 = 2 * log₂(log₂ n) + 3`.
  omega

/-! ## 2. Prefix-Free Encoding of Exponent Tuples (`encodeExponents`) -/

/--
Encodes a list of $k$ exponents `[e₁, e₂, ..., eₖ]` into a single binary tape by
concatenating the self-terminating codes `bar (bin eᵢ)` for each exponent.
-/
def encodeExponents : List ℕ → BinWord
  | [] => []
  | e :: es => bar (bin e) ++ encodeExponents es

/--
Unambiguous Decoding (Injectivity) of `encodeExponents` for fixed $k$:
If two exponent lists `es₁` and `es₂` of the same length $k$ produce the same binary tape,
then every exponent is identical (`es₁ = es₂`).
-/
theorem encodeExponents_inj_of_length_eq {es₁ es₂ : List ℕ}
    (h_len : es₁.length = es₂.length)
    (h_enc : encodeExponents es₁ = encodeExponents es₂) : es₁ = es₂ := by
  induction es₁ generalizing es₂ with
  | nil =>
    -- If `es₁ = []`, then `es₂.length = 0`, so `es₂ = []`.
    cases es₂ with
    | nil => rfl
    | cons e₂ tail₂ => contradiction
  | cons e₁ tail₁ ih =>
    cases es₂ with
    | nil => contradiction
    | cons e₂ tail₂ =>
      -- Both lists are non-empty: `e₁ :: tail₁` and `e₂ :: tail₂`.
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      simp only [encodeExponents] at h_enc
      -- Apply the prefix-free property `bar_append_inj` to peel off the first exponent!
      have ⟨h_bin_e, h_rest⟩ :=
        bar_append_inj (bin e₁) (bin e₂) (encodeExponents tail₁) (encodeExponents tail₂) h_enc
      -- Since `bin` is injective, `e₁ = e₂`.
      have he : e₁ = e₂ := bin_injective h_bin_e
      -- By the induction hypothesis on the remaining exponents, `tail₁ = tail₂`.
      have htail : tail₁ = tail₂ := ih h_len h_rest
      rw [he, htail]

/-! ## 3. Length Bound for the Encoded Exponent Tuple -/

/--
Total bit length of `encodeExponents es`:
If a list `es` has $k$ exponents (`es.length = k`) and every exponent $e \in es$ satisfies
$e \le \lfloor\log_2 n\rfloor$, then the total encoded length is at most
`es.length * (2 * ⌊log₂(⌊log₂ n⌋)⌋ + 3)`.
-/
theorem length_encodeExponents_le (n : ℕ) (es : List ℕ)
    (h_bounds : ∀ e ∈ es, e ≤ Nat.log2 n) :
    (encodeExponents es).length ≤ es.length * (2 * Nat.log2 (Nat.log2 n) + 3) := by
  induction es with
  | nil =>
    -- Base case: empty list `[]` has encoded length 0.
    simp [encodeExponents]
  | cons e tail ih =>
    -- Inductive step: `encodeExponents (e :: tail) = bar (bin e) ++ encodeExponents tail`.
    simp only [encodeExponents, List.length_append, List.length_cons]
    -- 1) Bound the head exponent `e` using `length_bar_bin_exponent_le`:
    have he_le : e ≤ Nat.log2 n := h_bounds e List.mem_cons_self
    have h_head := length_bar_bin_exponent_le he_le
    -- 2) Bound the tail exponents using the Induction Hypothesis `ih`:
    have h_tail_bounds : ∀ x ∈ tail, x ≤ Nat.log2 n :=
      fun x hx => h_bounds x (List.mem_cons_of_mem e hx)
    have h_tail := ih h_tail_bounds
    -- 3) Distributive arithmetic: `|head| + |tail| ≤ B + tail.length * B = (tail.length + 1) * B`.
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-! ## 4. Kolmogorov Upper Bound and Contradiction for Finite Primes -/

/--
Kolmogorov Complexity Upper Bound under Finite Prime Factorization:
If `bin n` is reconstructed from a list `es` of $k$ prime exponents (each $\le \lfloor\log_2 n\rfloor$)
with machine overhead `c`, then:
`M.ecomplexity (bin n) ≤ k * (2 * ⌊log₂(⌊log₂ n⌋)⌋ + 3) + c`.
-/
theorem ecomplexity_le_of_exponent_tuple
    (M : DescriptionMethod BinWord) (n c : ℕ) (es : List ℕ)
    (h_bounds : ∀ e ∈ es, e ≤ Nat.log2 n)
    (h_desc : M.ecomplexity (bin n) ≤ (((encodeExponents es).length + c : ℕ) : ℕ∞)) :
    M.ecomplexity (bin n) ≤ ((es.length * (2 * Nat.log2 (Nat.log2 n) + 3) + c : ℕ) : ℕ∞) := by
  have h_len := length_encodeExponents_le n es h_bounds
  have h_len_c : (encodeExponents es).length + c ≤ es.length * (2 * Nat.log2 (Nat.log2 n) + 3) + c :=
    Nat.add_le_add_right h_len c
  exact le_trans h_desc (ENat.natCast_le_natCast.mpr h_len_c)

/--
Contradiction with Incompressibility:
No non-zero integer `n` can simultaneously:
1. Be Kolmogorov-incompressible (`|bin n| ≤ M.ecomplexity (bin n)`),
2. Be described by $k$ exponents bounded by $\lfloor\log_2 n\rfloor$ with overhead `c`, and
3. Satisfy the asymptotic growth condition `k * (2 * ⌊log₂(⌊log₂ n⌋)⌋ + 3) + c < ⌊log₂ n⌋ + 1`.
This completes the Kolmogorov proof that there cannot be only finitely many ($k$) primes.
-/
theorem false_of_finite_prime_exponents
    (M : DescriptionMethod BinWord) (n c : ℕ) (es : List ℕ)
    (hn : n ≠ 0)
    (h_bounds : ∀ e ∈ es, e ≤ Nat.log2 n)
    (h_incomp : ((bin n).length : ℕ∞) ≤ M.ecomplexity (bin n))
    (h_desc : M.ecomplexity (bin n) ≤ (((encodeExponents es).length + c : ℕ) : ℕ∞))
    (h_large : es.length * (2 * Nat.log2 (Nat.log2 n) + 3) + c < Nat.log2 n + 1) :
    False := by
  -- 1) Combine `h_incomp` and the upper bound from `ecomplexity_le_of_exponent_tuple`:
  have h_upper := ecomplexity_le_of_exponent_tuple M n c es h_bounds h_desc
  have h_chain_enat := le_trans h_incomp h_upper
  -- 2) Project from `ℕ∞` to `ℕ` and expand `|bin n| = log₂ n + 1`:
  have h_chain_nat : (bin n).length ≤ es.length * (2 * Nat.log2 (Nat.log2 n) + 3) + c :=
    ENat.natCast_le_natCast.mp h_chain_enat
  rw [length_bin_pos n hn] at h_chain_nat
  -- 3) `h_chain_nat` states `log₂ n + 1 ≤ k * (...) + c`, directly contradicting `h_large`!
  omega

end KolmogorovPrimes
