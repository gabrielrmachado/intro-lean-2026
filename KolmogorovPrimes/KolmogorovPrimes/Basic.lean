import CslibFrontier.Computability.Kolmogorov.Basic
import CslibFrontier.Computability.Kolmogorov.Incompressibility
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Foundations: Binary Representation and Connection to Complexitylib

This module establishes the connection (Sections 1 and 2 of the report) between:
1. The arithmetic structure of the natural numbers (`ℕ`) in `Mathlib`;
2. Binary strings (`List Bool`) and Kolmogorov complexity (`ecomplexity`)
  from the `Complexitylib` library (`Cslib.Kolmogorov`).
-/
namespace KolmogorovPrimes

open Cslib
open Cslib.Kolmogorov

/-- Alias for binary words of arbitrary length `{0,1}*`. -/
abbrev BinWord := List Bool

/-! ## 1. Canonical Binary Representation (via `Mathlib`) -/

/--
Binary representation of a natural number `n : ℕ`.
We reuse `Nat.bits` from `Mathlib`, which produces the canonical list of bits
(from least to most significant, with no redundant bits).
-/
def bin (n : ℕ) : BinWord :=
  Nat.bits n

/--
Decoder for binary lists (`BinWord → ℕ`):
Reconstructs the natural number from a `List Bool` (from least to most significant
bit) using the rule `Nat.bit b k = 2 * k + b`.
We define `decodeBin` explicitly because `Nat.ofBits` in `Cslib` operates on
`Fin k → Bool` rather than `List Bool`.
-/
def decodeBin : BinWord → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (decodeBin bs)

/--
Left inverse lemma:
Applying `decodeBin` to the binary representation `bin n` recovers exactly `n`.
-/
theorem decodeBin_bin (n : ℕ) : decodeBin (bin n) = n := by
  unfold bin
  -- `Nat.binaryRec'` already excludes the degenerate case `Nat.bit false 0 = 0`,
  -- providing the hypothesis `k = 0 → b = true` required by `Nat.bits_append_bit`.
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit k b h, decodeBin, ih]

/--
Injectivity of `bin`:
Two natural numbers have the same binary representation if and only if they
are equal. This ensures that `bin` is a lossless encoding.
-/
theorem bin_injective : Function.Injective bin :=
  Function.LeftInverse.injective decodeBin_bin

/-! ## 2. Logarithmic Length of `bin` -/

/--
Length of `bin 0`: the empty list `[]` has length `0`.
-/
@[simp]
theorem length_bin_zero : (bin 0).length = 0 :=
  rfl

/--
Binary Length Theorem (footnote 1 of Schöning & Pruim):
For every positive integer `n > 0`, the number of bits in `bin n` is
`⌊log₂ n⌋ + 1`.
-/
theorem length_bin_pos (n : ℕ) (hn : n ≠ 0) :
    (bin n).length = Nat.log2 n + 1 := by
  -- `|bin n| = Nat.size n`, and `Nat.size n` is the unique `s` such that `2^(s-1) ≤ n < 2^s`.
  rw [bin, Nat.size_eq_bits_len]
  exact le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
    (Nat.lt_size.mpr (Nat.log2_self_le hn))

/--
General upper bound on the length of `bin n` (valid for every `n : ℕ`):
`|bin(n)| ≤ ⌊log₂ n⌋ + 1`.
-/
theorem length_bin_le (n : ℕ) : (bin n).length ≤ Nat.log2 n + 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (length_bin_pos n hn).le

/-! ## 3. Integration with `Complexitylib` (Incompressibility) -/

/--
Existence of Incompressible Binary Words (via `Complexitylib`):
For any description method `M` and any length `m : ℕ`, there exists a word `w`
of length `m` such that `M.ecomplexity w ≥ m`.
-/
theorem exists_incompressible_word (M : DescriptionMethod BinWord) (m : ℕ) :
    ∃ w : BinWord, w.length = m ∧ (m : ℕ∞) ≤ M.ecomplexity w :=
  M.exists_length_eq_le_ecomplexity m

end KolmogorovPrimes
