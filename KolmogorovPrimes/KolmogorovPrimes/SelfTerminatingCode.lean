import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import KolmogorovPrimes.Basic

/-!
# Self-Terminating Codes (Prefix-Free Encodings)

This module formalizes the hierarchy of self-terminating (prefix-free) encoding schemes
corresponding to Sections 3 and 5 of the report (Schöning & Pruim, Topic 9):
1. `bar`: Elementary bit-doubling code ($\overline{w}$) with length $2|w| + 1$;
2. `code`: Compact length-prefixed code ($\text{code}(w) = \overline{\text{bin}(|w|)}w$)
   with length $|w| + 2\lfloor\log_2 |w|\rfloor + O(1)$;
3. `code2`: Iterated length-prefixed code ($\text{code}_2(w) = \text{code}(\text{bin}(|w|))w$)
   with length $|w| + \lfloor\log_2 |w|\rfloor + 2\lfloor\log_2 \lfloor\log_2 |w|\rfloor\rfloor + O(1)$.
-/
namespace KolmogorovPrimes

/-! ## 1. Elementary Self-Terminating Code (`bar`) -/

/--
Elementary self-terminating encoding ($\overline{w}$).
For each bit `b` of the original word, we prefix the control bit `false` (0),
indicating continuation. At the end of the word, we insert the bit `true` (1)
as a stop delimiter.
-/
def bar (s : BinWord) : BinWord :=
  match s with
  | [] => [true]
  | b :: bs => false :: b :: bar bs

/--
Length lemma for `bar`:
The self-terminating code of a word `w` has exactly `2 * |w| + 1` bits.
-/
theorem length_bar (w: BinWord) : (bar w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
    simp [bar]
    simp [ih]
    simp [Nat.mul_add]

/--
Fundamental Self-Termination Theorem (Prefix-Free Property of `bar`):
If two encoded words `bar w₁` and `bar w₂`, concatenated with arbitrary
suffixes `v₁` and `v₂`, produce the same binary tape, then the original words
are identical (`w₁ = w₂`), as are the suffixes (`v₁ = v₂`).
-/
theorem bar_append_inj (w₁ w₂ v₁ v₂ : BinWord)
        (h : bar w₁ ++ v₁ = bar w₂ ++ v₂) : w₁ = w₂ ∧ v₁ = v₂ := by
  induction w₁ generalizing w₂ with
  | nil =>
    cases w₂ with
    | nil =>
      simp only [bar, List.singleton_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | cons b₂ bs₂ =>
      simp only [bar, List.cons_append, List.cons.injEq] at h
      cases h.1
  | cons b₁ bs₁ ih =>
    cases w₂ with
      | nil =>
        simp only [bar, List.cons_append, List.cons.injEq] at h
        cases h.1
      | cons b₂ bs₂ =>
        simp only [bar, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨hb, htail⟩ := h
        have ⟨hbs, hv⟩ := ih bs₂ htail
        rw [hb, hbs]
        exact ⟨rfl, hv⟩

/-! ## 2. Compact Length-Prefixed Code (`code`) -/

/--
Compact self-terminating code ($\text{code}(w) = \overline{\text{bin}(|w|)}w$):
Encodes the binary representation of the length `|w|` using `bar`, followed by `w` itself.
-/
def code (w : BinWord) : BinWord :=
  bar (bin w.length) ++ w

/--
Exact length of `code w`:
`|\text{code}(w)| = |w| + 2 * |\text{bin}(|w|)| + 1`.
-/
theorem length_code (w : BinWord) :
    (code w).length = w.length + (2 * (bin w.length).length + 1) := by
  unfold code
  rw [List.length_append, length_bar]
  omega

/--
Logarithmic upper bound on the length of `code w`:
`|\text{code}(w)| ≤ |w| + 2 * ⌊log₂ |w|⌋ + 3`.
-/
theorem length_code_le (w : BinWord) :
    (code w).length ≤ w.length + 2 * Nat.log2 w.length + 3 := by
  rw [length_code]
  have h_bin := length_bin_le w.length
  omega

/--
Prefix-free (self-terminating) property of `code`:
If `code w₁ ++ v₁ = code w₂ ++ v₂`, then `w₁ = w₂` and `v₁ = v₂`.
-/
theorem code_append_inj (w₁ w₂ v₁ v₂ : BinWord)
    (h : code w₁ ++ v₁ = code w₂ ++ v₂) : w₁ = w₂ ∧ v₁ = v₂ := by
  -- 1) Unfold `code` and reassociate list concatenation: `(A ++ B) ++ C = A ++ (B ++ C)`.
  unfold code at h
  rw [List.append_assoc, List.append_assoc] at h
  -- 2) Apply the prefix-free property of `bar` to isolate the length headers.
  have ⟨h_header, h_rest⟩ :=
    bar_append_inj (bin w₁.length) (bin w₂.length) (w₁ ++ v₁) (w₂ ++ v₂) h
  -- 3) Since `bin` is injective, equal binary headers imply equal word lengths (`|w₁| = |w₂|`).
  have h_len : w₁.length = w₂.length := bin_injective h_header
  -- 4) Words of equal length at the start of identical lists must be equal (`List.append_inj`).
  exact List.append_inj h_rest h_len

/-! ## 3. Iterated Self-Terminating Code (`code2`) -/

/--
Iterated self-terminating code ($\text{code}_2(w) = \text{code}(\text{bin}(|w|))w$):
Applies the compact `code` scheme to the binary length `bin |w|` instead of `bar`,
reducing the header overhead from $2\log_2 |w|$ to $\log_2 |w| + 2\log_2\log_2 |w|$.
-/
def code2 (w : BinWord) : BinWord :=
  code (bin w.length) ++ w

/--
Exact length of `code2 w`:
`|\text{code}_2(w)| = |w| + |\text{code}(\text{bin}(|w|))|`.
-/
theorem length_code2 (w : BinWord) :
    (code2 w).length = w.length + (code (bin w.length)).length := by
  unfold code2
  rw [List.length_append]
  omega

/--
Double-logarithmic upper bound on the length of `code2 w`:
`|\text{code}_2(w)| ≤ |w| + ⌊log₂ |w|⌋ + 2 * ⌊log₂(⌊log₂ |w|⌋ + 1)⌋ + 4`.
-/
theorem length_code2_le (w : BinWord) :
    (code2 w).length ≤
      w.length + Nat.log2 w.length + 2 * Nat.log2 (Nat.log2 w.length + 1) + 4 := by
  rw [length_code2]
  -- 1) Bound the outer `code` using `length_code_le`:
  have h_code := length_code_le (bin w.length)
  -- 2) Bound `|bin(|w|)|` using `length_bin_le`:
  have h_bin := length_bin_le w.length
  -- 3) Since `Nat.log2` is monotone (`a ≤ b → log₂ a ≤ log₂ b`), we bound `log₂(|bin(|w|)|)`:
  have h_log_mono : Nat.log2 (bin w.length).length ≤ Nat.log2 (Nat.log2 w.length + 1) :=
    by simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right h_bin
  -- 4) Combine linear inequalities via `omega`.
  omega

/--
Prefix-free (self-terminating) property of `code2`:
If `code2 w₁ ++ v₁ = code2 w₂ ++ v₂`, then `w₁ = w₂` and `v₁ = v₂`.
-/
theorem code2_append_inj (w₁ w₂ v₁ v₂ : BinWord)
    (h : code2 w₁ ++ v₁ = code2 w₂ ++ v₂) : w₁ = w₂ ∧ v₁ = v₂ := by
  -- Exact same 4-step structure as `code_append_inj`, reusing `code_append_inj` itself!
  unfold code2 at h
  rw [List.append_assoc, List.append_assoc] at h
  have ⟨h_header, h_rest⟩ :=
    code_append_inj (bin w₁.length) (bin w₂.length) (w₁ ++ v₁) (w₂ ++ v₂) h
  have h_len : w₁.length = w₂.length := bin_injective h_header
  exact List.append_inj h_rest h_len

end KolmogorovPrimes
