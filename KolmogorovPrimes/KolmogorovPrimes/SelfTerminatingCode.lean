import Mathlib.Data.List.Basic

/-!
# Self-Terminating Codes

This module formalizes the elementary prefix-free coding scheme (`bar`),
corresponding to the first construction in Section 3 of the technical report.
We use the `BitString` type (`List Bool`) provided by the `CSLib` library.
-/

namespace KolmogorovPrimes

/-- Binary string of arbitrary length (`{0,1}*`). -/
abbrev BinWord := List Bool

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

end KolmogorovPrimes
