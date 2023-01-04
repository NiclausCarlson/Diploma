import Diploma.Computational
import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order

namespace algebra
open polynomial
section orders
  
  private def lex_ordering_checker (l₁ l₂: List Nat) : Prop :=
    match l₁, l₂ with
      | [], []           => True
      | [n₁], [n₂]       => n₁ > n₂
      | n₁::ns₁, n₂::ns₂ => n₁ > n₂ ∨ lex_ordering_checker ns₁ ns₂
      | _, _ => False

  def lex (m₁ m₂: Monomial): Prop :=
    match m₁, m₂ with
      | Monomial.Const _, Monomial.Const _   => True
      | Monomial.Const _, Monomial.Monom _ _ => True
      | Monomial.Monom _ _, Monomial.Const _ => False
      | Monomial.Monom _ vs₁, Monomial.Monom _ vs₂ => 
        lex_ordering_checker vs₁.data vs₂.data 

  theorem lex_le_refl : ∀ (a : Monomial), lex a a := by 
    intro p
    cases p with
      | Const c => rw [lex]; simp
      | Monom _ m => rw [lex]
                     simp 
                     rw [lex_ordering_checker]
                     sorry

  theorem lex_le_trans : ∀ (a b c : Monomial), lex a b → lex b c → lex a c := by
    intros a b c
    sorry 
                                                  
  instance LexLinearOrder : LinearOrder (Monomial) where
      le m₁ m₂ := lex m₁ m₂
      le_refl := lex_le_refl
      le_trans := sorry
      le_antisymm := sorry
      le_total := sorry
      decidable_le := sorry
      decidable_eq := sorry

end orders

end algebra
