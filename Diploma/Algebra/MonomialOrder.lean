import Diploma.Computational
import Diploma.Polynomials.Polynomials

import Mathlib.Init.Algebra.Order

namespace algebra
open polynomials
open computational
  section orders
    instance : Ord Variable where
      compare v₁ v₂ := compare v₁.name v₂.name 

    def VariablesToStr (m: List Variable) : String :=
      match m with 
        | []    => ""
        | [v]   => v.name
        | v::vs => v.name ++ VariablesToStr vs

    instance : Ord (List Variable) where
      compare v₁ v₂ := compare (VariablesToStr v₁) (VariablesToStr v₂)

    instance : Ord (Monomial) where
      compare m₁ m₂ := compare m₁.vars m₂.vars

    private def ListLe [LE α] (l₁ l₂: List α) : Prop :=
        match l₁ with
                    | [] => match l₂ with
                                | [] => True
                                | _  => False
                    | [a₁] => match l₂ with
                                | []   => False
                                | [a₂] => a₁ ≤ a₂
                                | _    => False
                    | a₁ :: as₁ => match l₂ with
                                  | [] => False
                                  | [_] => False
                                  | a₂ :: as₂ => And (a₁ ≤ a₂) (ListLe as₁ as₂)   

    instance [LE α] : LE (List α) where
      le l₁ l₂ := ListLe l₁ l₂

    instance : LE String where
      le s₁ s₂ := s₁.data ≤ s₂.data

    instance LexLe  : LE (Monomial) where
      le m₁ m₂ := (VariablesToStr m₁.vars) ≤ (VariablesToStr m₂.vars)

    theorem lex_le_refl  (a: Monomial) : a ≤ a := sorry     

    instance LexLinearOrder  : LinearOrder (Monomial) where
      le := (·≤·)
      le_refl := sorry
      le_trans := sorry
      le_antisymm := sorry
      le_total := sorry
      decidable_le := sorry
      decidable_eq := sorry

  end orders

end algebra
