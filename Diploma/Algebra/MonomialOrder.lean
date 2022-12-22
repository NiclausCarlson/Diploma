import Std.Data.RBTree

import Diploma.Computational
import Diploma.Polynomials.Polynomials

namespace algebra
open polynomials
open computational
  namespace orders
    instance : Ord Variable where
      compare v₁ v₂ := compare v₁.name v₂.name 

    private def VariablesToStr (m: List Variable) : String :=
      match m with 
        | []    => ""
        | [v]   => v.name
        | v::vs => v.name ++ VariablesToStr vs

    instance : Ord (List Variable) where
      compare v₁ v₂ := compare (VariablesToStr v₁) (VariablesToStr v₂)

    instance [ToString α] [Inhabited α] [Computational α]: Ord (Monomial α) where
      compare m₁ m₂ := compare m₁.vars m₂.vars

    

    def lex [ToString α] [Inhabited α] [Computational α] (p q: Monomial α): Prop :=
      sorry

    def lex_ordering [ToString α] [Inhabited α] [Computational α] (l: List (Monomial α)): List (Monomial α) :=
      sorry 

    def p_lex_ordering [ToString α] [Inhabited α] [Computational α] (p: Polynomial α): Polynomial α :=
      sorry 

  end orders

  class LinearOrder [ToString α] [Inhabited α] [Computational α] (φ : Monomial α → Monomial α → Prop)  :=
    refl      : (∀ p     : Monomial α, φ p p)
    anty_symm : (∀ p q   : Monomial α, φ p q → ((φ q p) = False))
    trans     : (∀ m p q : Monomial α, (φ m p) ∧ (φ p q) → (φ m q))
    linear    : (∀ p q   : Monomial α, (φ p q) ∨ (φ q p) = True)

end algebra
