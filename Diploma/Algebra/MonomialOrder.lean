import Diploma.Computational
import Diploma.Polynomials.Polynomials

namespace algebra
open polynomials
open computational

  class LinearOrder (α: Type) [ToString α] [Inhabited α] [Computational α] :=
    leq       : Polynomial α → Polynomial α → Prop
    refl      : (∀ p     : Polynomial α, leq p p)
    anty_symm : (∀ p q   : Polynomial α, leq p q → ((leq q p) = False))
    trans     : (∀ m p q : Polynomial α, (leq m p) ∧ (leq p q) → (leq m q))
    linear    : (∀ p q   : Polynomial α, (leq p q) ∨ (leq q p) = True)

  class MonomialOrder (α: Type) [ToString α] [Inhabited α] [Computational α] :=
    sorry

end algebra
