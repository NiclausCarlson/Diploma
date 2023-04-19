import Diploma.Algebra.MonomialOrder
import Std.Data.RBMap

open polynomial


namespace algebra

class Lex (α : Type u) extends MonomialOrder α

instance LexOrder: Lex (Variables n) where
  le           := Order.lex 
  le_refl      := lex_le_refl
  le_trans     := lex_le_trans
  le_antisymm  := lex_le_antisymm
  le_total     := lex_le_total
--  add_le_add   := sorry
  decidable_le := Order.lex_decidable

class GrLex (α : Type u) extends MonomialOrder α

--instance GrlexOrder: GrLex (Variables n) where
--  le           := Order.grlex 
--  le_refl      := grlex_le_refl
--  le_trans     := grlex_le_trans
--  le_antisymm  := grlex_le_antisymm
--  le_total     := grlex_le_total
----  add_le_add   := sorry
--  decidable_le := Order.grlex_decidable
--
end algebra

namespace ordering

def m_cmp [algebra.MonomialOrder $ Variables n] (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if m₁.snd < m₂.snd then Ordering.gt
  else Ordering.lt

abbrev Polynomial (n: Nat) [algebra.MonomialOrder $ Variables n] := Std.RBSet (Monomial n) m_cmp

def p (m: Monomial n) [algebra.Lex $ Variables n]: Polynomial n := Std.RBSet.single m

end ordering
