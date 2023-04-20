import Diploma.Order.MonomialOrder
import Diploma.Order.AvailableOrders
import Std.Data.RBMap

open polynomial


namespace algebra

instance LexOrder: MonomialOrder (Variables n order.Lex) where
  le           := Order.lex 
  le_refl      := lex_le_refl
  le_trans     := lex_le_trans
  le_antisymm  := lex_le_antisymm
  le_total     := lex_le_total
--  add_le_add   := sorry
  decidable_le := Order.lex_decidable

instance GrlexOrder: MonomialOrder (Variables n order.GrLex) where
  le           := Order.grlex 
  le_refl      := grlex_le_refl
  le_trans     := grlex_le_trans
  le_antisymm  := grlex_le_antisymm
  le_total     := grlex_le_total
--  add_le_add   := sorry
  decidable_le := Order.grlex_decidable

end algebra

namespace ordering

def m_cmp [algebra.MonomialOrder $ Variables n ord] (m₁ m₂: Monomial n ord): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if m₁.snd < m₂.snd then Ordering.gt
  else Ordering.lt

abbrev Polynomial (n: Nat) [algebra.MonomialOrder $ Variables n ord] := Std.RBSet (Monomial n ord) m_cmp

end ordering
