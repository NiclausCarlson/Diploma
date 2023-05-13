import Std.Data.RBMap

import Diploma.Order.MonomialOrder
import Diploma.Order.AvailableOrders

open polynomial

namespace algebra

instance: HMul (Variables n ord) (Variables n ord) (Variables n ord) where
  hMul v₁ v₂ := Variables.mul v₁ v₂  

instance LexOrder: MonomialOrder (Variables n order.Lex) where
  le               := Order.lex
  lt               := Order.lex_lt
  le_refl          := lex_le_refl
  le_trans         := lex_le_trans
  le_antisymm      := lex_le_antisymm
  le_total         := lex_le_total
  lt_iff_le_not_le := lex_lt_iff_le_not_le
  add_le_add       := lex_add_le_add
  decidable_le     := Order.lex_decidable

instance GrlexOrder: MonomialOrder (Variables n order.GrLex) where
  le               := Order.grlex
  lt               := Order.grlex_lt
  le_refl          := grlex_le_refl
  le_trans         := grlex_le_trans
  le_antisymm      := grlex_le_antisymm
  le_total         := grlex_le_total
  lt_iff_le_not_le := grlex_lt_iff_le_not_le
  add_le_add       := grlex_add_le_add
  decidable_le     := Order.grlex_decidable

end algebra

namespace ordering

def m_cmp [algebra.MonomialOrder $ Variables n ord] (m₁ m₂: Monomial n ord): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if m₁.snd < m₂.snd then Ordering.gt
  else Ordering.lt

end ordering
