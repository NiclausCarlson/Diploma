import Std.Data.RBMap

import Diploma.Order.MonomialOrder
import Diploma.Order.AvailableOrders

open polynomial

namespace algebra

instance: HMul (Variables n ord) (Variables n ord) (Variables n ord) where
  hMul v₁ v₂ := Variables.mul v₁ v₂  

instance LexOrder: MonomialOrder (Variables n order.Lex) where
  lt               := Order.lex
  le               := Order.lex_le
  le_refl          := lex_le_refl
  le_trans         := lex_le_trans
  le_antisymm      := lex_le_antisymm
  le_total         := lex_le_total
  lt_iff_le_not_le := lex_lt_iff_le_not_le
  add_le_add       := sorry
  decidable_le     := Order.lex_decidable

instance GrlexOrder: MonomialOrder (Variables n order.GrLex) where
  lt               := Order.grlex
  le               := Order.grlex_le 
  le_refl          := grlex_le_refl
  le_trans         := grlex_le_trans
  le_antisymm      := grlex_le_antisymm
  le_total         := grlex_le_total
  lt_iff_le_not_le := grlex_lt_iff_le_not_le
  add_le_add       := sorry
  decidable_le     := Order.grlex_decidable

end algebra

namespace ordering

def m_cmp [algebra.MonomialOrder $ Variables n ord] (m₁ m₂: Monomial n ord): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if m₁.snd < m₂.snd then Ordering.gt
  else Ordering.lt

abbrev Polynomial (n: Nat) [algebra.MonomialOrder $ Variables n ord] := Std.RBSet (Monomial n ord) m_cmp

end ordering
