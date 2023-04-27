import Diploma.Polynomials.Polynomial
import Diploma.Order.MonomialOrder

open algebra polynomial

axiom t_zero_add {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a : Polynomial n ord), 0 + a = a

axiom t_add_comm {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (p₁ p₂: Polynomial n ord), p₁ + p₂ = p₂ + p₁ 

axiom t_add_assoc {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (p₁ p₂ p₃: Polynomial n ord), p₁ + p₂ + p₃ = p₁ + (p₂ + p₃) 

theorem t_add_zero [MonomialOrder $ Variables n ord]: ∀ (a : Polynomial n ord), a + 0 = a := by
  intros p
  simp [t_add_comm p, t_zero_add]

axiom t_zero_mul {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord]: ∀ (a : Polynomial n ord), 0 * a = 0
  
axiom t_mul_comm {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a b : Polynomial n ord), a * b = b * a
  
theorem t_mul_zero [MonomialOrder $ Variables n ord]: ∀ (a : Polynomial n ord), a * 0 = 0 := by
  intros p
  simp [t_mul_comm p, t_zero_mul]

axiom t_mul_assoc {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a b c : Polynomial n ord), a * b * c = a * (b * c) 

axiom t_left_distrib {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a b c : Polynomial n ord), a * (b + c) = a * b + a * c

axiom t_right_distrib {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a b c : Polynomial n ord), (a + b) * c = a * c + b * c

axiom t_one_mul {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord] : ∀ (a : Polynomial n ord), 1 * a = a 

theorem t_mul_one [MonomialOrder $ Variables n ord]: ∀ (a : Polynomial n ord), a * 1 = a := by
  intros p
  simp [t_mul_comm p, t_one_mul]

axiom t_add_left_neg {n: Nat} {ord: Type} [MonomialOrder $ Variables n ord]: ∀ (a : Polynomial n ord), a.invert_sign + a = 0

instance [MonomialOrder $ Variables n ord]: CommRing (Polynomial n ord) where
  add p₁ p₂ := Polynomial.add p₁ p₂
  zero_add := t_zero_add
  add_comm := t_add_comm
  add_assoc := t_add_assoc
  add_zero := t_add_zero
  mul := Polynomial.mul
  zero_mul := t_zero_mul
  mul_comm := t_mul_comm
  mul_zero := t_mul_zero
  mul_assoc := t_mul_assoc
  left_distrib := t_left_distrib
  right_distrib := t_right_distrib
  one_mul := t_one_mul
  mul_one := t_mul_one
  neg p := p.invert_sign
  add_left_neg := t_add_left_neg
