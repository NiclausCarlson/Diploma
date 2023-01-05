import Diploma.Polynomials.Polynomial
import Mathlib.Algebra.Ring.Defs 
import Std.Data.RBMap


namespace algebra
open polynomial

def Polynomial.add (p₁ p₂ : Polynomial) : Polynomial :=
  match p₁, p₂ with
    | Polynomial.Monom m₁, Polynomial.Monom m₂ => match m₁, m₂ with
        | Monomial.Const c₁, Monomial.Const c₂ => Polynomial.Monom (Monomial.Const (c₁ + c₂))
        | smth, Monomial.Const _ => Polynomial.Monom smth
        | Monomial.Const _, smth => Polynomial.Monom smth
        | smth₁, smth₂ => Polynomial.Add (Polynomial.Monom smth₁) (Polynomial.Monom smth₂)
    | Polynomial.Monom m , smth => if is_zero m then smth else Polynomial.Add (Polynomial.Monom m) smth
    | smth , Polynomial.Monom m => if is_zero m then smth else Polynomial.Add smth (Polynomial.Monom m)
    | smth₁, smth₂ => Polynomial.Add smth₁ smth₂
  where 
    is_zero (m: Monomial) : Bool := 
      match m with 
        | Monomial.Const c => c == 0
        | _ => false

instance : Add Polynomial := ⟨Polynomial.add⟩   

theorem t_zero_add : ∀ (a : Polynomial), 0 + a = a := by
  intro p
  cases p with
    | Monom m => cases m with
                   | Const c => simp [Polynomial.add]; sorry
                   | Monom _ => rfl
    | Add _ _ => rfl
    | Mult _ _ => rfl 

theorem t_add_zero : ∀ (a: Polynomial), a + 0 = a := by
  intro p
  cases p with
    | Monom m => cases m with
                  | Const c => simp [Polynomial.add]; sorry
                  | Monom _ => rfl
    | Add _ _ => rfl
    | Mult _ _ => rfl

def Polynomial.mult (p₁ p₂ : Polynomial) : Polynomial := 
  Polynomial.Mult p₁ p₂

theorem t_add_comm : ∀ (a b : Polynomial), a + b = b + a := by  
  intros p₁ p₂
  sorry

theorem t_add_assoc : ∀ (a b c : Polynomial), a + b + c = a + (b + c) := by sorry

instance : CommRing Polynomial where
    zero := 0
    one  := 1
    add p₁ p₂ := Polynomial.add p₁ p₂
    zero_add := t_zero_add
    add_zero := t_add_zero
    add_comm := t_add_comm
    add_assoc := sorry
    mul := sorry
    one_mul := sorry
    mul_one := sorry
    zero_mul := sorry
    mul_zero := sorry
    neg := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_assoc := sorry
    add_left_neg := sorry
    mul_comm := sorry   

end algebra
