import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order

import Diploma.Polynomials.PolynomialCommon

namespace algebra

open Vector
open polynomial
open Classical

def Order.lex (m₁ m₂: Monomial n): Prop := if m₁.snd = m₂.snd then True 
                                           else cmp diff
  where 
    diff : List Int := 
      (map₂ (fun x y => (Int.ofNat x) - (Int.ofNat y)) m₁.snd m₂.snd).toList
    cmp (l: List Int): Prop :=
      match l with
        | [] => True
        | [x] => if x > 0 then True else False
        | x::xs => if x = 0 then cmp xs
                   else if x > 0 then True
                   else False

instance (m₁ m₂: Monomial n): Decidable (Order.lex m₁ m₂) := by sorry
  

def Ordering.lex (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.lex m₁ m₂ then Ordering.gt
  else Ordering.lt


theorem lex_le_refl : ∀ (a : Monomial n), Order.lex a a := by
  intro a
  simp [Order.lex]
  
theorem lex_le_trans : ∀ (a b c : Monomial n), Order.lex a b → Order.lex b c → Order.lex a c := by
  simp [Order.lex]
  intros _ a _ b _ c h₁ h₂
  split at h₁; split at h₂
  split; simp
  sorry
  split; simp; simp [Order.lex.diff, map₂]
  sorry
  sorry

  
theorem lex_le_antisymm : ∀ (a b : Monomial n), Order.lex a b → Order.lex b a → a = b := by
  intros a b h₁ h₂
  sorry

theorem lex_le_total : ∀ (a b : Monomial n), Order.lex a b ∨ Order.lex b a := by
  intros a b
  sorry

instance LexOrder: LinearOrder (Monomial n) where
  le m₁ m₂ := Order.lex m₁ m₂
  le_refl := lex_le_refl
  le_trans := lex_le_trans
  le_antisymm := lex_le_antisymm
  le_total := lex_le_total
  decidable_le := sorry
  decidable_eq := sorry



def Order.grlex (m₁ m₂: Monomial n): Prop := 
  if elem_sum m₁ > elem_sum m₂ then True
  else if elem_sum m₁ = elem_sum m₂ then Order.lex m₁ m₂
  else False
  where
    elem_sum (m: Monomial n): Nat :=
      List.foldl (fun x y => x + y) 0 m.snd.toList

instance (m₁ m₂: Monomial n): Decidable (Order.grlex m₁ m₂) := sorry

def Ordering.grlex (m₁ m₂: Monomial n): Ordering :=
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.grlex m₁ m₂ then Ordering.gt
  else Ordering.lt

end algebra
