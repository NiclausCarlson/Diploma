import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order

import Diploma.Polynomials.PolynomialCommon

namespace algebra

open Vector
open polynomial
open Classical

def Order.lex (vs₁ vs₂: Variables n): Prop := if vs₁ = vs₂ then True 
                                            else cmp diff
  where 
    diff : List Int := 
      (map₂ (fun x y => (Int.ofNat x) - (Int.ofNat y)) vs₁ vs₂).toList
    cmp (l: List Int): Prop :=
      match l with
        | [] => True
        | [x] => if x > 0 then True else False
        | x::xs => if x = 0 then cmp xs
                   else if x > 0 then True
                   else False

instance (vs₁ vs₂: Variables n): Decidable (Order.lex vs₁ vs₂) := by sorry
  

def Ordering.lex (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.lex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt


theorem lex_le_refl : ∀ (a : Variables n), Order.lex a a := by
  intro a
  simp [Order.lex]
  
  
theorem lex_le_trans : ∀ (a b c : Variables n), Order.lex a b → Order.lex b c → Order.lex a c := by
  simp [Order.lex]
  intros a b c h₁ h₂
  split at h₁; split at h₂
  split; simp
  sorry
  split; simp; simp [Order.lex.diff, map₂]
  sorry
  sorry
  

theorem lex_le_antisymm : ∀ (a b : Variables n), Order.lex a b → Order.lex b a → a = b := by
  simp [Order.lex]
  intros a b h₁ h₂
  split at h₁
  split at h₂
  sorry
  sorry
  split at h₂
  sorry
  sorry
  

theorem lex_le_total : ∀ (a b : Variables n), Order.lex a b ∨ Order.lex b a := by
  simp [Order.lex]
  intros a b
  split; simp
  split; simp
  sorry
  

instance LexOrder: LinearOrder (Variables n) where
  le vs₁ vs₂ := Order.lex vs₁ vs₂
  le_refl := lex_le_refl
  le_trans := lex_le_trans
  le_antisymm := lex_le_antisymm
  le_total := lex_le_total
  decidable_le := sorry
  decidable_eq := sorry


def Order.grlex (vs₁ vs₂: Variables n): Prop := 
  if elem_sum vs₁ > elem_sum vs₂ then True
  else if elem_sum vs₁ = elem_sum vs₂ then Order.lex vs₁ vs₂
  else False
  where
    elem_sum (vs: Variables n): Nat :=
      List.foldl (fun x y => x + y) 0 vs.toList

instance (vs₁ vs₂: Variables n): Decidable (Order.grlex vs₁ vs₂) := sorry

def Ordering.grlex (m₁ m₂: Monomial n): Ordering :=
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.grlex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt

end algebra
