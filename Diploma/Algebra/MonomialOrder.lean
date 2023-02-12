import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order

import Diploma.Polynomials.PolynomialCommon


open Vector
open polynomial
open Classical

namespace algebra

def Order.lex (v₁ v₂ : Variables n): Prop :=
  match v₁, v₂ with
    | ⟨[], _⟩   , ⟨[], _⟩   => True
    | ⟨[x], _⟩  , ⟨[y], _⟩  => x < y
    | ⟨x::_, _⟩ , ⟨y::_, _⟩ => if x = y then Order.lex v₁.tail v₂.tail
                               else x < y 

instance: DecidableRel (Order.lex : Variables n → Variables n → Prop) :=
  fun v₁ v₂ => sorry

def Ordering.lex (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.lex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt


theorem lex_le_refl : ∀ (a : Variables n), Order.lex a a := by
  intro a
  cases a with
    | mk l p => cases l with
                  | nil => simp [Order.lex]
                  | cons a => sorry

  
  
theorem lex_le_trans : ∀ (a b c : Variables n), Order.lex a b → Order.lex b c → Order.lex a c := by
  intros a b c h₁ h₂
  sorry
  

theorem lex_le_antisymm : ∀ (a b : Variables n), Order.lex a b → Order.lex b a → a = b := by
  intros a b h₁ h₂
  sorry
  

theorem lex_le_total : ∀ (a b : Variables n), Order.lex a b ∨ Order.lex b a := by
  intros a b
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
