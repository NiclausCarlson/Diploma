import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order

import Diploma.Polynomials.PolynomialCommon


open Vector
open polynomial
open Classical

namespace algebra

def Order.lex_impl (v₁ v₂ : Vector Nat n): Prop :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => True
    | ⟨[x], _⟩ , ⟨[y], _⟩  => x <= y
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x = y then Order.lex_impl v₁.tail v₂.tail 
                              else x <= y

def Order.lex (v₁ v₂ : Variables n): Prop := Order.lex_impl v₁ v₂

theorem lex_le_refl : ∀ (a : Variables n), Order.lex a a := by
  intro a
  let rec aux (v: Variables n) : Order.lex v v := by
    match v with 
      | ⟨[], p⟩ => rw [Order.lex, Order.lex_impl]
                   split
                   simp
                   sorry
                   sorry                                   
      | ⟨[x], _⟩ => sorry
      | ⟨x::xs, _⟩ => sorry
  exact aux a

theorem lex_le_trans : ∀ (a b c : Variables n), Order.lex a b → Order.lex b c → Order.lex a c := by
  intros a b c h₁ h₂
  rw [Order.lex, Order.lex_impl]
  rw [Order.lex, Order.lex_impl] at h₁ h₂
  split
  split at h₁
  split at h₂
  exact h₁
  exact h₁
  exact h₁
  sorry


theorem lex_le_antisymm : ∀ (a b : Variables n), Order.lex a b → Order.lex b a → a = b := by
  intros a b h₁ h₂
  sorry
  

theorem lex_le_total : ∀ (a b : Variables n), Order.lex a b ∨ Order.lex b a := by
  intros a b
  sorry
  

noncomputable instance LexOrder: LinearOrder (Variables n) where
  le           := Order.lex 
  le_refl      := lex_le_refl
  le_trans     := lex_le_trans
  le_antisymm  := lex_le_antisymm
  le_total     := lex_le_total
  decidable_le := by infer_instance

instance: DecidableRel (Order.lex : Variables n → Variables n → Prop) :=
  fun v₁ v₂ => by 
                let rec aux (m: Nat) (a b: Vector Nat m) : Decidable (Order.lex_impl a b) := by
                  rw [Order.lex_impl]
                  match a, b with
                    | ⟨[], _⟩, ⟨[], _⟩       => exact isTrue (by simp)                         
                    | ⟨[x], _⟩, ⟨[y], _⟩     => apply Nat.decLe
                    | ⟨x::xs, _⟩, ⟨y::ys, _⟩ => split
                                                exact isTrue (by simp)
                                                apply Nat.decLe
                                                sorry
                exact aux n v₁ v₂


def Ordering.lex (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.lex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt


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
