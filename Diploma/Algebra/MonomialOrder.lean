import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch

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
  let rec aux (m: Nat) (v: Variables m) : Order.lex_impl v v := by
    match v with 
      | ⟨[], p⟩ => rw [Order.lex_impl]
                   split
                   simp at *
                   simp at p
                   simp at *
                   simp at *                                   
      | ⟨[x], _⟩ => rw [Order.lex_impl]
                    split
                    simp
                    simp at *
                    simp at *
                    simp [Nat.le_refl]
                    sorry
                    split
                    simp at *
                    apply aux (m-1) (tail ⟨[x], _⟩)
                    sorry
      | ⟨x::xs, _⟩ => rw [Order.lex_impl]
                      split
                      simp
                      sorry
                      split
                      apply aux (m-1) (tail ⟨x::xs, _⟩)
                      sorry

  exact aux n a

theorem lex_le_trans : ∀ (a b c : Variables n), Order.lex a b → Order.lex b c → Order.lex a c := by
  sorry

theorem lex_le_antisymm : ∀ (a b : Variables n), Order.lex a b → Order.lex b a → a = b := by
  intros a b h₁ h₂
  sorry
  
theorem lex_le_total : ∀ (a b : Variables n), Order.lex a b ∨ Order.lex b a := by
  intros v₁ v₂
  let rec aux (m: Nat) (a b: Vector Nat m) : Order.lex_impl a b ∨ Order.lex_impl b a := by
    match a, b with
      | ⟨[], p⟩, ⟨[], q⟩     => rw [Order.lex_impl]
                                split
                                simp
                                simp at *
                                split
                                simp
                                simp at *
                                simp
                                simp at *
      | ⟨[x], p⟩, ⟨[y], q⟩   => rw [Order.lex_impl]
                                split
                                simp
                                simp at *
                                simp at p q
                                sorry
                                simp at *
                                split
                                sorry
                                sorry
      | ⟨x::_, _⟩, ⟨y::_, _⟩ => sorry
  exact aux n v₁ v₂
  

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
                                                simp at *
                                                simp [apply_ite]
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
