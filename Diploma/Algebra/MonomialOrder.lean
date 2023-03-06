import Diploma.Polynomials.Polynomial

import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Vector.Basic

import Diploma.Polynomials.PolynomialCommon


open Vector
open polynomial
open Classical
open Nat

namespace algebra

private def Order.ble_lex_impl (v₁ v₂ : Vector Nat n): Bool :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => true
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x == y then ble_lex_impl v₁.tail v₂.tail 
                              else x <= y

def Order.lex_impl (v₁ v₂ : Vector Nat n): Prop :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => True
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x = y then lex_impl v₁.tail v₂.tail 
                              else x <= y

def Order.lex (v₁ v₂ : Variables n): Prop := Order.lex_impl v₁ v₂

theorem lex_le_refl : ∀ (a : Variables n), Order.lex a a := by
  intro a
  let rec aux (m: Nat) (v: Variables m) : Order.lex_impl v v := by 
    match v with 
      | ⟨[], p⟩    => rw [Order.lex_impl]
                      split
                      simp at *
                      simp at p
                      simp at *                                   
      | ⟨x::xs, _⟩ => rw [Order.lex_impl]
                      split
                      simp
                      simp at *
                      simp at *
                      simp [Nat.le_refl]
                      rename_i x₁ _ x₂ _ h₁ h₂
                      have h₃ := Eq.symm h₁.left
                      have h₄ := Eq.symm h₂.left
                      rw [h₃, h₄]
                      simp [Nat.le_refl]
                      apply aux (m-1) (tail ⟨x::xs, _⟩)
  exact aux n a

theorem lex_le_trans : ∀ (a b c : Variables n), Order.lex a b → Order.lex b c → Order.lex a c := by
  intros v₁ v₂ v₃ h₁ h₂
  let rec aux (m: Nat) (a b c: Variables m) 
              (ab : Order.lex_impl a b) (bc : Order.lex_impl b c) : Order.lex_impl a c := by 
    match a, b, c with
      | ⟨[], p⟩,    ⟨[], q⟩,    ⟨[], l⟩    => rw [Order.lex_impl]
                                              split
                                              simp
                                              simp at *
      | ⟨x::xs, p⟩, ⟨y::ys, q⟩, ⟨z::zs, l⟩ => rw [Order.lex_impl] 
                                              rw [Order.lex_impl] at ab bc
                                              split at ab
                                              split at bc
                                              split <;> simp at *
                                              split at bc
                                              split
                                              repeat (first 
                                                | rename_i heq₁ heq₂ _ _ _ _ _ _ _ _ heq₃ heq₄ _ _
                                                  rw [heq₂] at heq₃
                                                  simp at heq₃ 
                                                | split)
                                              split at ab
                                              split at bc
                                              rename_i heq₁ heq₂ _ _ _ _ _ _ heq₃ heq₄
                                              rw [heq₂] at heq₃
                                              simp at heq₃
                                              split at bc
                                              apply aux (m-1) (tail ⟨x::xs, p⟩) (tail ⟨y::ys, q⟩) (tail ⟨z::zs, l⟩) ab bc
                                              simp at *
                                              rename_i eq₁ eq₂ _ _ _ _ _  _ _ _ hneq heq₁ heq₂ heq₃ heq₄ 
                                              have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                              have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                              have x_cross_eq_x     := Eq.symm (heq₃.left)
                                              have y_cross_eq_x     := Eq.symm (heq₄.left)
                                              rw [x_cross_eq_x, y_cross_eq_x] at hneq
                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at eq₂
                                              rw [eq₂] at eq₁
                                              contradiction
                                              split at bc
                                              simp at *
                                              repeat (first | rename_i heq₁ heq₂ eq₁ neq₁ _ _ _ _ _ _ _ _ heq₃ heq₄ eq₂
                                                              simp at heq₁ heq₂ heq₃ heq₄
                                                              have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                                              have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                                              have x_cross_eq_x     := Eq.symm (heq₃.left)
                                                              have y_cross_eq_x     := Eq.symm (heq₄.left)
                                                              rw [x_cross_eq_x, y_cross_eq_x] at eq₂
                                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at neq₁
                                                              rw [eq₂] at neq₁
                                                              contradiction
                                                            | split at bc)
                                              rename_i heq₁ heq₂ eq₁ neq₁ _ _ _ _ _ _ _ _ heq₃ heq₄ neq₂ 
                                              simp at heq₁ heq₂ heq₃ heq₄
                                              have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                              have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                              have x_cross_eq_x     := Eq.symm (heq₃.left)
                                              have y_cross_eq_x     := Eq.symm (heq₄.left)
                                              rw [x_cross_eq_x, y_cross_eq_x] at neq₂ bc
                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at neq₁ ab
                                              rw [eq₁] at ab
                                              have eq_eq := Nat.le_antisymm bc ab
                                              contradiction 
                                              split at ab
                                              split at bc
                                              simp at *
                                              split at bc
                                              simp at *
                                              rename_i neq₁ eq₁ _ _ _ _ _ _ _ _ eq₂ heq₁ heq₂ heq₃ heq₄
                                              have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                              have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                              have x_cross_eq_x     := Eq.symm (heq₃.left)
                                              have y_cross_eq_x     := Eq.symm (heq₄.left)
                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at eq₁
                                              rw [x_cross_eq_x, y_cross_eq_x] at eq₂
                                              rw [eq₂] at eq₁
                                              contradiction
                                              repeat (first | simp at *
                                                              rename_i neq₁ eq₁ _ _ _ _ _ _ _ _ eq₂ heq₁ heq₂ heq₃ heq₄
                                                              have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                                              have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                                              have x_cross_eq_x     := Eq.symm (heq₃.left)
                                                              have y_cross_eq_x     := Eq.symm (heq₄.left)
                                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at eq₁
                                                              rw [x_cross_eq_x, y_cross_eq_x] at bc
                                                              rw [eq₁]
                                                              exact bc
                                                            | split at bc)
                                              simp at *
                                              split at bc <;> (simp at *
                                                               rename_i neq₁ neq₂ _ _ _ _ _ _ _ _ _ heq₁ heq₂ heq₃ heq₄
                                                               have x_cross_one_eq_x := Eq.symm (heq₁.left)
                                                               have y_cross_one_eq_y := Eq.symm (heq₂.left)
                                                               have x_cross_eq_x     := Eq.symm (heq₃.left)
                                                               have y_cross_eq_x     := Eq.symm (heq₄.left))
                                              rename_i eq
                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at neq₂ ab
                                              rw [x_cross_eq_x, y_cross_eq_x] at eq
                                              rw [eq] at ab
                                              exact ab
                                              rename_i neq₃
                                              rw [x_cross_one_eq_x, y_cross_one_eq_y] at neq₂ ab
                                              rw [x_cross_eq_x, y_cross_eq_x] at neq₃ bc
                                              have le_le := Nat.le_trans ab bc
                                              exact le_le                        
  exact aux n v₁ v₂ v₃ h₁ h₂

theorem eq_head_tail (v₁ v₂ : Vector Nat n) (eq: v₁ = v₂) : v₁.tail = v₂.tail := 
    by    
      match v₁, v₂ with
        | ⟨[], p⟩, ⟨[], q⟩       => simp 
        | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => sorry

theorem lex_le_antisymm : ∀ (a b : Variables n), Order.lex a b → Order.lex b a → a = b := by
  intros v₁ v₂ h₁ h₂
  let rec aux (m: Nat) (a b: Vector Nat m) (ab: Order.lex_impl a b) (ba: Order.lex_impl b a): a = b := by 
    match a, b with
      | ⟨[], p⟩, ⟨[], q⟩       => simp 
      | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => rw [Order.lex_impl] at ab ba
                                  simp at *
                                  split at ab
                                  split at ba
                                  rename_i heq₁ heq₂ 
                                  sorry
                                  rename_i eq neq
                                  have eq_symm := Eq.symm eq
                                  contradiction
                                  split at ba
                                  rename_i neq eq
                                  have eq_symm := Eq.symm eq
                                  contradiction
                                  rename_i neq₁ neq₂
                                  have eq := Nat.le_antisymm ab ba
                                  contradiction
  exact aux n v₁ v₂ h₁ h₂ 

theorem lex_le_total : ∀ (a b : Variables n), Order.lex a b ∨ Order.lex b a := by
  intros v₁ v₂
  let rec aux (m: Nat) (a b: Vector Nat m) : Order.lex_impl a b ∨ Order.lex_impl b a := by
    match a, b with
      | ⟨[], p⟩, ⟨[], q⟩       => rw [Order.lex_impl]
                                  split
                                  simp
                                  simp at *
      | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => rw [Order.lex_impl]
                                  simp [Or.comm]
                                  rw [Order.lex_impl]
                                  split
                                  simp
                                  split
                                  split
                                  simp [Or.comm]
                                  apply aux (m-1) (tail ⟨x::xs, p⟩) (tail ⟨y::ys, q⟩)
                                  simp at *
                                  rename_i eq neq heq₁ heq₂
                                  have s_eq := Eq.symm eq
                                  have eq_1 := Eq.symm heq₁.left
                                  have eq_2 := Eq.symm heq₂.left
                                  rw [eq_1, eq_2] at s_eq
                                  contradiction
                                  split
                                  simp at *
                                  rename_i neq eq heq₁ heq₂
                                  have s_eq := Eq.symm eq
                                  have eq_1 := heq₁.left
                                  have eq_2 := heq₂.left
                                  rw [eq_1, eq_2] at s_eq
                                  contradiction
                                  simp at *
                                  rename_i heq₁ heq₂
                                  have eq_1 := heq₁.left
                                  have eq_2 := heq₂.left
                                  rw [eq_1, eq_2]
                                  simp [Nat.le_total]
  exact aux n v₁ v₂


theorem Order.lex_true_of_ble_lex_true (h: Eq (Order.ble_lex_impl v₁ v₂) true): Order.lex v₁ v₂ := by
  let rec aux (m: Nat) (a b: Vector Nat m) (h: Eq (Order.ble_lex_impl a b) true): Order.lex a b := by
    rw [Order.lex]
    rw [Order.lex_impl]
    match a, b with
      | ⟨[], _⟩  , ⟨[], _⟩     => simp
      | ⟨x::xs, _⟩, ⟨y::ys, _⟩ => split
                                  simp
                                  split
                                  rw [Order.ble_lex_impl] at h
                                  simp at h
                                  split at h
                                  exact aux (m-1) (tail ⟨x::xs, _⟩) (tail ⟨y::ys, _⟩) h
                                  simp at *
                                  rename_i heq₁ hneq heq₂ heq₃
                                  have eq₁ := heq₂.left
                                  have eq₂ := heq₃.left
                                  rw [eq₁, eq₂] at hneq
                                  contradiction                                  
                                  rename_i heq₁ heq₂ hneq₁ 
                                  rw [Order.ble_lex_impl] at h
                                  split at h
                                  simp at *
                                  split at h
                                  rename_i heq₃ heq₄ hneq₂
                                  simp at heq₁ heq₂ heq₃ heq₄ hneq₂
                                  have eq₁ := heq₁.left
                                  have eq₂ := heq₂.left
                                  have eq₃ := heq₃.left
                                  have eq₄ := heq₄.left
                                  rw [eq₁] at eq₃
                                  rw [eq₂] at eq₄
                                  rw [eq₃, eq₄] at hneq₁
                                  contradiction
                                  simp at h
                                  rename_i heq₁ heq₂ _ _ _ _ _ _ _ _ _ _ _ heq₃ heq₄ _ 
                                  simp at heq₁ heq₂ heq₃ heq₄
                                  have eq₁ := heq₁.left
                                  have eq₂ := heq₂.left
                                  have eq₃ := heq₃.left
                                  have eq₄ := heq₄.left
                                  rw [eq₁] at eq₃
                                  rw [eq₂] at eq₄
                                  rw [eq₃, eq₄]
                                  exact h                                
  rename_i n
  exact aux n v₁ v₂ h                                 

theorem Order.ble_eq_true_of_lex (h: Order.lex_impl v₁ v₂) : Eq (Order.ble_lex_impl v₁ v₂) true := by
  let rec aux (m: Nat) (a b: Vector Nat m) (h: Order.lex_impl a b): Eq (Order.ble_lex_impl a b) true := by 
     match a, b with
      | ⟨[], _⟩, ⟨[], _⟩       => rw [Order.ble_lex_impl]
      | ⟨x::xs, _⟩, ⟨y::ys, _⟩ => rw [Order.ble_lex_impl]
                                  split;rfl
                                  split
                                  rw [lex_impl] at h
                                  simp at h
                                  split at h
                                  apply Order.ble_eq_true_of_lex h
                                  rename_i heq₁ heq₂ neq eq
                                  simp at heq₁ heq₂
                                  have eq₁ := heq₁.left
                                  have eq₂ := heq₂.left
                                  simp at neq
                                  rw [eq₁, eq₂] at eq
                                  contradiction
                                  rw [lex_impl] at h
                                  simp at h
                                  split at h
                                  rename_i heq₁ heq₂ neq eq
                                  simp at heq₁ heq₂
                                  have eq₁ := heq₁.left
                                  have eq₂ := heq₂.left
                                  simp at neq
                                  rw [eq₁, eq₂] at eq
                                  contradiction
                                  simp
                                  rename_i heq₁ heq₂ _ _
                                  simp at heq₁ heq₂
                                  have eq₁ := Eq.symm heq₁.left
                                  have eq₂ := Eq.symm heq₂.left
                                  rwa [eq₁, eq₂]
  rename_i n
  exact aux n v₁ v₂ h 

theorem Order.lex_false_of_ble_lex_false (h: Not (Eq (Order.ble_lex_impl v₁ v₂) true)): Not (Order.lex v₁ v₂) :=
  fun h' => absurd (Order.ble_eq_true_of_lex h') h

instance Order.lex_decidable (v₁ v₂: Variables n): Decidable (Order.lex v₁ v₂) :=
  dite (Eq (Order.ble_lex_impl v₁ v₂) true) (fun h => isTrue (Order.lex_true_of_ble_lex_true h))
                                            (fun h => isFalse (Order.lex_false_of_ble_lex_false h))

instance LexOrder: LinearOrder (Variables n) where
  le           := Order.lex 
  le_refl      := lex_le_refl
  le_trans     := lex_le_trans
  le_antisymm  := lex_le_antisymm
  le_total     := lex_le_total
  decidable_le := Order.lex_decidable

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
