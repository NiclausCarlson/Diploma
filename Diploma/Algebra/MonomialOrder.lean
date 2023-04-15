import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Vector.Basic

import Diploma.Polynomials.PolynomialCommon
import Diploma.Polynomials.Polynomial

open Vector
open polynomial
open Classical
open Nat

namespace algebra

section monomial_order

class MonomialOrder (α: Variables n) extends LinearOrder (Variables n) := 
  add_le_add := ∀ a b c: Variables n, a < b → Variables.mul a c < Variables.mul b c
      
end monomial_order

section monomials_lex_order

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
                                  simp [Vector]
                                  constructor
                                  exact heq₁ 
                                  have eq := aux (m-1) (tail ⟨x::xs, p⟩) (tail ⟨y::ys, q⟩) ab ba
                                  simp [tail, Vector] at eq
                                  exact eq
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

theorem empty_mul_empty_is_empty (a b: Variables 0) : Variables.mul a b = ⟨[], by rfl⟩ := by simp 

theorem lex_add_le_add : ∀ a b c: Variables n, Order.lex a b → Order.lex (Variables.mul a c) (Variables.mul b c) := by
  intros v₁ v₂ v₃
  let rec aux (m: Nat) (a b c: Vector Nat m) : Order.lex_impl a b → Order.lex_impl (Variables.mul a c) (Variables.mul b c) := by
   intros h 
   match a, b, c with
    | ⟨[], _⟩, ⟨[], _⟩, ⟨[], _⟩          => rw [Order.lex_impl ]
                                            split
                                            simp
                                            split
                                            repeat (rename_i prop₁ _ _ _ _ _ _ _ _ _ prop₄ _ _ _
                                                    simp at prop₁ prop₄
                                                    simp [Eq.symm prop₁] at prop₄)                                                                                  
    | ⟨x::xs, p₁⟩, ⟨y::ys, p₂⟩, ⟨z::zs, p₃⟩ => rw [Order.lex_impl]
                                               split
                                               simp
                                               split
                                               apply aux (m-1) (tail ⟨x::xs, p₁⟩) (tail ⟨y::ys, p₂⟩) (tail ⟨z::zs, p₃⟩)
                                               rw [Order.lex_impl] at h
                                               split at h
                                               rename_i prop₁ _ _ _ _ _ _ prop₂ _ _
                                               simp at prop₁ prop₂
                                               simp [Eq.symm prop₂] at prop₁
                                               split at h
                                               exact h
                                               simp at *
                                               rename_i var_mul₁ var_mul₂ _ _ _ _ _ _ _ _ eq neq heq₁ heq₂
                                               simp [map₂, Variables.mul, List.zipWith] at var_mul₁
                                               simp [map₂, Variables.mul] at var_mul₂
                                               have eq₁ := heq₁.left 
                                               have eq₂ := heq₂.left

                                               sorry
                                               sorry
  apply aux n v₁ v₂ v₃


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

instance LexOrder: MonomialOrder (α: Variables n) where
  le           := Order.lex 
  le_refl      := lex_le_refl
  le_trans     := lex_le_trans
  le_antisymm  := lex_le_antisymm
  le_total     := lex_le_total
  add_le_add   := sorry
  decidable_le := Order.lex_decidable

def Ordering.lex (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.lex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt

end monomials_lex_order


section monomials_grlex_order

private def Order.bgrlex (vs₁ vs₂: Variables n): Bool :=
  let sum₁ := elem_sum vs₁ 
  let sum₂ := elem_sum vs₂   
  if sum₁ < sum₂ then true
  else if sum₁ = sum₂ then Order.lex vs₁ vs₂
  else false
  where
    elem_sum (vs: Variables n): Nat :=
      List.foldl (fun x y => x + y) 0 vs.toList

def Order.grlex (vs₁ vs₂: Variables n): Prop :=
  let sum₁ := elem_sum vs₁ 
  let sum₂ := elem_sum vs₂   
  if sum₁ < sum₂ then True
  else if sum₁ = sum₂ then Order.lex vs₁ vs₂
  else False
  where
    elem_sum (vs: Variables n): Nat :=
      List.foldl (fun x y => x + y) 0 vs.toList

theorem grlex_le_refl: ∀ (a : Variables n), Order.grlex a a := by 
  intros a
  simp [Order.grlex]
  apply lex_le_refl

theorem grlex_le_trans : ∀ (a b c : Variables n), Order.grlex a b → Order.grlex b c → Order.grlex a c := by
  intros a b c ab bc
  simp [Order.grlex]
  simp [Order.grlex] at ab bc
  split <;> simp
  split at ab
  split at bc <;> split
  rename_i nleq leq₁ leq₂ eq
  rw [eq] at leq₁
  simp at *
  have asymm_leq₁ := Nat.lt_asymm leq₁
  contradiction
  rename_i nleq leq₁ leq₂ neq
  have contr := Nat.lt_trans leq₁ leq₂ 
  contradiction
  split at bc
  rename_i nleq₁ leq₁ nleq₂ eq₁ eq₂
  rw [eq₂] at leq₁
  repeat contradiction
  split at bc
  rename_i nleq₁ leq₁ nleq₂ neq₁ eq₂
  rw [eq₂] at leq₁
  repeat contradiction
  split <;> (split at ab; split at bc)
  rename_i nleq₁ nleq₂ eq₁ eq₂ leq
  have seq := Eq.symm eq₂
  rw [seq] at leq
  contradiction
  split at bc
  rename_i nleq₁ nleq₂ eq₁ eq₂ neq₁ eq₃
  simp at *
  apply lex_le_trans
  exact ab
  exact bc
  repeat contradiction
  rename_i nleq₁ nleq₂ neq₁ eq leq
  rw [eq] at nleq₁
  contradiction
  split at bc
  rename_i nleq₁ nleq₂ neq eq₁ nleq₃ eq₂
  rw [eq₁] at neq
  repeat contradiction
  
theorem grlex_le_antisymm : ∀ (a b : Variables n), Order.grlex a b → Order.grlex b a → a = b := by 
  intros a b ab ba
  simp [Order.grlex] at ab ba
  split at ab
  split at ba
  rename_i leq₁ leq₂
  have asymm_leq₁ := Nat.lt_asymm leq₁
  contradiction
  split at ba
  rename_i leq nleq eq
  rw [eq] at leq
  simp at leq
  contradiction
  split at ab
  split at ba
  rename_i nleq eq leq
  have symm := Eq.symm eq
  rw [symm] at leq
  simp at leq
  split at ba
  apply lex_le_antisymm 
  exact ab
  exact ba
  repeat contradiction

theorem grlex_le_total : ∀ (a b : Variables n), Order.grlex a b ∨ Order.grlex b a := by 
  intros a b
  simp [Order.grlex]
  split <;> simp
  split <;> repeat (first | split | simp)
  simp [lex_le_total] 
  rename_i nleq₁ eq nleq₂ neq
  have contr := Eq.symm eq 
  contradiction
  rename_i nleq₁ neq nleq₂ eq
  have contr := Eq.symm eq 
  contradiction
  simp
  rename_i nleq₁ neq nleq₂ eq
  simp at *
  have contr := Nat.le_antisymm nleq₁ nleq₂
  contradiction

theorem grlex_true_of_ble_grlex_true (h: Eq (Order.bgrlex v₁ v₂) true): Order.grlex v₁ v₂ := by
  simp [Order.grlex]
  split
  simp
  split
  simp [algebra.Order.bgrlex] at h
  split at h
  simp at h
  simp at *
  rw [Order.grlex.elem_sum, Order.grlex.elem_sum] at *
  rw [algebra.Order.bgrlex.elem_sum, algebra.Order.bgrlex.elem_sum] at *
  rename_i hh
  simp [hh] at h
  exact h
  rename_i nleq eq _
  contradiction
  simp [algebra.Order.bgrlex] at h
  split at h
  contradiction
  rename_i nleq neq₁ neq₂
  have leq := Nat.le_of_not_lt nleq
  exact h leq

theorem grble_eq_true_of_grlex (h: Order.grlex v₁ v₂): Eq (Order.bgrlex v₁ v₂) true := by
  simp [Order.grlex] at h
  split at h
  simp [algebra.Order.bgrlex]
  split
  rename_i h
  have le := Nat.le_of_eq h
  simp [h]
  rename_i hle _ 
  rw [Order.grlex.elem_sum, Order.grlex.elem_sum] at hle
  rw [algebra.Order.bgrlex.elem_sum, algebra.Order.bgrlex.elem_sum] at h
  rw [h] at hle
  simp at hle
  rename_i le neq
  intros nleq
  have le_contr := Nat.not_lt_of_le nleq
  rw [Order.grlex.elem_sum, Order.grlex.elem_sum] at le
  rw [algebra.Order.bgrlex.elem_sum, algebra.Order.bgrlex.elem_sum] at le_contr
  contradiction
  split at h
  simp [algebra.Order.bgrlex]
  intros le
  split
  exact h
  rename_i nlt eq neq
  rw [Order.grlex.elem_sum, Order.grlex.elem_sum] at nlt eq
  rw [algebra.Order.bgrlex.elem_sum, algebra.Order.bgrlex.elem_sum] at le neq
  repeat contradiction

theorem grlex_false_of_ble_grlex_false (h: Not (Eq (Order.bgrlex v₁ v₂) true)): Not (Order.grlex v₁ v₂) := 
  fun h' => absurd (grble_eq_true_of_grlex h') h
  
instance Order.grlex_decidable (v₁ v₂: Variables n): Decidable (Order.grlex v₁ v₂) := 
  dite (Eq (Order.bgrlex v₁ v₂) true) (fun h => isTrue (grlex_true_of_ble_grlex_true h))
                                      (fun h => isFalse (grlex_false_of_ble_grlex_false h))
  
-- instance GrlexOrder: LinearOrder (Variables n) where
--   le           := Order.grlex 
--   le_refl      := grlex_le_refl
--   le_trans     := grlex_le_trans
--   le_antisymm  := grlex_le_antisymm
--   le_total     := grlex_le_total
--   decidable_le := Order.grlex_decidable

def Ordering.grlex (m₁ m₂: Monomial n): Ordering :=
  if m₁.snd = m₂.snd then Ordering.eq
  else if Order.grlex m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt

end monomials_grlex_order

end algebra
