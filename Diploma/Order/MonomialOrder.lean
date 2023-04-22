import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Vector.Basic

import Diploma.Polynomials.PolynomialCommon
import Diploma.Order.AvailableOrders

open Vector Classical Nat polynomial 

namespace algebra

class MonomialOrder (α : Type u) [HMul α α α] extends LinearOrder α := 
 add_le_add : ∀ a b c: α, a < b → a * c < b * c

--# Lex order
--# a <_lex b ↔ ∃ c: a = c ++ p₁, b = c ++ p₂ ∧ p₁[0] < p₂[0]
def Order.lex_impl (v₁ v₂ : Vector Nat n): Prop :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => False
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x = y then lex_impl v₁.tail v₂.tail 
                              else x < y

def Order.lex (v₁ v₂ : Variables n order.Lex): Prop := Order.lex_impl v₁ v₂

def Order.lex_le (v₁ v₂ : Variables n order.Lex): Prop := if v₁ = v₂ then True
                                                          else Order.lex v₁ v₂  

private def Order.blt_lex_impl (v₁ v₂ : Vector Nat n): Bool :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => false
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x == y then blt_lex_impl v₁.tail v₂.tail 
                              else x < y

private def Order.ble_lex_impl (v₁ v₂ : Vector Nat n): Bool := v₁ == v₂ ∨ Order.blt_lex_impl v₁ v₂  

--# Ordering theorems
theorem lex_le_refl : ∀ (a : Variables n order.Lex), Order.lex_le a a := by
  intro a
  match a with 
    | ⟨[], p⟩    => rw [Order.lex_le]
                    simp                          
    | ⟨x::xs, _⟩ => rw [Order.lex_le, Order.lex, Order.lex_impl]
                    split
                    simp
                    simp at *

theorem lex_lt_trans (a b c : Variables n order.Lex): Order.lex a b → Order.lex b c → Order.lex a c := by
  intros h₁ h₂
  let rec aux (m: Nat) (a b c: Variables m order.Lex) 
              (ab : Order.lex_impl a b) (bc : Order.lex_impl b c) : Order.lex_impl a c := by 
    match a, b, c with
      | ⟨[], p⟩,    ⟨[], q⟩,    ⟨[], l⟩    => rw [Order.lex_impl] at ab bc
                                              split at ab 
                                              split at bc
                                              repeat contradiction
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
                                              have eq_eq := Nat.lt_asymm bc ab
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
                                              have le_le := Nat.lt_trans ab bc
                                              exact le_le                        
  exact aux n a b c h₁ h₂

theorem lex_le_trans : ∀ (a b c : Variables n order.Lex), Order.lex_le a b → Order.lex_le b c → Order.lex_le a c := 
  by
    intros a b c ab bc
    rw [Order.lex_le]
    rw [Order.lex_le] at ab bc
    split at ab
    split at bc
    rename_i eq₁ eq₂
    rw [eq₂] at eq₁
    simp [eq₁]
    rename_i eq leq
    rw [←eq] at leq
    simp [leq]
    rw [←eq] at bc
    exact bc
    split at bc
    rename_i neq eq
    rw [eq] at neq
    split
    simp
    rw [eq] at ab
    exact ab
    split
    simp
    exact lex_lt_trans a b c ab bc 

theorem lex_lt_antisymm : ∀ (a b : Variables n order.Lex), Order.lex a b → Order.lex b a → a = b := by
  intros v₁ v₂ h₁ h₂
  let rec aux (m: Nat) (a b: Vector Nat m) (ab: Order.lex_impl a b) (ba: Order.lex_impl b a): a = b := by 
    match a, b with
      | ⟨[], p⟩, ⟨[], _⟩       => simp 
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
                                  have eq := Nat.lt_asymm ab ba
                                  contradiction
  exact aux n v₁ v₂ h₁ h₂ 

theorem lex_le_antisymm : ∀ (a b : Variables n order.Lex), Order.lex_le a b → Order.lex_le b a → a = b := by
  intros a b le₁ le₂
  rw [Order.lex_le] at le₁ le₂
  split at le₁
  split at le₂
  rename_i h
  rw [h] 
  rename_i h _
  exact h
  split at le₂
  rename_i h
  simp [h]
  exact lex_lt_antisymm a b le₁ le₂  

theorem vectors_neq_r_head_neq (v₁ v₂: Vector Nat (Nat.succ n)) (h: v₁ ≠ v₂): head v₁ ≠ head v₂ := by sorry 

theorem lex_lt_semi_total (v₁ v₂ : Variables n order.Lex) (not_eq: v₁ ≠ v₂): Order.lex v₁ v₂ ∨ Order.lex v₂ v₁ := by
  let rec aux (m: Nat) (a b: Vector Nat m) (not_eq_: a ≠ b): (Order.lex_impl a b ∨ Order.lex_impl b a) := by
    match a, b with
      | ⟨[], p⟩, ⟨[], q⟩       => simp at not_eq_
      | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => rw [Order.lex_impl]
                                  split
                                  rw [Order.lex_impl]
                                  split
                                  simp
                                  simp at *
                                  split
                                  simp at *
                                  simp at *
                                  split
                                  simp at *
                                  rename_i eq ceq₁ ceq₂
                                  have eq₁ := ceq₁.left
                                  have eq₂ := ceq₂.left
                                  rw [← eq₁, ←eq₂] at eq
                                  sorry
                                  sorry
                                  -- rename_i eq neq heq₁ heq₂
                                  -- have s_eq := Eq.symm eq
                                  -- have eq_1 := Eq.symm heq₁.left
                                  -- have eq_2 := Eq.symm heq₂.left
                                  -- rw [eq_1, eq_2] at s_eq
                                  -- contradiction
                                  -- split
                                  -- simp at *
                                  -- rename_i neq eq heq₁ heq₂
                                  -- have s_eq := Eq.symm eq
                                  -- have eq_1 := heq₁.left
                                  -- have eq_2 := heq₂.left
                                  -- rw [eq_1, eq_2] at s_eq
                                  -- contradiction
                                  -- simp at *
                                  -- rename_i r _ heq₁ heq₂
                                  -- have eq_1 := heq₁.left
                                  -- have eq_2 := heq₂.left
                                  -- rw [eq_1, eq_2]
                                  -- simp [Nat.le_total]
                                  -- exact r
  exact aux n v₁ v₂ not_eq
  
theorem lex_le_total : ∀ (a b : Variables n order.Lex), Order.lex_le a b ∨ Order.lex_le b a := by 
  intros a b
  rw [Order.lex_le, Order.lex_le]
  split
  split
  simp; simp
  split
  simp
  rename_i h _
  simp [lex_lt_semi_total, h] 

theorem lex_lt_iff_le_not_le: ∀ (a b : Variables n order.Lex), Order.lex a b ↔ Order.lex_le a b ∧ ¬ Order.lex_le b a := by
  sorry
  
theorem lex_add_lt_add : ∀ a b c: Variables n order.Lex, Order.lex a b → Order.lex (Variables.mul a c) (Variables.mul b c) := by
  intros v₁ v₂ v₃
  let rec aux (m: Nat) (a b c: Variables m order.Lex) : Order.lex_impl a b → Order.lex_impl (Variables.mul a c) (Variables.mul b c) := by
   intros h 
   match a, b, c with
    | ⟨[], _⟩, ⟨[], _⟩, ⟨[], _⟩          => rw [Order.lex_impl]
                                            split
                                            simp
                                            sorry
                                            sorry
                                            repeat (rename_i prop₁ _ _ _ _ _ _ _ _ _ prop₄ _ _ _
                                                    simp at prop₁ prop₄
                                                    simp [Eq.symm prop₁] at prop₄)                                                                                  
    | ⟨x::xs, p₁⟩, ⟨y::ys, p₂⟩, ⟨z::zs, p₃⟩ => rw [Order.lex_impl]
                                               split
                                               simp
                                               sorry
                                               sorry
                                               --split
                                               --apply aux (m-1) (tail ⟨x::xs, p₁⟩) (tail ⟨y::ys, p₂⟩) (tail ⟨z::zs, p₃⟩)
                                               --rw [Order.lex_impl] at h
                                               --split at h
                                               --rename_i prop₁ _ _ _ _ _ _ prop₂ _ _
                                               --simp at prop₁ prop₂
                                               --simp [Eq.symm prop₂] at prop₁
                                               --split at h
                                               --exact h
                                               --simp at *
                                               --rename_i var_mul₁ var_mul₂ _ _ _ _ _ _ _ _ eq neq heq₁ heq₂
                                               --simp [map₂, Variables.mul, List.zipWith] at var_mul₁ var_mul₂
                                               --have eq₁ := heq₁.left 
                                               --have eq₂ := heq₂.left
                                               --cases var_mul₁
                                               --cases var_mul₂
                                               --rename_i sum_eq _
                                               --simp [eq₁, eq₂] at sum_eq
                                               --contradiction
                                               --rw [Order.lex_impl] at h
                                               --split at h
                                               --simp at *
                                               --split at h
                                               --rename_i var_mul₁ var_mul₂ _ _ _ _ _ _ _ _ _ heq₁ heq₂ eq
                                               --simp [map₂, Variables.mul, List.zipWith] at var_mul₁ var_mul₂
                                               --cases heq₁
                                               --cases heq₂
                                               --cases var_mul₁
                                               --cases var_mul₂
                                               --simp [eq]
                                               --rename_i eq _ _ hneq₂ _
                                               --simp at *
                                               --contradiction
                                               --rename_i var_mul₁ var_mul₂ _ _ _ _ _ _ _ _ _ heq₁ heq₂ neq
                                               --cases heq₁
                                               --cases heq₂
                                               --cases var_mul₁
                                               --cases var_mul₂
                                               --simp
                                               --exact h
  apply aux n v₁ v₂ v₃

--# Decidable theorems
theorem lex_true_of_blt_lex_true (h: Eq (Order.blt_lex_impl v₁ v₂) true): Order.lex v₁ v₂ := by
  let rec aux (m: Nat) (a b: Vector Nat m) (h: Eq (Order.blt_lex_impl a b) true): Order.lex a b := by
    rw [Order.lex]
    rw [Order.lex_impl]
    match a, b with
      | ⟨[], _⟩  , ⟨[], _⟩     => rw [Order.blt_lex_impl] at h
                                  split at h
                                  simp at *
                                  split
                                  rename_i heq _ _
                                  simp at heq
                                  rename_i heq _ _
                                  simp at heq
      | ⟨x::xs, _⟩, ⟨y::ys, _⟩ => split
                                  rw [Order.blt_lex_impl] at h
                                  split at h
                                  simp at h
                                  rename_i heq₁ heq₂ _ _ _ _ _ _ _ _ heq₃ heq₄ 
                                  split at h
                                  rw [heq₁] at heq₃ 
                                  rw [heq₂] at heq₄
                                  rename_i heq
                                  sorry
                                  sorry
                                  simp
                                  split
                                  rw [Order.blt_lex_impl] at h
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
                                  rw [Order.blt_lex_impl] at h
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

theorem lex_le_true_of_blt_lex_true (h: Eq (Order.blt_lex_impl v₁ v₂) true): Order.lex_le v₁ v₂ := by 
  rw [Order.lex_le]
  split
  simp
  simp [lex_true_of_blt_lex_true, h]

theorem blt_eq_true_of_lex_le (h: Order.lex_le v₁ v₂) : Eq (Order.ble_lex_impl v₁ v₂) true := by
  let rec aux (m: Nat) (a b: Vector Nat m) (h: Order.lex_le a b): Eq (Order.ble_lex_impl a b) true := by 
     match a, b with
      | ⟨[], _⟩, ⟨[], _⟩       => rw [Order.lex_le] at h
                                  split at h
                                  rw [Order.ble_lex_impl]
                                  simp
                                  simp at *
      | ⟨x::xs, _⟩, ⟨y::ys, _⟩ => rw [Order.lex_le] at h
                                  split at h
                                  rw [Order.ble_lex_impl, algebra.Order.blt_lex_impl]
                                  simp
                                  rename_i heq 
                                  split
                                  simp [heq]
                                  cases heq
                                  simp
                                  rw [Order.lex, Order.lex_impl] at h
                                  rw [Order.ble_lex_impl, algebra.Order.blt_lex_impl]
                                  split at h
                                  simp at *
                                  split at h
                                  simp at *
                                  simp
                                  split
                                  sorry
                                  sorry
                                  sorry
  rename_i n
  exact aux n v₁ v₂ h 

theorem lex_le_false_of_blt_lex_false (h: Not (Eq (Order.ble_lex_impl v₁ v₂) true)): Not (Order.lex_le v₁ v₂) :=  
  fun h' => absurd (blt_eq_true_of_lex_le h') h


instance Order.lex_decidable (v₁ v₂: Variables n order.Lex): Decidable (Order.lex_le v₁ v₂) :=
  dite (Eq (Order.blt_lex_impl v₁ v₂) true) (fun h => isTrue (lex_le_true_of_blt_lex_true h))
                                            (fun h => isFalse (lex_le_false_of_blt_lex_false h))


--# Grlex order
--# a <_grlex b ↔ |a| < |b| ∨ |a| = |b| ∧ a <_lex b 

def Order.grlex (vs₁ vs₂: Variables n order.GrLex): Prop :=
  let sum₁ := elem_sum vs₁ 
  let sum₂ := elem_sum vs₂   
  if sum₁ < sum₂ then True
  else if sum₁ = sum₂ then Order.lex vs₁ vs₂
  else False
  where
    elem_sum (vs: Variables n order.GrLex): Nat :=
      List.foldl (fun x y => x + y) 0 vs.toList

def Order.grlex_le (v₁ v₂ : Variables n order.GrLex): Prop := v₁ = v₂ ∨ Order.grlex v₁ v₂ 

private def Order.bgrlex (vs₁ vs₂: Variables n order.GrLex): Bool :=
  let sum₁ := elem_sum vs₁ 
  let sum₂ := elem_sum vs₂   
  if sum₁ < sum₂ then true
  else if sum₁ = sum₂ then Order.blt_lex_impl vs₁ vs₂
  else false
  where
    elem_sum (vs: Variables n order.GrLex): Nat :=
      List.foldl (fun x y => x + y) 0 vs.toList 

--# Ordering theorems
theorem grlex_lt_iff_le_not_le : ∀ (a b : Variables n order.GrLex), Order.grlex a b ↔ Order.grlex_le a b ∧ ¬Order.grlex_le b a := 
  by 
    intros a b 
    apply Iff.intro
    sorry
    sorry

theorem grlex_lt_refl: ∀ (a : Variables n order.GrLex), Order.grlex a a := by 
  intros a
  simp [Order.grlex]
  sorry

theorem grlex_le_refl: ∀ (a : Variables n order.GrLex), Order.grlex_le a a := by
  intros a
  rw [Order.grlex_le]
  simp

theorem grlex_lt_trans : ∀ (a b c : Variables n order.GrLex), Order.grlex a b → Order.grlex b c → Order.grlex a c := by
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
  apply lex_lt_trans
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

theorem grlex_le_trans : ∀ (a b c : Variables n order.GrLex), Order.grlex_le a b → Order.grlex_le b c → Order.grlex_le a c := by
  intros a b c ab bc
  rw [Order.grlex_le]
  rw [Order.grlex_le] at ab bc
  cases ab
  cases bc
  rename_i h₁ h₂
  rw [h₂] at h₁
  simp [h₁]
  rename_i h₁ h₂
  rw [←h₁] at h₂
  simp [h₂]
  cases bc
  rename_i h₁ h₂
  rw [h₂] at h₁
  simp [h₁]
  rename_i h₁ h₂
  apply Or.inr
  apply grlex_lt_trans a b c h₁ h₂ 

theorem grlex_lt_antisymm : ∀ (a b : Variables n order.GrLex), Order.grlex a b → Order.grlex b a → a = b := by 
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
  apply lex_lt_antisymm 
  exact ab
  exact ba
  repeat contradiction

theorem grlex_le_antisymm : ∀ (a b : Variables n order.GrLex), Order.grlex a b → Order.grlex b a → a = b := by 
  intros a b h₁ h₂
  rw [Order.grlex] at h₁ h₂
  simp at h₁ h₂
  split at h₁ 
  split at h₂
  rename_i lt₁
  have not_lt := Nat.lt_asymm lt₁
  contradiction
  split at h₂
  rename_i lt₁ nlt₂ eq
  rw [←eq] at lt₁ nlt₂
  simp at *
  contradiction
  split at h₁
  split at h₂
  rename_i nlt eq lt
  rw [eq] at lt nlt
  contradiction
  split at h₂
  apply lex_lt_antisymm a b h₁ h₂
  repeat contradiction

theorem grlex_lt_total : ∀ (a b : Variables n order.GrLex), Order.grlex a b ∨ Order.grlex b a := by 
  intros a b
  simp [Order.grlex]
  split <;> simp
  split <;> repeat (first | split | simp)
  sorry
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

theorem grlex_le_total : ∀ (a b : Variables n order.GrLex), Order.grlex_le a b ∨ Order.grlex_le b a := by 
  intros a b 
  rw [Order.grlex_le, Order.grlex_le]
  rw [or_or_or_comm]
  simp [grlex_lt_total]

theorem grlex_add_lt_add : ∀ a b c: Variables n order.GrLex, Order.grlex a b → Order.grlex (Variables.mul a c) (Variables.mul b c) := by
  intros v₁ v₂ v₃
  let rec aux (m: Nat) (a b c: Variables m order.GrLex) : Order.grlex a b → Order.grlex (Variables.mul a c) (Variables.mul b c) := by
    intros h 
    match a, b, c with
      | ⟨[], _⟩, ⟨[], _⟩, ⟨[], _⟩          => sorry
      | ⟨x::xs, p₁⟩, ⟨y::ys, p₂⟩, ⟨z::zs, p₃⟩ => sorry
  exact aux n v₁ v₂ v₃ 

--# Decidable theorems
theorem grlex_true_of_blt_grlex_true (h: Eq (Order.bgrlex v₁ v₂) true): Order.grlex v₁ v₂ := by
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

theorem grblt_eq_true_of_grlex (h: Order.grlex v₁ v₂): Eq (Order.bgrlex v₁ v₂) true := by
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

theorem grlex_false_of_blt_grlex_false (h: Not (Eq (Order.bgrlex v₁ v₂) true)): Not (Order.grlex v₁ v₂) := 
  fun h' => absurd (grblt_eq_true_of_grlex h') h
  
instance grlex_decidable (v₁ v₂: Variables n order.GrLex): Decidable (Order.grlex v₁ v₂) := 
  dite (Eq (Order.bgrlex v₁ v₂) true) (fun h => isTrue (grlex_true_of_blt_grlex_true h))
                                      (fun h => isFalse (grlex_false_of_blt_grlex_false h))

end algebra
