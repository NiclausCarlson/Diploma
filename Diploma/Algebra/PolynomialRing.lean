import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Fold

import Std.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Order.MonomialOrder

open polynomial
open List
open Vector
open MvPolynomial

noncomputable section 
open algebra

def zeroP (n: Nat): MvPolynomial (Fin n) Rat := 0 
def oneP (n: Nat): MvPolynomial (Fin n) Rat := 1 

def toMvMonomialImpl (vs: Vector Nat n) (idx: Nat) (real_n: Nat) : MvPolynomial (Fin real_n) Rat :=
  if h: idx < real_n then 
    match vs with
       | ⟨[], _⟩   => oneP real_n
       | ⟨a::_, _⟩ => get_p ⟨idx, h⟩ a * (toMvMonomialImpl (vs.tail) (idx+1) real_n)  
  else oneP real_n
where
  get_p (idx: Fin real_n) (deg: Nat): MvPolynomial (Fin real_n) Rat := (X idx) ^ deg

def toMvMonomial (m: Monomial n ord) : MvPolynomial (Fin n) Rat := (C m.fst) * (toMvMonomialImpl m.snd 0 n)

def toMvPolynomial [MonomialOrder $ Variables n ord] (p: Polynomial n ord): MvPolynomial (Fin n) Rat :=
  p.foldl (fun x y => x + toMvMonomial y) (zeroP n)

private def zeroPolynomial (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord]: Polynomial n ord := 0

-- We can't proof that, but we need that for Finset.fold
instance [MonomialOrder $ Variables n ord]: IsCommutative (Polynomial n ord) (Polynomial.add) where
  comm := sorry

instance [MonomialOrder $ Variables n ord]: IsAssociative (Polynomial n ord) (Polynomial.add) where
  assoc := sorry

theorem gt_ne_zero (n: Nat) (h: n > 0): n ≠ 0 := by simp; cases n; contradiction; simp  

def buildVariablesImpl (f: Fin n →₀ ℕ) (idx: Nat) (h₁: idx < n) (res: Variables n ord): Variables n ord :=
  let fin := ⟨idx, h₁⟩
  let updated := res.set fin (f.toFun fin)
  if h: idx > 0 then
    let idx_ne_zero := gt_ne_zero idx h
    let pred_idx_le_idx := Nat.pred_lt idx_ne_zero 
    let prev_idx_less_n := Nat.lt_trans pred_idx_le_idx h₁
    buildVariablesImpl f (idx - 1) prev_idx_less_n updated
  else updated

def buildVariables (f: Fin n →₀ ℕ) (ord: Type) [MonomialOrder $ Variables n ord]: Variables n ord:= 
  if h: n > 0 then
    buildVariablesImpl f (n - 1) 
                         (by cases n; contradiction; simp)
                         (get_variables n)
  else get_variables n

--def fromMvPolynomial (p: MvPolynomial (Fin n) Rat) (ord: Type) [MonomialOrder $ Variables n ord]: Polynomial n ord :=
--  Finset.fold (Polynomial.add)
--              (zeroPolynomial n ord)
--              (fun x => Polynomial.of_monomial ⟨coeff x p, buildVariables x ord⟩) p.support

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
