import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Fold

import Std.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.MonomialOrder

open polynomial
open List
open Vector
open MvPolynomial

noncomputable section 

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

def toMvMonomial (m: Monomial n) : MvPolynomial (Fin n) Rat := (C m.fst) * (toMvMonomialImpl m.snd 0 n)

def toMvPolynomial (p: Polynomial n _cmp): MvPolynomial (Fin n) Rat :=
  p.foldl (fun x y => x + toMvMonomial y) (zeroP n)

private def zeroPolynomial (n: Nat) (_cmp: Monomial n → Monomial n → Ordering) : Polynomial n _cmp := 0

-- We can't proof that, but we need that for Finset.fold
instance: IsCommutative (Polynomial n _cmp) (Polynomial.add) where
  comm := sorry

instance: IsAssociative (Polynomial n _cmp) (Polynomial.add) where
  assoc := sorry

theorem gt_ne_zero (n: Nat) (h: n > 0): n ≠ 0 := by simp; cases n; contradiction; simp  

def buildVariablesImpl (f: Fin n →₀ ℕ) (idx: Nat) (h₁: idx < n) (res: Variables n): Variables n :=
  let fin := ⟨idx, h₁⟩
  let updated := res.set fin (f.toFun fin)
  if h: idx > 0 then
    let idx_ne_zero := gt_ne_zero idx h
    let pred_idx_le_idx := Nat.pred_lt idx_ne_zero 
    let prev_idx_less_n := Nat.lt_trans pred_idx_le_idx h₁
    buildVariablesImpl f (idx - 1) prev_idx_less_n updated
  else updated

def buildVariables (f: Fin n →₀ ℕ): Variables n := 
  if h: n > 0 then
    buildVariablesImpl f (n - 1) 
                         (by cases n; contradiction; simp)
                         (get_variables n)
  else get_variables n

def fromMvPolynomial (p: MvPolynomial (Fin n) Rat) (_cmp: Monomial n → Monomial n → Ordering): Polynomial n _cmp :=
  Finset.fold (Polynomial.add)
              (zeroPolynomial n _cmp)
              (fun x => Polynomial.of_monomial ⟨coeff x p, buildVariables x⟩ _cmp) p.support
