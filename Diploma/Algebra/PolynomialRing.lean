import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.MvPolynomial.Variables

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
