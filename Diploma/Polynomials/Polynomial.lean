import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Vector
import Std.Data.RBMap

import Diploma.Polynomials.PolynomialCommon

namespace polynomial

open Rat

abbrev Polynomial (n: Nat) (cmp: (Monomial n) → (Monomial n) → Ordering) := Std.RBSet (Monomial n) cmp

instance: OfNat (Polynomial n cmp) m where
  ofNat := Std.RBSet.single (m, (get_variables n))

def Polynomial.add (p₁ p₂: Polynomial n cmp) : Polynomial n cmp := 
  Std.RBSet.mergeWith (fun x y => (x.fst + y.fst, x.snd)) p₁ p₂

instance: HAdd (Polynomial n cmp) (Polynomial n cmp) (Polynomial n cmp) where
  hAdd p₁ p₂ := Polynomial.add p₁ p₂  


def Monomial.mul (m₁ m₂: Monomial n) : Monomial n :=
  (m₁.fst * m₂.fst, Variables.mul m₁.snd m₂.snd)

def Polynomial.mul_monomial (p : Polynomial n cmp) (m: Monomial n) : Polynomial n cmp :=
  monomials_mul p.toList m
  where 
    monomials_mul (monomials: List (Monomial n)) (m: Monomial n) : Polynomial n cmp :=
      match monomials with
        | []     => 0
        | [m₁]   => Std.RBSet.single (Monomial.mul m₁ m)
        | m₁::ms => Polynomial.add (Std.RBSet.single (Monomial.mul m₁ m)) (monomials_mul ms m)

def Polynomial.mul (p₁ p₂: Polynomial n cmp) : Polynomial n cmp := monomials_mul p₁.toList p₂ 
  where 
    monomials_mul (monomials: List (Monomial n)) (p: Polynomial n cmp): Polynomial n cmp :=
      match monomials with
        | []    => p
        | [m]   => Polynomial.mul_monomial p m
        | m::ms => Polynomial.add (Polynomial.mul_monomial p m) (monomials_mul ms p)

instance: HMul (Polynomial n cmp) (Polynomial n cmp) (Polynomial n cmp) where
  hMul p₁ p₂ := Polynomial.mul p₁ p₂

  
end polynomial
