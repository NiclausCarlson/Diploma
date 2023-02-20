import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Vector
import Std.Data.RBMap

import Diploma.Polynomials.PolynomialCommon

namespace polynomial

open Rat

def NameShift := 97

abbrev Polynomial (n: Nat) (cmp: Monomial n → Monomial n → Ordering) := Std.RBSet (Monomial n) cmp

instance: OfNat (Monomial n) m where
  ofNat := ⟨m, get_variables n⟩  

instance: OfNat (Polynomial n cmp) m where
  ofNat := Std.RBSet.single (m, (get_variables n))

def Simplify (p: Polynomial n cmp) : Polynomial n cmp :=
  if p.size > 1 ∧ check_coeff (p.find? 0) then p.erase (fun x => cmp 0 x)
  else p
  where 
    check_coeff (om: Option (Monomial n)): Bool := 
      match om with
      | none   => false
      | some m => m.fst == 0

def ofRat (n: Nat) (cmp: Monomial n → Monomial n → Ordering) (m : Rat) : Polynomial n cmp := 
  Std.RBSet.single (m, get_variables n)

def Polynomial.of_monomial (m: Monomial n) (cmp: Monomial n → Monomial n → Ordering): Polynomial n cmp := empty.insert m
  where 
    empty : Polynomial n cmp := {}

def Polynomial.add (p₁ p₂: Polynomial n cmp) : Polynomial n cmp := 
  Simplify (Std.RBSet.mergeWith (fun x y => (x.fst + y.fst, x.snd)) p₁ p₂)

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

def Polynomial.mul (p₁ p₂: Polynomial n cmp) : Polynomial n cmp := Simplify (monomials_mul p₁.toList p₂) 
  where 
    monomials_mul (monomials: List (Monomial n)) (p: Polynomial n cmp): Polynomial n cmp :=
      match monomials with
        | []    => p
        | [m]   => Polynomial.mul_monomial p m
        | m::ms => Polynomial.add (Polynomial.mul_monomial p m) (monomials_mul ms p)

instance: HMul (Polynomial n cmp) (Polynomial n cmp) (Polynomial n cmp) where
  hMul p₁ p₂ := Polynomial.mul p₁ p₂

instance: HSub (Polynomial n cmp) (Polynomial n cmp) (Polynomial n cmp) where
  hSub p₁ p₂ := p₁ + ((ofRat n cmp (-1)) * p₂)

section ToString

private def Variables.toStringImpl (vars: Variables n) : String := impl vars.toList 0
where 
  impl (l: List Nat) (pos: Nat) : String :=
    match l with
      | []      => ""
      | [ch]    => get_var pos ch 
      | ch::chs => (get_var pos ch) ++ impl chs (pos + 1)
  get_var (pos deg: Nat) : String :=
    if deg == 0 then ""
    else if deg == 1 then mk_str pos
    else (mk_str pos) ++ "^" ++ (toString deg)
  mk_str (pos: Nat) : String :=
    String.mk [(Char.ofNat (pos + NameShift))]

instance: ToString (Variables n) := ⟨Variables.toStringImpl⟩

instance: ToString (Monomial n) where
  toString monom := if monom.fst == 1 then toString monom.snd
                    else if monom.fst == -1 then "-" ++ toString monom.snd
                    else toString monom.fst ++ toString monom.snd

private def Monomial.toStringImpl (ms: List (Monomial n)): String := 
  match ms with
    | []     => ""
    | [m]    => toString m
    | m::ms₁ => toString m ++ Monomial.toStringImpl ms₁

instance: ToString (List (Monomial n)) := ⟨Monomial.toStringImpl⟩ 

private def MonomialsListToString (l: List (Monomial n)) : String :=
    match l with
      | []    => ""
      | [x]   => toString x
      | x::xs => toString x ++ (get_sign xs) ++ (MonomialsListToString xs)
  where
    get_sign (xs: List (Monomial n)) : String :=
      match xs with
        | []   => ""
        | [y]  => sign y
        | y::_ => sign y  
    sign (x: Monomial n) : String :=
      if x.fst >= 0 then "+"
      else ""

instance: ToString (Polynomial n cmp) where
  toString p := MonomialsListToString p.toList

end ToString
  
end polynomial