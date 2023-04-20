import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Vector
import Std.Data.RBMap

import Diploma.Polynomials.PolynomialCommon

namespace polynomial

open Nat
open Rat

def NameShift := 120

def Polynomial (n: Nat) (ord: Type) (cmp: Monomial n ord → Monomial n ord → Ordering) := Std.RBSet (Monomial n ord) cmp

def AsRBSet (p: Polynomial n ord _cmp) : Std.RBSet (Monomial n ord) _cmp := p

def Polynomial.single (m: Monomial n ord): Polynomial n ord _cmp := Std.RBSet.single m 

instance: OfNat (Monomial n ord) m where
  ofNat := ⟨m, get_variables n⟩  

instance: OfNat (Polynomial n ord _cmp) m where
  ofNat := Std.RBSet.single (m, (get_variables n))

instance: EmptyCollection (Polynomial n ord _cmp) where
  emptyCollection := Std.RBSet.empty

instance: BEq (Polynomial n ord _cmp) where
  beq p₁ p₂ := if AsRBSet p₁ == AsRBSet 0 ∧ AsRBSet p₂ == AsRBSet 0 then p₁.max!.fst == p₂.max!.fst
               else  AsRBSet p₁ == AsRBSet p₂

def Polynomial.Simplify (p: Polynomial n ord _cmp) : Polynomial n ord _cmp := 
  check_non_empty (Std.RBSet.filter p (fun x => x.fst != 0))
  where 
    check_non_empty (p: Polynomial n ord _cmp): Polynomial n ord _cmp :=
      if p.isEmpty then 0
      else p

def ofRat (n: Nat) (cmp: Monomial n ord → Monomial n ord → Ordering) (m : Rat) : Polynomial n ord cmp := 
  Std.RBSet.single (m, get_variables n)

def Polynomial.of_monomial (m: Monomial n ord) (cmp: Monomial n ord → Monomial n ord → Ordering): Polynomial n ord cmp := empty.insert m
  where 
    empty : Polynomial n ord cmp := {}

def Polynomial.add (p₁ p₂: Polynomial n ord _cmp) : Polynomial n ord _cmp := 
  Simplify (Std.RBSet.mergeWith (fun x y => (x.fst + y.fst, x.snd)) p₁ p₂)

instance: HAdd (Polynomial n ord _cmp) (Polynomial n ord _cmp) (Polynomial n ord _cmp) where
  hAdd p₁ p₂ := Polynomial.add p₁ p₂  

def Monomial.mul (m₁ m₂: Monomial n ord) : Monomial n ord :=
  (m₁.fst * m₂.fst, Variables.mul m₁.snd m₂.snd)

def Polynomial.mul_monomial (p : Polynomial n ord _cmp) (m: Monomial n ord) : Polynomial n ord _cmp :=
  monomials_mul p.toList m
  where 
    monomials_mul (monomials: List (Monomial n ord)) (m: Monomial n ord) : Polynomial n ord _cmp :=
      match monomials with
        | []     => 0
        | [m₁]   => Std.RBSet.single (Monomial.mul m₁ m)
        | m₁::ms => Polynomial.add (Std.RBSet.single (Monomial.mul m₁ m)) (monomials_mul ms m)

def Polynomial.mul (p₁ p₂: Polynomial n ord _cmp) : Polynomial n ord _cmp := Simplify (monomials_mul p₁.toList p₂) 
  where 
    monomials_mul (monomials: List (Monomial n ord)) (p: Polynomial n ord _cmp): Polynomial n ord _cmp :=
      match monomials with
        | []    => p
        | [m]   => Polynomial.mul_monomial p m
        | m::ms => Polynomial.add (Polynomial.mul_monomial p m) (monomials_mul ms p)

instance: HMul (Polynomial n ord _cmp) (Polynomial n ord _cmp) (Polynomial n ord _cmp) where
  hMul p₁ p₂ := Polynomial.mul p₁ p₂

def Polynomial.invert_sign (p: Polynomial n ord _cmp): Polynomial n ord _cmp := (ofRat n _cmp (-1)) * p

instance: HSub (Polynomial n ord _cmp) (Polynomial n ord _cmp) (Polynomial n ord _cmp) where
  hSub p₁ p₂ := p₁ + p₂.invert_sign

section Eval

def Polynomial.eval (p: Polynomial n ord _cmp) (v: Vector Rat n): Rat :=
  p.foldl (fun res m => res + m.fst * (eval_subst m.snd v) 1) 0 
where
  eval_subst {m: Nat} (vars: Variables m ord) (v: Vector Rat m) (res: Rat): Rat := 
    match vars, v with
      | ⟨[], _⟩  , ⟨[], _⟩   => res
      | ⟨x::_, _⟩, ⟨y::_, _⟩ => (eval_subst vars.tail v.tail (res * (y^x)))

end Eval

section ToString

private def Variables.toStringImpl (vars: Variables n ord) : String := impl vars.toList 0
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

instance: ToString (Variables n ord) := ⟨Variables.toStringImpl⟩

private def Monomial.is_empty (m: Monomial n ord): Bool :=
  m.snd.toList.foldl (fun x y => x ∧ y == 0) true

instance: ToString (Monomial n ord) where
  toString monom := if monom.fst == 1 ∧ !monom.is_empty then toString monom.snd
                    else if monom.fst == -1 ∧ !monom.is_empty then "-" ++ toString monom.snd
                    else toString monom.fst ++ toString monom.snd

private def Monomial.toStringImpl (ms: List (Monomial n ord)): String := 
  match ms with
    | []     => ""
    | [m]    => toString m
    | m::ms₁ => toString m ++ Monomial.toStringImpl ms₁

instance: ToString (List (Monomial n ord)) := ⟨Monomial.toStringImpl⟩ 

private def MonomialsListToString (l: List (Monomial n ord)) : String :=
    match l with
      | []    => ""
      | [x]   => toString x
      | x::xs => toString x ++ (get_sign xs) ++ (MonomialsListToString xs)
  where
    get_sign (xs: List (Monomial n ord)) : String :=
      match xs with
        | []   => ""
        | [y]  => sign y
        | y::_ => sign y  
    sign (x: Monomial n ord) : String :=
      if x.fst >= 0 then "+"
      else ""

instance: ToString (Polynomial n ord _cmp) where
  toString p := MonomialsListToString p.toList

end ToString
  
end polynomial
