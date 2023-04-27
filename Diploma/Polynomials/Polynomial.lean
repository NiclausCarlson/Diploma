import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Vector
import Std.Data.RBMap

import Diploma.Polynomials.PolynomialCommon
import Diploma.Order.MonomialOrderInterface

namespace polynomial

open Nat Rat algebra

def Polynomial (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] := Std.RBSet (Monomial n ord) ordering.m_cmp

def AsRBSet [MonomialOrder $ Variables n ord] (p: Polynomial n ord) : Std.RBSet (Monomial n ord) ordering.m_cmp:= p

def Polynomial.single [MonomialOrder $ Variables n ord] (m: Monomial n ord): Polynomial n ord := Std.RBSet.single m 

instance: OfNat (Monomial n ord) m where
  ofNat := ⟨m, get_variables n⟩  

instance [MonomialOrder $ Variables n ord]: OfNat (Polynomial n ord) m where
  ofNat := Std.RBSet.single (m, (get_variables n))

instance [MonomialOrder $ Variables n ord]: EmptyCollection (Polynomial n ord) where
  emptyCollection := Std.RBSet.empty

instance [MonomialOrder $ Variables n ord]: BEq (Polynomial n ord) where
  beq p₁ p₂ := if AsRBSet p₁ == AsRBSet 0 ∧ AsRBSet p₂ == AsRBSet 0 then p₁.max!.fst == p₂.max!.fst
               else  AsRBSet p₁ == AsRBSet p₂

def Polynomial.Simplify [MonomialOrder $ Variables n ord] (p: Polynomial n ord) : Polynomial n ord := 
  check_non_empty (Std.RBSet.filter p (fun x => x.fst != 0))
  where 
    check_non_empty (p: Polynomial n ord): Polynomial n ord :=
      if p.isEmpty then 0
      else p

def ofRat (n: Nat) (ord: Type) (m : Rat) [MonomialOrder $ Variables n ord] : Polynomial n ord := 
  Std.RBSet.single (m, get_variables n)

def Polynomial.of_monomial (m: Monomial n ord) [MonomialOrder $ Variables n ord]: Polynomial n ord := empty.insert m
  where 
    empty : Polynomial n ord := {}

def Polynomial.add [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord) : Polynomial n ord := 
  Simplify (Std.RBSet.mergeWith (fun x y => (x.fst + y.fst, x.snd)) p₁ p₂)

instance [MonomialOrder $ Variables n ord]: HAdd (Polynomial n ord) (Polynomial n ord) (Polynomial n ord) where
  hAdd p₁ p₂ := Polynomial.add p₁ p₂  

def Monomial.mul (m₁ m₂: Monomial n ord) : Monomial n ord :=
  (m₁.fst * m₂.fst, Variables.mul m₁.snd m₂.snd)

def Polynomial.mul_monomial [MonomialOrder $ Variables n ord] (p : Polynomial n ord) (m: Monomial n ord) : Polynomial n ord :=
  monomials_mul p.toList m
  where 
    monomials_mul (monomials: List (Monomial n ord)) (m: Monomial n ord) : Polynomial n ord :=
      match monomials with
        | []     => 0
        | [m₁]   => Std.RBSet.single (Monomial.mul m₁ m)
        | m₁::ms => Polynomial.add (Std.RBSet.single (Monomial.mul m₁ m)) (monomials_mul ms m)

def Polynomial.mul [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord) : Polynomial n ord := Simplify (monomials_mul p₁.toList p₂) 
  where 
    monomials_mul (monomials: List (Monomial n ord)) (p: Polynomial n ord): Polynomial n ord :=
      match monomials with
        | []    => p
        | [m]   => Polynomial.mul_monomial p m
        | m::ms => Polynomial.add (Polynomial.mul_monomial p m) (monomials_mul ms p)

instance [MonomialOrder $ Variables n ord]: HMul (Polynomial n ord) (Polynomial n ord) (Polynomial n ord) where
  hMul p₁ p₂ := Polynomial.mul p₁ p₂

def Polynomial.invert_sign [MonomialOrder $ Variables n ord] (p: Polynomial n ord): Polynomial n ord := (ofRat n ord (-1)) * p

instance [MonomialOrder $ Variables n ord]: HSub (Polynomial n ord) (Polynomial n ord) (Polynomial n ord) where
  hSub p₁ p₂ := p₁ + p₂.invert_sign

def Polynomial.eval [MonomialOrder $ Variables n ord] (p: Polynomial n ord) (v: Vector Rat n): Rat :=
  p.foldl (fun res m => res + m.fst * (eval_subst m.snd v) 1) 0 
where
  eval_subst {m: Nat} (vars: Variables m ord) (v: Vector Rat m) (res: Rat): Rat := 
    match vars, v with
      | ⟨[], _⟩  , ⟨[], _⟩   => res
      | ⟨x::_, _⟩, ⟨y::_, _⟩ => (eval_subst vars.tail v.tail (res * (y^x)))

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
  mk_str (pos: Nat) : String := s!"x{pos}"

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

instance [MonomialOrder $ Variables n ord]: ToString (Polynomial n ord) where
  toString p := MonomialsListToString p.toList

end ToString
  
end polynomial
