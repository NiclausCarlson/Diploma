import Diploma.Polynomials.Polynomial

namespace polynomial
open Nat

--# Degs
def Polynomial.multideg (p: Polynomial n cmp): Variables n := 
  if p.size != 0 then p.max!.snd
  else get_variables n 

def Polynomial.lc (p: Polynomial n cmp): Rat :=
  if p.size != 0 then p.max!.fst
  else 0

def Polynomial.lm (p: Polynomial n cmp): Monomial n :=
  if p.size != 0 then (1, p.max!.snd)
  else (1, get_variables n) 

def Polynomial.lt (p: Polynomial n cmp): Monomial n :=
  if p.size != 0 then p.max!
  else (1, get_variables n)

--# is m₁ div m₂
def is_monomials_div (m₁ m₂: Monomial n) : Bool := impl n m₁.snd m₂.snd
where 
  impl (m: Nat) (v₁ v₂: Vector Nat m) : Bool :=
    match v₁, v₂ with
    | ⟨[], _⟩   , ⟨[], _⟩    => true
    | ⟨[x], _⟩  , ⟨[y], _⟩   => y >= x
    | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => y >= x ∧ impl (m-1) ⟨xs, congrArg pred p⟩ ⟨ys, congrArg pred q⟩

open Vector in
private def Variables.div (v₁ v₂: Variables n) : Variables n := map₂ (fun x y: Nat => x - y) v₁ v₂
def Monomial.div (m₁ m₂: Monomial n): Monomial n := (m₁.fst / m₂.fst, Variables.div m₁.snd m₂.snd)  

def divide (p₁ p₂: Polynomial n cmp): Option (Polynomial n cmp) := 
  if is_monomials_div p₁.lt p₂.lt then some (Polynomial.single (Monomial.div p₁.lt p₂.lt))
  else none

structure DivisionResult (n: Nat) (cmp: Monomial n → Monomial n → Ordering) where
  p: Polynomial n cmp
  r: Polynomial n cmp

def divide_many (p: Polynomial n cmp) (ps: List (Polynomial n cmp)): DivisionResult n cmp := sorry

end polynomial
