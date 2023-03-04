import Diploma.Polynomials.Polynomial

namespace polynomial
open Nat

--# Degs
def Polynomial.multideg (p: Polynomial n cmp): Variables n := 
  if p.size != 0 then p.min!.snd
  else get_variables n 

def Polynomial.lc (p: Polynomial n cmp): Rat :=
  if p.size != 0 then p.min!.fst
  else 0

def Polynomial.lm (p: Polynomial n cmp): Monomial n :=
  if p.size != 0 then (1, p.min!.snd)
  else (1, get_variables n) 

def Polynomial.lt (p: Polynomial n cmp): Monomial n :=
  if p.size != 0 then p.min!
  else (1, get_variables n)

def Polynomial.Lt (p: Polynomial n cmp): Polynomial n cmp :=
  if p.size != 0 then Polynomial.single p.min!
  else Polynomial.single (1, get_variables n)

-- is m₁ divides to m₂
def Monomial.is_div (m₁ m₂: Monomial n) : Bool := impl n m₁.snd m₂.snd
where 
  impl (m: Nat) (v₁ v₂: Vector Nat m) : Bool :=
    match v₁, v₂ with
    | ⟨[], _⟩   , ⟨[], _⟩    => true
    | ⟨[x], _⟩  , ⟨[y], _⟩   => x >= y
    | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => x >= y ∧ impl (m - 1) ⟨xs, congrArg pred p⟩ ⟨ys, congrArg pred q⟩

open Vector in
private def Variables.div (v₁ v₂: Variables n) : Variables n := map₂ (fun x y: Nat => x - y) v₁ v₂
def Monomial.div (m₁ m₂: Monomial n): Monomial n := (m₁.fst / m₂.fst, Variables.div m₁.snd m₂.snd)  

structure ReduceResult (n: Nat) (cmp: Monomial n → Monomial n → Ordering) where
  reduced: Polynomial n cmp
  reducer: Polynomial n cmp

--# Reduce p₁ by p₂
def reduce_lt (p₁ p₂: Polynomial n cmp): Option (ReduceResult n cmp) := 
  if p₁.lt.is_div p₂.lt then some (impl (Polynomial.single (p₁.lt.div p₂.lt)))
  else none
  where
    impl (p: Polynomial n cmp): ReduceResult n cmp := 
      let reducer := p * p₂
      {
        reduced := p₁ - reducer,
        reducer := reducer
      }

structure DivisionResult (n: Nat) (cmp: Monomial n → Monomial n → Ordering) where
  p: Polynomial n cmp
  r: Polynomial n cmp

def divide_many (divisible: Polynomial n cmp) (dividers: List (Polynomial n cmp)): DivisionResult n cmp := 
  impl divisible dividers {p:=0, r:=0}
  where
    impl (p: Polynomial n cmp) (ps: List (Polynomial n cmp)) (step: DivisionResult n cmp): DivisionResult n cmp :=
        if p == 0 then step
        else if ps == [] then step
        else match ps with
              | []    => impl p ps step
              | a::as => match reduce_lt p a with
                          | none     => impl (p - a.Lt)  as {p := step.p, r := step.r + a.Lt}
                          | some res => impl res.reduced as {p := step.p + res.reducer, r := step.r}
    termination_by impl p ps psp => p == 0
    decreasing_by {
      simp_wf
      sorry
    }
-- ex https://leanprover-community.github.io/archive/stream/270676-lean4/topic/using.20higher-order.20functions.20on.20inductive.20types.3A.20termination.html
end polynomial
