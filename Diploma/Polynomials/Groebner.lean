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
  if dividers == [] then {p:=0, r:=0}
  else impl divisible dividers {p:=0, r:=0}
  where
    impl (p: Polynomial n cmp) (ps: List (Polynomial n cmp)) (step: DivisionResult n cmp): DivisionResult n cmp :=
        if p == 0 then step
        else match ps with
              | []    => let r := step.r + p.Lt
                         let new_p := p - p.Lt
                         impl new_p dividers {p := step.p, r := r}
              | a::as => match reduce_lt p a with
                          | none     => impl p as step
                          | some res => impl res.reduced dividers {p := step.p + res.reducer, r := step.r}
    termination_by impl p ps psp => p == 0
    decreasing_by {
      simp_wf
      sorry
    }
-- ex https://leanprover-community.github.io/archive/stream/270676-lean4/topic/using.20higher-order.20functions.20on.20inductive.20types.3A.20termination.html

def Monomial.lcm (m₁ m₂: Monomial n): Monomial n := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial (p₁ p₂: Polynomial n cmp): Polynomial n cmp :=
  let lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  div_lcm_lt (lcm lt: Monomial n): Polynomial n cmp := Polynomial.single (lcm.div lt)

private def step (p q: Polynomial n cmp) (ps: List (Polynomial n cmp)) : Bool × Polynomial n cmp := 
  if p == q then (false, 0)
  else
    let div_result := divide_many (build_s_polynomial p q) ps
    (div_result.r == 0, div_result.r)

private def build (e: Polynomial n cmp) (ps: List (Polynomial n cmp)) (result: List (Polynomial n cmp)) : List (Polynomial n cmp) := 
  match result with
    | []    => result
    | a::as => let s := step e a as 
               if s.fst then build e ps result
               else [s.snd] ++ build e (ps ++ [s.snd]) as
termination_by build pl result => pl == []
decreasing_by {
  simp_wf
  sorry
}

def build_groebner_basis (pl: List (Polynomial n cmp)): List (Polynomial n cmp) := 
  match pl with
    | []    => []
    | a::as => impl as [a]
  where 
    impl (pl: List (Polynomial n cmp)) (result: List (Polynomial n cmp)): List (Polynomial n cmp) := 
      match pl with
        | []    => result 
        | p::ps => impl (ps ++ (build p result ps)) (result ++ [p])
    termination_by impl pl result => pl == []
    decreasing_by {
      simp_wf
      sorry
    }

end polynomial
