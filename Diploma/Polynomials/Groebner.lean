import Diploma.Polynomials.Polynomial
import Diploma.Polynomials.DegsFunctions

namespace polynomial
open algebra

-- is m₁ divides to m₂
open Nat in
def Monomial.is_div (m₁ m₂: Monomial n ord) : Bool := impl n m₁.snd m₂.snd
where 
  impl (m: Nat) (v₁ v₂: Vector Nat m) : Bool :=
    match v₁, v₂ with
    | ⟨[], _⟩   , ⟨[], _⟩    => true
    | ⟨[x], _⟩  , ⟨[y], _⟩   => x >= y
    | ⟨x::xs, p⟩, ⟨y::ys, q⟩ => x >= y ∧ impl (m - 1) ⟨xs, congrArg pred p⟩ ⟨ys, congrArg pred q⟩

open Vector in
private def Variables.div (v₁ v₂: Variables n ord) : Variables n ord := map₂ (fun x y: Nat => x - y) v₁ v₂
def Monomial.div (m₁ m₂: Monomial n ord): Monomial n ord := (m₁.fst / m₂.fst, Variables.div m₁.snd m₂.snd)  

def Monomial.mul_p [MonomialOrder $ Variables n ord] (m: Monomial n ord) (p₂: Polynomial n ord): Polynomial n ord := p₁ * p₂
where p₁ : Polynomial n ord := Polynomial.single m

instance [MonomialOrder $ Variables n ord]: HMul (Monomial n ord) (Polynomial n ord) (Polynomial n ord) where
  hMul m p := m.mul_p p

structure ReduceResult (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  reduced: Polynomial n ord
  reducer: Polynomial n ord

-- Reduce p₁ by p₂
def reduce_lt [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord): Option (ReduceResult n ord) := 
  if p₁.lt.is_div p₂.lt then some (impl (Polynomial.single (p₁.lt.div p₂.lt)))
  else none
  where
    impl (p: Polynomial n ord): ReduceResult n ord := 
      let reducer := p * p₂
      {
        reduced := p₁ - reducer,
        reducer := reducer
      }

structure DivisionResult (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  p: Polynomial n ord
  r: Polynomial n ord

def divide_many [MonomialOrder $ Variables n ord] (divisible: Polynomial n ord) (dividers: List (Polynomial n ord)): DivisionResult n ord := 
  if dividers == [] then {p:=0, r:=0}
  else impl divisible dividers {p:=0, r:=0}
  where
    impl (p: Polynomial n ord) (ps: List (Polynomial n ord)) (step: DivisionResult n ord): DivisionResult n ord :=
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

def Monomial.lcm (m₁ m₂: Monomial n ord): Monomial n ord := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord): Polynomial n ord :=
  let lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  div_lcm_lt (lcm lt: Monomial n ord): Polynomial n ord := Polynomial.single (lcm.div lt)

private def step [MonomialOrder $ Variables n ord] (p q: Polynomial n ord) (ps: List (Polynomial n ord)) : Bool × Polynomial n ord := 
  if p == q then (false, 0)
  else
    let div_result := divide_many (build_s_polynomial p q) ps
    (div_result.r == 0, div_result.r)

private def build [MonomialOrder $ Variables n ord]
                  (e: Polynomial n ord) 
                  (ps: List (Polynomial n ord)) 
                  (dividers: List (Polynomial n ord)) : List (Polynomial n ord) := 
  match ps with
    | []    => []
    | a::as => let s := step e a dividers 
               if s.fst then build e as dividers 
               else [s.snd] ++ (build e (as ++ [s.snd]) (dividers ++ [s.snd]))
termination_by build pl result => pl == []
decreasing_by {
  simp_wf
  sorry
}

def build_groebner_basis [MonomialOrder $ Variables n ord] (pl: List (Polynomial n ord)): List (Polynomial n ord) := impl pl pl
  where 
    impl (pl: List (Polynomial n ord)) (dividers: List (Polynomial n ord)): List (Polynomial n ord) := 
      match pl with
        | []    => dividers 
        | p::ps => let res := build p ps dividers
                   impl (ps ++ res) (dividers ++ res)
    termination_by impl pl result => pl == []
    decreasing_by {
      simp_wf
      sorry
    }

def is_in [MonomialOrder $ Variables n ord] (p: Polynomial n ord) (ps: List (Polynomial n ord)) : Bool := 
  let basis := build_groebner_basis ps
  let div_res := divide_many p basis
  div_res.r == 0

def is_in_basis [MonomialOrder $ Variables n ord] (p: Polynomial n ord) (groebner_basis: List (Polynomial n ord)) : Bool :=
  (divide_many p groebner_basis).r == 0

end polynomial
