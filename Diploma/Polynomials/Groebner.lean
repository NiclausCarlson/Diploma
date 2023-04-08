import Diploma.Polynomials.Polynomial
import Diploma.Polynomials.DegsFunctions

namespace polynomial
-- is m₁ divides to m₂
open Nat in
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

structure ReduceResult (n: Nat) (_cmp: Monomial n → Monomial n → Ordering) where
  reduced: Polynomial n _cmp
  reducer: Polynomial n _cmp

-- Reduce p₁ by p₂
def reduce_lt (p₁ p₂: Polynomial n _cmp): Option (ReduceResult n _cmp) := 
  if p₁.lt.is_div p₂.lt then some (impl (Polynomial.single (p₁.lt.div p₂.lt)))
  else none
  where
    impl (p: Polynomial n _cmp): ReduceResult n _cmp := 
      let reducer := p * p₂
      {
        reduced := p₁ - reducer,
        reducer := reducer
      }

structure DivisionResult (n: Nat) (_cmp: Monomial n → Monomial n → Ordering) where
  p: Polynomial n _cmp
  r: Polynomial n _cmp

def divide_many (divisible: Polynomial n _cmp) (dividers: List (Polynomial n _cmp)): DivisionResult n _cmp := 
  if dividers == [] then {p:=0, r:=0}
  else impl divisible dividers {p:=0, r:=0}
  where
    impl (p: Polynomial n _cmp) (ps: List (Polynomial n _cmp)) (step: DivisionResult n _cmp): DivisionResult n _cmp :=
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

def Monomial.lcm (m₁ m₂: Monomial n): Monomial n := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial (p₁ p₂: Polynomial n _cmp): Polynomial n _cmp :=
  let lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  div_lcm_lt (lcm lt: Monomial n): Polynomial n _cmp := Polynomial.single (lcm.div lt)

private def step (p q: Polynomial n _cmp) (ps: List (Polynomial n _cmp)) : Bool × Polynomial n _cmp := 
  if p == q then (false, 0)
  else
    let div_result := divide_many (build_s_polynomial p q) ps
    (div_result.r == 0, div_result.r)

private def build (e: Polynomial n _cmp) (ps: List (Polynomial n _cmp)) (dividers: List (Polynomial n _cmp)) : List (Polynomial n _cmp) := 
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

def build_groebner_basis (pl: List (Polynomial n _cmp)): List (Polynomial n _cmp) := impl pl pl
  where 
    impl (pl: List (Polynomial n _cmp)) (dividers: List (Polynomial n _cmp)): List (Polynomial n _cmp) := 
      match pl with
        | []    => dividers 
        | p::ps => let res := build p ps dividers
                   impl (ps ++ res) (dividers ++ res)
    termination_by impl pl result => pl == []
    decreasing_by {
      simp_wf
      sorry
    }

def is_in (p: Polynomial n _cmp) (ps: List (Polynomial n _cmp)) : Bool := 
  let basis := build_groebner_basis ps
  let div_res := divide_many p basis
  div_res.r == 0

def is_in_basis (p: Polynomial n _cmp) (groebner_basis: List (Polynomial n _cmp)) : Bool :=
  (divide_many p groebner_basis).r == 0

end polynomial
