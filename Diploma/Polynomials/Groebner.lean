import Diploma.Polynomials.Polynomial
import Diploma.Polynomials.DegsFunctions
import Diploma.Algebra.PolynomialRing

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

structure DivisionResult (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  p: Polynomial n ord
  r: Polynomial n ord

def build_division_remainder [MonomialOrder $ Variables n ord] (divisible: Polynomial n ord) (dividers: List (Polynomial n ord)): Polynomial n ord := 
  if dividers == [] then divisible
  else if dividers.any (fun p => p == 0) then divisible
  else impl divisible dividers 0 0 (by simp) 
  where 
    impl (p: Polynomial n ord)
         (ps: List (Polynomial n ord)) 
         (quotient: Polynomial n ord)
         (remainder: Polynomial n ord)
         (sum_eq : divisible = p + quotient + remainder) : Polynomial n ord :=
      if p == 0 then remainder
      else match ps with
               | []    => impl (p - p.Lt) dividers quotient 
                               (remainder + p.Lt) 
                               (
                                by 
                                  have h: remainder + Polynomial.Lt p = Polynomial.Lt p + remainder := 
                                    add_comm remainder (Polynomial.Lt p)
                                  have h₂: -Polynomial.Lt p + quotient = quotient + -Polynomial.Lt p :=
                                    add_comm (-Polynomial.Lt p) quotient
                                  rw [h, sub_eq_add_neg, add_assoc,
                                      add_assoc, add_comm, ←add_assoc,
                                      ←add_assoc, add_comm, h₂, add_comm, add_assoc, add_comm, 
                                      add_assoc, add_assoc, add_left_neg, add_zero, add_comm
                                      ]
                                  exact sum_eq
                               )
               | a::as => if p.lt.is_div a.lt then 
                             let reducer := (p.lt.div a.lt) * a
                             impl (p - reducer) dividers (quotient + reducer) 
                                  (remainder) 
                                  ( 
                                    by 
                                      have h: -reducer + (quotient + reducer) = (quotient + reducer) + -reducer := 
                                        add_comm (-reducer) (quotient + reducer) 
                                      rw [sub_eq_add_neg, ←add_assoc, add_comm, add_assoc,
                                          add_assoc, h, add_assoc, add_right_neg, add_zero, add_comm]
                                      exact sum_eq
                                  )
                          else impl p as quotient remainder sum_eq                                       
     termination_by impl p ps quotient remainder sum_eq => p == 0
     decreasing_by {
       sorry
     }
 
def divide_many [MonomialOrder $ Variables n ord] (divisible: Polynomial n ord) (dividers: List (Polynomial n ord)): DivisionResult n ord := 
   let remainder := build_division_remainder divisible dividers
   DivisionResult.mk (divisible - remainder) remainder

def Monomial.lcm (m₁ m₂: Monomial n ord): Monomial n ord := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord): Polynomial n ord :=
  let lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  div_lcm_lt (lcm lt: Monomial n ord): Polynomial n ord := Polynomial.single (lcm.div lt)

private def step [MonomialOrder $ Variables n ord] (p q: Polynomial n ord) (ps: List (Polynomial n ord)) : Bool × Polynomial n ord := 
  if p == q then (false, 0)
  else
    let div_result := build_division_remainder (build_s_polynomial p q) ps
    (div_result == 0, div_result)

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

def is_in_basis [MonomialOrder $ Variables n ord] (p: Polynomial n ord) (groebner_basis: List (Polynomial n ord)) : Bool :=
  (build_division_remainder p groebner_basis) == 0

end polynomial
