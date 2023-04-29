import Mathlib.RingTheory.Ideal.Basic

import Diploma.Algebra.PolynomialRing
import Diploma.Polynomials.Groebner

open polynomial algebra

def asSet [MonomialOrder $ Variables n ord] 
          (ps: List $ Polynomial n ord): Set $ Polynomial n ord := impl ps ∅
where impl (l: List $ Polynomial n ord) (set: Set $ Polynomial n ord): Set $ Polynomial n ord :=
  match l with
    | [] => set
    | x::xs => impl xs (set.insert x)

def asIdeal [MonomialOrder $ Variables n ord] 
            (l: List $ Polynomial n ord):
            Ideal $ Polynomial n ord := Ideal.span $ asSet l

namespace profs
open Ideal
theorem s_poly_in_ideal [MonomialOrder $ Variables n ord] 
                        (i: Ideal $ Polynomial n ord)
                        (p q: Polynomial n ord)
                        (h₁: p ∈ i)
                        (h₂: q ∈ i) : build_s_polynomial p q ∈ i :=
by
  rw [build_s_polynomial]
  have lcm := Monomial.lcm (Polynomial.lm p) (Polynomial.lm q)
  have sub_left := build_s_polynomial.div_lcm_lt lcm (Polynomial.lt p)
  have left := sub_left * p
  have left_in_ideal := mul_mem_left i sub_left h₁
  have sub_right := -build_s_polynomial.div_lcm_lt lcm (Polynomial.lt q)
  have right := sub_right * q
  have right_in_ideal := mul_mem_left i sub_right h₂
  --exact add_mem left_in_ideal right_in_ideal
  sorry

theorem remainder_in_ideal [MonomialOrder $ Variables n ord] 
                           (i: List $ Polynomial n ord)
                           (p: Polynomial n ord)
                           (h: p ∈ i) 
                           (div_res: DivisionResult p)
                           (hh: div_res = divide_many p i): div_res.r ∈ asIdeal i := 
by
  cases div_res
  rename_i divisible_ p₁ r sum_eq
  simp at * 
  sorry


structure GroebnerBasis (n: Nat) (ord: Type) [MonomialOrder $ Variables n ord] where
  basis : List $ Polynomial n ord
  buchberger_criterion : ∀ p ∈ basis, ∀ q ∈ basis, p ≠ q → (divide_many (build_s_polynomial p q) basis).r = 0

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

end profs
