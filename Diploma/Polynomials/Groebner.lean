import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.IdealHelpers
import Diploma.Polynomials.DegsFunctions
import Diploma.Algebra.PolynomialRing

namespace polynomial
open algebra Ideal IdealHelpers

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

structure DivisionResult [MonomialOrder $ Variables n ord] 
                         (divisible: Polynomial n ord)
                         (ideal: Ideal $ Polynomial n ord) where
  p: Polynomial n ord
  r: Polynomial n ord
  sum_eq: divisible = p + r
  p_in_ideal: p ∈ ideal
  r_in_ideal: divisible ∈ ideal → r ∈ ideal 

axiom beq_eq {n:Nat} {ord: Type} [MonomialOrder $ Variables n ord]:
   ∀ p: Polynomial n ord, (p == 0) = true → p = 0

theorem div_sum_r_eq_p [MonomialOrder $ Variables n ord] 
                       (divisible p quotient remainder: Polynomial n ord)
                       (sum_eq: divisible = p + quotient + remainder)
                       (h: (p == 0) = true): divisible = quotient + remainder := 
by
  have eq_zero := beq_eq p h 
  rw [eq_zero, zero_add] at sum_eq
  exact sum_eq

theorem erase_lt [MonomialOrder $ Variables n ord] 
                       (divisible p quotient remainder: Polynomial n ord)
                       (sum_eq: divisible = p + quotient + remainder)
                       : divisible = p - Polynomial.Lt p + quotient + (remainder + Polynomial.Lt p) := 
by
  have h: remainder + Polynomial.Lt p = Polynomial.Lt p + remainder := 
    add_comm remainder (Polynomial.Lt p)
  have h₂: -Polynomial.Lt p + quotient = quotient + -Polynomial.Lt p :=
    add_comm (-Polynomial.Lt p) quotient
  rw [h, sub_eq_add_neg, add_assoc,
      add_assoc, add_comm, ←add_assoc,
      ←add_assoc, add_comm, h₂, add_comm, add_assoc, add_comm, 
      add_assoc, add_assoc, add_left_neg, add_zero, add_comm]
  exact sum_eq

theorem erase_reducer [MonomialOrder $ Variables n ord] 
                       (divisible p quotient remainder reducer: Polynomial n ord)
                       (sum_eq: divisible = p + quotient + remainder)
                       : divisible = p - reducer + (quotient + reducer) + remainder := 
by
  have h: -reducer + (quotient + reducer) = (quotient + reducer) + -reducer := 
    add_comm (-reducer) (quotient + reducer) 
  rw [sub_eq_add_neg, ←add_assoc, add_comm, add_assoc,
      add_assoc, h, add_assoc, add_right_neg, add_zero, add_comm]
  exact sum_eq

theorem zero_r_in_ideal [MonomialOrder $ Variables n ord] 
                        (divisible: Polynomial n ord)
                        (dividers: List $ Polynomial n ord) 
                        : divisible ∈ asIdeal dividers → 0 ∈ asIdeal dividers := by intros; simp
 
theorem remainder_in_ideal [MonomialOrder $ Variables n ord] 
                            (divisible quotient remainder: Polynomial n ord)
                            (dividers: List $ Polynomial n ord)
                            (div_sum_r_eq_p: divisible = quotient + remainder) 
                            (quotient_in_ideal: quotient ∈ asIdeal dividers)
                              : divisible ∈ asIdeal dividers → remainder ∈ asIdeal dividers := 
by 
  intros divisible_in_ideal
  have r_eq: remainder = divisible - quotient
  rw [div_sum_r_eq_p, add_comm, sub_eq_add_neg, add_assoc,
      add_comm, add_right_neg, zero_add]
  rw [r_eq]
  exact sub_mem divisible_in_ideal quotient_in_ideal

def divide_many [MonomialOrder $ Variables n ord] 
                (divisible: Polynomial n ord) 
                (dividers: List $ Polynomial n ord)
                (dividers_non_empty: Not (dividers == []))
                (not_div_by_zero: Not $ dividers.any (fun p => p == 0)): DivisionResult divisible (asIdeal dividers) := 
  impl divisible dividers (by simp) 0 0 (by simp) (by simp) 
  where 
    impl (p: Polynomial n ord)
         (ps: List (Polynomial n ord))
         (ps_in_dividers: ps ⊆ dividers) 
         (quotient: Polynomial n ord)
         (remainder: Polynomial n ord)
         (quotient_in_ideal: quotient ∈ asIdeal dividers)
         (sum_eq : divisible = p + quotient + remainder) : DivisionResult divisible (asIdeal dividers) :=
      if h: p == 0 then let div_sum_r_eq_p := div_sum_r_eq_p divisible p quotient remainder sum_eq h
                        DivisionResult.mk 
                              quotient 
                              remainder 
                              div_sum_r_eq_p
                              (by exact quotient_in_ideal)
                              (remainder_in_ideal divisible quotient remainder dividers div_sum_r_eq_p quotient_in_ideal)
      else match ps with
               | []    => impl (p - p.Lt) dividers (by simp) quotient (remainder + p.Lt) quotient_in_ideal
                               (erase_lt divisible p quotient remainder sum_eq)
               | a::as => if p.lt.is_div a.lt then 
                             let reducer := (Polynomial.single $ p.lt.div a.lt) * a
                             impl (p - reducer) dividers (by simp) (quotient + reducer) remainder 
                                  (
                                    by 
                                      have a_in_ideal: a ∈ asIdeal dividers 
                                      have a_in_dividers: a ∈ dividers
                                      simp [HasSubset.Subset, List.Subset] at ps_in_dividers
                                      have left := ps_in_dividers.left
                                      exact left
                                      have in_ideal := listInIdeal dividers a a_in_dividers
                                      exact in_ideal
                                      have reducer_in_ideal : ((Polynomial.single $ Monomial.div (Polynomial.lt p) (Polynomial.lt a)) * a) ∈ asIdeal dividers
                                      exact mul_mem_left (asIdeal dividers) (Polynomial.single $ Monomial.div (Polynomial.lt p) (Polynomial.lt a)) a_in_ideal
                                      exact add_mem quotient_in_ideal reducer_in_ideal
                                  )
                                  (erase_reducer divisible p quotient remainder reducer sum_eq)
                          else impl p as
                                    (
                                      by 
                                        simp [HasSubset.Subset, List.Subset] at ps_in_dividers
                                        have right := ps_in_dividers.right  
                                        exact right
                                    )
                                    quotient remainder quotient_in_ideal sum_eq                                       
     termination_by impl p ps ps_in_dividers quotient remainder quotient_in_ideal sum_eq => p == 0
     decreasing_by {
       sorry
     }

def Monomial.lcm (m₁ m₂: Monomial n ord): Monomial n ord := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord): Polynomial n ord :=
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  div_lcm_lt (lcm lt: Monomial n ord): Polynomial n ord := Polynomial.single (lcm.div lt)

private def step [MonomialOrder $ Variables n ord]
                 (p q: Polynomial n ord)
                 (ps: List (Polynomial n ord)) : Bool × Polynomial n ord := 
  if p == q then (true, 0)
  else if h₁: ps == [] then (true, 0)
  else if h₂: ps.any (fun p => p == 0) then (true, 0)
  else
    let div_result := divide_many (build_s_polynomial p q) ps h₁ h₂
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

theorem sufficiency_poly_in_ideal [MonomialOrder $ Variables n ord] 
                                  (p: Polynomial n ord)
                                  (dividers: List $ Polynomial n ord)
                                  (dividers_non_empty: Not $ dividers == [])
                                  (not_div_by_zero: Not $ dividers.any (fun p => p == 0))
                                  (div_res : DivisionResult p (asIdeal dividers))
                                  (h: div_res = divide_many p dividers dividers_non_empty not_div_by_zero)
                                    : div_res.r = 0 → p ∈ asIdeal dividers :=
by
  intros is_zero
  cases div_res
  rename_i q r sum_eq p_in_ideal r_in_ideal
  simp at *
  simp [is_zero] at sum_eq
  rw [sum_eq]
  exact p_in_ideal

def is_in_basis [MonomialOrder $ Variables n ord]
                (p: Polynomial n ord)
                (groebner_basis: List (Polynomial n ord))
                (dividers_non_empty: Not $ groebner_basis == [])
                (not_div_by_zero: Not $ groebner_basis.any (fun p => p == 0)) : Bool :=
  (divide_many p groebner_basis dividers_non_empty not_div_by_zero).r == 0

end polynomial
