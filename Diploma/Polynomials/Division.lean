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

structure DivisionResult [MonomialOrder $ Variables n ord] 
                         (divisible: Polynomial n ord)
                         (dividers: List $ Polynomial n ord) where
  p: Polynomial n ord
  r: Polynomial n ord
  r_as_list: List $ Monomial n ord
  sum_eq: divisible = p + r
  correct_r: r_as_list = [] ∨ (∀m ∈ r_as_list, ∀d ∈ dividers, m.is_div d.lt == false)
  p_in_ideal: p ∈ asIdeal dividers
  r_in_ideal: divisible ∈ asIdeal dividers → r ∈ asIdeal dividers 

open Vector in
private def Variables.div (v₁ v₂: Variables n ord) : Variables n ord := map₂ (fun x y: Nat => x - y) v₁ v₂
def Monomial.div (m₁ m₂: Monomial n ord): Monomial n ord := (m₁.fst / m₂.fst, Variables.div m₁.snd m₂.snd)  

def Monomial.lcm (m₁ m₂: Monomial n ord): Monomial n ord := ⟨1, Vector.map₂ (fun x y => max x y) m₁.snd m₂.snd⟩  

def build_s_polynomial [MonomialOrder $ Variables n ord] (p₁ p₂: Polynomial n ord): Polynomial n ord :=
  (div_lcm_lt lcm p₁.lt) * p₁ - (div_lcm_lt lcm p₂.lt) * p₂
where
  lcm := Monomial.lcm (p₁.lm) (p₂.lm)
  div_lcm_lt (lcm lt: Monomial n ord): Polynomial n ord := Polynomial.single (lcm.div lt)


theorem s_poly_in_ideal [MonomialOrder $ Variables n ord] (ideal: Ideal $ Polynomial n ord)
                         : ∀p ∈ ideal, ∀ q ∈ ideal, build_s_polynomial p q ∈ ideal := by
  intros p h_in_p q h_in_q
  rw [build_s_polynomial]
  have left_mem
    : build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt p) * p ∈ ideal
  exact mul_mem_left ideal 
                     (build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt p)) 
                     h_in_p
  have right_mem
    : build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt q) * q ∈ ideal 
  exact mul_mem_left ideal 
                     (build_s_polynomial.div_lcm_lt (build_s_polynomial.lcm p q) (Polynomial.lt q)) 
                     h_in_q
  exact sub_mem left_mem right_mem  

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
                (not_div_by_zero: Not $ dividers.any (fun p => p == 0)): DivisionResult divisible dividers := 
  impl divisible dividers (by simp) 0 0 [] (by simp) (by simp) (by simp) 
  where 
    impl (p: Polynomial n ord)
         (ps: List (Polynomial n ord))
         (ps_in_dividers: ps ⊆ dividers) 
         (quotient: Polynomial n ord)
         (remainder: Polynomial n ord)
         (remainder_as_list: List $ Monomial n ord)
         (correct_remainder: remainder_as_list = [] ∨ (∀m ∈ remainder_as_list, ∀d ∈ dividers, m.is_div d.lt == false))
         (quotient_in_ideal: quotient ∈ asIdeal dividers)
         (sum_eq : divisible = p + quotient + remainder) : DivisionResult divisible dividers :=
      if h: p == 0 then let div_sum_r_eq_p := div_sum_r_eq_p divisible p quotient remainder sum_eq h
                        DivisionResult.mk 
                              quotient 
                              remainder
                              remainder_as_list 
                              div_sum_r_eq_p
                              correct_remainder
                              (by exact quotient_in_ideal)
                              (remainder_in_ideal divisible quotient remainder dividers div_sum_r_eq_p quotient_in_ideal)
      else match ps with
               | []    => impl (p - p.Lt) dividers (by simp) 
                               quotient (remainder + p.Lt) (remainder_as_list ++ [p.lt])
                               (
                                  by
                                    simp
                                    simp at *
                                    intros m in_remainders d in_dividers
                                    cases correct_remainder
                                    rename_i h
                                    simp [h] at in_remainders
                                    rw [in_remainders]
                                    sorry
                                    rename_i h
                                    cases in_remainders
                                    rename_i h₁
                                    exact h m h₁ d in_dividers 
                                    rename_i h
                                    rw [h]
                                    sorry
                               ) quotient_in_ideal
                               (erase_lt divisible p quotient remainder sum_eq)
               | a::as => if p.lt.is_div a.lt then 
                             let reducer := (Polynomial.single $ p.lt.div a.lt) * a
                             impl (p - reducer) dividers (by simp) 
                                  (quotient + reducer) remainder remainder_as_list correct_remainder
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
                                    quotient remainder remainder_as_list 
                                    correct_remainder quotient_in_ideal sum_eq                                       
     termination_by impl p ps ps_in_dividers 
                          quotient remainder remainder_as_list 
                          correct_remainder quotient_in_ideal sum_eq => p == 0
     decreasing_by {
       sorry
     }

end polynomial
