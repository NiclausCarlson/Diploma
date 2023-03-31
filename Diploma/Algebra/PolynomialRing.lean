import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.MvPolynomial.Basic

import Std.Data.List.Basic

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.MonomialOrder
import Diploma.tests.Common

open polynomial
open algebra
open List

def ms: Set Nat := {1, 2, 3}
def q := MvPolynomial ms Rat

structure NonEmptyPolynomial (n : Nat) (_cmp: Monomial n -> Monomial n -> Ordering) where
  poly: Polynomial n _cmp
  non_empty: poly.isEmpty ==  false

instance: OfNat (NonEmptyPolynomial n _cmp) m where
  ofNat := ⟨Std.RBSet.single (m, (get_variables n)), rfl⟩ 

private theorem non_empty_means_size_non_zero {p: Polynomial n _cmp} (h: p.isEmpty = false): p.size != 0:= by
  rw [Std.RBSet.isEmpty] at h
  split at h
  contradiction
  rename_i h₁
  rw [Polynomial, Std.RBSet] at p
  rename_i p₁ _
  cases p₁
  rename_i val prop
  simp [Std.RBSet.size]
  cases val
  have t := h₁ prop
  simp [t]
  rfl

def NonEmptyPolynomial.add (p₁ p₂: NonEmptyPolynomial n _cmp) : NonEmptyPolynomial n _cmp :=
  ⟨Polynomial.add p₁.poly p₂.poly,
   by rw [Polynomial.add, Polynomial.Simplify, Polynomial.Simplify.check_non_empty]
      split
      rfl
      simp at *
      rename_i h
      exact h
    ⟩   

theorem t_zero_add : ∀ (a : NonEmptyPolynomial n _cmp), NonEmptyPolynomial.add 0 a = a := by
  intros p
  cases p
  rename_i poly _
  simp [NonEmptyPolynomial.add, Polynomial.add, Polynomial.Simplify, Polynomial.Simplify.check_non_empty]
  split
  rename_i h
  simp [Std.RBSet.mergeWith] at h
  simp [Std.RBSet.find?, Std.RBNode.find?] at h
  simp [Polynomial] at poly
  simp [Polynomial]   
  sorry
  sorry
  

instance: CommRing (NonEmptyPolynomial n _cmp) where
  add p₁ p₂ := NonEmptyPolynomial.add p₁ p₂
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  add_assoc := sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  neg := sorry
  add_left_neg := sorry
  mul_comm := sorry

