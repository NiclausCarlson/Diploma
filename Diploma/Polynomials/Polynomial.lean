import Diploma.Computational
import Mathlib.Algebra.Field.Defs

open Rat

namespace polynomial

abbrev Variables := Array Nat

def get_variables : Variables := (Array.ofFn (fun _:Fin 26 => 0))

inductive Monomial where
  | Const : Rat → Monomial
  | Monom : Rat → Variables → Monomial

inductive Polynomial where
  | Monom : Monomial → Polynomial
  | Add   : Polynomial → Polynomial → Polynomial
  | Mult  : Polynomial → Polynomial → Polynomial

instance : OfNat Monomial n where
  ofNat := Monomial.Const n

instance : OfNat Polynomial n where
  ofNat := Polynomial.Monom (Monomial.Const n)

end polynomial
