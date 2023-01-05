import Diploma.Computational
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic

open Rat

namespace polynomial

def Variables (n: Nat) := Vector Nat n

def get_variables : Variables (n: Nat) := (Vector.ofFn (fun _:Fin n => 0))

inductive Monomial (n : Nat) where
  | Const : Rat → Monomial n
  | Monom : Rat → Variables n → Monomial n

inductive Polynomial (n : Nat) where
  | Monom : Monomial n → Polynomial n
  | Add   : Polynomial n → Polynomial n → Polynomial n

instance : OfNat (Monomial n) m where
  ofNat := Monomial.Const m

instance : OfNat (Polynomial n) m where
  ofNat := Polynomial.Monom (Monomial.Const m)

private def rat_pow (q: Rat) (n: Nat): Rat :=
  match n with
    | Nat.zero => 1
    | Nat.succ m => q * rat_pow q m

instance: HPow Rat Nat Rat where
  hPow q n := rat_pow q n

open Vector in
def substitute (vs: Variables n) (vars: Vector Rat n) : Rat := sum (subst vs vars).toList
  where
    subst (vs: Variables n) (vars: Vector Rat n) : Vector Rat n := 
      map₂ (fun (x: Rat) (y: Nat) => x ^ y) vars vs
    sum (vs: List Rat): Rat :=
      match vs with
        | [] => 0
        | [x] => x
        | x::xs => x + sum xs
 
def m_eval (m: Monomial n) (vars: Vector Rat n) : Rat :=
  match m with
    | Monomial.Const c => c  
    | Monomial.Monom c vs => c * (substitute vs vars)

def eval (p : Polynomial n) (vars: Vector Rat n): Rat := 
  match p with 
    | Polynomial.Monom m => m_eval m vars
    | Polynomial.Add p₁ p₂ => (eval p₁ vars) + (eval p₂ vars)

end polynomial
