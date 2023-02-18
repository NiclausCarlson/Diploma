import Mathlib.Data.Vector

namespace polynomial

abbrev Variables (n: Nat) := Vector Nat n

def get_variables (n: Nat) : Variables n := (Vector.ofFn (fun _:Fin n => 0))

open Vector in
def Variables.mul (v₁ v₂: Variables n): Variables n :=
  map₂ (fun x y => x + y) v₁ v₂

abbrev Monomial (n: Nat) := Rat × (Variables n) 

instance : Inhabited (Monomial n) where
  default := (0, get_variables n)
  
end polynomial
