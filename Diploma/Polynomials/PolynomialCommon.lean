import Mathlib.Data.Vector

namespace polynomial

def Variables (n: Nat) (ord: Type) := Vector Nat n

def AsVector (vars: Variables n ord): Vector Nat n := vars

def get_variables (n: Nat) : Variables n ord := (Vector.ofFn (fun _:Fin n => 0))

open Vector in
def Variables.mul (v₁ v₂: Variables n ord): Variables n ord :=
  map₂ (fun x y => x + y) v₁ v₂

def Monomial (n: Nat) (ord: Type) := Rat × (Variables n ord) 

instance : Inhabited (Monomial n ord) where
  default := (0, get_variables n)

-- TODO: maybe unused
instance: BEq (Variables n ord) where
  beq v₁ v₂ := AsVector v₁ == AsVector v₂

instance: BEq (Monomial n ord) where
  beq m₁ m₂ := m₁.snd == m₂.snd

end polynomial
