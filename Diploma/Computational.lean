
namespace Computational

  structure Computational where
    carrier: Type
    sum: carrier  → carrier  → carrier 
    sub: carrier  → carrier  → carrier 
    mul: carrier  → carrier  → carrier 
    div: carrier  → carrier  → carrier 
    pow: carrier  → Nat → carrier 

  infixl:65 " + "   => Computational.sum
  infixl:65 " - "   => Computational.sub
  infixl:70 " * "   => Computational.mul
  infixl:70 " / "   => Computational.div
  infixr:80 " ^ "   => Computational.pow

  def NatComputational: Computational := {
    carrier:=Nat,
    sum:=Nat.add,
    sub:=Nat.sub,
    mul:=Nat.mul,
    div:=Nat.div,
    pow:=Nat.pow
  }
  
  class A (α : Type) where
    sum: α → α → α 
    pow: α → α → α 

  instance [A Nat]: A Nat where
    sum x y := x + y
    pow x y := x ^ y
  
  structure B [A α] (α : Type) where
    coeff: α 

--  def f [A Nat] (a b: B Nat): Nat :=
--    A.sum a.coeff b.coeff

--  #eval f {coeff:=3} {coeff:=4}

end Computational
