
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
    sub:=Nat.add,
    mul:=Nat.add,
    div:=Nat.add,
    pow:=Nat.add
  }
  
end Computational
