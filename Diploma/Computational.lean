namespace Computational

  class Computational (α : Type) [ToString α] [Inhabited α] where
    sum: α → α → α 
    sub: α → α → α 
    mul: α → α → α 
    div: α → α → α 
    pow: α → Nat → α 

  infixl:65 " + " => Computational.sum
  infixl:65 " - " => Computational.sub
  infixl:70 " * " => Computational.mul
  infixl:70 " / " => Computational.div
  infixr:80 " ^ " => Computational.pow

  instance: Computational Nat where
    sum x y := x + y
    sub x y := x - y
    mul x y := x * y
    div x y := x / y
    pow x y := x ^ y

  instance: Computational Int where
    sum x y := x + y
    sub x y := x - y
    mul x y := x * y
    div x y := x / y
    pow x y := x ^ y
  
  instance: Computational Float where
    sum x y := x + y
    sub x y := x - y
    mul x y := x * y
    div x y := x / y
    pow x y := Float.pow x (Float.ofInt y)

end Computational
