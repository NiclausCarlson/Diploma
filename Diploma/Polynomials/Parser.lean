import Lean.Data.Parsec

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.MonomialOrder
import Std.Data.List.Basic

namespace polynomial
open Lean Parsec

def Dimension := 3

private def POrdImpl (v₁ v₂ : Vector Nat n): Bool :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => true
    | ⟨[x], _⟩ , ⟨[y], _⟩  => x <= y
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x = y then POrdImpl v₁.tail v₂.tail 
                              else x <= y

def POrd (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd == m₂.snd then Ordering.eq
  else if POrdImpl m₁.snd m₂.snd then Ordering.gt
  else Ordering.lt

structure Variable where
  deg: Nat
  name: Nat
deriving instance Inhabited for Variable
deriving instance Repr for Variable


def setI {n: Nat} (i: Nat) (value: Nat): Vector Nat n → Vector Nat n
  | ⟨l, h⟩ => ⟨List.set l i value, by simp; exact h⟩ 

def toInnerName (ch: Char) : Nat := ch.toNat - NameShift

def toVariables (vars: Array Variable) (n: Nat): Variables n := 
 impl vars.toList (get_variables n)
 where
  impl (arr: List Variable) (res: Variables n): Variables n := 
    match arr with
      | []    => res
      | [v]   => setI v.name v.deg res
      | v::vs => setI v.name v.deg (impl vs res)

open ParseResult in
open String.Iterator in
@[inline]
private def getCurr : Parsec Char := λ it =>
  if ¬(atEnd it) then success it (curr it) else error it unexpectedEndOfInput

def Zero : Parsec String := Parsec.pure "0"
def One  : Parsec String := Parsec.pure "1"

def Number: Parsec String := many1Chars digit

def Deg  : Parsec String   := (skipChar '^' *> Number) <|> One
def Var  : Parsec Variable := do
                                let name ← asciiLetter
                                let deg  ← String.toNat! <$> Deg
                                return {
                                    deg := deg
                                    name:= toInnerName name
                                }
                              
def Plus  : Parsec Char := pchar '+' 
def Minus : Parsec Char := pchar '-'

def Sign : Parsec Int := do
                          let sign ← Minus <|> Plus <|> getCurr
                          if sign == '-' then return -1
                          else return 1  

def Coeff : Parsec String := do 
                              let digits ← manyChars digit
                              if digits.isEmpty then return "1"
                              else return digits  

def Monom : Parsec (Monomial Dimension) := do
  let sign  ← ws *> Sign
  let coeff ← ws *> String.toInt! <$> (Coeff <|> One)
  let vars  ← many Var
  return (sign * coeff, toVariables vars Dimension)

def Polynom : Parsec (Polynomial Dimension POrd) := do
  let monomial  ← Monom
  let monomials ← many Monom
  return (Polynomial.of_monomial monomial POrd) +                    
         (Array.foldl (fun x (y: Monomial Dimension) => 
                          x + (Polynomial.of_monomial y POrd)) 0 monomials)

def parse (s: String) : Except String (Polynomial Dimension POrd) :=
  match Polynom s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res.Simplify
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

def parse! (s: String) : Polynomial Dimension POrd :=
  match (parse s) with
    | .ok res  => res
    | .error err => panic! err

end polynomial
