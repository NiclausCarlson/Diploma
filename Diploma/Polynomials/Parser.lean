import Lean.Data.Parsec

import Diploma.Polynomials.Polynomial
import Diploma.Algebra.MonomialOrder
import Std.Data.List.Basic

namespace polynomial
open Lean Parsec

def Dimension := 3

private def POrdImpl (v₁ v₂ : Vector Nat n): Bool :=
  match v₁, v₂ with
    | ⟨[], _⟩  , ⟨[], _⟩   => True
    | ⟨[x], _⟩ , ⟨[y], _⟩  => x <= y
    | ⟨x::_, _⟩, ⟨y::_, _⟩ => if x = y then POrdImpl v₁.tail v₂.tail 
                              else x <= y

def POrd (m₁ m₂: Monomial n): Ordering := 
  if m₁.snd = m₂.snd then Ordering.eq
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
@[inline]
private def stayCharImpl : Parsec Char := λ it =>
  if it.hasNext then success it it.next.curr else error it unexpectedEndOfInput

@[inline]
private def stayChar (c : Char) : Parsec Char := attempt do
  if (←stayCharImpl) = c then pure c else fail s!"expected: '{c}'"

def Zero : Parsec String   := Parsec.pure "0"
def One  : Parsec String   := Parsec.pure "1"
def Deg  : Parsec String   := skipChar '^' *> ((many1Chars digit) <|> One)
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
                          let sign ← Minus <|> Plus <|> pure '1'
                          if sign == '-' then return -1
                          else return 1  

def Coeff : Parsec Int := do
                           let sign   ← Sign 
                           let number ← String.toInt! <$> ((many1Chars digit) <|> One)
                           return sign * number

def MonomialParser : Parsec (Monomial Dimension) := do
  let coeff ← Coeff
  let vars  ← many Var
  return (coeff, toVariables vars Dimension)

def PolynomialParser : Parsec (Polynomial Dimension POrd) := do
  let monomial  ← MonomialParser
  let monomials ← many MonomialParser
  return (Polynomial.of_monomial monomial POrd) +                    
         (List.foldl (fun x (y: Monomial Dimension) => 
                     x + (Polynomial.of_monomial y POrd)) 0 monomials.toList)

def parse (s: String) : Except String (Polynomial Dimension POrd) :=
  match PolynomialParser s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

def parse! (s: String) : Polynomial Dimension POrd :=
  match (parse s) with
    | .ok res  => res
    | .error err => panic! err

end polynomial
