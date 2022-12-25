import Diploma.Polynomials.Polynomials
import Diploma.Computational
import Lean.Data.Parsec

namespace polynomials
 open computational 
 open Lean Parsec

def DegSymbol : Parsec Unit     := skipChar '^'
def One       : Parsec String   := Parsec.pure "1"
def Deg       : Parsec String   := ws *> DegSymbol *> ws *> (manyChars digit) <|> One
def Var       : Parsec Variable := do
                                    let name ← asciiLetter
                                    let deg  ← String.toNat! <$> Deg
                                    return {
                                        deg := deg
                                        name:= toString name
                                    }
                              
def Plus   : Parsec Char := pchar '+' <|> pure '+' 
def Number : Parsec Nat  := (String.toNat! <$> ((many1Chars digit) <|> One))
def Coeff  : Parsec Nat  := Number

def MonomialParser : Parsec (Monomial Nat) := do
  let coeff ← ws *> Coeff
  let vars ← many (ws *> Var)
  return {
    coeff := coeff
    vars  := vars.toList
  }

def Poly : Parsec (Polynomial Nat) := do
                                       let monomials ← many (ws *> MonomialParser)
                                       return {
                                         monomials := monomials.toList
                                       }

def parse (s: String) : Except String ((Polynomial Nat)) :=
  match Poly s.mkIterator with
    | Parsec.ParseResult.success _ res => Except.ok res
    | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

--#eval parse "1234x^3+xy" failed with stack overflow :(

end polynomials
