import Lean.Data.Parsec

import Diploma.Polynomials.Parser

def AssertEq {α:Type} [BEq α] [ToString α] (a b: α): Except String String :=
  if (a != b) then Except.error ("Values: " ++ (toString a) ++ " and " ++
                                (toString b) ++ " not equals")
  else Except.ok "Ok"


def ExpectTrue (b: Bool) : Except String String:=
  if b then Except.ok "Ok"
  else Except.error "true expected"  


open polynomial in
open Lean Parsec in
def parseMonomial! (s: String) : Monomial Dimension :=
  match Monom s.mkIterator with
    | Parsec.ParseResult.success _ res => res
    | Parsec.ParseResult.error it err  => panic! s!"offset {it.i.byteIdx}: {err}"

