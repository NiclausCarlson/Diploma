import Lean.Data.Parsec

import Diploma.Polynomials.Parser

def AssertEq {α:Type} [BEq α] [ToString α] (a b: α): Except String String :=
  if a == b then Except.ok "Ok"
  else Except.error ("Values: " ++ (toString a) ++ " and " ++
                                   (toString b) ++ " not equals")

def AssertTrue (b: Bool) (msg: Option String) : Except String String :=
  if b then Except.ok "Ok"
  else match msg with
        | none   => Except.error "true expected"
        | some m => Except.error m    

def ExpectTrue (b: Bool) : Except String String := AssertTrue b none

open polynomial
open Lean Parsec 

def parseMonomial! (s: String) : Monomial Dimension order.Lex :=
  match Monom order.Lex s.mkIterator with
    | Parsec.ParseResult.success _ res => res
    | Parsec.ParseResult.error it err  => panic! s!"Error at {s}; offset {it.i.byteIdx}: {err}"

open algebra
def parse_lex!   (s: String) : Polynomial Dimension order.Lex   := parse! s order.Lex
def parse_grlex! (s: String) : Polynomial Dimension order.GrLex := parse! s order.GrLex
