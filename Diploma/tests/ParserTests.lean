import Lean.Data.Parsec

import Diploma.tests.Common
import Diploma.Polynomials.Parser

open polynomial
open Lean Parsec

--# Test parse sign
private def parseSign! (s: String) : Int :=
  match Sign s.mkIterator with
    | Parsec.ParseResult.success _ res => SignToInt res
    | Parsec.ParseResult.error it err  => panic! s!"offset {it.i.byteIdx}: {err}"

#eval AssertEq (toString (parseSign! "-")) "-1"
#eval AssertEq (toString (parseSign! "+")) "1"


--# Test parse variable
private def parseVar! (s: String) : Variable :=
  match Var Dimension s.mkIterator with
    | Parsec.ParseResult.success _ res => res
    | Parsec.ParseResult.error it err  => panic! s!"offset {it.i.byteIdx}: {err}"

instance : ToString Variable where
  toString var := toString var.name ++ toString var.deg

#eval AssertEq (toString (parseVar! "x0"))   "01"
#eval AssertEq (toString (parseVar! "x0^5")) "05"
#eval AssertEq (toString (parseVar! "x1"))   "11"
#eval AssertEq (toString (parseVar! "x1^5")) "15"


--# Test monomial parsing
#eval AssertEq (toString (parseMonomial! "0"))   "0"
#eval AssertEq (toString (parseMonomial! "5"))   "5"
#eval AssertEq (toString (parseMonomial! "51"))  "51"
#eval AssertEq (toString (parseMonomial! "-5"))  "-5"
#eval AssertEq (toString (parseMonomial! "-51")) "-51"

#eval AssertEq (toString (parseMonomial! "x0"))      "x0"
#eval AssertEq (toString (parseMonomial! "5x0"))     "5x0"
#eval AssertEq (toString (parseMonomial! "x1^4"))    "x1^4"
#eval AssertEq (toString (parseMonomial! "5x1^4"))   "5x1^4"
#eval AssertEq (toString (parseMonomial! "12x0^12")) "12x0^12"
#eval AssertEq (toString (parseMonomial! "123x0"))   "123x0"

#eval AssertEq (toString (parseMonomial! "-x0"))      "-x0"
#eval AssertEq (toString (parseMonomial! "-5x0"))     "-5x0"
#eval AssertEq (toString (parseMonomial! "-x1^4"))    "-x1^4"
#eval AssertEq (toString (parseMonomial! "-5x1^4"))   "-5x1^4"
#eval AssertEq (toString (parseMonomial! "-12x0^12")) "-12x0^12"
#eval AssertEq (toString (parseMonomial! "-123x0"))   "-123x0"

#eval AssertEq (toString (parseMonomial! "x0^2x1^3x2^5"))  "x0^2x1^3x2^5"
#eval AssertEq (toString (parseMonomial! "-x0^2x1^3x2^5")) "-x0^2x1^3x2^5"


--# Test polynomial parsing
#eval AssertEq (toString (parse_lex! "0"))   "0"
#eval AssertEq (toString (parse_lex! "5"))   "5"
#eval AssertEq (toString (parse_lex! "51"))  "51"
#eval AssertEq (toString (parse_lex! "-5"))  "-5"
#eval AssertEq (toString (parse_lex! "-51")) "-51"
#eval AssertNEq (parse_lex! "1") (parse_lex! "2")
#eval AssertNEq (parse_lex! "x0+1") (parse_lex! "x0+2")

#eval AssertEq (toString (parse_lex! "x0"))      "x0"
#eval AssertEq (toString (parse_lex! "5x0"))     "5x0"
#eval AssertEq (toString (parse_lex! "x1^4"))    "x1^4"
#eval AssertEq (toString (parse_lex! "5x1^4"))   "5x1^4"
#eval AssertEq (toString (parse_lex! "12x0^12")) "12x0^12"
#eval AssertEq (toString (parse_lex! "123x0"))   "123x0"

#eval AssertEq (toString (parse_lex! "-x0"))      "-x0"
#eval AssertEq (toString (parse_lex! "-5x0"))     "-5x0"
#eval AssertEq (toString (parse_lex! "-x1^4"))    "-x1^4"
#eval AssertEq (toString (parse_lex! "-5x1^4"))   "-5x1^4"
#eval AssertEq (toString (parse_lex! "-12x0^12")) "-12x0^12"
#eval AssertEq (toString (parse_lex! "-123x0"))   "-123x0"

#eval AssertEq (toString (parse_lex! "12x0^3+x0x1"))          "12x0^3+x0x1"
#eval AssertEq (toString (parse_lex! "12x0^3x1^5-x0^4x1^7+3")) "-x0^4x1^7+12x0^3x1^5+3"
#eval AssertEq (toString (parse_lex! "x0^3x1^5-x0^4x1^7+3"))   "-x0^4x1^7+x0^3x1^5+3"

#eval AssertEq (toString (parse_lex! "     12x0^3x1^5 -       x0^4x1^7 +    3")) "-x0^4x1^7+12x0^3x1^5+3"

#eval AssertEq (toString (parse_grlex! "x0^3x1^20-x0^4x1^7+3")) "x0^3x1^20-x0^4x1^7+3"
#eval AssertEq (toString (parse_grlex! "x0^3x1^2-x0^3x1x2+3"))   "x0^3x1^2-x0^3x1x2+3"
#eval AssertEq (toString (parse_grlex! "-x0^3x1x2+x0^3x1^2+3"))  "x0^3x1^2-x0^3x1x2+3"
#eval AssertEq (toString (parse_grlex! "x0^2-2x1^2+x0"))       "x0^2-2x1^2+x0"
#eval AssertEq (toString (parse_grlex! "-2x1^2+x0^2x1+x0"))      "x0^2x1-2x1^2+x0"

#eval AssertEq (toString (parse_lex_! 0 "2")) "2"
#eval AssertEq (toString (parse_lex_! 0 "2x0")) ""
#eval AssertEq (toString (parse_lex_! 1 "2x0")) "2x0"
#eval AssertEq (toString (parse_lex_! 1 "-2x0")) "-2x0"
#eval AssertEq (toString (parse_lex_! 2 "2x0x1")) "2x0x1"
#eval AssertEq (toString (parse_lex_! 5 "2x0x1x2x3x4")) "2x0x1x2x3x4"
#eval AssertEq (toString (parse_lex_! 5 "2x0x1x2x3x4+x0^8+x1")) "x0^8+2x0x1x2x3x4+x1"
