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
  match Var s.mkIterator with
    | Parsec.ParseResult.success _ res => res
    | Parsec.ParseResult.error it err  => panic! s!"offset {it.i.byteIdx}: {err}"

instance : ToString Variable where
  toString var := toString var.name ++ toString var.deg

#eval AssertEq (toString (parseVar! "x"))   "01"
#eval AssertEq (toString (parseVar! "x^5")) "05"
#eval AssertEq (toString (parseVar! "y"))   "11"
#eval AssertEq (toString (parseVar! "y^5")) "15"


--# Test monomial parsing
#eval AssertEq (toString (parseMonomial! "0"))   "0"
#eval AssertEq (toString (parseMonomial! "5"))   "5"
#eval AssertEq (toString (parseMonomial! "51"))  "51"
#eval AssertEq (toString (parseMonomial! "-5"))  "-5"
#eval AssertEq (toString (parseMonomial! "-51")) "-51"

#eval AssertEq (toString (parseMonomial! "x"))      "x"
#eval AssertEq (toString (parseMonomial! "5x"))     "5x"
#eval AssertEq (toString (parseMonomial! "y^4"))    "y^4"
#eval AssertEq (toString (parseMonomial! "5y^4"))   "5y^4"
#eval AssertEq (toString (parseMonomial! "12x^12")) "12x^12"
#eval AssertEq (toString (parseMonomial! "123x"))   "123x"

#eval AssertEq (toString (parseMonomial! "-x"))      "-x"
#eval AssertEq (toString (parseMonomial! "-5x"))     "-5x"
#eval AssertEq (toString (parseMonomial! "-y^4"))    "-y^4"
#eval AssertEq (toString (parseMonomial! "-5y^4"))   "-5y^4"
#eval AssertEq (toString (parseMonomial! "-12x^12")) "-12x^12"
#eval AssertEq (toString (parseMonomial! "-123x"))   "-123x"

#eval AssertEq (toString (parseMonomial! "x^2y^3z^5"))  "x^2y^3z^5"
#eval AssertEq (toString (parseMonomial! "-x^2y^3z^5")) "-x^2y^3z^5"


--# Test polynomial parsing
#eval AssertEq (toString (parse_lex! "0"))   "0"
#eval AssertEq (toString (parse_lex! "5"))   "5"
#eval AssertEq (toString (parse_lex! "51"))  "51"
#eval AssertEq (toString (parse_lex! "-5"))  "-5"
#eval AssertEq (toString (parse_lex! "-51")) "-51"

#eval AssertEq (toString (parse_lex! "x"))      "x"
#eval AssertEq (toString (parse_lex! "5x"))     "5x"
#eval AssertEq (toString (parse_lex! "y^4"))    "y^4"
#eval AssertEq (toString (parse_lex! "5y^4"))   "5y^4"
#eval AssertEq (toString (parse_lex! "12x^12")) "12x^12"
#eval AssertEq (toString (parse_lex! "123x"))   "123x"

#eval AssertEq (toString (parse_lex! "-x"))      "-x"
#eval AssertEq (toString (parse_lex! "-5x"))     "-5x"
#eval AssertEq (toString (parse_lex! "-y^4"))    "-y^4"
#eval AssertEq (toString (parse_lex! "-5y^4"))   "-5y^4"
#eval AssertEq (toString (parse_lex! "-12x^12")) "-12x^12"
#eval AssertEq (toString (parse_lex! "-123x"))   "-123x"

#eval AssertEq (toString (parse_lex! "12x^3+xy"))          "12x^3+xy"
#eval AssertEq (toString (parse_lex! "12x^3y^5-x^4y^7+3")) "-x^4y^7+12x^3y^5+3"
#eval AssertEq (toString (parse_lex! "x^3y^5-x^4y^7+3"))   "-x^4y^7+x^3y^5+3"

#eval AssertEq (toString (parse_lex! "     12x^3y^5 -       x^4y^7 +    3")) "-x^4y^7+12x^3^5+3"

#eval AssertEq (toString (parse_grlex! "x^3y^20-x^4y^7+3")) "x^3y^20-x^4y^7+3"
#eval AssertEq (toString (parse_grlex! "x^3y^2-x^3yz+3"))   "x^3y^2-x^3yz+3"
#eval AssertEq (toString (parse_grlex! "-x^3yz+x^3y^2+3"))  "x^3y^2-x^3yz+3"
#eval AssertEq (toString (parse_grlex! "x^2-2y^2+x"))       "x^2-2y^2+x"
