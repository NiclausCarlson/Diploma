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

#eval AssertEq (toString (parseVar! "a"))   "01"
#eval AssertEq (toString (parseVar! "a^5")) "05"
#eval AssertEq (toString (parseVar! "b"))   "11"
#eval AssertEq (toString (parseVar! "b^5")) "15"


--# Test monomial parsing
#eval AssertEq (toString (parseMonomial! "0"))   "0"
#eval AssertEq (toString (parseMonomial! "5"))   "5"
#eval AssertEq (toString (parseMonomial! "51"))  "51"
#eval AssertEq (toString (parseMonomial! "-5"))  "-5"
#eval AssertEq (toString (parseMonomial! "-51")) "-51"

#eval AssertEq (toString (parseMonomial! "a"))      "a"
#eval AssertEq (toString (parseMonomial! "5a"))     "5a"
#eval AssertEq (toString (parseMonomial! "b^4"))    "b^4"
#eval AssertEq (toString (parseMonomial! "5b^4"))   "5b^4"
#eval AssertEq (toString (parseMonomial! "12a^12")) "12a^12"
#eval AssertEq (toString (parseMonomial! "123a"))   "123a"

#eval AssertEq (toString (parseMonomial! "-a"))      "-a"
#eval AssertEq (toString (parseMonomial! "-5a"))     "-5a"
#eval AssertEq (toString (parseMonomial! "-b^4"))    "-b^4"
#eval AssertEq (toString (parseMonomial! "-5b^4"))   "-5b^4"
#eval AssertEq (toString (parseMonomial! "-12a^12")) "-12a^12"
#eval AssertEq (toString (parseMonomial! "-123a"))   "-123a"

#eval AssertEq (toString (parseMonomial! "a^2b^3c^5"))  "a^2b^3c^5"
#eval AssertEq (toString (parseMonomial! "-a^2b^3c^5")) "-a^2b^3c^5"


--# Test polynomial parsing
#eval AssertEq (toString (parse_lex! "0"))   "0"
#eval AssertEq (toString (parse_lex! "5"))   "5"
#eval AssertEq (toString (parse_lex! "51"))  "51"
#eval AssertEq (toString (parse_lex! "-5"))  "-5"
#eval AssertEq (toString (parse_lex! "-51")) "-51"

#eval AssertEq (toString (parse_lex! "a"))      "a"
#eval AssertEq (toString (parse_lex! "5a"))     "5a"
#eval AssertEq (toString (parse_lex! "b^4"))    "b^4"
#eval AssertEq (toString (parse_lex! "5b^4"))   "5b^4"
#eval AssertEq (toString (parse_lex! "12a^12")) "12a^12"
#eval AssertEq (toString (parse_lex! "123a"))   "123a"

#eval AssertEq (toString (parse_lex! "-a"))      "-a"
#eval AssertEq (toString (parse_lex! "-5a"))     "-5a"
#eval AssertEq (toString (parse_lex! "-b^4"))    "-b^4"
#eval AssertEq (toString (parse_lex! "-5b^4"))   "-5b^4"
#eval AssertEq (toString (parse_lex! "-12a^12")) "-12a^12"
#eval AssertEq (toString (parse_lex! "-123a"))   "-123a"

#eval AssertEq (toString (parse_lex! "12a^3+ab"))          "12a^3+ab"
#eval AssertEq (toString (parse_lex! "12a^3b^5-a^4b^7+3")) "-a^4b^7+12a^3b^5+3"
#eval AssertEq (toString (parse_lex! "a^3b^5-a^4b^7+3"))   "-a^4b^7+a^3b^5+3"

#eval AssertEq (toString (parse_lex! "     12a^3b^5 -       a^4b^7 +    3")) "-a^4b^7+12a^3b^5+3"
