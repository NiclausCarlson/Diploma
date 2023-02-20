import Diploma.tests.Common
import Diploma.Polynomials.Parser

open polynomial


def sum (p₁ p₂: String): String :=
  toString (parse! p₁ + parse! p₂)

def sub (p₁ p₂: String): String :=
  toString (parse! p₁ - parse! p₂)

def mul (p₁ p₂: String): String :=
  toString (parse! p₁ * parse! p₂)
  

--# Test sum
#eval AssertEq (sum "1" "0")                        "1"
#eval AssertEq (sum "0" "1")                        "1"
#eval AssertEq (sum "0" "2")                        "2"
#eval AssertEq (sum "2" "0")                        "2"
#eval AssertEq (sum "2" "2")                        "4"
#eval AssertEq (sum "a" "0")                        "a"
#eval AssertEq (sum "a" "a")                        "2a"
#eval AssertEq (sum "2a" "a")                       "3a"
#eval AssertEq (sum "a^4" "a")                      "a^4+a"
#eval AssertEq (sum "3a^4" "a")                     "3a^4+a"
#eval AssertEq (sum "3a^4" "a^4")                   "4a^4"
#eval AssertEq (sum "3a^4b^2" "a^4")                "3a^4b^2+a^4"
#eval AssertEq (sum "3a^4b^2+a^4b^2+10c" "a^4+15c") "4a^4b^2+a^4+25c"

--# Test sub
#eval AssertEq (sub "1" "0")                        "1"
#eval AssertEq (sub "0" "1")                        "1"
#eval AssertEq (sub "0" "2")                        "-2"
#eval AssertEq (sub "2" "0")                        "2"
#eval AssertEq (sub "2" "2")                        "0"
#eval AssertEq (sub "a" "0")                        "a"
#eval AssertEq (sub "a" "a")                        "0a"
#eval AssertEq (sub "2a" "a")                       "a"
#eval AssertEq (sub "a^4" "a")                      "a^4-a"
#eval AssertEq (sub "3a^4" "a")                     "3a^4-a"
#eval AssertEq (sub "3a^4" "a^4")                   "2a^4"
#eval AssertEq (sub "3a^4b^2" "a^4")                "3a^4b^2-a^4"
#eval AssertEq (sub "3a^4b^2+a^4b^2+10c" "a^4+15c") "4a^4b^2-a^4-5c"

--# Test mul
#eval AssertEq (mul "1" "0")                                  "0"
#eval AssertEq (mul "a" "a")                                  "a^2"
#eval AssertEq (mul "2a" "a")                                 "2a^2"
#eval AssertEq (mul "2a" "3a^5")                              "6a^6"
#eval AssertEq (mul "a+b" "a-b")                              "a^2+0ab-b^2"
#eval AssertEq (mul "a+b-c" "a-b")                            "a^2+0ab-ac-b^2+bc"
#eval AssertEq (mul "6a^7+18a^4b^2c^2-abc" "17a^18-14b^34+c") "102a^25+306a^22b^2c^2-17a^19bc-84a^7b^34+6a^7c-252a^4b^36c^2+18a^4b^2c^3+14ab^35c-abc^2"
                                                              