import Diploma.Polynomials.Parser
import Diploma.tests.Common
import Diploma.Algebra.MonomialOrder

open polynomial
open algebra

-- #eval ExpectTrue ((Ordering.lex (parseMonomial! "x")
--                                 (parseMonomial! "x")) == Ordering.eq)
