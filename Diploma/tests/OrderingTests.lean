import Diploma.Polynomials.Parser
import Diploma.tests.Common
import Diploma.Order.MonomialOrder

open polynomial
open algebra

#eval ExpectTrue $ Order.lex (parseMonomial! "x").snd (parseMonomial! "x^2").snd
#eval ExpectTrue $ Order.lex (parseMonomial! "xy").snd (parseMonomial! "x^2").snd
#eval ExpectTrue $ Order.lex (parseMonomial! "x").snd (parseMonomial! "xy").snd

#eval ExpectTrue $ Order.grlex (parseMonomial! "x").snd (parseMonomial! "x^2").snd
#eval ExpectTrue $ Order.grlex (parseMonomial! "x^2").snd (parseMonomial! "xyz").snd
#eval ExpectTrue $ Order.grlex (parseMonomial! "xyz").snd (parseMonomial! "x^5").snd
