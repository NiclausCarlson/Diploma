import Diploma.Polynomials.Polynomials
import Diploma.Computational

namespace polynomials
 open computational in 
 def Parser (str: String) (α: Type) [ToString α] [Inhabited α] [Computational α] : Polynomial α := sorry
end polynomials
