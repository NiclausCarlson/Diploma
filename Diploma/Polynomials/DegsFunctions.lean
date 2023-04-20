import Diploma.Polynomials.Polynomial

namespace polynomial

def Polynomial.multideg (p: Polynomial n ord _cmp): Variables n ord := 
  if p.size != 0 then p.min!.snd
  else get_variables n 

def Polynomial.lc (p: Polynomial n ord _cmp): Rat :=
  if p.size != 0 then p.min!.fst
  else 0

def Polynomial.lm (p: Polynomial n ord _cmp): Monomial n ord :=
  if p.size != 0 then (1, p.min!.snd)
  else (1, get_variables n) 

def Polynomial.lt (p: Polynomial n ord _cmp): Monomial n ord :=
  if p.size != 0 then p.min!
  else (1, get_variables n)

def Polynomial.Lt (p: Polynomial n ord _cmp): Polynomial n ord _cmp :=
  if p.size != 0 then Polynomial.single p.min!
  else Polynomial.single (1, get_variables n)

end polynomial
