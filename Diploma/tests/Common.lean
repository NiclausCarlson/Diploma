
def AssertEq {α:Type} [BEq α] [ToString α] (a b: α): String :=
  if (a != b) then "Values: " ++ (toString a) ++ " and " ++
                    (toString b) ++ " not equals"
  else "Ok"


