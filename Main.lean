import Diploma.Polynomials.Polynomial
import Diploma.Interactive.Interactive

open BaseIO IO interactive

open EvalResult in
partial def run (stdin: FS.Stream) (dimension: Nat) : IO Unit := do
   let line ← IO.FS.Stream.getLine stdin
   let parsed := eval line dimension
   match parsed with
    | Except.ok res => match res with
                        | none     => return
                        | some val => match val with
                                      | new_dimension n => run stdin n
                                      | str s           => IO.println s
                                                           run stdin dimension
    | Except.error msg => IO.println msg
                          run stdin dimension
    
def main : IO Unit := do
 let stdin ← IO.getStdin
 run stdin 3
    