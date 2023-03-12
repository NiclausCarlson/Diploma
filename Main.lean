import Diploma.Polynomials.Polynomial
import Diploma.Interactive.Interactive

open BaseIO
open IO
open interactive

partial def run (stdin: FS.Stream) : IO Unit := do
   let line ← IO.FS.Stream.getLine stdin
   let parsed := eval line
   match parsed with
    | Except.ok res => match res with
                        | none => return
                        | some val => IO.println val  
    | Except.error msg => IO.println msg; return
    
def main : IO Unit := do
 let stdin ← IO.getStdin
 run stdin

