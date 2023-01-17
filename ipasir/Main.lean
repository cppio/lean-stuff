import Ipasir

instance : OfNat SAT.Var 1 := ⟨1, by decide⟩
instance : OfNat SAT.Var 2 := ⟨2, by decide⟩

open SAT.SolverM in
def main : IO Unit := do
  let solver ← Ipasir2.init
  solver.add    1  ; solver.add    2  ; solver.add 0
  solver.add    1  ; solver.add (0-2) ; solver.add 0
  solver.add (0-1) ; solver.add    2  ; solver.add 0
  solver.add (0-1) ; solver.add (0-2) ; solver.add 0
  solver.setLearn 1024 (do _ ← IO.println · |>.toBaseIO)
  let r ← solver.solve
  IO.println r

  let r : Option (Bool × Bool) ← run <|
    add [1] <|
    add [-2] <|
    solve (do
      let x ← val 1
      let y ← val 2
      return some (x, y)
    ) (return none)
  IO.println r

  let r : String ← run (learn? := some (do _ ← IO.println · |>.toBaseIO)) <|
    add [ 1,  2] <|
    add [ 1, -2] <|
    add [-1,  2] <|
    add [-1, -2] <|
    solve (pure "sat") (pure "unsat")
  IO.println r
