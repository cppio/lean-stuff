import Cont

def main : IO Unit :=
  IO.println <| Cont.callcc fun k => k.throw 42
