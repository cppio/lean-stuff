import Bindgen
import Resource

private extern "C" {
  const char *ipasir_signature(void);
  void *ipasir_init(void);
  void ipasir_release(void *solver);
  void ipasir_add(void *solver, int32_t lit_or_zero);
  void ipasir_assume(void *solver, int32_t lit);
  int ipasir_solve(void *solver);
  int32_t ipasir_val(void *solver, int32_t lit);
  int ipasir_failed(void *solver, int32_t lit);
  -- void ipasir_set_terminate(void *solver, void *data, int(*terminate)(void *data));
  -- void ipasir_set_learn(void *solver, void *data, int max_length, void(*learn)(void *data, int32_t *clause));
  void ipasir_set_terminate(void *solver, void *data, void *terminate);
  void ipasir_set_learn(void *solver, void *data, int max_length, void *learn);
}

safe opaque Ipasir.signature : String := .fromCstr! <| ipasir_signature ()

namespace Ipasir

private structure Sig where
  Ipasir : Type
  init : BaseIO Ipasir
  add (litOrZero : UInt32) (solver : Ipasir) : BaseIO Unit
  assume (lit : UInt32) (solver : Ipasir) : BaseIO Unit
  solve (solver : Ipasir) : BaseIO UInt32
  val (lit : UInt32) (solver : Ipasir) : BaseIO UInt32
  failed (lit : UInt32) (solver : Ipasir) : BaseIO UInt32

private unsafe def Impl : Sig where
  Ipasir                  := Resource Pointer
  init                    := (.ok (.mk (ipasir_init ()) ipasir_release  ) ·)
  add    litOrZero solver := (.ok (ipasir_add    solver.data litOrZero) ·)
  assume lit       solver := (.ok (ipasir_assume solver.data lit        ) ·)
  solve            solver := (.ok (ipasir_solve  solver.data            ) ·)
  val    lit       solver := (.ok (ipasir_val    solver.data lit        ) ·)
  failed lit       solver := (.ok (ipasir_failed solver.data lit        ) ·)

@[implemented_by Impl]
private opaque Imp : Sig := {
  Ipasir := Unit
  init := default
  add := default
  assume := default
  solve := default
  val := default
  failed := default
}

def _root_.Ipasir := Imp.Ipasir
opaque init : BaseIO Ipasir := Imp.init
opaque add (litOrZero : UInt32) (solver : Ipasir) : BaseIO Unit := Imp.add litOrZero solver
opaque assume (lit : UInt32) (solver : Ipasir) : BaseIO Unit := Imp.assume lit solver
opaque solve (solver : Ipasir) : BaseIO UInt32 := Imp.solve solver
opaque val (lit : UInt32) (solver : Ipasir) : BaseIO UInt32 := Imp.val lit solver
opaque failed (lit : UInt32) (solver : Ipasir) : BaseIO UInt32 := Imp.failed lit solver

end Ipasir

namespace Ipasir2

private structure Sig where
  Ipasir : Type
  init : BaseIO Ipasir
  add (litOrZero : UInt32) (solver : Ipasir) : BaseIO Unit
  assume (lit : UInt32) (solver : Ipasir) : BaseIO Unit
  solve (solver : Ipasir) : BaseIO UInt32
  val (lit : UInt32) (solver : Ipasir) : BaseIO UInt32
  failed (lit : UInt32) (solver : Ipasir) : BaseIO UInt32
  setLearn (maxLength : UInt32) (learn : Pointer → BaseIO Unit) (solver : Ipasir) : BaseIO Unit

@[extern c inline "(lean_inc((lean_object *) #1), lean_dec(lean_apply_2((lean_object *) #1, lean_box_usize(#2), lean_box(0))), lean_box(0))"]
private unsafe opaque apply_learn (data clause : Pointer) : Unit
@[export lean_apply_learn]
private unsafe def lean_apply_learn (data clause : Pointer) : Unit := apply_learn data clause
@[extern c inline "(size_t) lean_apply_learn"]
private unsafe opaque lean_apply_learn_addr : Unit → Pointer

private unsafe def Impl : Sig where
  Ipasir := Resource Pointer
  init                            := (.ok (.mk (ipasir_init ()) ipasir_release                                          ) ·)
  add      litOrZero       solver := (.ok (ipasir_add       solver.data litOrZero                                       ) ·)
  assume   lit             solver := (.ok (ipasir_assume    solver.data lit                                             ) ·)
  solve                    solver := (.ok (ipasir_solve     solver.data                                                 ) ·)
  val      lit             solver := (.ok (ipasir_val       solver.data lit                                             ) ·)
  failed   lit             solver := (.ok (ipasir_failed    solver.data lit                                             ) ·)
  setLearn maxLength learn solver := (.ok (ipasir_set_learn solver.data (.of learn) maxLength (lean_apply_learn_addr ())) ·)

@[implemented_by Impl]
private opaque Imp : Sig := {
  Ipasir := Unit
  init := default
  add := default
  assume := default
  solve := default
  val := default
  failed := default
  setLearn := default
}

def _root_.Ipasir2 : Type := Imp.Ipasir
opaque init : BaseIO Ipasir2 := Imp.init
opaque add (litOrZero : UInt32) (solver : Ipasir2) : BaseIO Unit := Imp.add litOrZero solver
opaque assume (lit : UInt32) (solver : Ipasir2) : BaseIO Unit := Imp.assume lit solver
opaque solve (solver : Ipasir2) : BaseIO UInt32 := Imp.solve solver
opaque val (lit : UInt32) (solver : Ipasir2) : BaseIO UInt32 := Imp.val lit solver
opaque failed (lit : UInt32) (solver : Ipasir2) : BaseIO UInt32 := Imp.failed lit solver
opaque setLearn (maxLength : UInt32) (learn : Pointer → BaseIO Unit) (solver : Ipasir2) : BaseIO Unit := Imp.setLearn maxLength learn solver

end Ipasir2

namespace SAT

def Var := { n // 0 < n ∧ n < 2 ^ 31 }
def Lit := Var × Bool

def Var.mk : (n : Nat) → (_ : 0 < n ∧ n < 2 ^ 31 := by decide) → Var := .mk

instance : Coe Var UInt32 where
  coe var := ⟨var.val, Nat.le_trans var.property.right <| by decide⟩

instance : Coe Lit UInt32 where
  coe lit := if lit.snd then lit.fst else 0 - lit.fst

instance [OfNat SAT.Var var] : OfNat SAT.Lit var := ⟨OfNat.ofNat var, true⟩

instance : Neg SAT.Lit := ⟨λ lit => ⟨lit.fst, !lit.snd⟩⟩

inductive Mode
  | Input
  | Sat
  | Unsat

structure Sig where
  SolverM : Mode → Type → Type
  [inst : Monad (SolverM m)]
  run : SolverM .Input α → Option (Pointer → BaseIO Unit) → BaseIO α
  add : List Lit → SolverM .Input α → SolverM m α
  solve : SolverM .Sat α → SolverM .Unsat α → SolverM m α
  val : Var → SolverM .Sat Bool

def Impl : Sig where
  SolverM := λ _ ↦ ReaderT Ipasir2 BaseIO
  run f learn? := do
    let solver ← Ipasir2.init
    if let some learn := learn? then
      solver.setLearn 0x7fffffff learn
    f solver
  add lits f solver := do
    for lit in lits do
      solver.add lit
    solver.add 0
    f solver
  solve sat unsat solver := do
    match ← solver.solve with
    | 10 => sat solver
    | 20 => unsat solver
    | _ => have := Inhabited.mk (unsat solver) ; unreachable!
  val var solver :=
    return (← solver.val var).toNat < 2 ^ 31

opaque Imp : Sig := Impl

abbrev SolverM : Mode → Type → Type := Imp.SolverM
instance : Monad (SolverM m) := Imp.inst
def SolverM.run (f : SolverM .Input α) (learn? : Option (Pointer → BaseIO Unit) := none) : BaseIO α := Imp.run f learn?
def SolverM.add (lits : List Lit) (f : SolverM .Input α) : SolverM m α := Imp.add lits f
def SolverM.solve (sat : SolverM .Sat α) (unsat : SolverM .Unsat α) : SolverM m α := Imp.solve sat unsat
def SolverM.val (var : Var) : SolverM .Sat Bool := Imp.val var

end SAT
