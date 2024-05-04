import Qq

open Lean

elab tk:"#print " "induct " id:ident : command => do
  let iv ← getConstInfoInduct <| ← resolveGlobalConstNoOverload id
  logInfoAt tk m!"name: {iv.name}{Format.line}levelParams: {iv.levelParams}{Format.line}type: {iv.type}{Format.line}numParams: {iv.numParams}{Format.line}numIndices: {iv.numIndices}{Format.line}all: {iv.all}{Format.line}ctors: {iv.ctors}{Format.line}isRec: {iv.isRec}{Format.line}isUnsafe: {iv.isUnsafe}{Format.line}isReflexive: {iv.isReflexive}{Format.line}isNested: {iv.isNested}"

elab tk:"#print " "ctor " id:ident : command => do
  let cv ← getConstInfoCtor <| ← resolveGlobalConstNoOverload id
  logInfoAt tk m!"name: {cv.name}{Format.line}levelParams: {cv.levelParams}{Format.line}type: {cv.type}{Format.line}induct: {cv.induct}{Format.line}cidx: {cv.cidx}{Format.line}numParams: {cv.numParams}{Format.line}numFields: {cv.numFields}{Format.line}isUnsafe: {cv.isUnsafe}"

elab tk:"#print " "rec " id:ident : command => do
  let rv ← getConstInfoRec <| ← resolveGlobalConstNoOverload id
  let rules := rv.rules.map fun rule => m!"{Format.line}ctor: {rule.ctor}{Format.line}nfields: {rule.nfields}{Format.line}rhs: {rule.rhs}".nestD
  logInfoAt tk m!"name: {rv.name}{Format.line}levelParams: {rv.levelParams}{Format.line}type: {rv.type}{Format.line}all: {rv.all}{Format.line}numParams: {rv.numParams}{Format.line}numIndices: {rv.numIndices}{Format.line}numMotives: {rv.numMotives}{Format.line}numMinors: {rv.numMinors}{Format.line}rules:{MessageData.joinSep rules Format.line}{Format.line}k: {rv.k}{Format.line}isUnsafe: {rv.isUnsafe}"

#print induct Nat
#print ctor Nat.zero
#print ctor Nat.succ
#print rec Nat.rec

mutual

inductive Even
  | zero
  | succ (o : Odd)

inductive Odd
  | succ (e : Even)

end

#print induct Even
#print induct Odd
#print ctor Even.zero
#print ctor Even.succ
#print ctor Odd.succ
#print rec Even.rec
#print rec Odd.rec

open Qq
