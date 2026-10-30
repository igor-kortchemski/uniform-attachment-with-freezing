module

import Lake.Check.Compare
import Lake.Check.Axioms
import Lake.Check.Util
import Lean.Data.Json

open Lean in
public def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq,
  ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce, ``Nat, ``String, ``Char, ``optParam,
  ``autoParam, ``semiOutParam, ``outParam]

open Lean in
def used (info : ConstantInfo) : Array Name := Id.run do
  let mut r : Array Name := info.type.getUsedConstants
  r := r.push info.name
  match ConstantInfo.value? info true with
  | some v => r := r ++ v.getUsedConstants
  | none => pure ()
  match info with
  | .inductInfo i => r := r ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => r := r.push i.induct
  | .recInfo i =>
    for rule in i.rules do
      r := r.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return r

open Lean in
public def main (args : List String) : IO UInt32 := do
  let [cfgPath, challengePath, solutionPath] := args
    | IO.eprintln "usage: CONFIG CHALLENGE.ndjson SOLUTION.ndjson"; return 2
  let cfgText ← IO.FS.readFile cfgPath
  let cfg ← IO.ofExcept (Json.parse cfgText)
  let strs (k : String) : Array Name :=
    match cfg.getObjValAs? (Array String) k with
    | .ok a => a.map String.toName
    | .error _ => #[]
  let theoremNames := strs "theorem_names"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let targets := Std.HashSet.ofArray theoremNames
  let mut worklist : Array Name := primitiveTargets
  for t in theoremNames do
    match solution.constMap[t]? with
    | some c => worklist := worklist ++ c.type.getUsedConstants
    | none => IO.println s!"target missing in solution {t}"
  let mut parent : Std.HashMap Name Name := {}
  let mut checked : Std.HashSet Name := {}
  let mut bad : Array String := #[]
  let mut count := 0
  while !worklist.isEmpty do
    let t := worklist.back!
    worklist := worklist.pop
    if checked.contains t then continue
    checked := checked.insert t
    count := count + 1
    let cc? := challenge.constMap[t]?
    let sc? := solution.constMap[t]?
    match cc?, sc? with
    | _, none => bad := bad.push s!"MISSING in solution: {t}"
    | none, some sc =>
      bad := bad.push s!"MISSING in challenge: {t}"
      worklist := worklist ++ (used sc)
    | some cc, some sc =>
      if targets.contains t then
        for u in sc.type.getUsedConstants do
          if !parent.contains u then parent := parent.insert u t
        worklist := worklist ++ sc.type.getUsedConstants
      else
        if cc != sc then
          let tyEq := cc.type == sc.type
          let vEq := match ConstantInfo.value? cc true, ConstantInfo.value? sc true with
            | some a, some b => a == b
            | none, none => true
            | _, _ => false
          let mut chain := s!"{t}"
          let mut cur := t
          for _ in [0:12] do
            match parent[cur]? with
            | some p => chain := chain ++ s!" <- {p}"; cur := p
            | none => break
          bad := bad.push s!"MISMATCH: {t} (type equal: {tyEq}, value equal: {vEq})\n    chain: {chain}"
        for u in used sc do
          if !parent.contains u then parent := parent.insert u t
        worklist := worklist ++ (used sc)
  IO.println s!"visited {count}"
  for b in bad do IO.println b
  return 0
