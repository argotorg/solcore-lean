import Solcore.Frontend.SourceCoreAssignmentFaultSites

/-! Assignment reasons preserve parsed statement/header metadata. Repeated
header operations deduplicate only when their parent, binder and kind match. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreAssignmentFaultSites

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreAssignmentFaultSites

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function sites(value: Word, rhs: Word) returns (Word) {",
    "  value += rhs; value = rhs; value ~=;",
    "  for (value += rhs, rhs += value, value += rhs, value -= rhs; false;",
    "       value *= rhs, value ~=, value *= rhs) { value ^= rhs; }",
    "  return value;",
    "}",
    "function equalOnly(value: (Word, Bool), rhs: (Word, Bool)) returns (Word, Bool) { value = rhs; return value; }"
  ] }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"assignment metadata fixture missing: {name}")

private def prepared (source : TypedSource) (firstReason : Nat) : IO Table := do
  match prepare source firstReason with
  | .ok table => pure table
  | .error error => throw (IO.userError s!"assignment metadata rejected: {reprStr error}")

private def testSites (function : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let table ← prepared source 100
  assertTrue (table.length == 8 && table.sites.map (·.reason.val) ==
      (List.range 8).map (100 + ·)) "assignment reasons wrapped, reordered or failed to deduplicate"
  let (value, rhs) ← match source.inputs with
    | [value, rhs] => pure (value.id, rhs.id)
    | _ => throw (IO.userError "assignment metadata input identity changed")
  let statements := source.nodes.filterMap fun
    | .statement node => some node
    | _ => none
  let ordinaryAdd ← match statements.find? (fun node => match node.form with
      | .assignValue _ .add _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "ordinary assignment occurrence missing")
  let ordinaryUnary ← match statements.find? (fun node => match node.form with
      | .assignBitNot _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "ordinary unary occurrence missing")
  let loop ← match statements.find? (fun node => match node.form with
      | .forLoop .. => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "header assignment parent missing")
  let body ← match statements.find? (fun node => match node.form with
      | .assignValue _ .bitXor _ => true | _ => false) with
    | some node => pure node
    | none => throw (IO.userError "loop body assignment occurrence missing")
  let expected : List (StatementNode × Resolved.LocalId × Kind) := [
    (ordinaryAdd, value, .value .add), (ordinaryUnary, value, .bitNot),
    (loop, value, .value .add), (loop, rhs, .value .add), (loop, value, .value .subtract),
    (loop, value, .value .multiply), (loop, value, .bitNot), (body, value, .value .bitXor)]
  for (site, (node, binder, kind)) in table.sites.zip expected do
    let location := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
    assertTrue (decide (site.site = location ∧ site.binder = binder ∧ site.kind = kind ∧
        site.span = node.span)) "assignment reason changed its parent, binder, kind or span"
    assertTrue (table.reasonAt location binder kind == site.reason)
      "assignment provider failed to distinguish exact binder and kind"
    let diagnostic : SourceCoreFaultSites.Diagnostic := {
      error := match kind with
        | .value operator => .invalidAssignmentOperands operator none (some .word)
        | .bitNot => .invalidUnaryOperand .bitNot none
      site := location
      span := some node.span
    }
    assertTrue (decide (table.diagnostic? site.reason = some diagnostic))
      "assignment failure reason returned the wrong source error"
    assertTrue (decide ((site.reason, diagnostic) ∈ table.diagnostics))
      "assignment diagnostic export lost the classified reason"
  assertTrue (table.diagnostics.length == table.length)
    "assignment diagnostic export changed table length"
  assertTrue (decide (table.diagnostic? (word 999) = none)) "unknown assignment reason produced a diagnostic"
  assertTrue (table.reasonAt (.occurrence ordinaryAdd.id.occurrence) rhs (.value .add) == Core.Word.zero)
    "assignment lookup matched a different binder"
  assertTrue (table.reasonAt (.occurrence ordinaryAdd.id.occurrence) value (.value .equal) == Core.Word.zero)
    "equal assignment acquired an unused absent-target reason"
  let boundary ← prepared source (Core.wordModulus - 8)
  assertTrue (boundary.sites.map (·.reason.val) ==
      (List.range 8).map (Core.wordModulus - 8 + ·)) "assignment reason boundary wrapped modulo"
  for firstReason in [Core.wordModulus - 7, Core.wordModulus] do
    match prepare source firstReason with
    | .error .reasonSpaceExhausted => pure ()
    | result => throw (IO.userError s!"assignment reason overflow was accepted: {reprStr result}")

private def testOwners (function foreign : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let wrongStatement := { source with nodes := source.nodes.map fun
    | .statement node => .statement { node with
        id := { node.id with occurrence := { node.id.occurrence with owner := foreign.declaration } } }
    | node => node }
  match prepare wrongStatement 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "statement owner rejection changed"
  | result => throw (IO.userError s!"foreign statement metadata was accepted: {reprStr result}")
  let wrongBinder := { source with nodes := source.nodes.map fun
    | .statement node => match node.form with
      | .assignValue assignment .add rhs =>
          let assignment := { assignment with target := { assignment.target with
            root := { assignment.target.root with owner := foreign.declaration } } }
          .statement { node with form := .assignValue assignment .add rhs }
      | _ => .statement node
    | node => node }
  match prepare wrongBinder 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "assignment binder owner rejection changed"
  | result => throw (IO.userError s!"foreign assignment binder was accepted: {reprStr result}")
  let wrongHeader := { source with nodes := source.nodes.map fun
    | .statement node => match node.form with
      | .forLoop initializer condition post body =>
          let initializer := initializer.map fun
            | .assignValue assignment operator rhs =>
                let assignment := { assignment with target := { assignment.target with
                  root := { assignment.target.root with owner := foreign.declaration } } }
                ForItemForm.assignValue assignment operator rhs
            | item => item
          .statement { node with form := .forLoop initializer condition post body }
      | _ => .statement node
    | node => node }
  match prepare wrongHeader 100 with
  | .error (.ownerMismatch expected actual) =>
      assertTrue (expected == source.owner && actual == foreign.declaration)
        "header binder owner rejection changed"
  | result => throw (IO.userError s!"foreign header binder was accepted: {reprStr result}")

private def testProfiles (function : CheckedFunction) : IO Unit := do
  let empty ← prepared function.typedBody 100
  assertTrue (empty.length == 0 && empty.diagnostics.isEmpty)
    "equal product assignment must have no absent-operand diagnostic"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"assignment metadata fixture checking failed: {reprStr errors}")
  let function ← named program "sites"
  let foreign ← named program "equalOnly"
  testSites function
  testOwners function foreign
  testProfiles foreign

end Tests.SourceCoreAssignmentFaultSites
