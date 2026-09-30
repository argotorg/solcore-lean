import Solcore.Frontend.SourceCompiler
import Solcore.Test.SourceCoreAssignmentEntries

/-! Automatic and explicit Core compilation execute the assignment profiles.
Snapshot and RHS failure tests need function values, so they also verify the
FunctionEntry fallback reaches public compilation with source diagnostics. -/

set_option autoImplicit false

namespace Tests.SourceCompilerAssignments

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCompiler

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def execution : RunOptions := { executionFuel := 30000 }

private def compileNamed (program : CheckedProgram) (name : String)
    (preference : BackendPreference) : IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public assignment fixture missing: {name}")
  match compileChecked program (.declaration signature.id []) {
      specializationBudget := 100, stagingFuel := 128, backendPreference := preference } with
  | .ok compiled =>
      assertTrue (compiled.backend == .core) "supported assignments did not select Core"
      pure compiled
  | .error error => throw (IO.userError s!"public assignment compilation rejected: {reprStr error}")

private def observation (result : Except RunError ExecutionResult) : IO Core.LanguageResult.Observation := do
  match result with
  | .ok (.coreLanguageResult result) => pure result
  | result => throw (IO.userError s!"public assignment lost its Core language result: {reprStr result}")

private def success (compiled : CompiledEntry) (arguments : List Core.Value)
    (expected : Core.Value) : IO Core.Store := do
  let completed ← observation (compiled.runCore arguments execution)
  let store ← match completed with
    | .succeeded value store =>
        assertTrue (value == expected) "public assignment changed its result"
        pure store
    | result => throw (IO.userError s!"public assignment failed: {reprStr result}")
  match ← observation (compiled.runCore arguments { execution with executionFuel := 10 }) with
  | .outOfFuel state =>
      assertTrue (Core.LanguageResult.observeResult (Core.runStateful 29990 state) == completed)
        "public assignment resume changed its snapshot or shared heap"
  | result => throw (IO.userError s!"public assignment lost its checkpoint: {reprStr result}")
  pure store

private def expectedDiagnostic (program : CheckedProgram) (name : String)
    (error : SourceTypedRuntime.RuntimeError) : IO SourceCoreFaultSites.Diagnostic := do
  let declaration ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature.id
    | none => throw (IO.userError "public assignment diagnostic owner missing")
  let function ← match program.functions.find? (·.declaration == declaration) with
    | some function => pure function
    | none => throw (IO.userError "public assignment source missing")
  match function.typedBody.nodes.find? (fun
      | .statement node => match node.form with
        | .assignValue _ operator _ => operator != .equal
        | .assignBitNot _ | .forLoop .. => true
        | _ => false
      | _ => false) with
  | some (.statement node) => pure { error, site := .occurrence node.id.occurrence, span := some node.span }
  | _ => throw (IO.userError "public assignment diagnostic occurrence missing")

private def failure (compiled : CompiledEntry) (arguments : List Core.Value)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : IO (Core.Word × Core.Store) := do
  match ← observation (compiled.runCore arguments execution) with
  | .failed reason store =>
      assertTrue (reason != Core.Word.zero && decide (compiled.coreFailureDiagnostic? reason = some diagnostic))
        "public assignment failure lost its exact source error, occurrence or span"
      pure (reason, store)
  | result => throw (IO.userError s!"public assignment lost its failure: {reprStr result}")

private def testProfile (program : CheckedProgram) (preference : BackendPreference) : IO Unit := do
  let operators ← compileNamed program "operators" preference
  discard <| success operators [scalar 2] (.word (word 8).bitNot)
  discard <| success operators [scalar 5] (.word (word 14).bitNot)
  discard <| success (← compileNamed program "forOrder" preference) [scalar 3] (.pair (scalar 23) (scalar 3))
  for (name, error) in ([
      ("absent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryAbsent", .invalidUnaryOperand .bitNot none),
      ("headerAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("postAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryPostAbsent", .invalidUnaryOperand .bitNot none)] :
      List (String × SourceTypedRuntime.RuntimeError)) do
    let compiled ← compileNamed program name preference
    discard <| failure compiled [] (← expectedDiagnostic program name error)
  let choose ← compileNamed program "choose" preference
  let mut tokens : List Core.Word := []
  for (flag, name, operator) in [(true, "failLeft", Syntax.ValueAssignOp.add), (false, "failRight", .subtract)] do
    let (reason, _) ← failure choose [.bool flag] (← expectedDiagnostic program name
      (.invalidAssignmentOperands operator none (some .word)))
    tokens := reason :: tokens
  assertTrue (tokens[0]? != tokens[1]?) "public callee assignment failures reused a token"
  let snapshot ← compileNamed program "snapshot" preference
  let store ← success snapshot [scalar 2] (scalar 5)
  assertTrue (store[snapshot.inputTypes.length + snapshot.specializationCount]? == some (present (scalar 5)))
    "public compound assignment used the latest captured-cell value"
  let absent ← compileNamed program "snapshotAbsent" preference
  let (_, store) ← failure absent [] (← expectedDiagnostic program "snapshotAbsent"
    (.invalidAssignmentOperands .add none (some .word)))
  assertTrue (store[absent.specializationCount]? == some (present (scalar 100)))
    "public absent-operand failure discarded RHS mutation"
  let priority ← compileNamed program "failurePriority" preference
  let function ← match program.functions.find? (·.declaration == priority.key.declaration) with
    | some function => pure function
    | none => throw (IO.userError "public RHS failure owner missing")
  let (node, binder) ← match function.typedBody.nodes.filterMap (fun
      | .expression node => match node.form with
        | .reference "absent" (.local binder) => some (node, binder)
        | _ => none
      | _ => none) with
    | [site] => pure site
    | _ => throw (IO.userError "public RHS failure occurrence missing")
  let (_, store) ← failure priority [] {
    error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }
  assertTrue (store[priority.specializationCount]? == some (present (scalar 100)))
    "public RHS failure lost its preceding mutation"
  discard <| success (← compileNamed program "captured" preference) [scalar 4] (.pair (scalar 6) (scalar 9))
  discard <| success (← compileNamed program "functionEqual" preference) [] (scalar 2)

def run : IO Unit := do
  let program ← match checkProgram Tests.SourceCoreAssignmentEntries.fixtures with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"public assignment fixtures failed checking: {reprStr errors}")
  for preference in [BackendPreference.automatic, .core] do
    testProfile program preference

end Tests.SourceCompilerAssignments
