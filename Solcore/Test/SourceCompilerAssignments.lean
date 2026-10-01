import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Test.SourceCoreAssignmentEntries

/-! Assignment regressions use public values and opaque checkpoints; the same
cached artifact supplies source-cell and complete-native-store effect audits. -/
set_option autoImplicit false
namespace Tests.SourceCompilerAssignments
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Tests.SourceCompilerFeatureSupport

private def success (entry : Entry) (arguments : List Value)
    (expected : Value) : IO (List SourceTypedRuntime.Cell) := do
  require ((← entry.run arguments) == expected) "public assignment changed its result"
  entry.checkResume arguments expected
  let complete ← entry.audit arguments
  let pending ← entry.audit arguments 10
  match ← nativeObservation pending with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "native assignment did not suspend")
  let resumed ← get "native assignment resume" (pending.resume 300000)
  require ((← nativeObservation resumed) == (← nativeObservation complete))
    "assignment resume changed its snapshot or complete shared native store"
  pure (sourceState complete).heap

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

private def failure (entry : Entry) (arguments : List Value)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : IO (Core.Word × List SourceTypedRuntime.Cell) := do
  let invocation ← entry.invoke arguments
  match invocation.outcome with
  | .failed reason _ =>
      require (reason != Core.Word.zero && decide ((← invocation.diagnostic reason) = some diagnostic))
        "assignment failure lost its exact source error, occurrence or span"
      let audit ← entry.audit arguments
      match audit.observation with
      | .fault error state =>
          require (decide (error = diagnostic.error)) "source observation changed failure priority"
          pure (reason, state.heap)
      | _ => throw (IO.userError "source observation lost the assignment failure")
  | _ => throw (IO.userError "public assignment did not fail")

private def hasWordCell (heap : List SourceTypedRuntime.Cell) (index : Nat) (expected : Core.Word) : Bool :=
  match heap[index]? with
  | some ⟨.word, some (.word actual)⟩ => actual == expected
  | _ => false

private def testProfile (program : CheckedProgram) : IO Unit := do
  let operators ← compileNamed program "operators"
  discard <| success operators [scalar 2] (.word (word 8).bitNot)
  discard <| success operators [scalar 5] (.word (word 14).bitNot)
  discard <| success (← compileNamed program "forOrder") [scalar 3] (.product (scalar 23) (scalar 3))
  for (name, error) in ([
      ("absent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryAbsent", .invalidUnaryOperand .bitNot none),
      ("headerAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("postAbsent", .invalidAssignmentOperands .add none (some .word)),
      ("unaryPostAbsent", .invalidUnaryOperand .bitNot none)] :
      List (String × SourceTypedRuntime.RuntimeError)) do
    let compiled ← compileNamed program name
    discard <| failure compiled [] (← expectedDiagnostic program name error)
  let choose ← compileNamed program "choose"
  let mut tokens : List Core.Word := []
  for (flag, name, operator) in [(true, "failLeft", Syntax.ValueAssignOp.add), (false, "failRight", .subtract)] do
    let (reason, _) ← failure choose [.bool flag] (← expectedDiagnostic program name
      (.invalidAssignmentOperands operator none (some .word)))
    tokens := reason :: tokens
  require (tokens[0]? != tokens[1]?) "public callee assignment failures reused a token"
  let snapshot ← compileNamed program "snapshot"
  let store ← success snapshot [scalar 2] (scalar 5)
  require (hasWordCell store 0 (word 5))
    "public compound assignment used the latest captured-cell value"
  let absent ← compileNamed program "snapshotAbsent"
  let (_, store) ← failure absent [] (← expectedDiagnostic program "snapshotAbsent"
    (.invalidAssignmentOperands .add none (some .word)))
  require (hasWordCell store 0 (word 100))
    "public absent-operand failure discarded RHS mutation"
  let priority ← compileNamed program "failurePriority"
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
  require (hasWordCell store 0 (word 100))
    "public RHS failure lost its preceding mutation"
  discard <| success (← compileNamed program "captured") [scalar 4] (.product (scalar 6) (scalar 9))
  discard <| success (← compileNamed program "functionEqual") [] (scalar 2)

def run : IO Unit := do
  let program ← get "assignment fixtures" (checkProgram Tests.SourceCoreAssignmentEntries.fixtures)
  testProfile program
end Tests.SourceCompilerAssignments
