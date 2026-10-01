import Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
import Solcore.Frontend.SourceTypedRuntime
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCoreIntegerAssignments

/-! Integer bit-not has two deliberately distinct admission boundaries. The closed
unary fixture `~5` is checker accepted; compound `value ~=` is currently rejected. The
trusted retained-IR and ordinary Core assignment implementations both already
execute Integer bit-not. No checker receipt is asserted for the edited IR. -/
set_option autoImplicit false
namespace Tests.SourceSemanticsIntegerBitNot
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def workspace (text : String) : Workspace.RawWorkspace :=
  { entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := text}] }

private def checkTrustedRetained (value : Int) : IO Unit := do
  let program ← get "retained baseline checked source" (checkProgram (workspace
    "function retained(value: integer) returns (integer) { return value; }"))
  let owner ← key program "retained"
  let plan ← match SourceSpecializationWorklist.run program [⟨owner.declaration, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"retained baseline worklist failed: {reprStr other}")
  let specialized ← get "retained entry" (SourceCompilationPlan.exactSpecialization plan owner)
  let input ← match specialized.function.typedBody.inputs with
    | [binder] => pure binder
    | _ => throw (IO.userError "retained entry input missing")
  let statementId : StatementId := ⟨⟨owner.declaration, 100000⟩⟩
  let assignment : AssignmentResolution := { target := { root := input.id, projections := [], type := .integer } }
  let statement : StatementNode := {
    id := statementId
    span := { source := {origin := .main, path := "main.solc"}, startByte := 0, endByte := 1 }
    type := .unit
    form := .assignBitNot assignment
  }
  let source := { specialized.function.typedBody with
    roots := .statement statementId :: specialized.function.typedBody.roots
    nodes := .statement statement :: specialized.function.typedBody.nodes }
  let rewritten := { specialized with function := { specialized.function with typedBody := source } }
  let trustedPlan := { plan with specializations := [rewritten] }
  match SourceTypedRuntime.runTrusted program trustedPlan owner [.integer value] 1000 with
  | .done (.integer result) finalState =>
      assertTrue (result == ~~~value) "trusted retained Integer ~= result changed"
      assertTrue (finalState.heap.length == 1) "trusted retained Integer ~= allocated an RHS cell"
  | result => throw (IO.userError s!"trusted retained Integer ~= failed: {reprStr result}")
  let scope : SourceCoreLocalCell.Scope := [(input.id, .integer)]
  let body ← get "native retained Integer ~= lowering" (SourceCoreAssignments.assignBitNot source scope assignment .integer
    (Core.OptionalCell.read .integer (.var 0) Core.Word.zero) Core.Word.zero)
  assertTrue (Core.infer? (SourceCoreLocalCell.coreContext scope) body == some (Core.LanguageResult.resultType .integer))
    "native retained Integer ~= checker failed"
  let initial := Core.State.initial body [.cellRef (Core.OptionalCell.cellType .integer) 0] [.inRight .unit (.integer value)]
  let expected := Core.StatefulRunResult.done (.inRight .word (.integer (~~~value))) [.inRight .unit (.integer (~~~value))]
  assertTrue (Core.runStateful 1000 initial == expected) "native retained Integer ~= result/store differed from old runtime"
  match Core.runStateful 2 initial with
  | .outOfFuel checkpoint => assertTrue (Core.runStateful 1000 checkpoint == expected) "native retained Integer ~= resume changed"
  | other => throw (IO.userError s!"native retained Integer ~= expected checkpoint: {reprStr other}")

def run : IO Unit := do
  match checkProgram (workspace "function rejected(value: integer) returns (integer) { value ~=; return value; }") with
  | .error [.inference _] => pure ()
  | result => throw (IO.userError s!"Integer ~= source admission changed: {reprStr result}")
  let compiled ← prepare "Integer unary bit-not" "function unary() returns (integer) { return ~5; }" ["unary"]
  let owner ← key compiled.sourceProgram "unary"
  discard <| expect compiled "unary" [] (.integer (-6)) 2
  match SourceTypedRuntime.run compiled.sourceProgram compiled.validationPlan owner [] 1000 with
  | .done (.integer result) _ => assertTrue (result == -6) "checked old Integer unary bit-not changed"
  | result => throw (IO.userError s!"checked old Integer unary failed: {reprStr result}")
  for value in [-7, 0, 5, -(Int.ofNat (2^300))] do
    have _sourcePrimitive := SourceSemantics.Dynamic.BitNotSnapshot.integer value
    have _finiteNative := SourceSemantics.CoreLowering.IntegerBitNotSnapshot.native_success value
      (environment := [.inRight .unit (.integer value)]) (snapshot := .var 0) (rhs := .unit) (.var (index := 0) rfl)
      none ([] : Core.Store) Core.Word.zero
    checkTrustedRetained value
  IO.println "Integer bit-not checked unary/compound rejection and trusted retained old/native assignment parity GREEN"

end Tests.SourceSemanticsIntegerBitNot
