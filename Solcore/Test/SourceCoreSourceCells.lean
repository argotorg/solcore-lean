import Solcore.Frontend.SourceCoreFunctions
import Solcore.Frontend.SourceCoreLoops

/-! Real shared traversal uses source allocation hooks for lets and lambda
parameters. Parameter markers skip the packed argument and temporary payload
while preserving the order of earlier parameter and outer lexical references. -/

set_option autoImplicit false
namespace Tests.SourceCoreSourceCells
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreSourceCells

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"source_cells", by decide⟩], by decide⟩⟩, 0⟩
private def binder (index : Nat) (name : String) : TypedBinder :=
  ⟨⟨owner, index⟩, name, .mono .bool, [], false, none⟩
private def outer := binder 0 "outer"
private def first := binder 1 "first"
private def second := binder 2 "second"
private def localBinder := binder 3 "local"
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "source_cells.solc"⟩, 0, 1⟩
private def allocate : Allocator := marked fun request =>
  pure ⟨⟨request.scope.length⟩, captureType request.scope⟩
private def reference : Ty := OptionalCell.referenceType .bool
private def definitions : DataEnvironment :=
  [⟨[.unit]⟩, ⟨[reference]⟩, ⟨[.product reference reference]⟩]
private def context : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0,
  solvedRequirements := [], internalReason := Word.zero }
private def policy : SourceCoreFunctions.Policy := {sourceCells := some allocate}
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun child fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {lowerExpression := child, sourceCells := some allocate}
      fuel source scope statements result reasonAt fellThrough escaped
private def lambdaSource : TypedSource := {
  owner, inputs := [outer], roots := [.expression (expression 0)], nodes := [
    .expression {id := expression 0, span, type := .function (.product .bool .bool) .bool, form := .lambda [first, second] .bool [statement 2]},
    .expression {id := expression 1, span, type := .bool, form := .reference "first" (.local first.id)},
    .statement {id := statement 2, span, type := .bool, form := .returnStmt (some (expression 1))}] }
private def letSource : TypedSource := {
  owner, inputs := [], roots := [.statement (statement 2), .statement (statement 3)], nodes := [
    .expression {id := expression 0, span, type := .bool, form := .reference "false" (.builtinBoolean false)},
    .expression {id := expression 1, span, type := .bool, form := .reference "local" (.local localBinder.id)},
    .statement {id := statement 2, span, type := .unit, form := .letDecl localBinder (some (expression 0))},
    .statement {id := statement 3, span, type := .bool, form := .returnStmt (some (expression 1))}] }
private def assertTrue (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

example : HasType [reference, .word, reference]
    (captures (Renaming.insertion 1) [(first.id, .bool), (outer.id, .bool)])
    (.product reference reference) definitions := by
  exact .pair (.var rfl) (.var rfl)

def run : IO Unit := do
  let .ok lowered := SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody 40 context lambdaSource
      [(outer.id, .bool)] (expression 0) (fun _ => Word.zero)
    | throw (IO.userError "shared lambda compiler rejected marked parameter allocation")
  let program : Core.Program := ⟨LanguageResult.resultType .bool,
    .letE (.newCell (OptionalCell.cellType .bool) (.inRight .unit (.bool true)))
      (TaggedFunction.call .bool lowered.expression (LanguageResult.success (.pair (.bool false) (.bool true)))),
    definitions⟩
  assertTrue program.check "marked lambda parameters failed whole Core checking"
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inRight .word (.bool false) && store.length == 5)
        "marked parameter order or source result changed"
      assertTrue (SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ store 1 ==
        some (.cellRef (OptionalCell.cellType .bool) 0, .inRight .unit (.bool false)))
        "first parameter captured the argument bundle or temporary payload"
      assertTrue (SourceCoreHeapMarkers.completedPair ⟨⟨2⟩, .product reference reference⟩ store 3 ==
        some (.pair (.cellRef (OptionalCell.cellType .bool) 2) (.cellRef (OptionalCell.cellType .bool) 0),
          .inRight .unit (.bool true)))
        "second parameter changed lexical capture order"
  | other => throw (IO.userError s!"marked parameter execution failed: {reprStr other}")
  let child : SourceCoreLoops.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt
  let .ok body := SourceCoreLoops.lowerStatementsWithPolicy {lowerExpression := child, sourceCells := some allocate}
      40 letSource [] [statement 2, statement 3] .bool (fun _ => Word.zero) Word.zero Word.zero
    | throw (IO.userError "shared statement compiler rejected marked let")
  let lets : Core.Program := ⟨LanguageResult.resultType .bool, body, definitions⟩
  assertTrue lets.check "marked let failed whole Core checking"
  match lets.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inRight .word (.bool false) && store.length == 2)
        "marked let changed its result or source allocation count"
  | other => throw (IO.userError s!"marked let execution failed: {reprStr other}")
  let .ok failedBody := letInitialized (some allocate) letSource [] Renaming.id localBinder .bool .bool
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 71))) (LanguageResult.success (.bool true))
    | throw (IO.userError "marked initializer fault did not compile")
  let failed : Core.Program := ⟨LanguageResult.resultType .bool, failedBody, definitions⟩
  assertTrue failed.check "marked initializer fault failed Core checking"
  match failed.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inLeft .bool (.word (Word.ofNatModulo 71)) && store.isEmpty)
        "failed initializer allocated a marker or payload"
  | other => throw (IO.userError s!"marked initializer fault changed: {reprStr other}")
  let .ok absentBody := letUninitialized (some allocate) letSource [] Renaming.id localBinder .bool
      (OptionalCell.read .bool (.var 0) (Word.ofNatModulo 72))
    | throw (IO.userError "marked uninitialized source cell did not compile")
  let absent : Core.Program := ⟨LanguageResult.resultType .bool, absentBody, definitions⟩
  assertTrue absent.check "marked uninitialized source cell failed Core checking"
  match absent.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .inLeft .bool (.word (Word.ofNatModulo 72)) &&
        SourceCoreHeapMarkers.completedPair ⟨⟨0⟩, .unit⟩ store 0 == some (.unit, .inLeft .bool .unit))
        "uninitialized source cell was replaced by a dummy value"
  | other => throw (IO.userError s!"marked uninitialized source cell changed: {reprStr other}")
  let .ok header := SourceCoreLoops.lowerForItems {lowerExpression := child, sourceCells := some allocate}
      (.declaration owner) 40 letSource [] [.letDecl localBinder (some (expression 0))] .bool
      (fun _ => Word.zero) (fun scope => do
        let read ← child 10 letSource scope (expression 1) (fun _ => Word.zero)
        pure (LocalLoop.returnValue .bool read.expression))
    | throw (IO.userError "marked for declaration did not compile")
  let forHeader : Core.Program := ⟨LocalLoop.resultType .bool, header, definitions⟩
  assertTrue forHeader.check "marked for declaration failed Core checking"
  match forHeader.runStateful 10000 with
  | .done value store =>
      assertTrue (value == LocalLoop.returnedValue (.bool false) && store.length == 2)
        "marked for declaration changed its scope or source cells"
  | other => throw (IO.userError s!"marked for declaration execution failed: {reprStr other}")
  let mut sawPartial := false
  for fuel in List.range 160 do
    match program.runStateful fuel with
    | .outOfFuel checkpoint =>
        if checkpoint.store.length == 2 then
          sawPartial := true
          assertTrue ((SourceCoreHeapMarkers.completedPair ⟨⟨1⟩, reference⟩ checkpoint.store 1).isNone)
            "unfinished parameter allocation exported a source payload"
        match Core.runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .inRight .word (.bool false)) "marked parameter resume changed"
        | other => throw (IO.userError s!"marked parameter resume failed: {reprStr other}")
    | .done value _ => assertTrue (value == .inRight .word (.bool false)) "marked parameter result changed"
    | .fault error _ => throw (IO.userError s!"marked parameter machine fault: {reprStr error}")
  assertTrue sawPartial "marked parameter checkpoints missed the marker-only boundary"
  IO.println "shared source allocation hooks and lexical parameter captures GREEN"

end Tests.SourceCoreSourceCells
