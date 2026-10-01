import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The actual compatible assignment executes two repeated effectful keys,
saves a snapshot, then runs an RHS that replaces the root. Compound writeback
uses the saved leaf and the latest siblings, retaining raw staged headers and
ordered duplicate entries. Faults skip the remaining phases; resume agrees. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatiblePlaceOrder
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_order", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_order.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool (.mapping .bool .word)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key, .index key], .word⟩, []⟩
private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier (first duplicate sibling : Nat) : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.mapping (.comptime .bool) .word)
    [(.bool true, .mapping (.comptime .bool) .word
      [(.bool true, .word (w first)), (.bool true, .word (w duplicate)), (.bool false, .word (w sibling))])]

private def keyCode (fail : Bool) : SourceCoreBasic.LoweredExpr := ⟨.bool,
  .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (.word (w 1))))
    (if fail then LanguageResult.failure .bool (.word (w 31)) else LanguageResult.success (.bool true))⟩

private def code (prepared : Prepared) (initial latest : Expr) (keyFails rhsFails : Bool) : Expr :=
  .letE (OptionalCell.allocateInitialized prepared.route.rootType initial)
    (.letE (.newCell .word (.word Word.zero))
      (execute prepared (.var 1) (SourceCoreCalls.packArguments [keyCode keyFails, keyCode false])
        (.letE (.storeCell (.var 1) (.inRight .unit latest))
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (.word (w 10))))
            (if rhsFails then LanguageResult.failure .word (.word (w 32)) else LanguageResult.success (.word (w 5)))))
        (LanguageResult.success (.pair (.loadCell (.var 0)) (.loadCell (.var 1))))
        (.product .word (OptionalCell.cellType prepared.route.rootType)) (some .wordAdd) false (w 33)))

private def verify (prepared : Prepared) (context : SourceCoreCompatibleValues.Context)
    (initial latest : Expr) (keyFails rhsFails : Bool) (expected : SourceCoreDataValues.Value)
    (count : Nat) (reason : Option Word) : IO Unit := do
  let body := code prepared initial latest keyFails rhsFails
  unless infer? [] body checked.catalog.definitions ==
      some (LanguageResult.resultType (.product .word (OptionalCell.cellType prepared.route.rootType))) do
    throw (IO.userError "compatible assignment order code rejected by actual checker")
  let initialState : Core.State := .initial body [] []
  match runStateful 200000 initialState with
  | .done result after =>
    match reason, result with
    | none, .inRight .word (.pair (.word actualCount) (.inRight .unit _)) =>
      unless actualCount == w count do throw (IO.userError "compatible assignment returned wrong effect count")
    | some expectedReason, .inLeft _ (.word actualReason) =>
      unless actualReason == expectedReason do throw (IO.userError "compatible assignment changed fault order")
    | _, _ => throw (IO.userError s!"compatible assignment unexpected outcome: {reprStr result}")
    unless after.read? 1 == some (.word (w count)) do throw (IO.userError "compatible assignment repeated or skipped an effect")
    match after.read? 0 with
    | some (.inRight .unit value) =>
      match SourceCoreCompatibleValues.decode 100 context rootType value with
      | .error error => throw (IO.userError s!"compatible assignment decode failed: {reprStr error}")
      | .ok actual => unless actual == expected do throw (IO.userError "compatible assignment lost snapshot/latest-root/duplicate/header semantics")
    | _ => throw (IO.userError "compatible assignment lost initialized root")
    match runStateful 17 initialState with
    | .outOfFuel checkpoint =>
      unless runStateful 200000 checkpoint == .done result after do throw (IO.userError "compatible assignment resume changed observation")
    | _ => throw (IO.userError "compatible assignment expected a checkpoint")
  | other => throw (IO.userError s!"compatible assignment did not complete: {reprStr other}")

def run : IO Unit := do
  let route ← match describe context checked.signatures source site assignment with
    | .ok route => pure route
    | .error error => throw (IO.userError s!"compatible assignment describe failed: {reprStr error}")
  let prepared ← match prepare context 100 route (w 33) (fun _ => w 34) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"compatible assignment prepare failed: {reprStr error}")
  match SourceCoreCompatibleValues.encode 100 context rootType (carrier 10 11 20) with
  | .error error => throw (IO.userError s!"compatible assignment initial encode failed: {reprStr error}")
  | .ok initial =>
    match SourceCoreCompatibleValues.encode 100 initial.context rootType (carrier 100 101 200) with
    | .error error => throw (IO.userError s!"compatible assignment latest encode failed: {reprStr error}")
    | .ok latest =>
      match SourceCoreCompatibleDataExpressions.quote initial.value, SourceCoreCompatibleDataExpressions.quote latest.value with
      | some initialCode, some latestCode =>
        verify prepared latest.context initialCode latestCode false false (carrier 15 101 200) 12 none
        verify prepared latest.context initialCode latestCode true false (carrier 10 11 20) 1 (some (w 31))
        verify prepared latest.context initialCode latestCode false true (carrier 100 101 200) 12 (some (w 32))
      | _, _ => throw (IO.userError "compatible assignment data values were not quotable")
  IO.println "compatible place snapshot/RHS/latest-root order GREEN"

end Tests.SourceCoreCompatiblePlaceOrder
