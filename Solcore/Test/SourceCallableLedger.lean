import Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Same erased function type, different original staging contracts. Additional
checks cover descriptor membership beyond Core typing and public-factory
coverage without a supplied row/guard certificate. -/

set_option autoImplicit false
namespace Tests.SourceCallableLedger
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"callable_ledger", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def parameter (marked : Bool) : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := marked }
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def function (marked : Bool) : Dynamic.Closure := {
  parameters := [parameter marked], resultType := .unit, body := [], source, captured := []
  context := Context.ofSignatures ⟨[], [], [], [], [], []⟩, evidence := [] }
private def contract (marked : Bool) : Staging.CallGuard.Contract := ⟨[parameter marked], false⟩
private def plan : SourceSpecializationWorklist.Plan := ⟨[], [], [], []⟩
private def stages : Staging.CallGuard.Frame := ⟨false, .unit, fun _ => some .runtime⟩
private def ledger : Staging.CallBoundary.Frame := {
  stages, Binds := CallableLedger.Binds plan
  userCallable := CallableLedger.Binds.userCallable, unique := CallableLedger.Binds.unique }

private theorem bound (marked : Bool) : ledger.Binds (.closure (function marked)) (contract marked) := by
  apply CallableLedger.Binds.closure rfl
  constructor
  · intro impossible; cases impossible
  · intro impossible; cases impossible

private theorem ordinaryCaller : ¬ Staging.CallGuard.Effectful stages := by
  rintro (marked | only)
  · cases marked
  · cases only

/-- Even the full source function type omits the explicit parameter flag. -/
example : FunctionValues.sourceType (function true) = FunctionValues.sourceType (function false) := rfl

/-- The ledger preserves that flag before the argument is evaluated. -/
example : Staging.CallBoundary.GuardRejects ledger (id 0) [id 1] (.closure (function true))
    (.argumentStage 0 (id 1) .runtime) := by
  apply Staging.CallBoundary.GuardRejects.contract (bound true)
  apply Staging.CallGuard.Rejects.arguments ordinaryCaller
  exact .head (.wrongStage (.inr (.inl rfl)) rfl (by decide))

example : Staging.CallBoundary.GuardAccepts ledger (id 0) [id 1] (.closure (function false)) := by
  apply Staging.CallBoundary.GuardAccepts.contract (bound false)
  apply Staging.CallGuard.Accepts.ordinary ordinaryCaller
  · apply Staging.CallGuard.ArgumentsAccept.cons
    · apply Staging.CallGuard.ArgumentAccepts.ordinary
      rintro (forced | marked | only)
      · cases forced
      · cases marked
      · cases only
    · exact .nil _
  · exact .ordinary rfl

/-- Core typing alone cannot admit an unregistered contract word, even when
an underlying payload relation accepts the function code and captures. -/
example {catalog : SourceCoreDataCatalog.Catalog} (underlying : CoreLowering.GenericHeap.PayloadModel catalog)
    (table : SourceCoreStageCodebook.Table) (mapping : CoreLowering.GeneralHeap.LocationMap)
    (world : Core.StoreTyping) (sourceType : TypeSystem.Ty) (value : Dynamic.Value) (raw : Core.Value)
    (word : Core.Word) (type : Core.Ty)
    (_typed : Core.RuntimeValueHasType world (.pair raw (.word word)) type catalog.definitions)
    (absent : ∀ entry, entry ∈ table.entries → entry.id ≠ word) :
    ¬ (CallableLedger.model underlying plan table).Represents mapping world sourceType value (.pair raw (.word word)) type := by
  intro represented
  obtain ⟨entry, member, same⟩ := AuthenticatedCallableLedger.descriptor_member represented.2
  exact absent entry member same

/-- The real public preparation result supplies dispatch coverage. There is
no external premise asserting a selected guard or a successful child call. -/
example {catalog : SourceCoreDataCatalog.Catalog} (underlying : CoreLowering.GenericHeap.PayloadModel catalog)
    {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (prepared : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying plan site.table) (CallableLedger.frame sidecar)
      site site.call arguments sourceType type := by
  intro mapping world value carrier contract represented bound
  exact AuthenticatedCallableLedger.covers_of_prepare underlying prepared caller contains form sourceType type represented bound

/-- Contextual source alignment preserves the complete active substitution,
not merely a final erased parameter/result type. -/
example (plan : SourceCoreStageCodebook.Plan) (sidecar : SourceCoreStageContracts.Sidecar)
    (prepared : SourceCoreLocalEvidence.Prepared) (id : ExpressionId) (contract : SourceCoreStageContracts.Contract)
    (selected : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
    (accepted : SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id = .ok contract) :
    (AuthenticatedCallableLedger.LambdaSource.contextual sidecar prepared id contract selected accepted).source =
      sidecar.source.applySubstitution prepared.substitution := rfl

end Tests.SourceCallableLedger
