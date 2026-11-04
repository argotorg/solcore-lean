import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GenericHeaps
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CaptureCopies
import Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Frontend.SourceCoreElaboration
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime

/-!
# Lambda views and marked captures

`LambdaMetadataViews`, the Source view of runtime metadata, with marked capture copies and their typing, the authenticated callable ledger, and the form of authenticated references.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
/-! The actual function finish helper preserves returned values, Unit
fallthrough, source faults and escaped loop control with their distinct source
call outcomes. The heap is unchanged after the flow has completed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

inductive FinishedRep {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (faults : FunctionCalls.FaultRep) :
    TypeSystem.Ty → Ty → Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      FinishedRep functions mapping world faults .unit .unit
        (.fallthrough environment) (.inRight .word .unit)
  | returned {expected type sourceValue value}
      (payload : ValueRep values.checked registry functions mapping world
        expected sourceValue value type) :
      FinishedRep functions mapping world faults expected type
        (.returned sourceValue) (.inRight .word value)
  | fault {expected type reason token} (matched : faults reason token) :
      FinishedRep functions mapping world faults expected type
        (.fault reason) (.inLeft type (.word token))
  | breaking {expected type token} (environment : Dynamic.Environment)
      (matched : faults .controlEscapedFunction token) :
      FinishedRep functions mapping world faults expected type
        (.breaking environment) (.inLeft type (.word token))
  | continuing {expected type token} (environment : Dynamic.Environment)
      (matched : faults .controlEscapedFunction token) :
      FinishedRep functions mapping world faults expected type
        (.continuing environment) (.inLeft type (.word token))

theorem result {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {control : Dynamic.ControlOutcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FinishedRep (registry := registry) functions mapping world faults
      expected type control value)
    (exit : CompatibleNamedBody.Exit expected control outcome) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world expected type faults outcome value := by
  cases related with
  | fallthrough environment => cases exit; exact .value .unit
  | returned payload => cases exit; exact .value payload
  | fault matched => cases exit; exact .fault matched
  | breaking environment matched => cases exit; exact .fault matched
  | continuing environment matched => cases exit; exact .fault matched

theorem rename (type : Ty) (flow : Expr) (fellThrough escaped : Word)
    (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

theorem input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {value : Value}
    (evaluated : Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) value after) :
    ∃ result middle, Evaluates environment before flow result middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

/-- Only a reached break or continue requests the escaped-control token. -/
def TransferFaults (faults : FunctionCalls.FaultRep) (escaped : Word)
    (outcome : Dynamic.ControlOutcome) : Prop :=
  (∀ next, outcome = .breaking next → faults .controlEscapedFunction escaped) ∧
  (∀ next, outcome = .continuing next → faults .controlEscapedFunction escaped)

/-- The caller derives the raw Unit condition from its source grammar and
actual successful fallthrough. Escaped control uses the real diagnostic token
and is reflected as the independent controlEscapedFunction fault. -/
theorem from_flow_with_transfers {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome}
    {flow : Expr} {value : Value}
    (rawUnit : ∀ next, outcome = .fallthrough next → expected = .unit)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (transferFaults : TransferFaults faults escaped outcome)
    (related : TypedLexicalWhile.FlowRep (registry := registry) functions
      mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      FinishedRep (registry := registry) functions mapping world faults
        expected type outcome result := by
  cases related with
  | fallthrough next =>
    have raw := rawUnit next rfl
    subst expected
    have native : type = .unit := by
      change Except.ok (.unit : Ty) = .ok type at projection
      exact Except.ok.inj projection.symm
    subst type
    exact ⟨_, LocalControl.finish_fallthrough .unit
      (LocalLoop.toControl_normal _ escaped evaluated)
      (by simpa [LanguageResult.success, Expr.weakenAt] using
        (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after
          (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)),
      .fallthrough next⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _
      (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩
  | breaking next =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_transfer _ escaped evaluated), .breaking next (transferFaults.1 next rfl)⟩
  | continuing next =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_transfer _ escaped evaluated), .continuing next (transferFaults.2 next rfl)⟩


theorem from_flow {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome}
    {flow : Expr} {value : Value}
    (rawUnit : ∀ next, outcome = .fallthrough next → expected = .unit)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (escapedFault : faults .controlEscapedFunction escaped)
    (related : TypedLexicalWhile.FlowRep (registry := registry) functions
      mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      FinishedRep (registry := registry) functions mapping world faults
        expected type outcome result := by
  exact from_flow_with_transfers functions rawUnit projection fellThrough escaped
    ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩ related evaluated

end Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger
/-! Actual artifact origins establish the static source-stage ledger for
represented callable values. Lambda code is joined to its original metadata
through an explicit source-table alignment, retaining the full local context.
That alignment is not recovered from Core typing or a boolean caller check.
No body execution is assumed; recursive stage-frame propagation is separate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger
open Frontend Frontend.SourceInference SourceCoreStageCodebook GeneralHeap
open CallContractCertificates CallEntryCertificates

/-- Which original source table supplies this lambda's metadata. -/
inductive LambdaSource (plan : Plan) : Key → ExpressionId → TypeSystem.Substitution → Contract → Type where
  | original (sidecar : Sidecar) (id : ExpressionId) (contract : Contract)
      (selected : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (prepared : SourceCoreStageContracts.Contract.lambda sidecar id = .ok contract) :
      LambdaSource plan sidecar.caller.key id [] contract
  | contextual (sidecar : Sidecar) (preparedContext : SourceCoreLocalEvidence.Prepared) (id : ExpressionId) (contract : Contract)
      (selected : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (prepared : SourceCoreStageContracts.Contract.contextualLambda sidecar preparedContext id = .ok contract) :
      LambdaSource plan sidecar.caller.key id preparedContext.substitution contract

def LambdaSource.source {plan : Plan} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {contract : Contract} : LambdaSource plan owner id active contract → TypedSource
  | .original sidecar _ _ _ _ => sidecar.source
  | .contextual sidecar preparedContext _ _ _ _ => sidecar.source.applySubstitution preparedContext.substitution

structure LambdaSite (plan : Plan) (table : Table) (owner : Key) (id : ExpressionId)
    (active : TypeSystem.Substitution) (descriptor : Core.Word) where
  entry : Entry
  member : entry ∈ table.entries
  origin : entry.origin = .lambda owner id active
  id_eq : entry.id = descriptor
  contract : Contract
  retained : entry.contract = some contract
  original : LambdaSource plan owner id active contract

/-- An actual descriptor and public prepare success recover its original
lambda factory receipt, including contextual substitutions and source owner. -/
theorem lambda_site_of_descriptor {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    (accepted : prepare program plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active)) :
    Nonempty (LambdaSite plan table owner id active descriptor.id) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepare_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | originalLambda selected prepared =>
    exact ⟨⟨entry, member, origin, id_eq, _, contract_eq, .original _ _ _ selected prepared⟩⟩
  | contextualLambda selected prepared =>
    exact ⟨⟨entry, member, origin, id_eq, _, contract_eq, .contextual _ _ _ _ selected prepared⟩⟩

/-- Named provenance uses the exact source instantiation selected by the plan;
its original parameter markers are obtained from the real named factory. -/
theorem named_origin {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table} {key : Key} {function : Dynamic.GlobalFunction}
    (accepted : prepare program plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.global function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepare_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named prepared =>
    have related := CallableLedger.OriginRep.named (raw := raw) member origin contract_eq selected prepared
    simpa only [id_eq] using related

/-- Builtin descriptors retain their bypass status, with no user-callable
contract fabricated from their projected Core function type. -/
theorem builtin_origin {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table} {function : Dynamic.BuiltinFunction}
    (accepted : prepare program plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.builtin function.id)) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.builtin function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepare_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | builtin =>
    have related := CallableLedger.OriginRep.builtin (plan := plan) (raw := raw) member origin contract_eq
    simpa only [id_eq] using related

/-- All values in this origin scope have a defined source guard outcome,
including builtin bypass. The ledger cannot silently omit a represented call. -/
theorem guard_complete {sidecar : Sidecar} {table : Table} {source : Dynamic.Value} {carrier : Core.Value}
    (origin : CallableLedger.OriginRep sidecar.plan table source carrier) (call : ExpressionId) (arguments : List ExpressionId) :
    Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) call arguments source ∨
      ∃ reason, Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) call arguments source reason := by
  cases origin with
  | closure _ _ _ provenance =>
    have bound := provenance.binds
    rcases Staging.CallGuard.complete (CallStageGuard.frame sidecar.caller) _ call arguments with yes | ⟨reason, no⟩
    · exact .inl (.contract bound yes)
    · exact .inr ⟨reason, .contract bound no⟩
  | named _ _ _ selected prepared =>
    have bound := CallableLedger.Binds.named selected prepared
    rcases Staging.CallGuard.complete (CallStageGuard.frame sidecar.caller) _ call arguments with yes | ⟨reason, no⟩
    · exact .inl (.contract bound yes)
    · exact .inr ⟨reason, .contract bound no⟩
  | builtin => exact .inl (.builtin _)

/-- Descriptor membership is a provenance obligation beyond Core typing. -/
theorem descriptor_member {plan : Plan} {table : Table} {source : Dynamic.Value} {raw : Core.Value} {id : Core.Word}
    (origin : CallableLedger.OriginRep plan table source (.pair raw (.word id))) :
    ∃ entry, entry ∈ table.entries ∧ entry.id = id := by
  cases origin with
  | closure member _ _ _ => exact ⟨_, member, rfl⟩
  | named member _ _ _ _ => exact ⟨_, member, rfl⟩
  | builtin member _ _ => exact ⟨_, member, rfl⟩

/-- Full source-table alignment and the actual compiled lambda occurrence
suffice to recover its source parameters/result/body. They are not additional
assumptions about a child execution or its result. -/
theorem LambdaSource.alignment {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {contract : Contract} (original : LambdaSource plan owner id active contract)
    {function : Dynamic.Closure} {node : ExpressionNode}
    (source_eq : function.source = original.source)
    (unique : NodeOccurrencesUnique function.source)
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) :
    CallableLedger.LambdaOrigin plan owner id active function contract := by
  cases original with
  | original sidecar id contract selected prepared =>
    change function.source = sidecar.source at source_eq
    obtain ⟨receipt⟩ := lambda_of_accepted prepared
    have contains : ContainsExpression sidecar.source id node := source_eq ▸ lookupExpression?_sound found
    have same := expression_unique receipt.selected contains
    have forms := form.symm.trans ((congrArg ExpressionNode.form same).trans receipt.form)
    have fields := ExpressionForm.lambda.inj forms
    exact .original prepared receipt (sidecar_of_accepted selected).1 rfl source_eq fields.1 fields.2.1 fields.2.2
  | contextual sidecar preparedContext id contract selected prepared =>
    obtain ⟨receipt⟩ := contextualLambda_of_accepted prepared
    have contains := FlexibleSubstitution.ContainsExpression.applySubstitution preparedContext.substitution (expression_sound receipt.selected)
    have atSource : ContainsExpression function.source id (receipt.node.applySubstitution preparedContext.substitution) :=
      source_eq.symm ▸ contains
    have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique atSource))
    have mappedForm : (receipt.node.applySubstitution preparedContext.substitution).form =
        .lambda (receipt.parameters.map (TypedBinder.applySubstitution preparedContext.substitution))
          (preparedContext.substitution.apply receipt.result) receipt.body := by
      simp only [ExpressionNode.applySubstitution, receipt.form, ExpressionForm.applySubstitution]
    have forms := form.symm.trans ((congrArg ExpressionNode.form same).trans mappedForm)
    have fields := ExpressionForm.lambda.inj forms
    exact .contextual prepared receipt (sidecar_of_accepted selected).1 rfl source_eq fields.1 fields.2.1 fields.2.2

/-- Join original stage provenance to the existing code/capture certificate.
The inserted administrative environment stays inside the original value
relation; the static origin proof does not rewrite closure captures. -/
theorem code_origin {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {plan : Plan} {table : Table} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : Core.StoreTyping}
    {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (site : LambdaSite plan table compilation.owner code.id active code.descriptor.id)
    (source_eq : function.source = site.original.source) :
    CallableLedger.OriginRep plan table (.closure function)
      (ContractedFunctionValues.value code.artifact.raw.parameterCore code.artifact.raw.resultCore
        code.artifact.raw.rawBody layout.embedding actual code.descriptor.id) := by
  have origin := site.original.alignment source_eq code.frame.code.graph.nodeOccurrencesUnique
    code.artifact.raw.found code.artifact.raw.form
  have related := CallableLedger.OriginRep.closure (raw := FunctionValues.value code.artifact.raw.parameterCore
    code.artifact.raw.resultCore code.artifact.raw.rawBody layout.embedding actual)
    site.member site.origin site.retained origin
  simpa only [ContractedFunctionValues.value, site.id_eq] using related

/-- A formed closure inhabits the scoped stage-aware payload model once its
original source alignment has been authenticated. -/
theorem represented_code {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {plan : Plan} {table : Table} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : Core.StoreTyping}
    {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (site : LambdaSite plan table compilation.owner code.id active code.descriptor.id)
    (source_eq : function.source = site.original.source) :
    (CallableLedger.model (ContractedFunctionValues.model catalog program bodyCertificate table) plan table).Represents
      mapping world (FunctionValues.sourceType function) (.closure function)
      (ContractedFunctionValues.value code.artifact.raw.parameterCore code.artifact.raw.resultCore
        code.artifact.raw.rawBody layout.embedding actual code.descriptor.id)
      (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) :=
  ⟨.closure layout code, code_origin layout code site source_eq⟩

/-- Public factory success supplies all guarded rows needed by `Covers` for
this refined model. The remaining hypotheses are original caller/call metadata. -/
theorem covers_of_prepare {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepare program plan checked limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying plan site.table) (CallableLedger.frame sidecar)
      site site.call arguments sourceType type := by
  have rows := CallCodebookCertificates.rows_of_prepare accepted caller contains form
  rw [← (sidecar_of_accepted caller).1]
  intro mapping world source carrier contract represented bound
  exact CallableLedger.covers underlying rows sourceType type represented bound

end Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LambdaSourceAlignment
/-! Canonical source provenance from actual specialization preparation.
The local-evidence factory reconstructs the original plan caller and applies
its complete active substitution. Its success therefore establishes source
alignment without reflecting the unrelated boolean equality of entire callers.

The compiler also uses temporary raw metadata views during output coercion
lowering. Those views are not equal to the complete original source table.
`SourceReceipt` certifies canonical original/contextual inputs only; forwarding
it through arbitrary raw views requires an occurrence correspondence, not an
assertion that the source tables remain equal. No execution premise is used. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.LambdaSourceAlignment
open Frontend Frontend.SourceInference SourceCoreStageContracts
open AuthenticatedCallableLedger

private theorem bind_ok {α β ε : Type} {operation : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (operation >>= next) = .ok value) :
    ∃ result, operation = .ok result ∧ next result = .ok value := by
  cases operation with
  | error => cases accepted
  | ok result => exact ⟨result, rfl, accepted⟩

/-- The public sidecar and compiler use the same exact plan lookup. -/
theorem sidecar_lookup {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.exactSpecialization plan key = .ok sidecar.caller := by
  unfold prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; rfl
        · cases accepted

/-- The source equality here comes from the factory's propositional check. -/
theorem exactCaller_source {plan : Plan} {binding : SourceCoreLocalPolymorphism.Binding}
    {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok caller) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan binding.caller with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok original =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · next same =>
      split at accepted
      · cases accepted; exact ⟨rfl, Classical.not_not.mp same⟩
      · cases accepted

/-- Actual preparation returns a contextual source of the exact original
caller. It retains the candidate's entire cumulative substitution. -/
theorem prepared_source {program : CheckedProgram} {plan : Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    ∃ original,
      SourceCompilationPlan.exactSpecialization plan candidate.origin.caller = .ok original ∧
      original.function.typedBody = candidate.origin.source ∧
      prepared.substitution = candidate.origin.substitution ∧
      prepared.source = original.function.typedBody.applySubstitution prepared.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨original, selected, accepted⟩ := bind_ok accepted
  have authenticated := exactCaller_source selected
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact ⟨original, authenticated.1, authenticated.2, rfl, rfl⟩

/-- A static input source comes from an actual compiler preparation path.
The contextual constructor requires real local-evidence factory success,
not a freely supplied equality of its returned metadata. -/
inductive SourceReceipt (program : CheckedProgram) (plan : Plan) :
    Key → TypeSystem.Substitution → TypedSource → Prop where
  | original {owner : Key} {caller : SourceSpecialization.SpecializedFunction}
      (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok caller) :
      SourceReceipt program plan owner [] caller.function.typedBody
  | contextual {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
      {prepared : SourceCoreLocalEvidence.Prepared}
      (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
      SourceReceipt program plan candidate.origin.caller prepared.substitution prepared.source

/-- The canonical sidecar identifies the same source for either preparation
path, including an empty cumulative local substitution. -/
theorem SourceReceipt.source {program : CheckedProgram} {plan : Plan} {owner : Key}
    {active : TypeSystem.Substitution} {source : TypedSource} {sidecar : Sidecar}
    (receipt : SourceReceipt program plan owner active source)
    (selected : prepareSidecar plan owner = .ok sidecar) :
    source = sidecar.source.applySubstitution active := by
  have original := sidecar_lookup selected
  cases receipt with
  | original caller =>
    have same := Except.ok.inj (caller.symm.trans original)
    cases same
    simp only [EmptySourceSubstitution.source, Sidecar.source]
  | contextual prepared =>
    obtain ⟨caller, exactCaller, _, _, source_eq⟩ := prepared_source prepared
    have same := Except.ok.inj (exactCaller.symm.trans original)
    cases same
    exact source_eq

/-- A codebook lambda receipt uses precisely the sidecar's source with the
origin's full active substitution, even when insertion reused an older entry. -/
theorem LambdaSource.canonical {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {contract : Contract}
    (original : AuthenticatedCallableLedger.LambdaSource plan owner id active contract) :
    ∃ sidecar, prepareSidecar plan owner = .ok sidecar ∧
      original.source = sidecar.source.applySubstitution active := by
  cases original with
  | original sidecar id contract selected prepared =>
    exact ⟨sidecar, selected, (EmptySourceSubstitution.source _).symm⟩
  | contextual sidecar preparedContext id contract selected prepared =>
    exact ⟨sidecar, selected, rfl⟩

/-- Eliminate the previous free source-equality premise using actual compiler
preparation and the actual codebook lambda site. -/
theorem source_alignment {program : CheckedProgram} {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {source : TypedSource} {contract : Contract}
    (receipt : SourceReceipt program plan owner active source)
    (original : AuthenticatedCallableLedger.LambdaSource plan owner id active contract) :
    source = original.source := by
  obtain ⟨sidecar, selected, source_eq⟩ := LambdaSource.canonical original
  exact (receipt.source selected).trans source_eq.symm


/-- The original decorated-code relation now consumes a factory receipt,
rather than an unconstrained equality with the codebook's source table. -/
theorem code_origin {catalog : SourceCoreDataCatalog.Catalog} {checkedProgram : CheckedProgram} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (site : LambdaSite plan table compilation.owner code.id active code.descriptor.id)
    (receipt : SourceReceipt checkedProgram plan compilation.owner active function.source) :
    CallableLedger.OriginRep plan table (.closure function)
      (ContractedFunctionValues.value code.artifact.raw.parameterCore code.artifact.raw.resultCore
        code.artifact.raw.rawBody layout.embedding actual code.descriptor.id) :=
  AuthenticatedCallableLedger.code_origin layout code site (source_alignment receipt site.original)

/-- Actual public codebook preparation and the descriptor in the emitted
closure recover its lambda site; callers do not supply a chosen site. -/
theorem code_origin_of_prepare {catalog : SourceCoreDataCatalog.Catalog} {checkedProgram : CheckedProgram} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (receipt : SourceReceipt checkedProgram plan compilation.owner active function.source) :
    CallableLedger.OriginRep plan table (.closure function)
      (ContractedFunctionValues.value code.artifact.raw.parameterCore code.artifact.raw.resultCore
        code.artifact.raw.rawBody layout.embedding actual code.descriptor.id) := by
  obtain ⟨site⟩ := lambda_site_of_descriptor accepted code.descriptor
  exact code_origin layout code site receipt

end Solcore.SourceSemantics.CoreLowering.LambdaSourceAlignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
/-! Temporary metadata views preserve the source shapes used by callable
contracts. The actual evidence lowerer can change an expression's output type,
requirements, and coercion path without changing its occurrence or form.

The source table remains distinct from the compiler view. This relation proves
lambda parameter/result/body provenance, not typing or execution equivalence
of arbitrary metadata edits, nor general decorated-body code correspondence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
open Frontend Frontend.SourceInference DataPatternValues

inductive NodeView : Node → Node → Prop where
  | expression {before after : ExpressionNode} (id : before.id = after.id)
      (form : before.form = after.form) : NodeView (.expression before) (.expression after)
  | statement (node : StatementNode) : NodeView (.statement node) (.statement node)

theorem NodeView.occurrence {before after : Node} (related : NodeView before after) :
    before.occurrenceId = after.occurrenceId := by
  cases related with
  | expression id _ => exact congrArg ExpressionId.occurrence id
  | statement => rfl

theorem NodeView.refl (node : Node) : NodeView node node := by
  cases node with
  | expression => exact .expression rfl rfl
  | statement => exact .statement _

theorem NodeView.symm {before after : Node} (related : NodeView before after) : NodeView after before := by
  cases related with
  | expression id form => exact .expression id.symm form.symm
  | statement => exact .statement _

theorem NodeView.trans {a b c : Node} (left : NodeView a b) (right : NodeView b c) : NodeView a c := by
  cases left with
  | expression id form => cases right with | expression id' form' => exact .expression (id.trans id') (form.trans form')
  | statement => exact right

structure MetadataView (original view : TypedSource) : Prop where
  owner : original.owner = view.owner
  inputs : original.inputs = view.inputs
  roots : original.roots = view.roots
  nodes : ListRel NodeView original.nodes view.nodes

private theorem nodes_refl (nodes : List Node) : ListRel NodeView nodes nodes := by
  induction nodes with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.refl head) ih

private theorem nodes_symm {a b : List Node} (related : ListRel NodeView a b) : ListRel NodeView b a := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons head.symm ih

private theorem nodes_trans {a b c : List Node} (left : ListRel NodeView a b) (right : ListRel NodeView b c) :
    ListRel NodeView a c := by
  induction left generalizing c with
  | nil => exact right
  | cons head rest ih => cases right with | cons head' rest' => exact .cons (head.trans head') (ih rest')

theorem MetadataView.refl (source : TypedSource) : MetadataView source source :=
  ⟨rfl, rfl, rfl, nodes_refl _⟩

theorem MetadataView.symm {a b : TypedSource} (related : MetadataView a b) : MetadataView b a :=
  ⟨related.owner.symm, related.inputs.symm, related.roots.symm, nodes_symm related.nodes⟩

theorem MetadataView.trans {a b c : TypedSource} (left : MetadataView a b) (right : MetadataView b c) :
    MetadataView a c :=
  ⟨left.owner.trans right.owner, left.inputs.trans right.inputs, left.roots.trans right.roots,
    nodes_trans left.nodes right.nodes⟩

private theorem nodes_occurrences {a b : List Node} (related : ListRel NodeView a b) :
    a.map Node.occurrenceId = b.map Node.occurrenceId := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.occurrence, ih]

theorem MetadataView.unique {original view : TypedSource} (related : MetadataView original view)
    (unique : NodeOccurrencesUnique original) : NodeOccurrencesUnique view := by
  change (view.nodes.map Node.occurrenceId).Nodup
  rw [← nodes_occurrences related.nodes]
  exact unique

private inductive Selection : Option Node → Option Node → Prop where
  | none : Selection none none
  | some {before after : Node} (related : NodeView before after) : Selection (some before) (some after)

private theorem nodes_declared {a b : List Node} (related : ListRel NodeView a b) :
    a.flatMap SourceSemantics.CaptureBinders.nodeBinders = b.flatMap SourceSemantics.CaptureBinders.nodeBinders := by
  induction related with
  | nil => rfl
  | cons head _ ih =>
    cases head with
    | expression _ form => simp only [List.flatMap_cons, SourceSemantics.CaptureBinders.nodeBinders, form, ih]
    | statement => simp only [List.flatMap_cons, ih]

/-- A metadata view declares the same binders, so closures copy the same
captured bindings under it. -/
theorem MetadataView.copiedBinder {original view : TypedSource} (related : MetadataView original view) :
    SourceSemantics.CaptureBinders.copiedBinder? original = SourceSemantics.CaptureBinders.copiedBinder? view := by
  funext id
  have declared : SourceSemantics.CaptureBinders.declaredBinders original =
      SourceSemantics.CaptureBinders.declaredBinders view := by
    unfold SourceSemantics.CaptureBinders.declaredBinders
    rw [related.inputs]
    congr 1
    exact nodes_declared related.nodes
  simp only [SourceSemantics.CaptureBinders.copiedBinder?, declared]

private theorem find_related {a b : List Node} (related : ListRel NodeView a b) (id : OccurrenceId) :
    Selection (a.find? fun node => decide (node.occurrenceId = id))
      (b.find? fun node => decide (node.occurrenceId = id)) := by
  induction related with
  | nil => exact .none
  | @cons before tail after rest head _ ih =>
    simp only [List.find?_cons, head.occurrence]
    split
    · exact .some head
    · exact ih

/-- An actual view lookup reconstructs the original occurrence and its exact
form; no claim is made that the expression metadata fields are equal. -/
theorem MetadataView.expression {original view : TypedSource} (related : MetadataView original view)
    {id : ExpressionId} {node : ExpressionNode} (found : view.lookupExpression? id = some node) :
    ∃ originalNode, original.lookupExpression? id = some originalNode ∧
      originalNode.id = node.id ∧ originalNode.form = node.form := by
  have selected := find_related related.nodes id.occurrence
  change Selection (original.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupExpression? at found ⊢
  cases left : original.lookupNode? id.occurrence <;> cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected found ⊢
  · cases found
  · cases selected
  · cases found
  · cases selected with
    | some values =>
      cases values with
      | expression sameId sameForm =>
        cases found
        exact ⟨_, rfl, sameId, sameForm⟩
      | statement => cases found

/-- Raw expression views leave every statement node intact. This supports
later body certificates that retain the original statement metadata. -/
theorem MetadataView.statement {original view : TypedSource} (related : MetadataView original view)
    {id : StatementId} {node : StatementNode} (found : view.lookupStatement? id = some node) :
    original.lookupStatement? id = some node := by
  have selected := find_related related.nodes id.occurrence
  change Selection (original.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupStatement? at found ⊢
  cases left : original.lookupNode? id.occurrence <;> cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected found ⊢
  · cases found
  · cases selected
  · cases found
  · cases selected with
    | some values =>
      cases values with
      | expression => cases found
      | statement => exact found

private theorem nodes_map (nodes : List Node) (change : Node → Node)
    (each : ∀ old ∈ nodes, NodeView old (change old)) : ListRel NodeView nodes (nodes.map change) := by
  induction nodes with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (each head (by simp)) (ih (by intro old member; exact each old (List.mem_cons_of_mem head member)))

private theorem withNode_nodes {source : TypedSource} {node replacement : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (sameId : node.id = replacement.id) (sameForm : node.form = replacement.form) :
    ListRel NodeView source.nodes (SourceCoreEvidence.withNode source replacement).nodes := by
  change ListRel NodeView source.nodes (source.nodes.map _)
  apply nodes_map
  intro old member
  cases old with
  | statement current => exact .statement _
  | expression current =>
    by_cases same : current.id = replacement.id
    · have lookup := lookupExpression?_complete unique (show ContainsExpression source node.id current from
        ⟨member, same.trans sameId.symm⟩)
      have eq := Option.some.inj (lookup.symm.trans found)
      subst current
      simpa only [same, ↓reduceIte] using NodeView.expression sameId sameForm
    · simpa only [same, ↓reduceIte] using NodeView.expression (before := current) rfl rfl

/-- The real evidence lowerer's replacement preserves the metadata view when
it retains the selected occurrence's ID and form. -/
theorem withNode_view {source : TypedSource} {node replacement : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (sameId : node.id = replacement.id) (sameForm : node.form = replacement.form) :
    MetadataView source (SourceCoreEvidence.withNode source replacement) :=
  ⟨rfl, rfl, rfl, withNode_nodes unique found sameId sameForm⟩

/-- Exact raw view emitted by `SourceCoreEvidence.lowerWithCaller`. Ordinary
requirement ownership can change independently of the preserved lambda form. -/
theorem raw_view {source : TypedSource} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (ordinary : List RequirementId) :
    MetadataView source (SourceCoreEvidence.withNode source
      { node with type := node.rawType, requirements := ordinary, coercions := [] }) :=
  withNode_view unique found rfl rfl

/-- Local scheme-evidence normalization has the same metadata-view law.
The accepted factory compares the actual occurrence before replacing only its
ordinary requirements; repeated normalization preserves the current view. -/
theorem normalized_view {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source normalized : TypedSource} {id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id = .ok normalized) :
    MetadataView source normalized := by
  unfold SourceCoreLocalEvidence.normalizeOccurrence at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next reference reference_found =>
      split at accepted
      · next current current_found =>
        split at accepted
        · next ordinary ordinary_found =>
          split at accepted
          · next same =>
            cases accepted
            subst current
            have atSelf : source.lookupExpression? reference.original.id = some reference.original := by
              simpa only [(lookupExpression?_sound current_found).2] using current_found
            have related := withNode_view (replacement := reference.normalized) unique atSelf rfl rfl
            have sameId : reference.normalized.id = id := (lookupExpression?_sound current_found).2
            have views : { source with nodes := source.nodes.map (fun
                | .expression old => if old.id = id then .expression reference.normalized else .expression old
                | .statement old => .statement old) } = SourceCoreEvidence.withNode source reference.normalized := by
              unfold SourceCoreEvidence.withNode
              apply congrArg (fun (nodes : List Node) => ({ source with nodes := nodes } : TypedSource))
              apply List.map_congr_left
              intro item _
              cases item with
              | expression old => by_cases equal : old.id = id <;> simp [sameId, equal]
              | statement => rfl
            exact views.symm ▸ related
          · split at accepted
            · cases accepted; exact .refl _
            · cases accepted
        · cases accepted
      · cases accepted

/-- Canonical preparation plus actual raw-view lookup suffices for source
lambda provenance. The source closure keeps the canonical table; the code
certificate may separately refer to the compiler's temporary view. -/
theorem lambda_origin {checked : CheckedProgram} {plan : SourceCoreStageContracts.Plan}
    {owner : SourceCoreStageContracts.Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {contract : SourceCoreStageContracts.Contract} {function : Dynamic.Closure} {view : TypedSource}
    {node : ExpressionNode}
    (receipt : LambdaSourceAlignment.SourceReceipt checked plan owner active function.source)
    (original : AuthenticatedCallableLedger.LambdaSource plan owner id active contract)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) :
    CallableLedger.LambdaOrigin plan owner id active function contract := by
  obtain ⟨sourceNode, selected, _, sameForm⟩ := metadata.expression found
  exact original.alignment (LambdaSourceAlignment.source_alignment receipt original) unique selected (sameForm.trans form)

/-- The real codebook factory and descriptor recover callable provenance for
a lambda compiled through temporary metadata views. This is the origin half
of the payload relation: the raw code/capture certificate remains separate. -/
theorem origin_of_prepare {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {owner : SourceCoreStageCodebook.Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {function : Dynamic.Closure} {view : TypedSource} {node : ExpressionNode}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt checkedProgram plan owner active function.source)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨site⟩ := AuthenticatedCallableLedger.lambda_site_of_descriptor accepted descriptor
  have origin := lambda_origin receipt site.original metadata unique found form
  have represented := CallableLedger.OriginRep.closure (raw := raw) site.member site.origin site.retained origin
  simpa only [site.id_eq] using represented

/-- Consume the actual accepted decorated-lambda certificate at its compiler
view, while keeping the source closure and its staging contract canonical.
This theorem concerns provenance; a value simulation must additionally relate
the certificate's emitted raw body and captured environment. -/
theorem decorated_origin_of_prepare {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view scope id node
      function.parameters function.resultType function.body reportedType lowered) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) :=
  origin_of_prepare accepted descriptor receipt metadata unique artifact.raw.found artifact.raw.form raw

end Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarkedSupport
/-! Support for the marked copies of a closure's captured cells. The copy chain
walks a suffix of the scope head first, counting the copies made so far, while
the renaming of the body is fixed over the whole scope. The bookkeeping here
relates the two: the copied slots of a suffix, the renaming's value on the
slot being copied or skipped, and a pending agreement that sends the processed
slots past the copies still to be made. One marked copy evaluates under the
actual renaming by transporting the allocator's receipts. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopies
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open SourceSemantics.CaptureBinders (copiedBinder?)
open CallableIndexedAllocationCompletion (PayloadAt optionalValue)

/-! ## The copy renaming -/

/-- A position outside the copied ones moves past every copy. -/
theorem copyRenaming_not_mem {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    SourceCoreSourceCells.copyRenaming positions index = index + positions.length := by
  have none : positions.findIdx? (fun position => decide (position = index)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro position mem
    simp only [decide_eq_false_iff_not]
    intro same
    exact absent (same ▸ mem)
  simp [SourceCoreSourceCells.copyRenaming, none]

/-- The copy of a position lies below the copies made after it. -/
theorem copyRenaming_mem {done remaining : List Nat} {index : Nat} (fresh : index ∉ done) :
    SourceCoreSourceCells.copyRenaming (done ++ index :: remaining) index = remaining.length := by
  have none : done.findIdx? (fun position => decide (position = index)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro position mem
    simp only [decide_eq_false_iff_not]
    intro same
    exact fresh (same ▸ mem)
  simp only [SourceCoreSourceCells.copyRenaming, List.findIdx?_append, none, List.findIdx?_cons,
    decide_true, ↓reduceIte, Option.none_or, Option.map_some, List.length_append, List.length_cons]
  omega

/-! ## Copied slots of a scope suffix -/

/-- The copied slots of the suffix `rest` of a scope, whose first slot has
scope index `index`. -/
def copiedSlotsFrom (source : TypedSource) (rest : SourceCoreLocalCell.Scope) (index : Nat) :
    List (Nat × TypedBinder × Core.Ty) :=
  (rest.zipIdx index).filterMap fun ((id, type), index) =>
    (copiedBinder? source id).map fun binder => (index, binder, type)

theorem copiedSlots_eq (source : TypedSource) (scope : SourceCoreLocalCell.Scope) :
    SourceCoreSourceCells.copiedSlots source scope = copiedSlotsFrom source scope 0 := rfl

theorem copiedSlotsFrom_nil (source : TypedSource) (index : Nat) :
    copiedSlotsFrom source [] index = [] := rfl

theorem copiedSlotsFrom_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index : Nat) (uncopied : copiedBinder? source id = none) :
    copiedSlotsFrom source ((id, type) :: rest) index = copiedSlotsFrom source rest (index + 1) := by
  simp [copiedSlotsFrom, uncopied]

theorem copiedSlotsFrom_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (copied : copiedBinder? source id = some binder) :
    copiedSlotsFrom source ((id, type) :: rest) index =
      (index, binder, type) :: copiedSlotsFrom source rest (index + 1) := by
  simp [copiedSlotsFrom, copied]

/-- Every copied slot of a suffix lies at or past its first index. -/
theorem copiedSlotsFrom_le (source : TypedSource) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat) (slot : Nat × TypedBinder × Core.Ty),
      slot ∈ copiedSlotsFrom source rest index → index ≤ slot.1
  | [], _, _, mem => by simp [copiedSlotsFrom] at mem
  | (id, type) :: rest, index, slot, mem => by
      cases copied : copiedBinder? source id with
      | none =>
          rw [copiedSlotsFrom_shared rest index copied] at mem
          exact Nat.le_of_succ_le (copiedSlotsFrom_le source rest (index + 1) slot mem)
      | some binder =>
          rw [copiedSlotsFrom_copied rest index copied, List.mem_cons] at mem
          rcases mem with same | mem
          · subst same; exact Nat.le_refl _
          · exact Nat.le_of_succ_le (copiedSlotsFrom_le source rest (index + 1) slot mem)

/-- The copies the chain over `rest` still makes. -/
def pendingCopies (source : TypedSource) (rest : SourceCoreLocalCell.Scope) (index : Nat) : Nat :=
  (copiedSlotsFrom source rest index).length

/-- The body renaming seen from a chain state: `done` holds the positions
already copied, `rest` at `index` the slots still to process. -/
def chainRenaming (source : TypedSource) (preLength : Nat) (done : List Nat)
    (rest : SourceCoreLocalCell.Scope) (index : Nat) : Renaming :=
  SourceCoreSourceCells.copyRenaming
    (done ++ (copiedSlotsFrom source rest index).map fun slot => slot.1 + preLength)

theorem chainRenaming_scope (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (preLength : Nat) :
    chainRenaming source preLength [] scope 0 = SourceCoreSourceCells.scopeCopyRenaming source scope (· + preLength) :=
  rfl

theorem chainRenaming_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (preLength : Nat) (done : List Nat) (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (uncopied : copiedBinder? source id = none) :
    chainRenaming source preLength done ((id, type) :: rest) index =
      chainRenaming source preLength done rest (index + 1) := by
  simp only [chainRenaming, copiedSlotsFrom_shared rest index uncopied]

theorem chainRenaming_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (preLength : Nat) (done : List Nat) (rest : SourceCoreLocalCell.Scope)
    (index : Nat) (copied : copiedBinder? source id = some binder) :
    chainRenaming source preLength done ((id, type) :: rest) index =
      chainRenaming source preLength (done ++ [index + preLength]) rest (index + 1) := by
  simp only [chainRenaming, copiedSlotsFrom_copied rest index copied, List.map_cons, List.append_assoc,
    List.singleton_append]

theorem pendingCopies_shared {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index : Nat) (uncopied : copiedBinder? source id = none) :
    pendingCopies source ((id, type) :: rest) index = pendingCopies source rest (index + 1) := by
  simp only [pendingCopies, copiedSlotsFrom_shared rest index uncopied]

theorem pendingCopies_copied {source : TypedSource} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} (rest : SourceCoreLocalCell.Scope) (index : Nat)
    (copied : copiedBinder? source id = some binder) :
    pendingCopies source ((id, type) :: rest) index = pendingCopies source rest (index + 1) + 1 := by
  simp only [pendingCopies, copiedSlotsFrom_copied rest index copied, List.length_cons]

/-- A position outside the earlier copies and the suffix's copied slots
moves past every copy. -/
theorem chainRenaming_not_mem {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index position : Nat}
    (fresh : position ∉ done)
    (outside : ∀ slot ∈ copiedSlotsFrom source rest index, slot.1 + preLength ≠ position) :
    chainRenaming source preLength done rest index position = position + (done.length + pendingCopies source rest index) := by
  unfold chainRenaming
  rw [copyRenaming_not_mem, List.length_append, List.length_map]
  · rfl
  intro mem
  rw [List.mem_append] at mem
  rcases mem with mem | mem
  · exact fresh mem
  · rw [List.mem_map] at mem
    obtain ⟨slot, mem, same⟩ := mem
    exact outside slot mem same

/-- A position below the suffix and outside the earlier copies moves past
every copy. -/
theorem chainRenaming_below {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index position : Nat}
    (fresh : position ∉ done) (below : position < index + preLength) :
    chainRenaming source preLength done rest index position = position + (done.length + pendingCopies source rest index) := by
  apply chainRenaming_not_mem fresh
  intro slot mem
  have := copiedSlotsFrom_le source rest index slot mem
  omega

/-- The slot being copied is sent below the copies still to be made. -/
theorem chainRenaming_copy {source : TypedSource} {preLength : Nat} {done : List Nat}
    {rest : SourceCoreLocalCell.Scope} {index : Nat}
    (doneBelow : ∀ position ∈ done, position < index + preLength) :
    chainRenaming source preLength (done ++ [index + preLength]) rest (index + 1) (index + preLength) =
      pendingCopies source rest (index + 1) := by
  unfold chainRenaming
  rw [List.append_assoc, List.singleton_append, copyRenaming_mem, List.length_map]
  · rfl
  intro mem
  have := doneBelow _ mem
  omega

/-! ## Pending agreement -/

/-- The entries of `source` are sent by `σ` past `pending` copies still to be
made, onto slots of `target` holding the same entries. -/
def Pending {α : Type} (σ : Renaming) (pending : Nat) (source target : List α) : Prop :=
  ∀ {index : Nat} {entry : α}, source[index]? = some entry →
    ∃ slot, σ index = slot + pending ∧ target[slot]? = some entry

namespace Pending

variable {α : Type} {σ : Renaming} {pending : Nat} {source target : List α}

/-- One more copy made: every earlier slot moves up by one. -/
theorem push (related : Pending σ (pending + 1) source target) (entry : α) :
    Pending σ pending source (entry :: target) := by
  intro index found selected
  obtain ⟨slot, same, selected⟩ := related selected
  exact ⟨slot + 1, by omega, by simpa using selected⟩

/-- The copy of the next slot is the entry just pushed. -/
theorem copied (related : Pending σ (pending + 1) source target)
    (position : σ source.length = pending) (entry : α) :
    Pending σ pending (source ++ [entry]) (entry :: target) := by
  intro index found selected
  rcases Nat.lt_or_ge index source.length with below | above
  · rw [List.getElem?_append_left below] at selected
    exact related.push entry selected
  · have same : index = source.length := by
      have bound := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst same
    rw [List.getElem?_concat_length] at selected
    obtain rfl := Option.some.inj selected
    exact ⟨0, by simpa using position, rfl⟩

/-- A slot that keeps its entry is sent to that entry's current slot. -/
theorem shared (related : Pending σ pending source target) {slot : Nat} {entry : α}
    (position : σ source.length = slot + pending) (selected : target[slot]? = some entry) :
    Pending σ pending (source ++ [entry]) target := by
  intro index found found
  rcases Nat.lt_or_ge index source.length with below | above
  · rw [List.getElem?_append_left below] at found
    exact related found
  · have same : index = source.length := by
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst same
    rw [List.getElem?_concat_length] at found
    obtain rfl := Option.some.inj found
    exact ⟨slot, position, selected⟩

/-- With no copy pending, composing with an agreement of the target gives an
agreement of the source. -/
theorem agree {ρ : Renaming} {final : List α} (related : Pending σ 0 source target)
    (agrees : ∀ {index : Nat} {entry : α}, target[index]? = some entry → final[ρ index]? = some entry)
    {index : Nat} {entry : α} (found : source[index]? = some entry) :
    final[Renaming.comp ρ σ index]? = some entry := by
  obtain ⟨slot, same, selected⟩ := related found
  show final[ρ (σ index)]? = some entry
  rw [same, Nat.add_zero]
  exact agrees selected

end Pending

/-! ## List bookkeeping -/

/-- An agreement of environments transfers along an equality of sources. -/
theorem agree_of_eq {ρ : Renaming} {source source' target : Environment} (same : source = source')
    (agrees : EnvironmentsAgree ρ source target) : EnvironmentsAgree ρ source' target := same ▸ agrees

/-- A renaming respecting a context respects an equal context. -/
theorem respects_of_eq {ρ : Renaming} {source source' target : Core.Context} (same : source = source')
    (respects : Renaming.Respects ρ source target) : Renaming.Respects ρ source' target := same ▸ respects

/-- Indexing past a prefix of known length. -/
theorem getElem?_append_shift {α : Type} {prefixList rest : List α} {count index : Nat}
    (length : prefixList.length = count) : (prefixList ++ rest)[index + count]? = rest[index]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-! ## Scope environments -/

/-- The scope part of a represented environment, with no administrative tail. -/
theorem scope_environments {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical
      definitions) :
    DataHeap.EnvRepresents catalog mapping world [] scope environment (canonical.take scope.length) definitions := by
  induction related with
  | nil _ => exact .nil .nil
  | cons reference _ ih => exact .cons reference ih
  | internal typed absent _ ih => exact .internal typed absent ih

/-- A copy of the lexical environment binds no identifier the original does
not bind. -/
theorem copies_absent {source : TypedSource} {environment copies : Dynamic.Environment}
    {heap after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment heap copies after)
    {id : Resolved.LocalId} (absent : ∀ location, ¬ Dynamic.Environment.LooksUp environment id location) :
    ∀ location, ¬ Dynamic.Environment.LooksUp copies id location := by
  intro location lookup
  obtain ⟨original, originalLookup, _⟩ := copy.looksUp lookup
  exact absent original originalLookup

/-! ## Optional payloads -/

/-- A typed optional cell value is an optional payload. -/
theorem optional_of_typed {world : StoreTyping} {definitions : DataEnvironment} {value : Value} {type : Ty}
    (typed : RuntimeValueHasType world value (OptionalCell.cellType type) definitions) :
    ∃ payload, value = optionalValue type payload := by
  unfold OptionalCell.cellType at typed
  cases typed with
  | inLeft unitTyped => cases unitTyped; exact ⟨none, rfl⟩
  | inRight _ => exact ⟨some _, rfl⟩

/-- A represented optional cell value is an optional payload. -/
theorem optional_of_cell {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type) :
    ∃ payload, value = optionalValue type payload := by
  cases represented with
  | uninitialized _ => exact ⟨none, rfl⟩
  | initialized _ => exact ⟨some _, rfl⟩

/-! ## Chain inversions -/

theorem copyChain_shared (allocator : Option SourceCoreSourceCells.Allocator) {source : TypedSource}
    (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) {id : Resolved.LocalId} {type : Core.Ty}
    (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (body : Expr)
    (uncopied : copiedBinder? source id = none) :
    SourceCoreSourceCells.copyChain allocator source scope base ((id, type) :: rest) index ordinal body =
      SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1) ordinal body := by
  simp only [SourceCoreSourceCells.copyChain, uncopied]

theorem copyChain_copied {allocator : Option SourceCoreSourceCells.Allocator} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat} {id : Resolved.LocalId} {type : Core.Ty}
    {binder : TypedBinder} {rest : SourceCoreLocalCell.Scope} {index ordinal : Nat} {body emitted : Expr}
    (copied : copiedBinder? source id = some binder)
    (accepted : SourceCoreSourceCells.copyChain allocator source scope base ((id, type) :: rest) index ordinal
      body = .ok emitted) :
    ∃ copy continuation,
      SourceCoreSourceCells.copyCell allocator source scope
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
        (.var (base index + ordinal)) = .ok copy ∧
      SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1) (ordinal + 1) body =
        .ok continuation ∧
      emitted = .letE copy continuation := by
  simp only [SourceCoreSourceCells.copyChain, copied] at accepted
  cases copyAccepted : SourceCoreSourceCells.copyCell allocator source scope
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      (.var (base index + ordinal)) with
  | error error => simp [copyAccepted, bind, Except.bind] at accepted
  | ok copy =>
    cases chainAccepted : SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1)
        (ordinal + 1) body with
    | error error => simp [copyAccepted, chainAccepted, bind, Except.bind] at accepted
    | ok continuation =>
      simp only [copyAccepted, chainAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      exact ⟨copy, continuation, rfl, rfl, accepted.symm⟩

theorem copyChain_nil (allocator : Option SourceCoreSourceCells.Allocator) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) (index ordinal : Nat) {body emitted : Expr}
    (accepted : SourceCoreSourceCells.copyChain allocator source scope base [] index ordinal body = .ok emitted) :
    emitted = body := by
  simp only [SourceCoreSourceCells.copyChain, pure, Except.pure, Except.ok.injEq] at accepted
  exact accepted.symm

theorem copyCell_some {allocate : SourceCoreSourceCells.Allocator} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {references : Renaming} {binder : TypedBinder}
    {type : Core.Ty} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell (some allocate) source scope references binder type reference =
      .ok copy) :
    ∃ absent present,
      allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type, none⟩ =
        .ok absent ∧
      allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type, some (.var 0)⟩ =
        .ok present ∧
      copy = .caseE (.loadCell reference) absent present := by
  simp only [SourceCoreSourceCells.copyCell] at accepted
  cases absentAccepted : allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder, type,
      none⟩ with
  | error error => simp [absentAccepted, bind, Except.bind] at accepted
  | ok absent =>
    cases presentAccepted : allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references, binder,
        type, some (.var 0)⟩ with
    | error error => simp [absentAccepted, presentAccepted, bind, Except.bind] at accepted
    | ok present =>
      simp only [absentAccepted, presentAccepted, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at accepted
      exact ⟨absent, present, rfl, rfl, accepted.symm⟩

/-! ## Administrative copies -/

/-- Three appended administrative cells preserve every earlier one. -/
theorem administrative_append (mapping : LocationMap) (store : Store) (first second third : Value) :
    AdministrativePreserved mapping store mapping (store ++ [first, second, third]) := by
  have steps := (AdministrativePreserved.allocate_administrative mapping store first).trans
    ((AdministrativePreserved.allocate_administrative mapping (store ++ [first]) second).trans
      (AdministrativePreserved.allocate_administrative mapping (store ++ [first] ++ [second]) third))
  simpa [List.append_assoc] using steps

/-- A copy of an internal slot: the snapshot, marker and payload cells are
all administrative, and the payload cell keeps the slot's type. -/
theorem heap_allocate_administrative {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (payloadTyped : RuntimeValueHasType world payload (OptionalCell.cellType payloadType) definitions) :
    GenericHeap.CellHeapRepresents cells mapping
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      heap (store ++ [snapshot, marker, payload]) ∧
    (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])[store.length + 2]? =
      some (OptionalCell.cellType payloadType) := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have payloadHeaps := markerHeaps.allocate_administrative (payloadTyped.weaken
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩))
  refine ⟨by simpa [Store.allocate, List.append_assoc] using payloadHeaps, ?_⟩
  have lengthEq := heaps.runtime_hasTypes.length_eq
  rw [List.getElem?_append_right (by omega)]
  have same : store.length + 2 - world.length = 2 := by omega
  rw [same]
  rfl

/-- A mapped copy of a source cell in any cell model: the snapshot and marker
cells are administrative, and the payload cell represents the copied cell as
the original does. -/
theorem heap_allocate_copy {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {copied : Dynamic.Cell} {sourceLocation : Dynamic.Location}
    {snapshot marker payload : Value} {snapshotType markerType payloadType : Ty}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (cell : cells.Represents mapping world copied payload payloadType)
    (allocated : Dynamic.Heap.AllocatesCopy before copied sourceLocation after) :
    GenericHeap.CellHeapRepresents cells (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
      after (store ++ [snapshot, marker, payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType payloadType])
        sourceLocation (store.length + 2) payloadType := by
  have snapshotHeaps := heaps.allocate_administrative snapshotTyped
  have markerHeaps := snapshotHeaps.allocate_administrative
    (markerTyped.weaken (show WorldExtends world (world ++ [snapshotType]) from ⟨_, rfl⟩))
  have extended := cells.extend cell (LocationMap.Extends.refl mapping)
    (show WorldExtends world ((world ++ [snapshotType]) ++ [markerType]) from ⟨[snapshotType, markerType], by simp⟩)
  cases allocated
  simpa [Store.allocate, List.append_assoc, Nat.add_assoc] using markerHeaps.append extended

/-! ## One renamed marked copy -/

/-- The frame reference of a copy's request: every copy counts the packed
argument like a named input's own allocation. -/
theorem copyReferences_frame (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (binder : TypedBinder) (base : Nat → Nat) (ordinal globals : Nat) :
    SourceCoreSourceCells.copyReferences source scope binder base ordinal
      (scope.length + (if source.inputs.any (fun input => decide (input.id = binder.id)) then 0 else 1) + globals) =
      base (scope.length + 1 + globals) + ordinal := by
  unfold SourceCoreSourceCells.copyReferences
  cases named : source.inputs.any (fun input => decide (input.id = binder.id))
  · simp
  · simp only [↓reduceIte, Nat.add_zero]
    rw [if_neg (by omega)]
    congr 2
    omega

/-- One branch of a marked copy, transported under the actual renaming: the
frame snapshot, a typed marker over the scope's original slots and the
payload cell. -/
theorem branch_evaluates {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (sameDefinitions : layouts.definitions = definitions)
    (payloadShape : request.payload = none ∨ request.payload = some (.var 0))
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical layoutEnvironment current : Environment} {store : Store} {contextLocation : Location}
    {native : CallableIndexedHistory.NativeFrame} {payload : Option Value} {ρ : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world [] request.scope environment canonical definitions)
    (agrees : EnvironmentsAgree request.references canonical layoutEnvironment)
    (reference : layoutEnvironment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (payloadAt : PayloadAt request layoutEnvironment payload)
    (actual : EnvironmentsAgree ρ layoutEnvironment current) :
    ∃ marker markerType,
      RuntimeValueHasType world marker markerType definitions ∧
      Evaluates current store (annotation.expression.rename ρ)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker,
          optionalValue request.payloadType payload]) := by
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed environments agrees
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope =
      SourceCoreSourceCells.captureType request.scope
    rw [allocation.keyExact]
    rfl
  have markerRegistered : allocation.entry.layout.Registered definitions := sameDefinitions ▸ allocation.registered
  refine ⟨SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, allocation.entry.layout.type,
    .constructed markerRegistered.payloadLookup (captureType.symm ▸ typed), ?_⟩
  exact CallableIndexedAllocationRenaming.transport allocation annotation same payloadShape
    (CallableIndexedAllocationCompletion.evaluates allocation annotation same reference read selected payloadAt)
    actual

/-- A marked copy of a slot, under the actual renaming: it reads the slot's
cell and returns a reference to a fresh payload cell holding the same
optional value, after the frame snapshot and a typed marker. -/
theorem copy_evaluates {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal slot : Nat} {copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      (.var slot) = .ok copy)
    (sameDefinitions : layouts.definitions = definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical layoutEnvironment current : Environment} {store : Store}
    {contextLocation target : Location} {native : CallableIndexedHistory.NativeFrame}
    {payload : Option Value} {ρ : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world [] scope environment
      (canonical.take scope.length) definitions)
    (slots : ∀ index, index < scope.length → layoutEnvironment[base index + ordinal]? = canonical[index]?)
    (frame : layoutEnvironment[base (scope.length + 1 + globals) + ordinal]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (found : layoutEnvironment[slot]? = some (.cellRef (OptionalCell.cellType type) target))
    (cell : store.read? target = some (optionalValue type payload))
    (agrees : EnvironmentsAgree ρ layoutEnvironment current) :
    ∃ marker markerType,
      RuntimeValueHasType world marker markerType definitions ∧
      Evaluates current store (copy.rename ρ) (.cellRef (OptionalCell.cellType type) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, optionalValue type payload]) := by
  obtain ⟨absent, present, absentAccepted, presentAccepted, rfl⟩ := copyCell_some accepted
  obtain ⟨absentAllocation, absentAnnotation, absentSame, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError absentAccepted
  obtain ⟨presentAllocation, presentAnnotation, presentSame, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError presentAccepted
  have scrutinee : Evaluates current store ((Expr.loadCell (.var slot)).rename ρ) (optionalValue type payload) store :=
    .loadCell (.var (agrees found)) cell
  have shifted : ∀ value : Value,
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0)
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal))
        (canonical.take scope.length) (value :: layoutEnvironment) := by
    intro value index entry selected
    have below : index < scope.length := by
      have bound := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_take] at bound
      omega
    rw [List.getElem?_take_of_lt below] at selected
    show (value :: layoutEnvironment)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal index)]? = some entry
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ,
      SourceCoreSourceCells.copyReferences, below]
    rw [slots index below]
    exact selected
  have frameAt : ∀ (value : Value) (payloadExpression : Option Expr),
      (value :: layoutEnvironment)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
          payloadExpression⟩]? = some (.cellRef layout.type contextLocation) := by
    intro value payloadExpression
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
          payloadExpression⟩ = source.inputs.any (fun input => decide (input.id = binder.id)) := rfl
    show (value :: layoutEnvironment)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal
        (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
          ⟨source, scope, Renaming.comp (Renaming.insertion 0)
            (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
            payloadExpression⟩ then 0 else 1) + globals))]? =
      some (.cellRef layout.type contextLocation)
    rw [named, copyReferences_frame]
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ]
    exact frame
  cases payload with
  | none =>
    obtain ⟨marker, markerType, markerTyped, evaluated⟩ := branch_evaluates absentAllocation absentAnnotation
      absentSame sameDefinitions (Or.inl rfl) environments (shifted .unit) (frameAt .unit none)
      read (.absent rfl) (agrees.lift .unit)
    exact ⟨marker, markerType, markerTyped, .caseLeft scrutinee evaluated⟩
  | some value =>
    obtain ⟨marker, markerType, markerTyped, evaluated⟩ := branch_evaluates presentAllocation presentAnnotation
      presentSame sameDefinitions (Or.inr rfl) environments (shifted value)
      (frameAt value (some (.var 0))) read (.initialized rfl rfl) (agrees.lift value)
    exact ⟨marker, markerType, markerTyped, .caseRight scrutinee evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CaptureCopies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarked
/-! The copies a closure makes of its captured cells through the indexed
marked allocator. Each copied slot reads its cell, then allocates a frame
snapshot, a marker over the scope's original slots and a payload cell holding
the read value, exactly as a marked `let` does. The source copies the same
bindings, so the copies of a represented scope pair up slot by slot; the frame
cell is read and never written. The prefix agreement is sized, so a completed
evaluation of the copies and their continuation unwraps to a continuation
completion no larger. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopies
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

/-- A finite prefix around a continuation: wrapping is exact, and a sized
completion of the whole unwraps to a continuation completion no larger. -/
structure PrefixAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ smaller, smaller ≤ size ∧ EvaluationSize smaller nextEnvironment nextStore next result finalStore

namespace PrefixAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    PrefixAgreement environment store code environment store code :=
  ⟨id, fun evaluation => ⟨_, Nat.le_refl _, evaluation⟩⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : PrefixAgreement environment store whole middleEnvironment middleStore middle)
    (second : PrefixAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    PrefixAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluation => first.wrap (second.wrap evaluation), ?_⟩
  intro size result finalStore evaluation
  obtain ⟨middleSize, middleLe, middleEvaluation⟩ := first.unwrap evaluation
  obtain ⟨nextSize, nextLe, nextEvaluation⟩ := second.unwrap middleEvaluation
  exact ⟨nextSize, Nat.le_trans nextLe middleLe, nextEvaluation⟩

/-- Forgetting the sizes leaves the finite continuation agreement. -/
theorem continuation {environment nextEnvironment : Environment} {store nextStore : Store}
    {whole next : Expr} (agreement : PrefixAgreement environment store whole nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨agreement.wrap, ?_⟩
  intro result finalStore evaluation
  obtain ⟨size, sized⟩ := evaluation_has_size evaluation
  obtain ⟨_, _, smaller⟩ := agreement.unwrap sized
  exact smaller.sound

/-- A `let` with a known initializer: its body's sized completion is
strictly smaller than the whole's. -/
theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    PrefixAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun evaluation => .letE evaluated evaluation, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, below, body⟩ := evaluation.let_body evaluated
  exact ⟨smaller, Nat.le_of_lt below, body⟩

end PrefixAgreement

open SourceSemantics.CaptureBinders (copiedBinder?)

/-- The marked copies of the scope suffix `rest`, at scope index `index`
after `ordinal` copies at the positions `done`. The copies made so far sit
below the original slots of the layout environment, the processed slots are
pending behind the copies still to be made, and the actual environment agrees
with the layout under `ρ`. -/
theorem marked_chain_prefix
    {catalog : SourceCoreDataCatalog.Catalog}
    {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {administrativeContext preContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {pre canonical : Environment}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (preLength : preContext.length = pre.length) (rest : SourceCoreLocalCell.Scope) :
    ∀ {taken : SourceCoreLocalCell.Scope} {index ordinal : Nat} {done : List Nat}
      {mapping : LocationMap} {world : StoreTyping} {environmentRest : Dynamic.Environment}
      {canonicalRest copies processed current : Environment}
      {copyTypes processedContext currentContext : Core.Context}
      {heap : Dynamic.Heap} {store : Store} {ρ : Renaming} {inner emitted : Expr},
      scope = taken ++ rest → taken.length = index →
      (∀ i, canonicalRest[i]? = canonical[index + i]?) →
      done.length = ordinal → (∀ position ∈ done, position < index + pre.length) →
      copies.length = ordinal → copyTypes.length = ordinal →
      processed.length = index → processedContext.length = index →
      DataHeap.EnvRepresents catalog mapping world administrativeContext rest environmentRest canonicalRest
        definitions →
      DataHeap.EnvRepresents catalog mapping world [] scope environment (canonical.take scope.length) definitions →
      GenericHeap.CellHeapRepresents cells mapping world heap store →
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) →
      Pending (chainRenaming source pre.length done rest index) (pendingCopies source rest index)
        (pre ++ processed) (copies ++ (pre ++ canonical)) →
      Pending (chainRenaming source pre.length done rest index) (pendingCopies source rest index)
        (preContext ++ processedContext)
        (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) →
      EnvironmentsAgree ρ (copies ++ (pre ++ canonical)) current →
      Renaming.Respects ρ
        (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)))
        currentContext →
      RuntimeEnvironmentHasTypes world current currentContext definitions →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope (· + pre.length) rest index ordinal inner = .ok emitted →
      ∃ copiesRest finalHeap finalCanonicalRest finalActual finalActualContext finalStore finalMap finalWorld
        finalRho,
        Dynamic.EnvironmentCopies source environmentRest heap copiesRest finalHeap ∧
        DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext rest copiesRest
          finalCanonicalRest definitions ∧
        (∀ i, rest.length ≤ i → finalCanonicalRest[i]? = canonicalRest[i]?) ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ (∃ suffix, finalStore = store ++ suffix) ∧
        finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
        EnvironmentsAgree (Renaming.comp finalRho (chainRenaming source pre.length done rest index))
          (pre ++ processed ++ finalCanonicalRest) finalActual ∧
        Renaming.Respects (Renaming.comp finalRho (chainRenaming source pre.length done rest index))
          (preContext ++ processedContext ++ (SourceCoreLocalCell.coreContext rest ++ administrativeContext))
          finalActualContext ∧
        RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
        PrefixAgreement current store (emitted.rename ρ) finalActual finalStore (inner.rename finalRho) := by
  induction rest with
  | nil =>
    intro taken index ordinal done mapping world environmentRest canonicalRest copies processed current
      copyTypes processedContext currentContext heap store ρ inner emitted split takenLength dropped
      doneLength doneBelow copiesLength copyTypesLength processedLength processedContextLength
      environmentsRest environmentsScope heaps read pendingValues pendingTypes agrees respects
      currentTyped accepted
    obtain rfl := copyChain_nil _ _ _ _ _ _ accepted
    cases environmentsRest with
    | nil typed =>
      have scopeLength : scope.length = index := by
        rw [split, List.append_nil]
        exact takenLength
      have past : ∀ position, index + pre.length ≤ position →
          chainRenaming source pre.length done [] index position = position + ordinal := by
        intro position above
        rw [chainRenaming_not_mem (fun mem => by have := doneBelow position mem; omega)
          (fun slot mem => by simp [copiedSlotsFrom] at mem)]
        simp only [pendingCopies, copiedSlotsFrom_nil, List.length_nil, Nat.add_zero, doneLength]
      refine ⟨[], heap, _, current, currentContext, store, mapping, world, ρ, .nil heap, .nil typed,
        fun _ _ => rfl, heaps, LocationMap.Extends.refl _, WorldExtends.refl _,
        AdministrativePreserved.refl _ _, ⟨[], (List.append_nil store).symm⟩, read, ?_, ?_, currentTyped,
        PrefixAgreement.refl _ _ _⟩
      · intro position value found
        rcases Nat.lt_or_ge position (pre.length + index) with below | above
        · rw [List.getElem?_append_left (by simp [processedLength]; omega)] at found
          exact pendingValues.agree agrees found
        · rw [List.getElem?_append_right (by simp [processedLength]; omega)] at found
          show current[ρ (chainRenaming source pre.length done [] index position)]? = some value
          rw [past position (by omega)]
          apply agrees
          rw [getElem?_append_shift copiesLength, List.getElem?_append_right (by omega)]
          rw [dropped] at found
          rw [← found]
          congr 1
          simp only [List.length_append, processedLength]
          omega
      · intro position type found
        have found : (preContext ++ processedContext ++ administrativeContext)[position]? = some type := found
        rcases Nat.lt_or_ge position (pre.length + index) with below | above
        · rw [List.getElem?_append_left (by simp [processedContextLength, preLength]; omega)] at found
          exact pendingTypes.agree (fun found => respects found) found
        · rw [List.getElem?_append_right (by simp [processedContextLength, preLength]; omega)] at found
          show currentContext[ρ (chainRenaming source pre.length done [] index position)]? = some type
          rw [past position (by omega)]
          apply respects
          rw [getElem?_append_shift copyTypesLength, List.getElem?_append_right (by omega),
            List.getElem?_append_right (by simp [SourceCoreLocalCell.coreContext, scopeLength]; omega), ← found]
          congr 1
          simp only [List.length_append, processedContextLength, SourceCoreLocalCell.coreContext,
            List.length_map, scopeLength]
          omega
  | cons head rest ih =>
    obtain ⟨id, type⟩ := head
    intro taken index ordinal done mapping world environmentRest canonicalRest copies processed current
      copyTypes processedContext currentContext heap store ρ inner emitted split takenLength dropped
      doneLength doneBelow copiesLength copyTypesLength processedLength processedContextLength
      environmentsRest environmentsScope heaps read pendingValues pendingTypes agrees respects
      currentTyped accepted
    have slotFound : scope[index]? = some (id, type) := by
      rw [split, List.getElem?_append_right (by omega)]
      simp [takenLength]
    have splitNext : scope = (taken ++ [(id, type)]) ++ rest := by
      rw [split, List.append_assoc, List.singleton_append]
    have takenNextLength : (taken ++ [(id, type)]).length = index + 1 := by simp [takenLength]
    have canonicalAt : ∀ i, (pre ++ canonical)[i + pre.length]? = canonical[i]? := fun i => by
      rw [List.getElem?_append_right (by omega)]
      congr 1
      omega
    have contextAt : (preContext ++ (SourceCoreLocalCell.coreContext scope ++
        administrativeContext))[index + pre.length]? = some (.cell (OptionalCell.cellType type)) := by
      have bound : index < scope.length := by
        rw [split]
        simp only [List.length_append, List.length_cons]
        omega
      rw [List.getElem?_append_right (by omega),
        List.getElem?_append_left (by simp [SourceCoreLocalCell.coreContext]; omega)]
      have same : index + pre.length - preContext.length = index := by omega
      simp [SourceCoreLocalCell.coreContext, same, slotFound]
    have processedAt : (pre ++ processed).length = index + pre.length := by
      simp only [List.length_append, processedLength]
      omega
    have processedContextAt : (preContext ++ processedContext).length = index + pre.length := by
      simp only [List.length_append, processedContextLength, preLength]
      omega
    have bound : contextLocation < store.length :=
      (List.getElem?_eq_some_iff.mp (read : store[contextLocation]? = _)).1
    have frameAt : (copies ++ (pre ++ canonical))[(· + pre.length) (scope.length + 1 + globals) + ordinal]? =
        some (.cellRef layout.type contextLocation) := by
      show (copies ++ (pre ++ canonical))[scope.length + 1 + globals + pre.length + ordinal]? = _
      rw [getElem?_append_shift copiesLength, canonicalAt]
      exact reference
    have slotsAt : ∀ i, i < scope.length →
        (copies ++ (pre ++ canonical))[(· + pre.length) i + ordinal]? = canonical[i]? := by
      intro i _
      show (copies ++ (pre ++ canonical))[i + pre.length + ordinal]? = canonical[i]?
      rw [getElem?_append_shift copiesLength, canonicalAt]
    cases copied : copiedBinder? source id with
    | none =>
      rw [copyChain_shared _ _ _ _ _ _ _ copied] at accepted
      rw [chainRenaming_shared pre.length done rest index copied, pendingCopies_shared rest index copied]
        at pendingValues pendingTypes
      rw [chainRenaming_shared pre.length done rest index copied]
      have doneBelowNext : ∀ position ∈ done, position < index + 1 + pre.length := fun position mem => by
        have := doneBelow position mem
        omega
      have position : chainRenaming source pre.length done rest (index + 1) (index + pre.length) =
          index + pre.length + ordinal + pendingCopies source rest (index + 1) := by
        rw [chainRenaming_below (fun mem => by have := doneBelow _ mem; omega) (by omega), doneLength]
        omega
      cases environmentsRest with
      | @cons _ environmentTail canonicalTail _ sourceLocation target _ headReference tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        have pendingValuesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) target])) (copies ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          refine pendingValues.shared (by rw [processedAt]; exact position) ?_
          rw [getElem?_append_shift copiesLength, canonicalAt]
          exact (dropped 0).symm
        have pendingTypesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          refine pendingTypes.shared (by rw [processedContextAt]; exact position) ?_
          rw [getElem?_append_shift copyTypesLength]
          exact contextAt
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih splitNext takenNextLength droppedNext doneLength doneBelowNext copiesLength copyTypesLength
            (by simp [processedLength]) (by simp [processedContextLength]) tail environmentsScope heaps read
            pendingValuesNext pendingTypesNext agrees respects currentTyped accepted
        refine ⟨(id, sourceLocation) :: copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) target :: finalCanonicalRest, finalActual, finalActualContext,
          finalStore, finalMap, finalWorld, finalRho, .shared copied copyTail,
          .cons (headReference.extend maps worlds) envTail, ?_, finalHeaps, maps, worlds, frame, storePrefix,
          finalRead,
          ?_, ?_, finalTyped, agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
      | @internal _ _ canonicalTail _ target _ typed absent tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        have pendingValuesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) target])) (copies ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          refine pendingValues.shared (by rw [processedAt]; exact position) ?_
          rw [getElem?_append_shift copiesLength, canonicalAt]
          exact (dropped 0).symm
        have pendingTypesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          refine pendingTypes.shared (by rw [processedContextAt]; exact position) ?_
          rw [getElem?_append_shift copyTypesLength]
          exact contextAt
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih splitNext takenNextLength droppedNext doneLength doneBelowNext copiesLength copyTypesLength
            (by simp [processedLength]) (by simp [processedContextLength]) tail environmentsScope heaps read
            pendingValuesNext pendingTypesNext agrees respects currentTyped accepted
        refine ⟨copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) target :: finalCanonicalRest, finalActual, finalActualContext,
          finalStore, finalMap, finalWorld, finalRho, copyTail,
          .internal (worlds.lookup typed) (copies_absent copyTail absent) envTail, ?_, finalHeaps, maps, worlds,
          frame, storePrefix, finalRead, ?_, ?_, finalTyped, agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
    | some binder =>
      obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ := copyChain_copied copied accepted
      rw [chainRenaming_copied pre.length done rest index copied, pendingCopies_copied rest index copied]
        at pendingValues pendingTypes
      rw [chainRenaming_copied pre.length done rest index copied]
      have doneBelowNext : ∀ position ∈ done ++ [index + pre.length], position < index + 1 + pre.length := by
        intro position mem
        rw [List.mem_append, List.mem_singleton] at mem
        rcases mem with mem | rfl
        · have := doneBelow position mem
          omega
        · omega
      have position : chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1)
          (index + pre.length) = pendingCopies source rest (index + 1) :=
        chainRenaming_copy doneBelow
      have readNext : ∀ (snapshot marker payload : Value),
          (store ++ [snapshot, marker, payload]).read? contextLocation =
            some (SourceCoreCallableIndexedFrames.encode layout native) := by
        intro snapshot marker payload
        show (store ++ [snapshot, marker, payload])[contextLocation]? = _
        rw [List.getElem?_append_left bound]
        exact read
      have snapshotTyped := SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native
      cases environmentsRest with
      | @cons _ environmentTail canonicalTail _ sourceLocation target _ headReference tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        obtain ⟨cell, value, payloadType, sourceRead, worldTyped, storeRead, cellRel⟩ :=
          heaps.cells headReference.mapped
        have samePayload : payloadType = type := by
          have same := Option.some.inj (worldTyped.symm.trans headReference.typed)
          simpa [OptionalCell.cellType] using same
        subst payloadType
        obtain ⟨payload, rfl⟩ := optional_of_typed (cells.runtime_hasType cellRel)
        obtain ⟨marker, markerType, markerTyped, evaluated⟩ := copy_evaluates copyAccepted sameDefinitions
          environmentsScope slotsAt frameAt read
          (by rw [getElem?_append_shift copiesLength, canonicalAt]; exact (dropped 0).symm) storeRead agrees
        obtain ⟨heapsNext, referenceNext⟩ := heap_allocate_copy heaps
          snapshotTyped markerTyped cellRel (Dynamic.Heap.AllocatesCopy.append)
        have pendingValuesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) (store.length + 2)]))
            ((.cellRef (OptionalCell.cellType type) (store.length + 2) :: copies) ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          exact pendingValues.copied (by rw [processedAt]; exact position) _
        have pendingTypesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            ((.cell (OptionalCell.cellType type) :: copyTypes) ++
              (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          exact pendingTypes.copied (by rw [processedContextAt]; exact position) _
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih (mapping := mapping ++ [store.length + 2])
            (world := world ++ [layout.type, markerType, OptionalCell.cellType type])
            splitNext takenNextLength droppedNext (by simp [doneLength]) doneBelowNext (by simp [copiesLength])
            (by simp [copyTypesLength]) (by simp [processedLength]) (by simp [processedContextLength])
            (tail.extend ⟨_, rfl⟩ ⟨_, rfl⟩) (environmentsScope.extend ⟨_, rfl⟩ ⟨_, rfl⟩) heapsNext
            (readNext _ _ _) pendingValuesNext pendingTypesNext (agrees.lift _) (respects.lift _)
            (.cons (.cellRef referenceNext.typed) (currentTyped.weaken ⟨_, rfl⟩)) continuationAccepted
        refine ⟨(id, ⟨heap.cells.length⟩) :: copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) (store.length + 2) :: finalCanonicalRest, finalActual,
          finalActualContext, finalStore, finalMap, finalWorld, finalRho,
          .copied copied sourceRead .append copyTail, .cons (referenceNext.extend maps worlds) envTail, ?_,
          finalHeaps, LocationMap.Extends.trans ⟨_, rfl⟩ maps, WorldExtends.trans ⟨_, rfl⟩ worlds,
          AdministrativePreserved.trans
            (CallableIndexedAllocationCompletion.allocation_frame mapping store _ _ _) frame,
          (by obtain ⟨suffix, storeEq⟩ := storePrefix; exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩),
          finalRead, ?_, ?_, finalTyped, (PrefixAgreement.letE evaluated).trans agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
      | @internal _ _ canonicalTail _ target _ typed absent tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        obtain ⟨value, storeRead, valueTyped⟩ := heaps.runtime_hasTypes.lookup typed
        obtain ⟨payload, rfl⟩ := optional_of_typed valueTyped
        obtain ⟨marker, markerType, markerTyped, evaluated⟩ := copy_evaluates copyAccepted sameDefinitions
          environmentsScope slotsAt frameAt read
          (by rw [getElem?_append_shift copiesLength, canonicalAt]; exact (dropped 0).symm) storeRead agrees
        obtain ⟨heapsNext, typedNext⟩ := heap_allocate_administrative heaps snapshotTyped markerTyped valueTyped
        have pendingValuesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) (store.length + 2)]))
            ((.cellRef (OptionalCell.cellType type) (store.length + 2) :: copies) ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          exact pendingValues.copied (by rw [processedAt]; exact position) _
        have pendingTypesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            ((.cell (OptionalCell.cellType type) :: copyTypes) ++
              (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          exact pendingTypes.copied (by rw [processedContextAt]; exact position) _
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih (mapping := mapping) (world := world ++ [layout.type, markerType, OptionalCell.cellType type])
            splitNext takenNextLength droppedNext (by simp [doneLength]) doneBelowNext (by simp [copiesLength])
            (by simp [copyTypesLength]) (by simp [processedLength]) (by simp [processedContextLength])
            (tail.extend (LocationMap.Extends.refl _) ⟨_, rfl⟩)
            (environmentsScope.extend (LocationMap.Extends.refl _) ⟨_, rfl⟩) heapsNext
            (readNext _ _ _) pendingValuesNext pendingTypesNext (agrees.lift _) (respects.lift _)
            (.cons (.cellRef typedNext) (currentTyped.weaken ⟨_, rfl⟩)) continuationAccepted
        refine ⟨copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) (store.length + 2) :: finalCanonicalRest, finalActual,
          finalActualContext, finalStore, finalMap, finalWorld, finalRho, copyTail,
          .internal (worlds.lookup typedNext) (copies_absent copyTail absent) envTail, ?_,
          finalHeaps, maps, WorldExtends.trans ⟨_, rfl⟩ worlds,
          AdministrativePreserved.trans (administrative_append mapping store _ _ _) frame,
          (by obtain ⟨suffix, storeEq⟩ := storePrefix; exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩),
          finalRead, ?_, ?_, finalTyped, (PrefixAgreement.letE evaluated).trans agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types

/-- The marked copies of a scope in any cell model: the source copies the same
bindings, the heap and lexical relations extend to the copies, the frame cell
keeps its value, and the copies' continuation agrees with the whole in both
directions. Slots past the scope keep their canonical values. -/
theorem marked_copies_prefix_cells
    {catalog : SourceCoreDataCatalog.Catalog}
    {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext preContext actualContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body emitted : Expr}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (· + pre.length) body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ canonical) actual)
    (preLength : preContext.length = pre.length)
    (types : Renaming.Respects ξ
      (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ copies finalHeap finalCanonical finalActual finalActualContext finalStore finalMap finalWorld
      finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalCanonical definitions ∧
      (∀ index, scope.length ≤ index → finalCanonical[index]? = canonical[index]?) ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ (∃ suffix, finalStore = store ++ suffix) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalCanonical) finalActual ∧
      Renaming.Respects finalEmbedding
        (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) finalActualContext ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
      PrefixAgreement actual store (emitted.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  have positions : ∀ position, position < pre.length →
      chainRenaming source pre.length [] scope 0 position = position + pendingCopies source scope 0 := by
    intro position below
    rw [chainRenaming_not_mem (List.not_mem_nil) (fun slot _ => by omega)]
    simp
  have pendingValues : Pending (chainRenaming source pre.length [] scope 0) (pendingCopies source scope 0)
      (pre ++ []) ([] ++ (pre ++ canonical)) := by
    intro position value found
    rw [List.append_nil] at found
    have below : position < pre.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨position, positions position below, by rw [List.nil_append, List.getElem?_append_left below]; exact found⟩
  have pendingTypes : Pending (chainRenaming source pre.length [] scope 0) (pendingCopies source scope 0)
      (preContext ++ []) ([] ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
    intro position type found
    rw [List.append_nil] at found
    have below : position < preContext.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨position, positions position (by omega),
      by rw [List.nil_append, List.getElem?_append_left below]; exact found⟩
  obtain ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalRho, copy, finalEnvironments, slots, finalHeaps, maps, worlds, frame, storePrefix, finalRead, lookups,
      types, finalTyped, agreement⟩ :=
    marked_chain_prefix sameDefinitions frameRegistered reference preLength scope (taken := [])
      (done := []) (copies := []) (copyTypes := []) (processed := []) (processedContext := []) rfl rfl
      (fun i => by simp) rfl (fun _ mem => absurd mem List.not_mem_nil) rfl rfl rfl rfl environments
      (scope_environments environments) heaps read pendingValues pendingTypes actualLayout types actualTyped
      accepted
  refine ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
    Renaming.comp finalRho (chainRenaming source pre.length [] scope 0), copy, finalEnvironments, slots,
    finalHeaps, maps, worlds, frame, storePrefix, finalRead, agree_of_eq (by simp) lookups,
    respects_of_eq (by simp) types,
    finalTyped, ?_⟩
  rw [chainRenaming_scope, ← Expr.rename_comp]
  exact agreement

/-- The marked copies of a scope: the source copies the same bindings, the
heap and lexical relations extend to the copies, the frame cell keeps its
value, and the copies' continuation agrees with the whole in both directions.
Slots past the scope keep their canonical values. -/
theorem marked_copies_prefix
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext preContext actualContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body emitted : Expr}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (· + pre.length) body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ canonical) actual)
    (preLength : preContext.length = pre.length)
    (types : Renaming.Respects ξ
      (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ copies finalHeap finalCanonical finalActual finalActualContext finalStore finalMap finalWorld
      finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalCanonical definitions ∧
      (∀ index, scope.length ≤ index → finalCanonical[index]? = canonical[index]?) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalCanonical) finalActual ∧
      Renaming.Respects finalEmbedding
        (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) finalActualContext ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
      PrefixAgreement actual store (emitted.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalEmbedding, copy, finalEnvironments, slots, finalHeaps, maps, worlds, frame, _storePrefix, rest⟩ :=
    marked_copies_prefix_cells (cells := GenericHeap.CellModel.ordinary model) accepted sameDefinitions
      frameRegistered environments (GenericHeap.ordinaryHeap_iff.mpr heaps) actualLayout preLength types
      actualTyped reference read
  exact ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
    finalEmbedding, copy, finalEnvironments, slots, GenericHeap.ordinaryHeap_iff.mp finalHeaps, maps, worlds, frame,
    rest⟩

end Solcore.SourceSemantics.CoreLowering.CaptureCopies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopyIndexedTyping
/-! Typing of the copies a closure makes through the indexed marked
allocator. Each copy is a frame snapshot, a marker over the scope's slots and a
cell of the copied slot's payload type, so it has the type of the slot it
copies, and copies keep the typing of the expression they precede. Conversely,
each copy ends by allocating a cell of its slot's payload type, so the
redirection of copied slots pulls the copies' typing back to the expression. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
open Core Frontend Frontend.SourceInference CaptureCopyRenaming
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming)

/-- One branch of a marked copy, below its payload binder: the frame snapshot
before an allocation of the slot's payload type whose marker captures the
scope's slots, `ordinal` copies past their original positions. -/
private theorem markedBranch_hasType {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal : Nat} {payload : Option Expr} {context : Core.Context} {inserted : Ty}
    {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)
      ⟨source, scope, Renaming.comp (Renaming.insertion 0)
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type, payload⟩ =
      .ok code)
    (frameRegistered : layout.Registered layouts.definitions)
    (payloadWF : type.WellFormed layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (slotType : Ty), scope[index]? = some (id, slotType) →
      context[base index + ordinal]? = some (.cell (OptionalCell.cellType slotType)))
    (frame : context[base (scope.length + 1 + globals) + ordinal]? = some (.cell layout.type))
    (initializer : ∀ expression, payload = some expression →
      HasType (inserted :: context) expression type layouts.definitions) :
    HasType (inserted :: context) code (OptionalCell.referenceType type) layouts.definitions := by
  obtain ⟨allocation, annotation, same, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError accepted
  rw [annotation.exact, same]
  apply SourceCoreCallableIndexedAllocationFrames.snapshotBefore_hasType frameRegistered
  · apply HasType.var
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type, payload⟩ =
        source.inputs.any (fun input => decide (input.id = binder.id)) := rfl
    show (inserted :: context)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal
        (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
          ⟨source, scope, Renaming.comp (Renaming.insertion 0)
            (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
            payload⟩ then 0 else 1) + globals))]? = some (.cell layout.type)
    rw [named, CaptureCopies.copyReferences_frame]
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ]
    exact frame
  · apply allocation.hasType payloadWF _ initializer
    apply SourceCoreSourceCells.captures_hasType
    intro position binding found
    have below : position < scope.length := (List.getElem?_eq_some_iff.mp found).1
    show (inserted :: context)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal position)]? =
        some (OptionalCell.referenceType binding.2)
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ,
      SourceCoreSourceCells.copyReferences, below]
    exact slots position binding.1 binding.2 found

/-- One marked copy of a slot is a cell of the slot's payload type: both
branches of the payload test allocate one. -/
private theorem markedCopy_hasType {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal : Nat} {context : Core.Context} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      reference = .ok copy)
    (frameRegistered : layout.Registered layouts.definitions)
    (payloadWF : type.WellFormed layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (slotType : Ty), scope[index]? = some (id, slotType) →
      context[base index + ordinal]? = some (.cell (OptionalCell.cellType slotType)))
    (frame : context[base (scope.length + 1 + globals) + ordinal]? = some (.cell layout.type))
    (referenceTyped : HasType context reference (.cell (OptionalCell.cellType type)) layouts.definitions) :
    HasType context copy (.cell (OptionalCell.cellType type)) layouts.definitions := by
  obtain ⟨absent, present, absentAccepted, presentAccepted, rfl⟩ := CaptureCopies.copyCell_some accepted
  exact .caseE (.loadCell referenceTyped)
    (markedBranch_hasType absentAccepted frameRegistered payloadWF slots frame
      (fun _ found => by cases found))
    (markedBranch_hasType presentAccepted frameRegistered payloadWF slots frame
      (fun _ found => by cases found; exact .var rfl))

/-- One more copy, of a slot of type `slotType`, keeps the copy renaming
type-respecting. -/
private theorem respects_markedCopy {done : List Nat} {position : Nat} {context copies : Core.Context}
    {slotType : Ty} (respects : Renaming.Respects (copyRenaming done) context (copies ++ context))
    (slot : context[position]? = some slotType) :
    Renaming.Respects (copyRenaming (done ++ [position])) context ((slotType :: copies) ++ context) := by
  intro index type found
  by_cases member : index ∈ done
  · rw [copyRenaming_snoc_of_mem member]
    simpa using respects found
  · by_cases same : index = position
    · subst index
      rw [copyRenaming_snoc_self member]
      rw [slot] at found
      simpa using found
    · rw [copyRenaming_snoc_of_ne same]
      simpa using respects found

/-- The remaining marked copies of a chain type its body, renamed to the
copies, in the context extended by every copy. -/
private theorem copyChainIndexed_hasType {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty}
    (frameRegistered : layout.Registered layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (frame : context[base (scope.length + 1 + globals)]? = some (.cell layout.type))
    (bodyTyped : HasType context body type layouts.definitions) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (done : List Nat) (copies : Core.Context)
      (emitted : Expr),
      done.length = ordinal → copies.length = ordinal →
      Renaming.Respects (copyRenaming done) context (copies ++ context) →
      (∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty), rest[offset]? = some (id, payload) →
        context[base (index + offset)]? = some (.cell (OptionalCell.cellType payload))) →
      (∀ binding ∈ rest, binding.2.WellFormed layouts.definitions) →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope base rest index ordinal
        (body.rename (copyRenaming (done ++ chainPositions source base rest index))) = .ok emitted →
      HasType (copies ++ context) emitted type layouts.definitions
  | [], _, _, done, copies, emitted, _, _, respects, _, _, accepted => by
      rw [CaptureCopies.copyChain_nil _ _ _ _ _ _ accepted]
      simpa [chainPositions] using bodyTyped.rename respects
  | (id, payload) :: rest, index, ordinal, done, copies, emitted, doneLength, copiesLength, respects,
      restSlots, wellFormed, accepted => by
      have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
        simpa using restSlots 0 id payload rfl
      have later : ∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty),
          rest[offset]? = some (id, payload) →
          context[base (index + 1 + offset)]? = some (.cell (OptionalCell.cellType payload)) := by
        intro offset id payload found
        have shifted := restSlots (offset + 1) id payload (by simpa using found)
        rwa [show index + (offset + 1) = index + 1 + offset by omega] at shifted
      have laterWellFormed : ∀ binding ∈ rest, binding.2.WellFormed layouts.definitions :=
        fun binding member => wellFormed binding (List.mem_cons_of_mem _ member)
      cases copied : copiedBinder? source id with
      | none =>
          have positions : chainPositions source base ((id, payload) :: rest) index =
              chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied]
          rw [CaptureCopies.copyChain_shared _ _ _ _ _ _ _ copied, positions] at accepted
          exact copyChainIndexed_hasType frameRegistered slots frame bodyTyped rest (index + 1) ordinal done
            copies emitted doneLength copiesLength respects later laterWellFormed accepted
      | some binder =>
          have positions : done ++ chainPositions source base ((id, payload) :: rest) index =
              (done ++ [base index]) ++ chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied, List.append_assoc, List.singleton_append]
          rw [positions] at accepted
          obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ :=
            CaptureCopies.copyChain_copied copied accepted
          have copyTyped : HasType (copies ++ context) copy (.cell (OptionalCell.cellType payload))
              layouts.definitions := by
            apply markedCopy_hasType copyAccepted frameRegistered (wellFormed (id, payload) (by simp))
            · intro position slotId slotType found
              rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact slots position slotId slotType found
            · rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact frame
            · apply HasType.var
              rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact slot
          have tail := copyChainIndexed_hasType frameRegistered slots frame bodyTyped rest (index + 1)
            (ordinal + 1) (done ++ [base index]) (.cell (OptionalCell.cellType payload) :: copies)
            continuation (by simp [doneLength]) (by simp [copiesLength]) (respects_markedCopy respects slot)
            later laterWellFormed continuationAccepted
          exact .letE copyTyped tail

/-- Marked copies keep an expression's type when every scope slot holds a cell
of its well-formed payload type and the frame slot holds the frame cell. -/
theorem copyScopeIndexed_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body emitted : Expr} {type : Ty}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError))) source scope base body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (payloads : ∀ binding ∈ scope, binding.2.WellFormed definitions)
    (frame : context[base (scope.length + 1 + globals)]? = some (.cell layout.type))
    (typed : HasType context body type definitions) :
    HasType context emitted type definitions := by
  subst sameDefinitions
  simp only [SourceCoreSourceCells.copyScope, scopeCopyRenaming_eq] at accepted
  exact copyChainIndexed_hasType frameRegistered slots frame typed scope 0 0 [] [] emitted rfl rfl
    (fun _ _ found => by simpa [copyRenaming_nil] using found)
    (fun offset id payload found => by simpa using slots offset id payload found)
    payloads (by simpa only [List.nil_append] using accepted)

/-- The absent branch of a marked copy ends by allocating a cell of the
request's optional payload type, so that is its only type. -/
private theorem markedAbsent_type {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
      (layouts.allocatorAt owner active onError) request)
    (same : annotation.original = allocation.expression) (absent : request.payload = none)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context annotation.expression result definitions) :
    result = OptionalCell.referenceType request.payloadType := by
  rw [annotation.exact] at typed
  cases typed with
  | letE _ original =>
    have allocated := TypedLexicalWhile.Native.remove_front original
    rw [same, allocation.expressionExact] at allocated
    unfold SourceCoreAllocationLayouts.allocation at allocated
    simp only [absent] at allocated
    unfold SourceCoreHeapMarkers.allocate at allocated
    cases allocated with
    | letE _ cell =>
      unfold OptionalCell.allocate at cell
      cases cell with
      | newCell _ => rfl

/-- A marked copy of a slot has only the type of a cell of the slot's payload
type. -/
private theorem markedCopy_type {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {references : Renaming}
    {binder : TypedBinder} {type : Ty} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope references binder type reference = .ok copy)
    {definitions : DataEnvironment} {context : Core.Context} {copyType : Ty}
    (typed : HasType context copy copyType definitions) :
    copyType = .cell (OptionalCell.cellType type) := by
  obtain ⟨absent, present, absentAccepted, _, rfl⟩ := CaptureCopies.copyCell_some accepted
  obtain ⟨allocation, annotation, same, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError absentAccepted
  cases typed with
  | caseE _ absentTyped _ => exact markedAbsent_type allocation annotation same rfl absentTyped

/-- One more copy, of a slot holding the copy's type, keeps the copy renaming
pulling typings back to the original context. -/
private theorem pullsBack_markedCopy {done : List Nat} {position : Nat} {context copies : Core.Context}
    {slotType : Ty}
    (back : TypedLexicalWhile.Native.PullsBack (copyRenaming done) context (copies ++ context))
    (slot : context[position]? = some slotType) :
    TypedLexicalWhile.Native.PullsBack (copyRenaming (done ++ [position])) context
      ((slotType :: copies) ++ context) := by
  intro index type found
  by_cases member : index ∈ done
  · rw [copyRenaming_snoc_of_mem member] at found
    exact back index type (by simpa using found)
  · by_cases same : index = position
    · subst index
      rw [copyRenaming_snoc_self member] at found
      rw [slot]
      simpa using found
    · rw [copyRenaming_snoc_of_ne same] at found
      exact back index type (by simpa using found)

/-- Typed marked copies of a chain type its body, renamed to the copies, in
the context extended by the copies' types; the copy renaming pulls that typing
back to the original context. -/
private theorem copyChainIndexed_body_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty} :
    ∀ (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (done : List Nat) (copies : Core.Context)
      (emitted : Expr),
      TypedLexicalWhile.Native.PullsBack (copyRenaming done) context (copies ++ context) →
      (∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty), rest[offset]? = some (id, payload) →
        context[base (index + offset)]? = some (.cell (OptionalCell.cellType payload))) →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope base rest index ordinal
        (body.rename (copyRenaming (done ++ chainPositions source base rest index))) = .ok emitted →
      HasType (copies ++ context) emitted type definitions →
      HasType context body type definitions
  | [], _, _, done, copies, emitted, back, _, accepted, typed => by
      rw [CaptureCopies.copyChain_nil _ _ _ _ _ _ accepted] at typed
      simp only [chainPositions, List.append_nil] at typed
      exact TypedLexicalWhile.Native.typing body back typed
  | (id, payload) :: rest, index, ordinal, done, copies, emitted, back, restSlots, accepted, typed => by
      have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
        simpa using restSlots 0 id payload rfl
      have later : ∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty),
          rest[offset]? = some (id, payload) →
          context[base (index + 1 + offset)]? = some (.cell (OptionalCell.cellType payload)) := by
        intro offset id payload found
        have shifted := restSlots (offset + 1) id payload (by simpa using found)
        rwa [show index + (offset + 1) = index + 1 + offset by omega] at shifted
      cases copied : copiedBinder? source id with
      | none =>
          have positions : chainPositions source base ((id, payload) :: rest) index =
              chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied]
          rw [CaptureCopies.copyChain_shared _ _ _ _ _ _ _ copied, positions] at accepted
          exact copyChainIndexed_body_hasType rest (index + 1) ordinal done copies emitted back later
            accepted typed
      | some binder =>
          have positions : done ++ chainPositions source base ((id, payload) :: rest) index =
              (done ++ [base index]) ++ chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied, List.append_assoc, List.singleton_append]
          rw [positions] at accepted
          obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ :=
            CaptureCopies.copyChain_copied copied accepted
          cases typed with
          | letE copyTyped continuationTyped =>
            obtain rfl := markedCopy_type copyAccepted copyTyped
            exact copyChainIndexed_body_hasType rest (index + 1) (ordinal + 1) (done ++ [base index])
              (.cell (OptionalCell.cellType payload) :: copies) continuation (pullsBack_markedCopy back slot)
              later continuationAccepted continuationTyped

/-- Marked copies around an expression type it in the original context, when
every scope slot holds a cell of its payload type. -/
theorem copyScopeIndexed_body_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body emitted : Expr} {type : Ty}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError))) source scope base body = .ok emitted)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (typed : HasType context emitted type definitions) :
    HasType context body type definitions := by
  simp only [SourceCoreSourceCells.copyScope, scopeCopyRenaming_eq] at accepted
  exact copyChainIndexed_body_hasType scope 0 0 [] [] emitted
    (by intro index type found; simpa [copyRenaming_nil] using found)
    (fun offset id payload found => by simpa using slots offset id payload found)
    (by simpa only [List.nil_append] using accepted) typed

end Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
/-! A successful local-reference authenticator retains the exact binder
identity checked against its actual original node. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
open Frontend SourceInference SourceCoreLocalEvidence

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual form guard identifies the same local binder even when the
reference is authenticated inside a contextual lambda. -/
theorem original_form
    {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : Binding} {parent : Option Prepared} {id : ExpressionId}
    {reference : Reference}
    (accepted : authenticateReference program plan binding parent id = .ok reference) :
    ∃ name, reference.original.form = .reference name (.local binding.binder.id) := by
  unfold authenticateReference at accepted
  obtain ⟨caller, _caller, accepted⟩ := bind_ok accepted
  obtain ⟨⟨active, inherited⟩, _context, accepted⟩ := bind_ok accepted
  obtain ⟨validated, _validated, accepted⟩ := bind_ok accepted
  cases validated
  dsimp only at accepted
  split at accepted
  · next node found =>
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · next name localId form =>
        split at accepted
        · cases accepted
        · next same =>
          split at accepted
          · next owned ownedEq =>
            obtain ⟨available, _available, accepted⟩ := bind_ok accepted
            obtain ⟨⟨child, witnesses⟩, _factory, accepted⟩ := bind_ok accepted
            obtain ⟨validated, _witnesses, accepted⟩ := bind_ok accepted
            cases validated
            cases accepted
            have sameBinder : localId = binding.binder.id := by
              by_cases equal : localId = binding.binder.id
              · exact equal
              · exact False.elim (same equal)
            exact ⟨name, by simpa only [sameBinder] using form⟩
          · cases accepted
      · cases accepted
  · cases accepted

end Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
open Frontend SourceInference SourceCoreElaboration
open SourceCoreElaboration.Internal

/-- Only actually consumed implementation rows must be valid. The full ledger is retained. -/
def UsedValid (context : Context) (solved : List SolvedRequirement) (used : List RequirementId) : Prop :=
  ∀ row proof, row ∈ solved → row.id ∈ used → row.evidence = .implementation proof → SolvedRequirementValid context row

theorem UsedValid.mono {context : Context} {solved : List SolvedRequirement} {small large : List RequirementId}
    (valid : UsedValid context solved large) (subset : ∀ id, id ∈ small → id ∈ large) : UsedValid context solved small := by
  intro row proof member used actual
  exact valid row proof member (subset row.id used) actual

theorem selected_proves {context : Context} {solved : List SolvedRequirement} {used : List RequirementId}
    {resolution : IntegerLiteralResolution} {implementation : ProgramImplId}
    (selected : NumericLiteralEvidenceReceipts.Selected solved resolution implementation)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved used)
    (usedHere : resolution.requirement ∈ used) : RequirementProves context resolution.requirement resolution.predicate := by
  obtain ⟨row, singleton, predicate, evidence⟩ := selected
  have member : row ∈ solved.filter (fun row => decide (row.id = resolution.requirement)) := by rw [singleton]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have identifier : row.id = resolution.requirement := of_decide_eq_true identity
  exact ⟨row, ⟨ledger ▸ member, identifier⟩, predicate,
    valid row _ member (identifier ▸ usedHere) evidence⟩

def bindingValue (binding : Staged.Binding) : Int := by
  cases binding with
  | mk binder value => exact value

/-- An actual compiler lookup refers to the same initialized ordinary source cell. -/
def EnvironmentRep (actual : Staged.Environment) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop :=
  ∀ id binding, Staged.lookup actual id = some binding → ∃ location cell,
    Dynamic.Environment.LooksUp environment id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = none ∧ cell.value = some (.integer (bindingValue binding))

private theorem of_raw {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
  rw [empty]
  exact .nil

private theorem integer_literal {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {validated : NativeIntegerLiteral}
    (found : source.lookupExpression? id = some node) (form : node.form = .integerLiteral literal resolution)
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved validated.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer validated.value) heap := by
  have metadata := validateNativeIntegerLiteral_sound accepted
  have proves := selected_proves (NumericLiteralEvidenceReceipts.integer accepted) ledger valid
    (by rw [metadata.consumedRequirements]; simp)
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.integer validated.value) := by
    rw [metadata.value]
    cases resolution with
    | mk raw target requirement =>
      have targetEq := metadata.targetType
      dsimp only at targetEq
      subst target
      exact .integer metadata.meaning proves
  apply of_raw found metadata.coercions
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl constructs

private theorem word_literal {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {validated : WordIntegerLiteral}
    (found : source.lookupExpression? id = some node) (form : node.form = .integerLiteral literal resolution)
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (ledger : context.solvedRequirements = solved) (valid : UsedValid context solved validated.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word validated.value) heap := by
  have metadata := validateWordIntegerLiteral_sound accepted
  have proves := selected_proves (NumericLiteralEvidenceReceipts.word accepted) ledger valid
    (by rw [metadata.consumedRequirements]; simp)
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution (.word validated.value) := by
    rw [metadata.value]
    cases resolution with
    | mk raw target requirement =>
      have targetEq := metadata.targetType
      dsimp only at targetEq
      subst target
      exact .word metadata.meaning proves
  apply of_raw found metadata.coercions
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl constructs

private theorem group {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id inner : ExpressionId} {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (child : Dynamic.ExpressionEvaluates program context evidence source environment heap inner value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found coercions
  rw [form, requirements, coercions]
  exact .group rfl child

private theorem builtin {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id callee : ExpressionId} {node : ExpressionNode} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {values : List Dynamic.Value} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .call callee arguments (.builtinFunction function))
    (validated : Staged.BuiltinChecked source node callee arguments function)
    (children : Dynamic.ExpressionsEvaluate program context evidence source environment heap arguments values heap)
    (applies : Dynamic.BuiltinApplies function values value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found validated.coercions
  rw [form, validated.requirements, validated.coercions]
  exact .builtinCall rfl children (.builtin applies)

private theorem binary_applies {function : BuiltinFunctionId} {operation : Staged.BinaryOperation}
    (selected : Staged.binaryOperation? function = some operation) (a b : Int) :
    Dynamic.BuiltinApplies function [.integer a, .integer b] (.integer (Staged.applyBinary operation a b)) := by
  cases function <;> simp only [Staged.binaryOperation?] at selected <;> try contradiction
  all_goals cases selected
  · exact .integerSub a b
  · exact .integerAdd a b
  · exact .integerMul a b

private theorem comparison_applies {function : BuiltinFunctionId} {operation : Staged.Comparison}
    (selected : Staged.comparison? function = some operation) (a b : Int) :
    Dynamic.BuiltinApplies function [.integer a, .integer b] (.bool (Staged.applyComparison operation a b)) := by
  cases function <;> simp only [Staged.comparison?] at selected <;> try contradiction
  all_goals cases selected
  · exact .integerEq a b
  · exact .integerLt a b


private theorem conditional {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id condition yes no : ExpressionId} {node : ExpressionNode} {truth : Bool} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (form : node.form = .conditional condition yes no)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (test : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool truth) heap)
    (branch : Dynamic.ExpressionEvaluates program context evidence source environment heap (if truth then yes else no) value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply of_raw found coercions
  rw [form, requirements, coercions]
  cases truth
  · exact .conditionalFalse rfl test branch
  · exact .conditionalTrue rfl test branch

variable {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  (ledger : context.solvedRequirements = solved) (environments : EnvironmentRep actual environment heap)

include ledger environments in
/-- The three mutually dependent checks yield independent source executions.
Validation-only children are retained, and only the selected branch executes. -/
theorem checked_meaning (fuel : Nat) :
    (∀ {id result}, Staged.IntegerChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap) ∧
    (∀ {id result}, Staged.WordChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap) ∧
    (∀ {id result}, Staged.BoolChecked solved source actual true fuel id result →
      UsedValid context solved result.consumedRequirements →
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro id result checked valid <;> cases checked
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro id result checked valid
      cases checked with
      | literal found form accepted => exact integer_literal found form accepted ledger valid
      | «local» found form _ requirements coercions _ selected _ _ _ _ =>
        obtain ⟨location, cell, lookup, read, ordinary, initialized⟩ := environments _ _ selected
        apply of_raw found coercions
        rw [form, requirements, coercions]
        exact .local rfl lookup read ordinary initialized
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.1 child valid)
      | binary found form operation validated leftChecked rightChecked =>
        have left := ih.1 leftChecked (valid.mono (by intro id member; exact List.mem_append_left _ member))
        have right := ih.1 rightChecked (valid.mono (by intro id member; exact List.mem_append_right _ member))
        exact builtin found form validated (.cons left (.cons right .nil)) (binary_applies operation _ _)
      | fromWord found form validated child =>
        exact builtin found form validated (.cons (ih.2.1 child valid) .nil) (.wordToInteger _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.1 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.1 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
    · intro id result checked valid
      cases checked with
      | literal found form accepted => exact word_literal found form accepted ledger valid
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.2.1 child valid)
      | fromInteger found form validated child =>
        exact builtin found form validated (.cons (ih.1 child valid) .nil) (.wordFromInteger _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.2.1 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.2.1 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
    · intro id result checked valid
      cases checked with
      | literal found form _ requirements coercions _ =>
        apply of_raw found coercions
        rw [form, requirements, coercions]
        exact .builtinBoolean rfl
      | group found form _ requirements coercions child =>
        exact group found form requirements coercions (ih.2.2 child valid)
      | comparison found form operation validated leftChecked rightChecked =>
        have left := ih.1 leftChecked (valid.mono (by intro id member; exact List.mem_append_left _ member))
        have right := ih.1 rightChecked (valid.mono (by intro id member; exact List.mem_append_right _ member))
        exact builtin found form validated (.cons left (.cons right .nil)) (comparison_applies operation _ _)
      | conditional found form _ requirements coercions guardChecked yesChecked noChecked =>
        rename_i condition yes no node guardResult leftResult rightResult typed
        have guard := ih.2.2 guardChecked (valid.mono (by
          intro id member
          exact List.mem_append_left _ (List.mem_append_left _ member)))
        cases truth : guardResult.value with
        | false =>
          have branch := ih.2.2 (by simpa only [truth, Bool.true_and, Bool.not_false] using noChecked)
            (valid.mono (by intro id member; exact List.mem_append_right _ member))
          simpa only [truth, Bool.false_eq_true, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)
        | true =>
          have branch := ih.2.2 (by simpa only [truth, Bool.true_and] using yesChecked)
            (valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member)))
          simpa only [truth, ↓reduceIte] using conditional found form requirements coercions guard (by simpa only [truth, Bool.false_eq_true, ↓reduceIte] using branch)


/-- An empty compiler environment places no restriction on the source heap. -/
theorem EnvironmentRep.empty (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    EnvironmentRep [] environment heap := by
  intro id binding found
  change none = some binding at found
  contradiction

include ledger environments in
/-- Actual accepted Integer evaluation yields the exact validation/consumption
tree and an independent source execution, preserving the entire input heap. -/
theorem integer_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : Staged.integer solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap := by
  have checked := Staged.integer_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).1 checked valid⟩

include ledger environments in
/-- Conversions use the same source Word carrier, including modulo conversion. -/
theorem word_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedWordEvaluation}
    (accepted : Staged.word solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap := by
  have checked := Staged.word_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).2.1 checked valid⟩

include ledger environments in
/-- Comparisons and conditional selection follow the independent source rules. -/
theorem bool_of_accepted {fuel : Nat} {id : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : Staged.bool solved source actual true fuel id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source actual true fuel id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap := by
  have checked := Staged.bool_checked accepted
  exact ⟨checked, (checked_meaning ledger environments fuel).2.2 checked valid⟩

include ledger in
/-- The existing public Integer evaluator is sound for every accepted closed
fragment. Unused ledger rows and all source heap cells are retained. -/
theorem evaluateStagedInteger_sound {id : ExpressionId} {result : StagedIntegerEvaluation}
    (accepted : evaluateStagedInteger solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.integer result.value) heap :=
  integer_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

include ledger in
/-- The existing public Word evaluator returns its exact validation receipt and
same-heap source witness, without imposing validity on unused ledger rows. -/
theorem evaluateStagedWord_sound {id : ExpressionId} {result : StagedWordEvaluation}
    (accepted : evaluateStagedWord solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.word result.value) heap :=
  word_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

include ledger in
/-- Both branches are statically checked and consumed in order. The independent
source witness executes only the selected branch. -/
theorem evaluateStagedBool_sound {id : ExpressionId} {result : StagedBoolEvaluation}
    (accepted : evaluateStagedBool solved source id = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) id result ∧
      Dynamic.ExpressionEvaluates program context evidence source environment heap id (.bool result.value) heap :=
  bool_of_accepted ledger (EnvironmentRep.empty environment heap) accepted valid

end Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
end
