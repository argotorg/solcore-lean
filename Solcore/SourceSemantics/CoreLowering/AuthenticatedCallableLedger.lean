import Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
import Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates

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
