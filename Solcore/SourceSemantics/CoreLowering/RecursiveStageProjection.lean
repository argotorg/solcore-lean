import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry

/-! Codebook authentication and recursive lambda scope selection for the actual
projection-parameterized public factory. No law about the projection is needed
to recover original contracts: their markers and complete contextual source
substitutions come from retained factory receipts. This does not infer payload
code or capture correctness from the projected Core type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
open Frontend Frontend.SourceInference SourceCoreStageCodebook GeneralHeap
open CallContractCertificates CallEntryCertificates AuthenticatedCallableLedger RecursiveStageRegistry

theorem lambda_site_of_descriptor {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active)) :
    Nonempty (LambdaSite plan table owner id active descriptor.id) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
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
theorem named_origin {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {key : Key} {function : Dynamic.GlobalFunction}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.global function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
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
theorem builtin_origin {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {function : Dynamic.BuiltinFunction}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.builtin function.id)) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.builtin function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | builtin =>
    have related := CallableLedger.OriginRep.builtin (plan := plan) (raw := raw) member origin contract_eq
    simpa only [id_eq] using related


/-- Actual lambda metadata selects its original invocation frame under the
projection-parameterized public factory. -/
theorem selected_of_prepare {checkedProgram : CheckedProgram} {plan : Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {sidecar : Sidecar} {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {lexical : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram plan projectType limits firstId = .ok table)
    (prepared : SourceCoreStageContracts.prepareSidecar plan compilation.owner = .ok sidecar)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (owner : function.source.owner = compilation.owner.declaration)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view lexical id node
      function.parameters function.resultType function.body reportedType lowered) :
    (registry checkedProgram plan table).Closure function (scope sidecar active function) := by
  obtain ⟨site⟩ := lambda_site_of_descriptor accepted descriptor
  have same := (CallContractCertificates.sidecar_of_accepted prepared).2
  let alignedSite : LambdaSite plan table sidecar.caller.key id active descriptor.id := by
    simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source := by
    simpa only [same] using source
  exact Selected.lambda (by simpa only [same] using prepared) alignedSite alignedSource
    (by simpa only [same] using owner)
    (LambdaMetadataViews.lambda_origin alignedSource alignedSite.original metadata unique artifact.raw.found artifact.raw.form)


/-- The same actual decision rows cover the represented guarded calls. -/
theorem covers_of_prepare {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying plan site.table) (CallableLedger.frame sidecar)
      site site.call arguments sourceType type := by
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection accepted caller contains form
  rw [← (sidecar_of_accepted caller).1]
  intro mapping world source carrier contract represented bound
  exact CallableLedger.covers underlying rows sourceType type represented bound


end Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
