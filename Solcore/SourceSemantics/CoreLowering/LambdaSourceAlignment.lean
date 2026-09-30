import Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution

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
