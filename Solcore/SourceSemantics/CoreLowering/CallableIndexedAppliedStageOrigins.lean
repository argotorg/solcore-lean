import Solcore.SourceSemantics.CoreLowering.CallableLedger
import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues

/-! Applied-view stage origins retain the actual two-parent recipe and both
metadata factories. A supplied full source equality connects an actual Code to
that recipe; its ordered header then follows from the actual lookup. The
rewritten source is not identified with a substitution-only source receipt,
and this module does not construct body typing or an execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
open Frontend SourceInference GeneralHeap CallableAppliedViewProvenance
open SourceCoreCallableAncestryReadRecipes CallContractCertificates AuthenticatedCallableLedger

variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical view target)

/-- All closure components come from the same applied lexical recipe. Its
context, captured cells and dictionary remain independently supplied. -/
structure Alignment (function : Dynamic.Closure) : Prop where
  source : function.source = (recipe.read.after lexical).metadata.source
  parameters : function.parameters = recipe.applied.parameters.map
    (TypedBinder.applySubstitution recipe.read.substitution)
  result : function.resultType = recipe.read.substitution.apply recipe.applied.resultType
  body : function.body = recipe.applied.body

variable {function : Dynamic.Closure}

theorem origin {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) :
    CallableLedger.LambdaOrigin base.plan recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active function contract :=
  .applied recipe canonical retained rfl rfl rfl aligned.source aligned.parameters aligned.result aligned.body

private theorem descriptor_id : recipe.read.descriptor.id = target :=
  of_decide_eq_true (List.find?_some
    (p := fun entry : SourceCoreStageCodebook.Entry => decide (entry.id = target)) recipe.read.descriptorSelected)

theorem origin_rep {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) (payload : Core.Value) :
    CallableLedger.OriginRep base.plan inputs.callable.table (.closure function) (.pair payload (.word target)) := by
  have related := CallableLedger.OriginRep.closure (raw := payload)
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected) recipe.read.templateOrigin retained
    (origin recipe canonical retained aligned)
  simpa only [descriptor_id recipe] using related

private theorem lambda_original {plan : SourceCompilationPlan.Plan} {owner : SourceCompilationPlan.Key}
    {id : ExpressionId} {active : TypeSystem.Substitution} {count : Nat}
    {attached : Option SourceCoreStageContracts.Contract}
    (authenticated : CallEntryCertificates.OriginContract plan (.lambda owner id active) count attached) :
    ∃ contract, attached = some contract ∧ Nonempty (LambdaSource plan owner id active contract) := by
  cases authenticated with
  | originalLambda prepared accepted => exact ⟨_, rfl, ⟨.original _ _ _ prepared accepted⟩⟩
  | contextualLambda prepared accepted => exact ⟨_, rfl, ⟨.contextual _ _ _ _ prepared accepted⟩⟩

private theorem site_of_prepared
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table) :
    ∃ site : LambdaSite base.plan inputs.callable.table recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active target, site.entry = recipe.read.descriptor := by
  have authenticated := CallEntryCertificates.prepareWithProjection_authenticates accepted recipe.read.descriptor
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected)
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [recipe.read.templateOrigin] at authenticated
  obtain ⟨contract, retained, ⟨original⟩⟩ := lambda_original authenticated
  exact ⟨⟨_, List.mem_of_find?_eq_some recipe.read.descriptorSelected, recipe.read.templateOrigin,
    descriptor_id recipe, contract, retained, original⟩, rfl⟩

/-- The returned recursive scope uses the semantic substitution. The selected
codebook row retains the separate native active context. -/
theorem selected
    {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {ownership : checked.signatures = program.signatures} {fuel : Nat}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (prepared : SourceCoreStageContracts.prepareSidecar base.plan sidecar.caller.key = .ok sidecar)
    (sameOwner : recipe.read.template.owner = sidecar.caller.key)
    (aligned : Alignment recipe function)
    (owner : function.source.owner = sidecar.caller.key.declaration) :
    (RecursiveStageRegistry.registry base.sourceProgram base.plan inputs.callable.table).Closure function
      (RecursiveStageRegistry.scope sidecar (recipe.read.substitution.compose lexical.metadata.active) function) := by
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared accepted table recipe.read
  obtain ⟨site, entryEq⟩ := site_of_prepared recipe table
  have contractEq : site.contract = contract := Option.some.inj (site.retained.symm.trans (entryEq ▸ retained))
  let site' : LambdaSite base.plan inputs.callable.table sidecar.caller.key recipe.read.template.id
      recipe.read.template.active target := {
    entry := site.entry, member := site.member, origin := by rw [← sameOwner]; exact site.origin
    id_eq := site.id_eq, contract := site.contract, retained := site.retained
    original := sameOwner ▸ site.original }
  have provenance : CallableLedger.LambdaOrigin base.plan sidecar.caller.key recipe.read.template.id
      recipe.read.template.active function site'.contract := by
    change CallableLedger.LambdaOrigin _ _ _ _ _ site.contract
    rw [contractEq]
    exact .applied recipe canonical retained rfl sameOwner rfl
      aligned.source aligned.parameters aligned.result aligned.body
  exact .applied recipe rfl rfl rfl prepared sameOwner site' aligned.source owner provenance

section Code
variable {indexed : SourceCoreCallableIndexedPrograms.Prepared checked}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe indexed.ancestry.graph.inputs callerFrame lexicalFrame caller lexical view target)
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code indexed function scope administrative)

/-- Actual lookup and the recipe's full source equality determine the lambda
header. A native type or history alone supplies neither premise. -/
theorem code_alignment
    (source : function.source = (recipe.read.after lexical).metadata.source)
    (sameId : code.id = recipe.read.entry.view.principal.initializer) : Alignment recipe function := by
  have found := code.sourceFound
  rw [source, sameId] at found
  have nodeEq := Option.some.inj (found.symm.trans recipe.source_node)
  have forms := ExpressionForm.lambda.inj
    (code.sourceForm.symm.trans ((congrArg ExpressionNode.form nodeEq).trans recipe.source_node_form))
  exact ⟨source, forms.1, forms.2.1, forms.2.2⟩

/-- The actual indexed closure carrier receives the same descriptor's origin.
Static body/evidence transport remains a separate obligation. -/
theorem code_origin
    {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {ownership : checked.signatures = program.signatures} {fuel : Nat}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok indexed.base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection indexed.base.sourceProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    (source : function.source = (recipe.read.after lexical).metadata.source)
    (sameId : code.id = recipe.read.entry.view.principal.initializer)
    (sameTarget : code.descriptor.id = target)
    (embedding : Core.Renaming) (native : CallableIndexedHistory.NativeFrame) (captured : Core.Environment) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table (.closure function)
      (CallableIndexedLambdaValues.value code embedding native captured) := by
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared accepted table recipe.read
  have related := origin_rep recipe canonical retained (code_alignment recipe code source sameId)
    (.pair (.inLeft .word .unit) (.closure code.receipt.parameterCore
      (Core.LanguageResult.resultType code.receipt.resultCore) (code.body.rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame native :: captured)))
  simpa only [CallableIndexedLambdaValues.value, sameTarget] using related
end Code

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
