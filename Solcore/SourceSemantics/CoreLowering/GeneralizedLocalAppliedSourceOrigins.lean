import Solcore.SourceSemantics.CoreLowering.CallableLedger
import Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts

/-! An actual local-scheme use supplies the source origin of its visible
descriptor. The independently substituted Source remains paired with the
read's metadata; its entire source table need not equal the rewritten table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins
open Core Frontend SourceInference TypeSystem GeneralHeap
open CallableAppliedViewProvenance
open SourceCoreCallableAncestryReadRecipes
open GeneralizedLocalDescriptorOrigin

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem catalog_of_automatic {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    ∃ ownership : automatic.checked.signatures = program.signatures,
      SourceCoreCompatibleFunctions.prepareWithCatalog program plan automatic.checked ownership fuel =
        .ok automatic.prepared := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨_, prepared⟩

theorem catalog_of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    ∃ (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
      (ownership : compiled.compatible.checked.signatures = program.signatures) (fuel : Nat),
      SourceCoreCompatibleFunctions.prepareWithCatalog program plan compiled.compatible.checked ownership fuel =
        .ok compiled.indexed.base := by
  obtain ⟨ownership, prepared⟩ := catalog_of_automatic compiled.compatiblePrepared
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared]
  exact ⟨_, _, ownership, _, prepared⟩

variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Word}
    (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)

/-- The contract and runtime source originate at the same applied descriptor.
The body and captured cells remain the responsibility of the value relation. -/
theorem origin_rep {function : Dynamic.Closure} {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs
      (.appliedView id target callerFrame lexicalFrame) (recipe.read.after lexical) function.source)
    (header : ExpressionForm.lambda function.parameters function.resultType function.body =
      recipe.read.template.node.form) (payload : Value) :
    CallableLedger.OriginRep base.plan inputs.callable.table (.closure function)
      (.pair payload (.word target)) := by
  have descriptor : recipe.read.descriptor.id = target := by
    simpa using List.find?_some recipe.read.descriptorSelected
  have provenance : CallableLedger.LambdaOrigin base.plan recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active function contract :=
    .independentApplied recipe canonical retained rfl rfl rfl paired header
  have result := CallableLedger.OriginRep.closure (raw := payload)
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected)
    recipe.read.templateOrigin retained provenance
  simpa only [descriptor] using result

theorem materialized {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {active : Substitution}
    (origin : Origin compiled.indexed function binding active)
    {callerFrame : SourceCoreCallablePairedFrames.Frame} {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Word}
    (recipe : Recipe compiled.indexed.ancestry.graph.inputs callerFrame origin.ghost
      caller origin.metadata id target)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actual : TypeSystem.Ty} {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence function.binder
      actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) (payload : Value) :
    let result := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    LambdaMetadataViews.MetadataView result.source (recipe.read.after origin.metadata).metadata.source ∧
      CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
        (.closure result) (.pair payload (.word target)) := by
  obtain ⟨paired, _, header, _, _⟩ :=
    origin.materialize recipe captures unique instantiation sameScheme sameType
  obtain ⟨program, plan, ownership, fuel, prepared⟩ := catalog_of_compiled compiled
  have table := (RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected).accepted
  rw [← (SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at table
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared prepared table recipe.read
  exact ⟨CallableIndependentSourceViews.of_pair paired,
    origin_rep recipe canonical retained paired header payload⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins
