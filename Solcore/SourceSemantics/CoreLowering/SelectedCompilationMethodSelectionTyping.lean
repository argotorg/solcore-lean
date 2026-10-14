import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionSourceSelection
open CallableNamedMetadata (evidence environment)
open CallableCoercionMethodInstantiation (bodyInstance Formation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}

theorem retained_valid (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method) :
    MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked receipt.retained) :=
  bodies.methods receipt.retained ⟨cached.index, cached.named, method, cached.selected, cached.same,
    receipt.toSelection, receipt.retainedMember, receipt.retainedId, receipt.completeCheckedEq⟩

theorem certificate
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    {primary : TypedTraitResolution.Evidence} {name : String}
    (selected : CallableCoercionMethodInstantiation.Selection compiled.sourceProgram primary name method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution) :
    ∃ definition, definition ∈ (Program.ofChecked compiled.sourceProgram).methods ∧
      definition.id = selected.declaration.id ∧
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        selected.implementation selected.declaration selected.trait definition
        method.specialized.parameterSubstitution (bodyInstance compiled.sourceProgram method) ∧
      ∃ types lexical facts, Dynamic.TraitMethodInstanceTypingCertificate
        (Program.ofChecked compiled.sourceProgram) selected.declaration method.specialized.parameterSubstitution
        definition (bodyInstance compiled.sourceProgram method) types lexical facts := by
  obtain ⟨definition, member, identity, instantiated⟩ := selected.instantiates checked parameters range
  obtain ⟨retained, retainedMember, retainedId, retainedBody⟩ := selected.toSelection.retained checked
  have retainedValid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same, selected.toSelection,
      retainedMember, retainedId, retainedBody⟩
  have sameDefinition : definition = MethodDefinition.ofChecked retained :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup bodies.method_ids member
      (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (identity.trans (retainedId.trans selected.methodId).symm)
  have valid : MethodDefinition.Valid compiled.sourceProgram.signatures definition :=
    sameDefinition ▸ retainedValid
  exact ⟨definition, member, identity, instantiated,
    instantiated.certificate_of_valid bodies.signatures valid⟩

theorem selects
    {method : ExecutableImplMethods.CheckedMethod}
    (loadedAccepted : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled method.specialized)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {primaryId : RequirementId} {methodIds : List RequirementId} {arity : Nat}
    {traitName methodName : String} {context : Context}
    (receipt : MethodCertificate compiled.sourceProgram caller node available primaryId methodIds arity traitName methodName method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence compiled.sourceProgram caller node ⟨primaryId, method⟩ = .ok dictionary) :
    TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context (environment available) traitName methodName
      (primaryId :: methodIds) (bodyInstance compiled.sourceProgram method) (environment dictionary) := by
  obtain ⟨definition, definitionMember, definitionId, instantiated, certified⟩ :=
    certificate loadedAccepted bodies cached receipt.selected formed.parameters range
  have determined := receipt.selected.determines formed
  have headTrait : receipt.selected.goal.trait = receipt.selected.implementation.head.trait := by
    exact (congrArg (fun goal : ProgramPredicate => goal.trait) determined.2.2).symm
  have produced := requirement_produces signatures ledger assumptions resolved
    receipt.roots.primarySelected receipt.roots.primaryValid
  have sourceSelected : EvidenceSelectsMethod (Program.ofChecked compiled.sourceProgram)
      (evidence receipt.roots.primary) methodName definition := by
    simpa only [receipt.selected.primaryShape, evidence] using
      (EvidenceSelectsMethod.source (premises := method.implementationPremises.map evidence)
        receipt.selected.implementationMember headTrait receipt.selected.methodMember
        receipt.selected.declarationName definitionMember definitionId)
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal receipt.roots.primary = receipt.selected.goal := by
    exact congrArg SourceCompilationPlan.runtimeEvidenceGoal receipt.selected.primaryShape
  rw [primaryGoal] at produced
  have methodsProduced := requirements_produce signatures ledger assumptions resolved
    receipt.roots.methodsSelected receipt.roots.methodsValid
  have methodsGoals : receipt.roots.methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal =
      receipt.selected.declaration.wherePredicates.map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) := by
    rw [← receipt.roots.methods, receipt.selected.methodsGoals, receipt.selected.method_predicates formed]
  rw [methodsGoals] at methodsProduced
  have assembled := (CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
    (CallableCoercionEvidenceOrigins.materialized_operator materialized)).1
  have methodAssumptions : method.specialized.assumptions =
      (SourceSemantics.methodAssumptions receipt.selected.trait receipt.selected.implementation receipt.selected.declaration).map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) :=
    (CallableCoercionBodyProvenance.specialization_fields receipt.selected.specialized).2
  rw [methodAssumptions] at assembled
  have traitOwner : receipt.selected.declaration.traitMethod.trait = receipt.selected.trait.id := by
    have found := receipt.selected.traitLookup
    unfold ProgramSignatures.trait? at found
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = receipt.selected.declaration.traitMethod.trait)) found)).symm
  refine .intro (.intro produced sourceSelected) ?_ receipt.selected.implementationMember
    receipt.selected.traitMember receipt.traitName receipt.selected.goalTrait determined
    receipt.selected.methodMember receipt.selected.declarationName traitOwner methodsProduced instantiated ?_ ?_ certified
  · exact ⟨method.implementationPremises.map evidence, by
      simpa only [evidence] using congrArg evidence receipt.selected.primaryShape⟩
  · simpa only [environment, List.map_map, Function.comp_def] using assembled
  · obtain ⟨_, valid, goals⟩ := CallableCoercionEvidenceOrigins.roots_origins receipt.roots covered resolved
      (CallableCoercionEvidenceOrigins.materialized_operator materialized)
    refine ⟨valid, ?_⟩
    intro goal member
    exact EvidenceEnvironment.LooksUp.exists_of_key_mem (goals.symm ▸ member)


theorem source_selects
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Core.Word} {policy : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {receipt : Operator compiled.sourceProgram project caller compilation child fuel source scope id reasonAt policy node output}
    (cached : Cached compiled receipt.selection.method.specialized)
    (selected : SourceReceipt receipt)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : Context} (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method) :
    TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context (environment receipt.available)
      selected.traitName selected.methodName receipt.requirements
      (bodyInstance compiled.sourceProgram receipt.selection.method) (environment receipt.dictionary) := by
  rw [selected.requirements]
  exact selects checked bodies cached selected.certificate formed range signatures ledger assumptions
    receipt.resolved covered receipt.materialized

theorem selected_typed {sourceProgram : Program} {context : Context}
    {callerEvidence dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : Dynamic.BodyInstance}
    (selected : Dynamic.TypedOperatorMethodSelected sourceProgram context callerEvidence traitName methodName
      requirements body dictionary) :
    ∃ types lexicalContext facts,
      Dynamic.BodyInstanceTypingCertificate sourceProgram body types lexicalContext facts ∧
      CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements lexicalContext dictionary := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers certified =>
    obtain ⟨types, lexicalContext, facts, typed⟩ := certified
    refine ⟨types, lexicalContext, facts, typed.toBodyInstanceTypingCertificate, ?_⟩
    exact (show CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements body.context dictionary from
      ⟨rfl, typed.requirement_ledger.toRuntime, covers⟩).mono typed.typing.inputs_extend

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping
