import Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
import Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive

/-! Paired read-caller and lexical-principal metadata laws. The witness factory
reads the caller's occurrence metadata; substitution and requirement rewriting
act on the lexical principal source. Only the substitution is determined by
matching types. The witnesses retain the caller's actual requirement IDs.

These are laws about sealed preparation receipts, not runtime-history or
capture-ownership proofs. Independent dynamic instantiation does not rewrite
requirement IDs, so the comparison with it erases those lists only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata CallableAncestryProfiles
open CallableAncestryProfiles.SourceComposition

/-- Matching fixes the substitution without equating dictionaries or
occurrence IDs. Both callers and available evidence may differ. -/
theorem factory_substitution_eq
    {leftCaller rightCaller : SourceSpecialization.SpecializedFunction}
    {leftAvailable rightAvailable : SourceCompilationPlan.EvidenceEnvironment}
    {leftBinder rightBinder : TypedBinder} {leftNode rightNode : ExpressionNode}
    {leftSubstitution rightSubstitution : Substitution}
    {leftWitnesses rightWitnesses : List Witness}
    (left : SourceCompilationPlan.localRequirementWitnesses leftCaller leftAvailable leftBinder leftNode =
      .ok (leftSubstitution, leftWitnesses))
    (right : SourceCompilationPlan.localRequirementWitnesses rightCaller rightAvailable rightBinder rightNode =
      .ok (rightSubstitution, rightWitnesses))
    (scheme : leftBinder.scheme = rightBinder.scheme)
    (rawType : leftNode.rawType = rightNode.rawType) : leftSubstitution = rightSubstitution := by
  have matched := witnesses_matched left
  rw [scheme, rawType] at matched
  exact Option.some.inj (matched.symm.trans (witnesses_matched right))

/-- This derives equality from the actual factories and the two matching
inputs. It does not use the receipt's separate `substitutionExact` check. -/
theorem read_substitution_from_metadata
    {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution = read.entry.view.ownSubstitution :=
  factory_substitution_eq read.factory read.entry.view.exactFactory scheme rawType

section Read
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)

theorem read_member : read.entry ∈ inputs.views.entries :=
  List.mem_of_find?_eq_some read.selected

/-- The generator receipt can also be derived from the two matching inputs,
without using the read factory's explicit substitution equality check. -/
theorem read_generator_from_metadata
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution ∈ CallableAncestrySourceActive.generators inputs.views := by
  rw [read_substitution_from_metadata read scheme rawType]
  exact List.mem_map.mpr ⟨read.entry, read_member read, rfl⟩

/-- Successful read authentication selects a generator from the actual owned
table. The checked equality is sufficient even before metadata alignment has
been obtained from the native/source occurrence correspondence. -/
theorem read_generator : read.substitution ∈ CallableAncestrySourceActive.generators inputs.views := by
  rw [read.substitutionExact]
  exact List.mem_map.mpr ⟨read.entry, read_member read, rfl⟩

theorem after_reachable (lexical : SourceCoreCallableAncestryReadRecipes.State)
    (reachable : CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) (read.after lexical).metadata.active :=
  .step reachable (read_generator read)

theorem after_finite (lexical : SourceCoreCallableAncestryReadRecipes.State)
    (reachable : CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    RangesClosed (read.after lexical).metadata.active ∧
      (read.after lexical).metadata.active.domain.Nodup ∧
      (read.after lexical).metadata.active.length ≤ (CallableAncestrySourceActive.domainAlphabet (CallableAncestrySourceActive.generators inputs.views)).length ∧
      (read.after lexical).metadata.active ∈ CallableAncestrySourceActive.keySpace (CallableAncestrySourceActive.generators inputs.views) := by
  have valid := CallableAncestrySourceActive.generators_valid inputs.views
  have reached := after_reachable read lexical reachable
  exact ⟨reached.closed valid, reached.domain_unique valid, reached.length_bound valid, reached.keySpace_member valid⟩

/-- The source-active field composes with lexical creation metadata. No
equality with the native compilation context is asserted. -/
theorem after_contexts (lexical : SourceCoreCallableAncestryReadRecipes.State) :
    (read.after lexical).metadata.owner = lexical.metadata.owner ∧
      (read.after lexical).metadata.active = read.substitution.compose lexical.metadata.active ∧
      (read.after lexical).nativeActive = read.entry.view.cumulative := ⟨rfl, rfl, rfl⟩

theorem actual_ids_from_caller {ids : List RequirementId} (bounded : Bounded ids caller.metadata.source) :
    ∀ witness ∈ read.witnesses, witness.actualRequirement ∈ ids := by
  intro witness member
  have selected := witnesses_actual_subset read.factory witness member
  have owned := ordinary_requirements_subset read.requirementsSelected witness.actualRequirement selected
  exact lookup_requirements_bounded bounded read.found _ owned

theorem after_bounded (lexical : SourceCoreCallableAncestryReadRecipes.State) {ids : List RequirementId}
    (callerBounded : Bounded ids caller.metadata.source) (lexicalBounded : Bounded ids lexical.metadata.source) :
    Bounded ids (read.after lexical).metadata.source :=
  bounded_rewrite (bounded_substitute lexicalBounded read.substitution) (actual_ids_from_caller read callerBounded)

/-- A common finite alphabet may be formed from separate caller and lexical
alphabets. No unproved same-owner alphabet identity is needed. -/
theorem after_bounded_union (lexical : SourceCoreCallableAncestryReadRecipes.State) {callerIds lexicalIds : List RequirementId}
    (callerBounded : Bounded callerIds caller.metadata.source)
    (lexicalBounded : Bounded lexicalIds lexical.metadata.source) :
    Bounded (callerIds ++ lexicalIds) (read.after lexical).metadata.source := by
  apply after_bounded read lexical
  · intro spine member requirement occurs
    exact List.mem_append_left _ (callerBounded spine member requirement occurs)
  · intro spine member requirement occurs
    exact List.mem_append_right _ (lexicalBounded spine member requirement occurs)

theorem after_spines (lexical : SourceCoreCallableAncestryReadRecipes.State) :
    (requirementProfile (read.after lexical).metadata.source).map List.length =
      (requirementProfile lexical.metadata.source).map List.length := by
  change (requirementProfile (SourceTypedRuntime.rewriteLocalRequirements _
    (TypedSource.applySubstitution _ _))).map List.length = _
  rw [lengths_rewrite, profile_substitute]

theorem after_canonical (lexical : SourceCoreCallableAncestryReadRecipes.State) (original : TypedSource)
    (closed : RangesClosed lexical.metadata.active)
    (canonical : eraseRequirements lexical.metadata.source =
      eraseRequirements (original.applySubstitution lexical.metadata.active)) :
    eraseRequirements (read.after lexical).metadata.source =
      eraseRequirements (original.applySubstitution (read.after lexical).metadata.active) := by
  change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements _
    (TypedSource.applySubstitution _ _)) = eraseRequirements (original.applySubstitution (read.substitution.compose _))
  rw [rewrite_erased, erase_substitute, canonical, ← erase_substitute, source read.substitution _ closed]

end Read

section Applied
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} {read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target}
  {lexical : SourceCoreCallableAncestryReadRecipes.State} (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)

/-- The independently defined principal carrier for comparison of metadata.
The caller supplies a definition context, original binder, and captured source
locations. This definition does not authenticate those inputs. -/
def principal (context : Context) (binder : TypedBinder) (captured : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context lexical.metadata.source captured binder
    read.entry.view.principal.initializer applied.parameters applied.resultType applied.body

theorem instantiated_metadata (context : Context) (binder : TypedBinder) (captured : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) :
    let result := (principal applied context binder captured).instantiate read.substitution evidence
    eraseRequirements (read.after lexical).metadata.source = eraseRequirements result.source ∧
      ExpressionForm.lambda result.parameters result.resultType result.body = read.template.node.form ∧
      result.captured = captured ∧ result.evidence = evidence := by
  refine ⟨?_, applied.nativeHeader, rfl, rfl⟩
  exact rewrite_erased read.witnesses (lexical.metadata.source.applySubstitution read.substitution)

/-- The exported instance wraps the original lexical closure. Its raw header,
source, evidence, and complete ordered capture list remain unmodified. The
native target's closed header is used only when applying that instance. -/
theorem export_original (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue captured evidence = .instantiated read.substitution read.witnesses
      (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
        captured evidence) := rfl

theorem export_captures_injective {left right : SourceTypedRuntime.Environment}
    {leftEvidence rightEvidence : SourceCompilationPlan.EvidenceEnvironment}
    (same : applied.sourceValue left leftEvidence = applied.sourceValue right rightEvidence) :
    left = right ∧ leftEvidence = rightEvidence := by
  simpa only [SourceCoreCallableAncestryReadRecipes.Applied.sourceValue, SourceTypedRuntime.Value.instantiated.injEq,
    SourceTypedRuntime.Value.closure.injEq, true_and] using same

end Applied
end Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
