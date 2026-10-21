import Solcore.SourceSemantics.SourceBodyGeneralizationLedger
import Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
import Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
import Solcore.SourceSemantics.SourceCompiledGeneralizationLifetimeSeeds
import Solcore.SourceSemantics.SourceCompiledHeaderLifetimeSeeds
import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts

/-! The actual initializer and its semantic boundary supply the forward
generalization condition. The remaining exclusion is consumed at that exact
receipt, together with the lifetime of its actual computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationBarrierConnection
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

variable {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    {selected : BodySelection compiled row fuel}

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro a b same
    cases a; cases b
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro a; cases a; simp [BEq.beq, instBEqRequirementId.beq]

/-- Actual cached specialization closes non-template predicates. Every
remaining variable belongs to the quantifiers of a different retained owner. -/
theorem ledger_variables
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (body : BodySelection compiled named.specialized fuel)
    {binder : TypedBinder}
    (distinct : ∀ other ∈ initializedLetBindings (evidenceSource body),
      other.binder ≠ binder → ∀ q ∈ binder.scheme.quantified, q ∉ other.binder.scheme.quantified)
    {target : SourceSemantics.Context}
    (solvedEq : target.solvedRequirements = body.body.finalized.solvedRequirements) :
    ∀ q ∈ binder.scheme.quantified,
      q ∉ (target.solvedRequirements.filter fun requirement =>
        !(localSchemeTemplateIds (binder.applySubstitution body.body.finalized.substitution)).contains
          requirement.id).flatMap fun requirement =>
            TypedTraitResolution.predicateVariables requirement.predicate := by
  intro q quantified appears
  obtain ⟨requirement, selectedRow, occurs⟩ := List.mem_flatMap.mp appears
  obtain ⟨member, notOwn⟩ := List.mem_filter.mp selectedRow
  have excluded : requirement.id ∉
      localSchemeTemplateIds (binder.applySubstitution body.body.finalized.substitution) := by
    intro own
    have present := List.contains_iff_mem.mpr own
    simp only [present, Bool.not_true] at notOwn
    contradiction
  rw [solvedEq] at member
  obtain ⟨owner, present, _sameId, _samePredicate, different, ownerQuantified⟩ :=
    SourceBodyGeneralizationLedger.raw_other_owner artifact checked position body member excluded occurs
  exact (distinct ⟨owner.binder, owner.initializer⟩
    (LocalSchemeTemplateOwner.binding_mem present) different) q quantified ownerQuantified

/-- All operational premises of the finalizer barrier come from this same
accepted declaration and its entering invariant. -/
theorem statement_from_private_quantifiers
    {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    (privateQuantifiers : ∀ q ∈ occurrence.receipt.binding.1.scheme.quantified,
      q ∉ GeneralizationBlockedVariablesExcept target
        (localSchemeTemplateIds occurrence.initializerBinding.binder)) :
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds occurrence.initializerBinding.binder) := by
  have aligned := ((boundary.invariant.active.allocateStatementId rfl).inferExprFuel
    occurrence.receipt.child).aligned
  have wellFormed := (Detail.inferExprFuel_direct_progress occurrence.receipt.child).wellFormed
    boundary.operational.requirements
  have rows : occurrence.receipt.ready.requirements ⊆ selected.body.returned.requirements := by
    have same : occurrence.result.state.requirements = occurrence.receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) occurrence.receipt.completed
    simpa only [same] using boundary.requirements
  exact GeneralizedBarrierTransport.barrier_from_finalizer selected.body.resources
    wellFormed aligned
    (boundary.operational.origins.congr_localBinders occurrence.receipt.ready_binders)
    rows occurrence.extension boundary.invariant.solvedRequirementsEq occurrence.retained
    rfl rfl privateQuantifiers

/-- The lexical exclusion uses the event made from this exact receipt; its
ready state is definitionally the one in the boundary's actual child call. -/
theorem statement_locals
    (checked : checkProgram raw fuel = .ok compiled.program)
    {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    {entryNext : Nat}
    (lifetime : GeneralizationLifetime occurrence.lifetimeEvent
      entryNext selected.body.body.state []) :
    ∀ q ∈ occurrence.receipt.binding.1.scheme.quantified,
      q ∉ target.locals.flatMap (fun entry => entry.2.freeVariables) := by
  exact SourceBodyGeneralizationLocalPrivacy.local_variables selected checked
    occurrence.lifetimeEvent lifetime
    (SourceBodyGeneralizationLocalPrivacy.statement_ready_live checked occurrence boundary)
    (((boundary.invariant.active.allocateStatementId rfl).inferExprFuel occurrence.receipt.child).aligned)

/-- Header finalization uses the same actual row cutoff, inference state and
retained binder as the accepted header item. -/
theorem header_from_private_quantifiers
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final))
    (privateQuantifiers : ∀ q ∈ receipt.binding.1.scheme.quantified,
      q ∉ GeneralizationBlockedVariablesExcept target
        (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))) :
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution)) := by
  have aligned := (boundary.invariant.active.inferExprFuel receipt.child).aligned
  have wellFormed := (Detail.inferExprFuel_direct_progress receipt.child).wellFormed
    boundary.operational.requirements
  have rows : receipt.ready.requirements ⊆ selected.body.returned.requirements := by
    have same : final.requirements = receipt.ready.requirements :=
      congrArg (fun result : ForItemForm × State => result.2.requirements) receipt.completed
    simpa only [same] using boundary.requirements
  have extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    have atResult := boundary.extension
    rwa [receipt.inference_eq] at atResult
  have retained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
    apply (boundary.bindingsRetained ⟨receipt.binding.1, .expression receipt.value.id⟩ ?_).1
    have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [congrArg forItemInitializedLetBindings itemEq]
    exact List.mem_singleton_self _
  exact GeneralizedBarrierTransport.barrier_from_finalizer selected.body.resources
    wellFormed aligned (boundary.operational.origins.congr_localBinders receipt.ready_binders)
    rows extension boundary.invariant.solvedRequirementsEq retained rfl rfl privateQuantifiers

/-- The header event also uses this receipt's ready state, including when it
is returned by the actual traversal with independent proof fields. -/
theorem header_locals
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final))
    (ready : receipt.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    {entryNext : Nat}
    (lifetime : GeneralizationLifetime
      (HeaderLifetime.event receipt ready extension retained binderRetained)
      entryNext selected.body.body.state []) :
    ∀ q ∈ receipt.binding.1.scheme.quantified,
      q ∉ target.locals.flatMap (fun entry => entry.2.freeVariables) := by
  exact SourceBodyGeneralizationLocalPrivacy.local_variables selected checked
    (HeaderLifetime.event receipt ready extension retained binderRetained) lifetime
    (SourceBodyGeneralizationLocalPrivacy.header_ready_live checked boundary receipt)
    (boundary.invariant.active.inferExprFuel receipt.child).aligned

/-- Compose the concrete statement's lifetime with actual cache ownership and
the complete retained-owner separation supplied by the execution traversal. -/
theorem statement_of_lifetime
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (body : BodySelection compiled named.specialized fuel)
    {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence body source)
    {expectedReturn : Ty} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context}
    (boundary : StatementBoundary body (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    {entryNext : Nat}
    (lifetime : GeneralizationLifetime occurrence.lifetimeEvent entryNext body.body.body.state [])
    (distinct : ∀ other ∈ initializedLetBindings (evidenceSource body),
      other.binder ≠ occurrence.receipt.binding.1 →
      ∀ q ∈ occurrence.receipt.binding.1.scheme.quantified, q ∉ other.binder.scheme.quantified) :
    GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      body.body.finalized.substitution target
      (localSchemeTemplateIds occurrence.initializerBinding.binder) := by
  apply statement_from_private_quantifiers occurrence boundary
  intro q quantified blocked
  rcases List.mem_append.mp blocked with contextual | ledger
  · rcases List.mem_append.mp contextual with variables | locals
    · obtain ⟨other, present, different, ownerQuantified⟩ :=
        SourceBodyGeneralizationFrameOrigins.statement occurrence boundary variables
      exact (distinct other present different) q quantified ownerQuantified
    · exact statement_locals checked occurrence boundary lifetime q quantified locals
  · exact ledger_variables artifact checked position body distinct
      boundary.invariant.solvedRequirementsEq q quantified ledger

/-- Header events use the identical final-ledger and local-scheme argument,
with their actual header containment relation for the active type variables. -/
theorem header_of_lifetime
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (body : BodySelection compiled named.specialized fuel)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary body (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final))
    (ready : receipt.ready.InferenceReady)
    (extension : body.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource body))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource body).initializedLetBinders)
    {entryNext : Nat}
    (lifetime : GeneralizationLifetime
      (HeaderLifetime.event receipt ready extension retained binderRetained)
      entryNext body.body.body.state [])
    (distinct : ∀ other ∈ initializedLetBindings (evidenceSource body),
      other.binder ≠ receipt.binding.1 →
      ∀ q ∈ receipt.binding.1.scheme.quantified, q ∉ other.binder.scheme.quantified) :
    GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) body.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution body.body.finalized.substitution)) := by
  apply header_from_private_quantifiers boundary receipt
  intro q quantified blocked
  rcases List.mem_append.mp blocked with contextual | ledger
  · rcases List.mem_append.mp contextual with variables | locals
    · obtain ⟨other, present, different, ownerQuantified⟩ :=
        SourceBodyGeneralizationFrameOrigins.header boundary receipt variables
      exact (distinct other present different) q quantified ownerQuantified
    · exact header_locals checked boundary receipt ready extension retained binderRetained lifetime
        q quantified locals
  · exact ledger_variables artifact checked position body distinct
      boundary.invariant.solvedRequirementsEq q quantified ledger

end Solcore.SourceSemantics.SourceBodyGeneralizationBarrierConnection
