import Solcore.SourceSemantics.Internal.Privacy.LifetimeContinuations
import Solcore.SourceSemantics.Internal.Compiled.InitializerPrivacy
import Solcore.SourceSemantics.Internal.Compiled.Expressions
import Solcore.SourceSemantics.Internal.Prepared.TemplateScope
import Solcore.SourceSemantics.Internal.Prepared.CallEdges
import Solcore.SourceSemantics.Internal.Compiled.LifetimeSeeds
import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Compiled.ActualEntries
import Solcore.SourceSemantics.Internal.Compiled.OperationalState
import Solcore.SourceSemantics.Internal.Compiled.BodyAssembly
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation

/-!
# Discharging initializer barriers

The steps that discharge the remaining premise of body assembly: reachable initializer lifetimes,
separation of specialized quantifiers and local domains, the nested privacy of initializers, and the
connection from the semantic boundary to the forward generalization condition.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
/-! An actual generalization lifetime transports the entering lexical schemes
through the enclosing computation and its real finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization
open SourceCompiledGeneralizedSoundness

private theorem scheme_variable_origin (substitution : Substitution) (scheme : Scheme)
    {q : TypeVarId} (occurs : q ∈ (scheme.apply substitution).freeVariables) :
    ∃ source, source ∈ scheme.freeVariables ∧
      q ∈ (substitution.apply (.variable source)).freeVariables := by
  obtain ⟨body, outside⟩ := List.mem_filter.mp occurs
  have notQuantified : q ∉ scheme.quantified := by
    intro member
    simp only [Scheme.apply, member, decide_true, Bool.not_true] at outside
    contradiction
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin
    (substitution.without scheme.quantified) scheme.body q body
  have sourceOutside : source ∉ scheme.quantified := by
    intro member
    have same : q = source := by
      simpa only [Substitution.apply, Substitution.lookup?_without_of_mem substitution member,
        Option.getD_none, Ty.freeVariables, List.mem_singleton] using image
    exact notQuantified (same ▸ member)
  refine ⟨source, List.mem_filter.mpr ⟨sourceMember, ?_⟩, ?_⟩
  · simp [sourceOutside]
  · simpa only [Substitution.apply,
      FlexibleSubstitution.Substitution.lookup?_without_of_not_mem substitution sourceOutside] using image

/-- The final local-variable exclusion consumes the actual lifetime's
transport, including after the original lexical scope has been restored. -/
theorem local_variables {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {binder : TypedBinder} {initializer : ExpressionId}
    (event : RetainedGeneralization (SourceCompiledGeneralizedSoundness.evidenceSource selected)
      selected.body.finalized.substitution binder initializer)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext selected.body.body.state outputs)
    (live : LiveBindersSafe binder.scheme.quantified event.readyState)
    {target : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned event.readyState selected.body.finalized.substitution target) :
    ∀ q ∈ binder.scheme.quantified,
      q ∉ target.locals.flatMap (fun entry => entry.2.freeVariables) := by
  intro q quantified occurs
  obtain ⟨entry, member, free⟩ := List.mem_flatMap.mp occurs
  have originalMember := aligned.locals_perm.mem_iff.mpr member
  obtain ⟨older, olderMember, same⟩ := List.mem_map.mp originalMember
  subst entry
  have free : q ∈ (older.scheme.apply selected.body.finalized.substitution).freeVariables := by
    simpa only [FlexibleSubstitution.applyTypedBinder_scheme] using free
  obtain ⟨metavariable, freeVariable, image⟩ := scheme_variable_origin
    selected.body.finalized.substitution older.scheme free
  have readySafe := (live older olderMember).body metavariable freeVariable
  have finalSafe := selected.finishPrivacy checked binder.scheme.quantified (.variable metavariable)
    (lifetime.transport _ readySafe)
  exact finalSafe q image quantified

/-- The actual statement boundary derives ready-state lexical privacy from
the executable generalizer and retained finalizer checks. -/
theorem statement_ready_live {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}
    (checked : checkProgram raw fuel = .ok compiled.program)
    {source : Syntax.Statement} (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target) :
    LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready := by
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt boundary.operational.backed boundary.invariant.ready
    boundary.operational.requirements (boundary.scope.formation checked)
    (boundary.scope.functionsCanonical checked)
  exact generalized_live_from_finalizer selected.body.resources
    (boundary.operational.origins.congr_localBinders occurrence.receipt.ready_binders)
    occurrence.extension occurrence.retained rfl templates

/-- The same derivation uses the literal header binder retained by the actual
for-item boundary. -/
theorem header_ready_live {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final)) :
    LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready := by
  have templates := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.templates_before
    receipt boundary.operational.backed boundary.invariant.ready boundary.operational.requirements
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
  have extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    have atResult := boundary.extension
    rwa [receipt.inference_eq] at atResult
  have retained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
    apply (boundary.bindingsRetained ⟨receipt.binding.1, .expression receipt.value.id⟩ ?_).1
    have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [congrArg forItemInitializedLetBindings itemEq]
    exact List.mem_singleton_self _
  exact generalized_live_from_finalizer selected.body.resources
    (boundary.operational.origins.congr_localBinders receipt.ready_binders)
    extension retained rfl templates

end Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyGeneralizationBarrierConnection
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBodyReadCutoff
/-! The actual selected body has an empty initial node table, so the relative
read bound starts without any earlier-read premise. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem body_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    LocalReadCutoff selected.body.body.state := by
  exact CallIndex.localReadCutoff selected.inferenceCall_accepted
    (selected.inferenceCall_inputs checked) (State.initial_localBindersBelowNextLocal _ _ _)
    (by intro id impossible; cases impossible)
    (by intro node impossible; cases impossible)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerLambdaResume
/-! An initializer inside a lambda keeps its quantifiers private through the
actual return unification, saved scope restoration and final expression fit.
The enclosing parameter and return types were allocated before the initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables Detail

private theorem parameter_binders_subset
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result) :
    initial.localBinders ⊆ result.2.2.localBinders := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    exact List.Subset.refl _
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))

private theorem prefix_binders
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final) :
    final.localBinders = initial.localBinders := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ fresh =>
    rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
    rfl
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact congrArg LexicalScope.binders (unify_preserves_lexicalScope unified)

theorem InitializedBlockResume.finish_lambda
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel childFuel : Nat} {selected : Selected compiled row fuel}
    {context : SourceInference.Context} {expression : Syntax.Expr} {source : Syntax.Statement}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {prefixState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {final : InferredExpression × State}
    (resume : InitializedBlockResume selected {context with loopDepth := 0}
      resultType prefixState bodyResult source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (parametersRun : bindLambdaParameters context parameters.elements 0 []
      initial.allocateExpressionId.2 = .ok (boundParameters, parameterTypes, parameterState))
    (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType prefixState)
    (bodyRun : inferStatementsFuel childFuel {context with loopDepth := 0}
      body.value resultType prefixState = .ok bodyResult)
    (unified : unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restoredEq : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context expression initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok final) :
    SafeTransport resume.actual.receipt.binding.1.scheme.quantified resume.actual.receipt.ready final.2 ∧
      Safe resume.actual.receipt.binding.1.scheme.quantified final.2 final.1.type ∧
      LiveBindersSafe resume.actual.receipt.binding.1.scheme.quantified final.2 ∧
      ∀ requirement ∈ final.2.requirements, requirement ∉ resume.actual.receipt.ready.requirements →
        PredicateSafe resume.actual.receipt.binding.1.scheme.quantified final.2 requirement.predicate := by
  let protectedVars := resume.actual.receipt.binding.1.scheme.quantified
  let allocated := initial.allocateExpressionId.2
  have allocation : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have parametersProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parametersProperties.2.2
  have initialToParameter := allocation.trans parametersProperties.1
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parametersProperties.2.1
    parameterBelow (fun type member => (expectedBelow type member).weaken initialToParameter.next_le)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 formation canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress resume.ready.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady resume.ready bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedPrivacy : SafeTransport protectedVars bodyResult.state unifiedState :=
    ProtectedVariables.unify resume.resultSafe resume.expectedSafe unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parametersProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoredReady : restored.InferenceReady := restoredProperties.2
  have restorePrivacy : SafeTransport protectedVars unifiedState restored := .of_substitution_eq rfl
  have restoreProgress : unifiedState.InferenceProgress restored := .restoreLexicalScope _ _ unifiedReady.solved
  have bodyToRestored := unifiedPrivacy.trans restorePrivacy
  have parametersAtBody := resume.olderSafe (Ty.productMany parameterTypes)
    (parameterBelow.weaken prefixProperties.1.next_le)
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have expectedAtBody : ∀ type ∈ expected, Safe protectedVars bodyResult.state type := by
    intro type member
    exact resume.olderSafe type ((expectedBelow type member).weaken initialToPrefix.next_le)
  have savedSubset : allocated.localBinders ⊆ bodyResult.state.localBinders := by
    apply (parameter_binders_subset parametersRun).trans
    apply List.Subset.trans (l₂ := prefixState.localBinders)
    · rw [prefix_binders prefixFacts]
      exact List.Subset.refl _
    · exact inferStatementsFuel_binders_subset bodyRun
  have restoredLive : LiveBindersSafe protectedVars restored := by
    intro binder member
    have before := resume.live binder (savedSubset member)
    exact before.transport bodyToRestored
  have resultToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have initialToRestored := allocation.trans restoredProperties.1
  have recordPrivacy := recordExpressionWithExpected_private catalog restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le)
    ((safe_function_iff _ _ _ _).mpr
      ⟨safe_resolved restoredReady (bodyToRestored _ parametersAtBody),
        safe_resolved restoredReady (bodyToRestored _ resume.expectedSafe)⟩)
    (fun type member => bodyToRestored type (expectedAtBody type member)) restoredLive recorded
  refine ⟨resume.transport.trans (bodyToRestored.trans recordPrivacy.1),
    recordPrivacy.2.1,recordPrivacy.2.2.1,?_⟩
  have bodyRows : ∀ requirement ∈ restored.requirements,
      requirement ∉ resume.actual.receipt.ready.requirements →
        PredicateSafe protectedVars restored requirement.predicate := by
    intro requirement member fresh type typeMember
    apply bodyToRestored
    apply resume.newRows requirement _ fresh type typeMember
    change requirement ∈ unifiedState.requirements at member
    simpa only [unify_requirements_eq unified] using member
  exact new_requirements_trans bodyRows recordPrivacy.2.2.2 recordPrivacy.1

private theorem parameter_owner
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result) :
    result.2.2.owner = initial.owner := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    rfl
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        have tailOwner := ih _ _ _ (by assumption)
        exact tailOwner.trans rfl
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          have tailOwner := ih _ _ _ (by assumption)
        exact tailOwner.trans rfl

private theorem prefix_owner
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final) :
    final.owner = initial.owner := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ fresh =>
    rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
    rfl
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact congrArg State.Header.owner (unify_state_header unified)

/-- Follow the actual lambda computation to a chosen initialized declaration
and back to the enclosing expression's actual result. No lambda body typing
or initializer barrier is needed. -/
theorem lambda_initializer_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {context : SourceInference.Context} {expression : Syntax.Expr}
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    {expected : Option Ty} {initial : State} {final : InferredExpression × State}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection context)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected.toBodySelection))
    (owner : initial.owner = (evidenceSource selected.toBodySelection).owner)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (retained : final.2.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends final.2.inference.substitution)
    (form : expression.value = .lambda keyword parameters annotation body)
    (accepted : inferExprFuel (childFuel + 1) context expression expected initial = .ok final)
    (position : body.value[index]? = some statement)
    {name : Syntax.Identifier} {localAnnotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (statementForm : statement.value = .letDecl name localAnnotation (some initializer)) :
    ∃ actual : InitializerOccurrence selected statement,
      actual.inferenceContext = {context with loopDepth := 0} ∧
      SafeTransport actual.receipt.binding.1.scheme.quantified actual.receipt.ready final.2 ∧
      Safe actual.receipt.binding.1.scheme.quantified final.2 final.1.type ∧
      LiveBindersSafe actual.receipt.binding.1.scheme.quantified final.2 ∧
      (∀ q ∈ actual.receipt.binding.1.scheme.quantified,
        q.index < final.2.inference.next) ∧
      (∀ type, type.VariablesBelow initial.inference.next →
        Safe actual.receipt.binding.1.scheme.quantified final.2 type) ∧
      ∀ requirement ∈ final.2.requirements, requirement ∉ actual.receipt.ready.requirements →
        PredicateSafe actual.receipt.binding.1.scheme.quantified final.2 requirement.predicate := by
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType, prefixState,
    bodyResult, unifiedState, restoredState, parametersRun, prefixFacts, bodyRun,
    unified, restoredEq, recorded⟩ :=
    inferExprFuel_success_lambda_facts form (Prod.eta initial.allocateExpressionId).symm accepted
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  let allocated := initial.allocateExpressionId.2
  have allocation : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have parameterProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parameterProperties.2.2
  have initialToParameter := allocation.trans parameterProperties.1
  have expectedAtParameter := fun type member => (expectedBelow type member).weaken initialToParameter.next_le
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parameterProperties.2.1
    parameterBelow expectedAtParameter
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 formation canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have restoreProgress : unifiedState.InferenceProgress restoredState := by
    rw [restoredEq]
    exact .restoreLexicalScope _ _ unifiedReady.solved
  have throughBody := parameterProperties.1.trans
    (prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress))
  have restoredProperties : allocated.InferenceProgress restoredState ∧ restoredState.InferenceReady := by
    rw [restoredEq]
    exact State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId throughBody
  have parameterToRestored := prefixProperties.1.trans
    (bodyProperties.1.trans (unifiedProgress.trans restoreProgress))
  have prefixToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have recordProperties := recordExpressionWithExpected_inferenceProperties restoredProperties.2
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parameterToRestored.resolve_variablesBelow parameterBelow,
        prefixToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken (allocation.trans restoredProperties.1).next_le)
    recorded
  have bodyExtension := extension.trans
    ((unifiedProgress.trans restoreProgress).trans recordProperties.1).substitution_extends
  have bodyNodes : bodyResult.state.nodes <+: final.2.nodes := by
    have nodes := recordExpressionWithExpected_success_nodesPrefix recorded
    rw [restoredEq, State.restoreLexicalScope_nodes, (unify_occurrenceState_eq unified).1] at nodes
    exact nodes
  have parameterScope := bindLambdaParameters_operational ready.allocateExpressionId
    operational.allocateExpressionId parametersRun
  have parameterPrivacy : ∀ binder ∈ parameterState.localBinders,
      Safe binder.scheme.quantified parameterState (Ty.productMany parameterTypes) ∧
      (∀ type ∈ expected, Safe binder.scheme.quantified parameterState type) := by
    intro binder member
    rcases bindLambdaParameters_quantified_origin parametersRun binder member with old | mono
    · have privacy := bindLambdaParameters_private ready.allocateExpressionId
        (operational.quantifiersBelow binder old) (operational.allocateExpressionId.privacy binder old) parametersRun
      exact ⟨safe_productMany _ _ _ privacy.2.1,
        fun type present => privacy.1 type (expectedSafe binder old type present)⟩
    · rw [mono]
      simp [Safe, Avoids]
  have prefixScope := lambdaPrefixFacts_operational parameterProperties.2.1
    parameterScope parameterBelow
    (fun binder member => (parameterPrivacy binder member).1) expectedAtParameter
    (fun binder member => (parameterPrivacy binder member).2) prefixFacts
  have prefixNodes := lambdaPrefixFacts_nodesBelowNextOccurrence prefixFacts
    ((bindLambdaParameters_occurrenceBoundExtends parametersRun).nodesBelowNextOccurrence
      (State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodesBelow))
  have prefixOwner := (prefix_owner prefixFacts).trans ((parameter_owner parametersRun).trans owner)
  obtain ⟨resume⟩ := initialized_block_resume checked (scope.withLoopDepth 0)
    prefixProperties.2.1 prefixNodes ⟨prefixScope.1,prefixScope.2,prefixOwner⟩
    prefixProperties.2.2 (bodyNodes.trans retained) bodyExtension bodyRun position statementForm
  have finished := resume.finish_lambda ready (scope.catalog checked) formation canonical expectedBelow
    parametersRun prefixFacts bodyRun unified restoredEq recorded
  exact ⟨resume.actual,resume.context,finished.1,finished.2.1,finished.2.2.1,
    fun q member => Nat.lt_of_lt_of_le (resume.bound q member)
      (((unifiedProgress.trans restoreProgress).trans recordProperties.1).next_le),
    fun type below => finished.1 type (resume.olderAtReady type (below.weaken initialToPrefix.next_le)),
    finished.2.2.2⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledSpecializedQuantifierSeparation
/-! Actual flexible finalization and rigid specialization preserve the owner
and quantified variables of every initialized local in a cached body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

/-- A specialized initialized binding is the actual finalization and parameter
application of an initialized binding in the same inferred body. -/
theorem BodySelection.specialized_initialized_origin
    (selected : BodySelection compiled named.specialized fuel)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings named.specialized.function.typedBody) :
    ∃ original ∈ initializedLetBindings (evidenceSource selected),
      current = StructuralSubstitution.applyInitializedLetBinding named.specialized.parameterSubstitution
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original) ∧
      current.binder.scheme.quantified = original.binder.scheme.quantified ∧
      current.initializer = original.initializer := by
  rw [selected.source, selected.body.resources.source_eq] at member
  change current ∈ initializedLetBindings
    (StructuralSubstitution.applyTypedSource named.specialized.parameterSubstitution
      ((evidenceSource selected).applySubstitution selected.body.finalized.substitution)) at member
  rw [StructuralSubstitution.initializedLetBindings_applyTypedSource,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at member
  obtain ⟨finalized, finalMember, same⟩ := List.mem_map.mp member
  obtain ⟨original, originalMember, finalSame⟩ := List.mem_map.mp finalMember
  subst finalized
  subst current
  exact ⟨original, originalMember, rfl, rfl, rfl⟩

/-- Distinct owners in the authentic cached specialized source have disjoint
quantifiers. This uses the actual checker result and cache position. -/
theorem BodySelection.specialized_initialized_quantifiers_disjoint
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings named.specialized.function.typedBody) :
    ∀ other ∈ initializedLetBindings named.specialized.function.typedBody,
      other.binder ≠ current.binder →
      ∀ q ∈ current.binder.scheme.quantified, q ∉ other.binder.scheme.quantified := by
  obtain ⟨left, leftMember, leftEq, leftQuantified, _⟩ :=
    selected.specialized_initialized_origin member
  intro other otherMember different
  obtain ⟨right, rightMember, rightEq, rightQuantified, _⟩ :=
    selected.specialized_initialized_origin otherMember
  have rawDifferent : right.binder ≠ left.binder := by
    intro same
    apply different
    rw [rightEq, leftEq]
    change SourceSpecialization.applyBinder _ (right.binder.applySubstitution _) =
      SourceSpecialization.applyBinder _ (left.binder.applySubstitution _)
    rw [same]
  simpa only [leftQuantified, rightQuantified] using
    selected.initialized_quantifiers_disjoint artifact checked position leftMember
      right rightMember rawDifferent

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalDomainSeparation
/-! Actual discovery order and the same cached body's quantified owners
exclude earlier owners from a contextual instance's substitution domain. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceCompiledGeneralizedSoundness
open CoreLowering.GeneralizedLocalLexicalOrigin

private theorem initialized_binding_of_lexical_origin
    {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance) :
    ({ binder := localInstance.binding.binder,
       initializer := .expression localInstance.binding.initializer } : InitializedLetBinding) ∈
      initializedLetBindings source := by
  obtain ⟨statement, present, form⟩ :=
    localLambdaBindings_statement_origin origin.binding_member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, present, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

/-- The order used by the domain induction is supplied by the actual inferred
initializer and the exact reads in its direct lexical body. -/
theorem contextual_read_order
    (selected : BodySelection compiled named.specialized fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    ContextualReadOrder named.specialized.function.typedBody := by
  intro parent origin nodes accepted expression member name target form
  exact selected.local_lambda_read_binder_lt checked origin accepted member form

/-- Every key of the actual cumulative substitution belongs to an owner at
or after this instance. A distinct, earlier initialized owner cannot contribute
that same quantified variable. -/
theorem local_domain_excludes_earlier
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin
      named.specialized.function.typedBody localInstance)
    {earlier : InitializedLetBinding}
    (earlierMember : earlier ∈ initializedLetBindings named.specialized.function.typedBody)
    (before : earlier.binder.id.binderIndex <
      localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ localInstance.substitution.domain := by
  intro key
  obtain ⟨owner, ownerOrigin, ownerQuantified, afterInstance⟩ :=
    domain_owner_at_or_after origin (selected.contextual_read_order checked) key
  let ownerBinding : InitializedLetBinding :=
    { binder := owner.binding.binder, initializer := .expression owner.binding.initializer }
  have ownerMember : ownerBinding ∈
      initializedLetBindings named.specialized.function.typedBody :=
    initialized_binding_of_lexical_origin ownerOrigin
  have different : ownerBinding.binder ≠ earlier.binder := by
    intro same
    have sameIndex := congrArg (fun binder : TypedBinder => binder.id.binderIndex) same
    change owner.binding.binder.id.binderIndex = earlier.binder.id.binderIndex at sameIndex
    have ordered := Nat.lt_of_lt_of_le before afterInstance
    omega
  exact selected.specialized_initialized_quantifiers_disjoint artifact checked position
    earlierMember ownerBinding ownerMember different q quantified ownerQuantified

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedInitializerResume
/-! A genuine enclosing initializer receipt supplies the lambda call and its
retention. The inner declaration is selected from that lambda's real body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

structure NestedInitializerResume
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : Selected compiled row fuel}
    {outerSource : Syntax.Statement} (outer : InitializerOccurrence selected outerSource)
    (innerSource : Syntax.Statement) where
  inner : InitializerOccurrence selected innerSource
  context : inner.inferenceContext = {outer.inferenceContext with loopDepth := 0}
  transport : SafeTransport inner.receipt.binding.1.scheme.quantified inner.receipt.ready outer.receipt.ready
  valueSafe : Safe inner.receipt.binding.1.scheme.quantified outer.receipt.ready outer.receipt.value.type
  live : LiveBindersSafe inner.receipt.binding.1.scheme.quantified outer.receipt.ready
  bound : ∀ q ∈ inner.receipt.binding.1.scheme.quantified, q.index < outer.receipt.ready.inference.next
  olderSafe : ∀ type, type.VariablesBelow outer.entry.inference.next →
    Safe inner.receipt.binding.1.scheme.quantified outer.receipt.ready type
  newRows : ∀ requirement ∈ outer.receipt.ready.requirements,
    requirement ∉ inner.receipt.ready.requirements →
    PredicateSafe inner.receipt.binding.1.scheme.quantified outer.receipt.ready requirement.predicate

theorem InitializerOccurrence.lambdaResume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {outerSource innerSource : Syntax.Statement}
    (outer : InitializerOccurrence selected outerSource)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection outer.inferenceContext)
    (ready : outer.entry.InferenceReady) (nodesBelow : outer.entry.NodesBelowNextOccurrence)
    (operational : GeneralizedActualStateInvariant outer.entry (evidenceSource selected.toBodySelection))
    (owner : outer.entry.owner = (evidenceSource selected.toBodySelection).owner)
    (retained : outer.result.state.nodes <+: selected.body.returned.nodes)
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    (form : outer.receipt.initializer.value = .lambda keyword parameters annotation body)
    {index : Nat} (position : body.value[index]? = some innerSource)
    {name : Syntax.Identifier} {localAnnotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (innerForm : innerSource.value = .letDecl name localAnnotation (some initializer)) :
    Nonempty (NestedInitializerResume outer innerSource) := by
  have child := outer.receipt.child
  cases fuelEq : outer.childFuel with
  | zero =>
    conv at child => lhs; arg 1; rw [fuelEq]
    simp [Detail.inferExprFuel] at child
  | succ childFuel =>
    conv at child => lhs; arg 1; rw [fuelEq]
    have readyRetained : outer.receipt.ready.nodes <+: selected.body.returned.nodes := by
      apply List.IsPrefix.trans (l₂ := outer.result.state.nodes) _ retained
      rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) outer.receipt.completed]
      exact List.prefix_append _ _
    obtain ⟨inner,context,transport,valueSafe,live,bound,olderSafe,newRows⟩ :=
      lambda_initializer_resume (selected := selected)
        (final := (outer.receipt.value, outer.receipt.ready)) checked scope ready.allocateStatementId
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence _ nodesBelow)
        operational.allocateStatementId owner
        (outer.receipt.annotationAccepted.variablesBelow _)
        (fun _ _ type member => safe_closed _ _
          (outer.receipt.annotationAccepted.variablesBelow 0 type member))
        readyRetained outer.extension form child position innerForm
    exact ⟨⟨inner,context,transport,valueSafe,live,bound,olderSafe,newRows⟩⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledSelectedStatementResume
/-! The same selected checker invocation supplies every entry condition for
a statement position and its exact continuation through the whole body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

theorem Selected.statementResume {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    Nonempty (StatementPrivacyResume (checkingContext selected.toBodySelection) source
      (Ty.productMany selected.signature.returnTypes)
      (initial selected.signature selected.body.declaration) selected.body.body
      (ResumeEntryInvariant selected (Ty.productMany selected.signature.returnTypes))) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow 0)
  have bodyOwner := Detail.inferStatementsFuel_preserves_owner selected.body.inferred
  have returnOwner := congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)
  have owner : (initial selected.signature selected.body.declaration).owner =
      (evidenceSource selected.toBodySelection).owner := bodyOwner.symm.trans returnOwner.symm
  apply selected_statement_privacy_resume checked (.refl selected.toBodySelection) progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) _ progress.returnBelow
    (by rw [selected.body.returned_nodes]; exact List.prefix_refl _)
    progress.final_substitution selected.body.inferred position
  refine ⟨?_,fun binder member => safe_closed _ _ closed,owner⟩
  apply GeneralizedActualStateInvariant.initial
  intro entry present
  obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp present
  rfl

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedInitializerFinalPrivacy
/-! A selected outer declaration, a declaration inside its actual lambda
initializer, every remaining statement and the actual finalizer form one
privacy continuation. The outer binder's templates come from compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

structure NestedInitializerFinalPrivacy
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (outerSource innerSource : Syntax.Statement) where
  outer : InitializerOccurrence selected outerSource
  nested : NestedInitializerResume outer innerSource
  final : ∀ type, Safe nested.inner.receipt.binding.1.scheme.quantified
    nested.inner.receipt.ready type →
    Avoids nested.inner.receipt.binding.1.scheme.quantified
      (selected.body.finalized.substitution.apply type)
  outerValue : Avoids nested.inner.receipt.binding.1.scheme.quantified
    (selected.body.finalized.substitution.apply outer.receipt.value.type)
  olderTypes : ∀ type, type.VariablesBelow outer.entry.inference.next →
    Avoids nested.inner.receipt.binding.1.scheme.quantified
      (selected.body.finalized.substitution.apply type)
  disjoint : ∀ q ∈ nested.inner.receipt.binding.1.scheme.quantified,
    q ∉ outer.receipt.binding.1.scheme.quantified
  newRows : ∀ requirement ∈ selected.body.body.state.requirements,
    requirement ∉ nested.inner.receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids nested.inner.receipt.binding.1.scheme.quantified
        (selected.body.finalized.substitution.apply type)

theorem Selected.nestedLambdaPrivacy
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations)
    (selected : Selected compiled row options.checkingFuel)
    {outerIndex innerIndex : Nat} {outerSource innerSource : Syntax.Statement}
    (outerPosition : selected.signature.source.value.body.value[outerIndex]? = some outerSource)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (outerForm : outerSource.value = .letDecl name annotation (some initializer))
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    (lambdaForm : initializer.value = .lambda keyword parameters returnAnnotation body)
    (innerPosition : body.value[innerIndex]? = some innerSource)
    {innerName : Syntax.Identifier} {innerAnnotation : Option Syntax.TypeExpr}
    {innerInitializer : Syntax.Expr}
    (innerForm : innerSource.value = .letDecl innerName innerAnnotation (some innerInitializer)) :
    Nonempty (NestedInitializerFinalPrivacy selected outerSource innerSource) := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  let scope : CheckingScope selected.toBodySelection (checkingContext selected.toBodySelection) := .refl selected.toBodySelection
  obtain ⟨resume⟩ := selected.statementResume checked outerPosition
  obtain ⟨childFuel,receipt,_,_⟩ := resume.toOccurrence.initialized outerForm
    (scope.formation checked) (scope.functionsCanonical checked)
  have retained : resume.result.state.nodes <+: selected.body.returned.nodes := by
    rw [selected.body.returned_nodes]
    exact resume.retained
  let outer := InitializerOccurrence.ofReceipt checked scope receipt resume.ready
    resume.entryInvariant.1 (retained.subset receipt.recorded)
    (progress.final_substitution.trans resume.continuation.substitution_extends)
  have initializerEq : receipt.initializer = initializer := by
    have same := receipt.form.symm.trans outerForm
    simp only [Syntax.StatementValue.letDecl.injEq, Option.some.injEq] at same
    exact same.2.2
  have actualLambda : outer.receipt.initializer.value =
      .lambda keyword parameters returnAnnotation body := by
    change receipt.initializer.value = _
    rw [initializerEq]
    exact lambdaForm
  obtain ⟨nested⟩ := InitializerOccurrence.lambdaResume (selected := selected) outer checked scope resume.ready resume.entryNodesBelow
    resume.entryInvariant.1 resume.entryInvariant.2.2 retained actualLambda innerPosition innerForm
  have added := SourceCompiledNestedTemplatePrivacy.outer_binder_safe
    accepted member outer nested.inner nested.valueSafe
  have unchanged : SafeTransport nested.inner.receipt.binding.1.scheme.quantified
      receipt.ready resume.result.state :=
    .of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
  have live : LiveBindersSafe nested.inner.receipt.binding.1.scheme.quantified resume.result.state := by
    intro binder present
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (nested.live binder ?_) unchanged
      change binder ∈ receipt.ready.localBinders
      rw [receipt.ready_binders]
      exact old
  have bound : ∀ q ∈ nested.inner.receipt.binding.1.scheme.quantified,
      q.index < resume.result.state.inference.next := by
    intro q quantified
    rw [receipt.inference_eq]
    exact nested.bound q quantified
  have older : ∀ type, type.VariablesBelow resume.entry.inference.next →
      Safe nested.inner.receipt.binding.1.scheme.quantified resume.result.state type :=
    fun type below => unchanged type (nested.olderSafe type below)
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow 0)
  have resultSafe : Safe nested.inner.receipt.binding.1.scheme.quantified
      resume.result.state resume.result.type := by
    have resultType : resume.result.type = .unit :=
      congrArg Detail.StatementResult.type receipt.completed
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  have suffix := resume.resume _ bound live (safe_closed _ _ closed) resultSafe older
  refine ⟨{
    outer, nested
    final := fun type safe => selected.finishPrivacy checked _ type
      (suffix.1 type (unchanged type (nested.transport type safe)))
    outerValue := selected.finishPrivacy checked _ _ (suffix.1 _ (unchanged _ nested.valueSafe))
    olderTypes := fun type below => selected.finishPrivacy checked _ type (suffix.1 type (older type below))
    disjoint := ?_
    newRows := ?_ }⟩
  · intro q innerMember outerMember
    exact nested.valueSafe q (List.mem_filter.mp outerMember).1 innerMember
  · intro requirement present fresh type typeMember
    apply selected.finishPrivacy checked _ type
    by_cases earlier : requirement ∈ receipt.ready.requirements
    · exact suffix.1 type (unchanged type (nested.newRows requirement earlier fresh type typeMember))
    · apply suffix.2.2.2 requirement present _ type typeMember
      have same : resume.result.state.requirements = receipt.ready.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
      simpa only [same] using earlier

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedInitializerPublicPrivacy
/-! Public compilation supplies the same selected checker receipt used for
the complete nested initializer privacy continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

theorem compile_nested_lambda_privacy
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {outerIndex innerIndex : Nat} {outerSource innerSource : Syntax.Statement},
        selected.signature.source.value.body.value[outerIndex]? = some outerSource →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          outerSource.value = .letDecl name annotation (some initializer) →
          ∀ {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
            {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block},
            initializer.value = .lambda keyword parameters returnAnnotation body →
            body.value[innerIndex]? = some innerSource →
            ∀ {innerName : Syntax.Identifier} {innerAnnotation : Option Syntax.TypeExpr}
              {innerInitializer : Syntax.Expr},
              innerSource.value = .letDecl innerName innerAnnotation (some innerInitializer) →
              Nonempty (NestedInitializerFinalPrivacy selected outerSource innerSource) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro outerIndex innerIndex outerSource innerSource outerPosition name annotation initializer
    outerForm keyword parameters returnAnnotation body lambdaForm innerPosition
    innerName innerAnnotation innerInitializer innerForm
  exact selected.nestedLambdaPrivacy accepted member outerPosition outerForm lambdaForm innerPosition innerForm

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledReachableInitializerLifetime
/-! The semantic boundary's exact initializer event is the one whose actual
call path supplies the completed lifetime. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized fuel}

theorem BodyInitializerOccurrence.actual_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {source : Syntax.Statement} (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty}
    (here : selected.InferenceCall (.statement (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result)) :
    GeneralizationLifetime occurrence.lifetimeEvent selected.inferenceCall.initial.inference.next
      selected.body.body.state [] := by
  have retained : ({binder := occurrence.receipt.binding.1, initializer := .expression occurrence.receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) :=
    List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩
  obtain ⟨ready, extension, life⟩ := selected.statement_lifetime artifact checked position here occurrence.receipt retained
  exact life

theorem HeaderLifetime.actual_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (childFuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial result)
    (ready : receipt.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders) :
    GeneralizationLifetime (HeaderLifetime.event receipt ready extension retained binderRetained)
      selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  obtain ⟨actualReady, actualExtension, life⟩ := selected.header_lifetime artifact checked position here receipt retained
  exact life

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end
