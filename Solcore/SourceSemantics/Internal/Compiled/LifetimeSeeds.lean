import Solcore.SourceSemantics.Internal.Privacy.LifetimeContinuations
import Solcore.SourceSemantics.Internal.Prepared.TemplateScope
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.SourceSemantics.Internal.Privacy.ProtectedInference
import Solcore.SourceSemantics.Internal.Inference.StatementDispatch
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.SourceSemantics.Internal.Privacy.LifetimeMatches
import Solcore.SourceSemantics.Internal.Privacy.Active
import Solcore.SourceSemantics.Internal.Compiled.LoopHeaders

/-!
# Seeds of generalization lifetimes

Every lifetime starts at a real initialized declaration or header. Return privacy of statements and
sequences, and the resumption of a statement prefix, are stated against those seeds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizationLifetimeAllocation
/-! When an initializer contains an earlier generalization, the real outer
allocation must preserve its privacy as well. The completed compilation
supplies the outer binder's template predicate scope, including methods. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

namespace GeneralizationLifetime
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized fuel}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializer}
    {entryNext : Nat} {outputs : List Ty}

theorem finishStatementReceipt
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (outer : LocalLetRequirementTiming.Receipt childFuel context source initial result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (lifetime : GeneralizationLifetime event entryNext outer.ready outputs)
    (valuePresent : outer.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.binding.1.scheme.quantified := by
  have bodySafe := lifetime.values _ valuePresent
  have added := SourceBodyRetainedTemplatePrivacy.cached_statement_receipt artifact checked position
    outer ready extension retained binder event.binderRetained bodySafe
  have unchanged : SafeTransport binder.scheme.quantified outer.ready result.state :=
    .of_substitution_eq (congrArg InferState.substitution outer.inference_eq)
  have live : LiveBindersSafe binder.scheme.quantified result.state := by
    intro liveBinder present
    rw [outer.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (lifetime.live liveBinder ?_) unchanged
      rw [outer.ready_binders]
      exact old
  have resultType : result.type = .unit :=
    congrArg Detail.StatementResult.type outer.completed
  have requirements : result.state.requirements = outer.ready.requirements :=
    congrArg (fun output : Detail.StatementResult => output.state.requirements) outer.completed
  refine ⟨lifetime.append ?_ unchanged live ?_ ?_, ?_⟩
  · rw [outer.inference_eq]
    exact Nat.le_refl _
  · intro type present
    cases List.mem_singleton.mp present
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  · intro requirement present fresh
    exact False.elim (fresh (requirements ▸ present))
  · intro q innerQuantified outerQuantified
    exact bodySafe q (List.mem_filter.mp outerQuantified).1 innerQuantified

theorem finishStatement
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {source : Syntax.Statement}
    (outer : BodyInitializerOccurrence selected source)
    (lifetime : GeneralizationLifetime event entryNext outer.receipt.ready outputs)
    (valuePresent : outer.receipt.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext outer.result.state (outputs ++ [outer.result.type]) ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.receipt.binding.1.scheme.quantified :=
  finishStatementReceipt artifact checked position outer.receipt outer.ready
    outer.extension outer.retained lifetime valuePresent

theorem finishHeader
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (outer : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel context source initial result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (lifetime : GeneralizationLifetime event entryNext outer.ready outputs)
    (valuePresent : outer.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext result.2 outputs ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.binding.1.scheme.quantified := by
  have bodySafe := lifetime.values _ valuePresent
  have added := SourceBodyRetainedTemplatePrivacy.cached_header artifact checked position
    outer ready extension retained binder event.binderRetained bodySafe
  have unchanged : SafeTransport binder.scheme.quantified outer.ready result.2 :=
    .of_substitution_eq (congrArg InferState.substitution outer.inference_eq)
  have live : LiveBindersSafe binder.scheme.quantified result.2 := by
    intro liveBinder present
    rw [outer.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (lifetime.live liveBinder ?_) unchanged
      rw [outer.ready_binders]
      exact old
  have requirements : result.2.requirements = outer.ready.requirements :=
    congrArg (fun output : ForItemForm × State => output.2.requirements) outer.completed
  constructor
  · have finished := lifetime.append (newOutputs := []) ?_ unchanged live (by simp) ?_
    · simpa only [List.append_nil] using finished
    · rw [outer.inference_eq]
      exact Nat.le_refl _
    · intro requirement present fresh
      exact False.elim (fresh (requirements ▸ present))
  · intro q innerQuantified outerQuantified
    exact bodySafe q (List.mem_filter.mp outerQuantified).1 innerQuantified

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerQuantifierFreshness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem quantified_at_or_after_entry
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected)) :
    ∀ q ∈ occurrence.receipt.binding.1.scheme.quantified,
      occurrence.entry.inference.next ≤ q.index := by
  have inferred := occurrence.receipt.initializer_inference ready
    (scope.formation checked) (scope.functionsCanonical checked)
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt operational.backed ready operational.requirements
    (scope.formation checked) (scope.functionsCanonical checked)
  have live : LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready :=
    generalized_live_from_finalizer selected.body.resources
      (operational.origins.congr_localBinders occurrence.receipt.ready_binders)
      occurrence.extension occurrence.retained rfl templates
  intro q quantified
  by_cases later : occurrence.entry.inference.next ≤ q.index
  · exact later
  exfalso
  have earlier : q.index < occurrence.entry.inference.next := Nat.lt_of_not_ge later
  have occurs : q ∈ (occurrence.receipt.ready.resolve occurrence.receipt.value.type).freeVariables :=
    (List.mem_filter.mp quantified).1
  have outside := occurrence.ready.solved.apply_variables_outside_domain
    occurrence.receipt.value.type q occurs
  have fixed : occurrence.receipt.ready.inference.substitution.apply (.variable q) = .variable q := by
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ type, Safe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready type →
      Safe [q] occurrence.entry.allocateStatementId.2 type := by
    intro type privateType v present member
    have same : v = q := List.mem_singleton.mp member
    subst v
    exact privateType q (fixed_variable_occurs_at_final inferred.1.substitution_extends fixed present) quantified
  have entryLive : LiveBindersSafe [q] occurrence.entry.allocateStatementId.2 := by
    intro binder member
    have readyMember : binder ∈ occurrence.receipt.ready.localBinders := by
      rw [occurrence.receipt.ready_binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro v free
      exact backwards _ (prior.1 v free)
    · intro requirement present type typeMember v free unbound
      exact backwards _ (prior.2 requirement present type typeMember v free unbound)
  have actual := inferExprFuel_private [q] occurrence.childFuel occurrence.inferenceContext
    occurrence.receipt.initializer occurrence.receipt.expected occurrence.entry.allocateStatementId.2
    ready.allocateStatementId operational.requirements
    (by intro v member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    (occurrence.receipt.annotationAccepted.variablesBelow _)
    (fun type present => safe_closed _ _ (occurrence.receipt.annotationAccepted.variablesBelow 0 type present))
    _ occurrence.receipt.child
  exact actual.2.1 q occurs (List.mem_singleton_self _)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (quantified_at_or_after_entry)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerReturnPrivacy
/-! Newly generalized variables cannot enter a type already present at the
initializer entry. The actual child computation supplies fixedness of any
older variable which its live context avoids. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem generalized_type_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    {type : Ty} (typeBelow : type.VariablesBelow occurrence.entry.inference.next) :
    Safe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready type := by
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt operational.backed ready operational.requirements
    (scope.formation checked) (scope.functionsCanonical checked)
  have live : LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready :=
    generalized_live_from_finalizer selected.body.resources
      (operational.origins.congr_localBinders occurrence.receipt.ready_binders)
      occurrence.extension occurrence.retained rfl templates
  exact inferExprFuel_fresh_quantifiers_safe ready.allocateStatementId operational.requirements
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    (occurrence.receipt.annotationAccepted.variablesBelow 0) occurrence.receipt.child
    (occurrence.quantified_at_or_after_entry checked scope ready operational) live typeBelow

theorem return_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    {expectedReturn : Ty}
    (returnBelow : expectedReturn.VariablesBelow occurrence.entry.inference.next)
    (returnSafe : ∀ binder ∈ occurrence.entry.localBinders,
      Safe binder.scheme.quantified occurrence.entry expectedReturn) :
    ∀ binder ∈ occurrence.result.state.localBinders,
      Safe binder.scheme.quantified occurrence.result.state expectedReturn := by
  intro binder member
  rw [occurrence.receipt.result_binders] at member
  rcases List.mem_cons.mp member with rfl | old
  · have safe := occurrence.generalized_type_safe checked scope ready operational returnBelow
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe
  · have privacy := inferExprFuel_private binder.scheme.quantified occurrence.childFuel
      occurrence.inferenceContext occurrence.receipt.initializer occurrence.receipt.expected
      occurrence.entry.allocateStatementId.2 ready.allocateStatementId operational.requirements
      (operational.quantifiersBelow binder old) (operational.allocateStatementId.privacy binder old)
      (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
      (occurrence.receipt.annotationAccepted.variablesBelow _)
      (fun type present => safe_closed _ _ (occurrence.receipt.annotationAccepted.variablesBelow 0 type present))
      _ occurrence.receipt.child
    have safe := privacy.1 expectedReturn (returnSafe binder old)
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (generalized_type_safe return_safe)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizationLifetimeSeeds
/-! Every lifetime starts at a real initialized declaration, with the exact
binder and initializer retained by the same finalizer. No semantic typing or
continuation privacy premise is needed to produce this initial event. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

namespace BodyInitializerOccurrence
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

def lifetimeEvent (occurrence : BodyInitializerOccurrence selected source) :
    RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution
      occurrence.receipt.binding.1 occurrence.receipt.value.id where
  context := occurrence.inferenceContext
  entry := occurrence.entry
  readyState := occurrence.receipt.ready
  value := occurrence.receipt.value
  valueId := rfl
  computation := .statement occurrence.receipt
  ready := occurrence.ready
  extension := occurrence.extension
  retained := List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩
  binderRetained := occurrence.retained

theorem lifetime
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    (owner : occurrence.entry.owner = (evidenceSource selected).owner)
    (retained : occurrence.result.state.nodes <+: selected.body.returned.nodes) :
    GeneralizationLifetime occurrence.lifetimeEvent occurrence.entry.inference.next
      occurrence.result.state [occurrence.result.type] := by
  have extension : selected.body.finalized.substitution.SemanticallyExtends
      occurrence.result.state.inference.substitution := by
    simpa only [occurrence.receipt.inference_eq] using occurrence.extension
  have resultOwner : occurrence.result.state.owner = occurrence.entry.owner := by
    have accepted := initializedReceipt_accepted occurrence.receipt .unit
    exact Detail.inferStatementFuel_preserves_owner accepted
  have afterSource : TypingSourceExtends
      (occurrence.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected) :=
    ⟨(resultOwner.trans owner).symm, retained⟩
  have after := operational.ofInitializer occurrence.receipt selected.body.resources ready
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    retained afterSource extension
  have member : occurrence.receipt.binding.1 ∈ occurrence.result.state.localBinders := by
    rw [occurrence.receipt.result_binders]
    exact List.mem_cons_self
  have resultType : occurrence.result.type = .unit :=
    congrArg Detail.StatementResult.type occurrence.receipt.completed
  have sameRequirements : occurrence.result.state.requirements = occurrence.receipt.ready.requirements :=
    congrArg (fun result : Detail.StatementResult => result.state.requirements) occurrence.receipt.completed
  refine {
    createdAfter := Nat.le_refl _
    allocated := occurrence.quantified_at_or_after_entry checked scope ready operational
    bound := after.quantifiersBelow _ member
    transport := SafeTransport.of_substitution_eq
      (congrArg InferState.substitution occurrence.receipt.inference_eq)
    live := after.privacy _ member
    values := ?_
    older := ?_
    newRows := ?_ }
  · intro type present
    cases List.mem_singleton.mp present
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  · intro type below
    have safe := occurrence.generalized_type_safe checked scope ready operational below
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe
  · intro requirement present fresh
    exact False.elim (fresh (sameRequirements ▸ present))

end BodyInitializerOccurrence
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedControlStatements
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem statement_break
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .breakStmt)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_break_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_break_sound form rfl boundary.accepted boundary.invariant.active (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact boundary.operational.allocateStatementId.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.recordNode]
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

theorem statement_continue
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .continueStmt)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_continue_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_continue_sound form rfl boundary.accepted boundary.invariant.active (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact boundary.operational.allocateStatementId.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.recordNode]
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

/-- Bare return uses its real closed-left unification. The ambient return type
may be a fresh lambda variable; no expected-return privacy premise is needed. -/
theorem statement_returnUnit
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .returnStmt none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨unified, accepted, _, resultEq, _⟩ :=
    inferStatementFuel_success_returnUnit_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_returnUnit_sound form rfl boundary.accepted boundary.invariant.active
      boundary.extension (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have unifiedOperational := boundary.operational.allocateStatementId.unifyClosedLeft allocatedInvariant.ready
    (Ty.variablesBelow_constructor 0 _) allocatedInvariant.returnBelow accepted
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact unifiedOperational.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have same := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using same
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementReturnPrivacy
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization ProtectedVariables

/-- The actual statement preserves return-type privacy, including a new generalized binder. -/
theorem StatementBoundary.return_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected childFuel inferenceContext statement expectedReturn initial result frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn) :
    ∀ binder ∈ result.state.localBinders, Safe binder.scheme.quantified result.state expectedReturn := by
  intro binder member
  rcases inferStatementFuel_quantified_origin boundary.accepted binder member with old | mono | created
  · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
      initial boundary.invariant.ready boundary.operational.requirements (boundary.operational.quantifiersBelow binder old)
      (boundary.operational.privacy binder old) (boundary.scope.catalog checked) (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) boundary.invariant.returnBelow (returnSafe binder old)
      result boundary.accepted).1 _ (returnSafe binder old)
  · intro q _ quantified
    simp [mono] at quantified
  · obtain ⟨initializerFuel, receipt, rfl⟩ := created
    have idEq : result.id = initial.allocateStatementId.1 :=
      congrArg Detail.StatementResult.id receipt.completed
    have recorded : .statement {
        id := initial.allocateStatementId.1, span := statement.span, type := .unit
        form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes := by
      apply boundary.rawSubtree.nodes _ receipt.recorded
      exact .inl (congrArg NodeId.statement idEq.symm)
    let occurrence := BodyInitializerOccurrence.ofReceipt checked boundary.scope receipt boundary.invariant.ready
      boundary.operational recorded boundary.extension
    have safe := occurrence.generalized_type_safe checked boundary.scope boundary.invariant.ready
      boundary.operational boundary.invariant.returnBelow
    simpa only [occurrence, BodyInitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementSequence
/-! Source-order composition passes only the actual head and tail calls to
their semantic consumers. Each call remains tied to one selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem statements_nil
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext [] expectedReturn
      initial result frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  have same := inferStatementsFuel_success_nil_facts boundary.accepted
  subst result
  exact ⟨target, .empty, boundary.invariant, boundary.actual, boundary.operational,
    .nil _ _, BlockResultMatchesFactsAfterSubstitution.empty _ _⟩

theorem statements_singleton
    {statement : Syntax.Statement}
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext [statement] expectedReturn
      initial result frames target)
    (recursive : ∀ {head : Detail.StatementResult},
      StatementBoundary selected childFuel inferenceContext statement expectedReturn
        initial head frames target →
      StatementConclusion selected inferenceContext expectedReturn head frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨head, accepted, same⟩ := inferStatementsFuel_success_singleton_facts boundary.accepted
  subst result
  obtain ⟨finalContext, facts, invariant, actual, operational, typing, agreement⟩ :=
    recursive ({
      accepted
      interfaces := boundary.interfaces
      extension := boundary.extension
      scope := boundary.scope
      invariant := boundary.invariant
      actual := boundary.actual
      operational := boundary.operational
      rawSubtree := boundary.rawSubtrees head.id (by simp)
      integerPatterns := boundary.integerPatterns
      integerLiterals := boundary.integerLiterals
      requirements := boundary.requirements
      covered := boundary.covered head.id (by simp)
      actualCovered := boundary.actualCovered head.id (by simp) } :
      StatementBoundary selected childFuel inferenceContext statement expectedReturn initial head frames target)
  exact ⟨finalContext, .singleton facts, invariant, actual, operational,
    .singleton typing, BlockResultMatchesFactsAfterSubstitution.singleton agreement⟩

theorem statements_cons
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result frames target)
    (headSound : ∀ {head : Detail.StatementResult},
      StatementBoundary selected childFuel inferenceContext statement expectedReturn
        initial head frames target →
      StatementConclusion selected inferenceContext expectedReturn head frames target)
    (tailSound : ∀ {head : Detail.StatementResult} {tail : Detail.BlockResult}
        {middle : SourceSemantics.Context},
      Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial = .ok head →
      StatementsBoundary selected childFuel inferenceContext (next :: rest) expectedReturn
        head.state tail frames middle →
      StatementsConclusion selected inferenceContext expectedReturn tail frames middle) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨head, tail, headAccepted, tailAccepted, resultEq⟩ :=
    inferStatementsFuel_success_cons_facts boundary.accepted
  subst result
  have headProperties := Detail.inferStatementFuel_inferenceProperties boundary.invariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    boundary.invariant.returnBelow headAccepted
  have tailProperties := Detail.inferStatementsFuel_inferenceProperties headProperties.2.1
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    (boundary.invariant.returnBelow.weaken headProperties.1.next_le) tailAccepted
  have headBelow := (Detail.inferStatementFuel_occurrenceBoundExtends headAccepted
    ).nodesBelowNextOccurrence boundary.invariant.nodesBelow
  have headToTail := inferStatementsFuel_success_typingSourceExtends tailAccepted
    headBelow (bodyRoots selected)
  obtain ⟨middle, headFacts, middleInvariant, middleActual, middleOperational, headTyping, headAgreement⟩ :=
    headSound ({
      accepted := headAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension.trans tailProperties.1.substitution_extends
      scope := boundary.scope
      invariant := boundary.invariant
      actual := boundary.actual
      operational := boundary.operational
      rawSubtree := (boundary.rawSubtrees head.id (by simp)).monoBefore headToTail
      integerPatterns := (Detail.inferStatementsFuel_integerPatterns_subset tailAccepted).trans boundary.integerPatterns
      integerLiterals := (Detail.inferStatementsFuel_integerLiterals_subset tailAccepted).trans boundary.integerLiterals
      requirements := (Detail.inferStatementsFuel_requirements_subset tailAccepted).trans boundary.requirements
      covered := boundary.covered head.id (by simp)
      actualCovered := boundary.actualCovered head.id (by simp) } :
      StatementBoundary selected childFuel inferenceContext statement expectedReturn initial head frames target)
  have assumptionsEq := statementHasType_assumptions_eq headTyping
  have covered : ∀ id ∈ tail.statements,
      TemplateScopeCovered selected.body.finalized.typedSource middle (.statement id) := by
    intro id member owner scopes
    change owner.requirement.predicate ∈ middle.assumptions
    rw [assumptionsEq]
    exact boundary.covered id (by simp [member]) owner scopes
  obtain ⟨finalContext, tailFacts, invariant, actual, operational, tailTyping, tailAgreement⟩ :=
    tailSound headAccepted ({
      accepted := tailAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension
      scope := boundary.scope
      invariant := middleInvariant
      actual := middleActual
      operational := middleOperational
      rawSubtrees := fun id member => boundary.rawSubtrees id (by simp [member])
      integerPatterns := boundary.integerPatterns
      integerLiterals := boundary.integerLiterals
      requirements := boundary.requirements
      covered
      actualCovered := fun id member => boundary.actualCovered id (by simp [member]) } :
      StatementsBoundary selected childFuel inferenceContext (next :: rest) expectedReturn
        head.state tail frames middle)
  obtain ⟨tailHead, tailRest, tailEq⟩ := inferStatementsFuel_success_statements_eq_cons tailAccepted
  have typing : StatementsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (head.id :: tail.statements) finalContext (.cons headFacts tailFacts) := by
    rw [tailEq]
    exact .cons headTyping (by simpa [tailEq] using tailTyping)
  exact ⟨finalContext, .cons headFacts tailFacts, invariant, actual, operational, typing,
    BlockResultMatchesFactsAfterSubstitution.cons headAgreement tailAgreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledHeaderLifetimeSeeds
/-! Header events retain the same allocated binder and initializer as their
containing for node. Their initial lifetime follows from that actual receipt
and the finalizer which retained it. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem initializedHeaderReceipt_accepted
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
    Detail.inferForItemFuel (fuel + 1) context source initial = .ok result := by
  rcases receipt with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  cases annotationAccepted with
  | none =>
    simp [Detail.inferForItemFuel, form, child, completed,
      SourceInference.LocalHeaderRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  | some annotationAccepted =>
    simp [Detail.inferForItemFuel, form, annotationAccepted, child, completed,
      SourceInference.LocalHeaderRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩

namespace HeaderLifetime
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.ForItem}
    {inferenceContext : SourceInference.Context} {entry : State} {result : ForItemForm × State}

def event
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : receipt.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders) :
    RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution
      receipt.binding.1 receipt.value.id where
  context := inferenceContext
  entry
  readyState := receipt.ready
  value := receipt.value
  valueId := rfl
  computation := .header receipt
  ready
  extension
  retained
  binderRetained

theorem lifetime
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected inferenceContext)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    ∃ readyAtEvent readyExtension,
      GeneralizationLifetime (event receipt readyAtEvent readyExtension retained binderRetained)
        entry.inference.next result.2 [] := by
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  have readyAtEvent := (receipt.initializer_inference ready formation canonical).2.1
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have itemRetained : result.1.initializedLetBinders ⊆ (evidenceSource selected).initializedLetBinders := by
    rw [receipt.recorded]
    intro binder present
    obtain rfl := List.mem_singleton.mp present
    exact binderRetained
  have after := operational.ofRetainedHeader selected.body.resources ready (scope.catalog checked)
    formation canonical itemRetained extension (initializedHeaderReceipt_accepted receipt)
  have member : receipt.binding.1 ∈ result.2.localBinders := by
    rw [receipt.result_binders]
    exact List.mem_cons_self
  have sameRequirements : result.2.requirements = receipt.ready.requirements :=
    congrArg (fun result : ForItemForm × State => result.2.requirements) receipt.completed
  refine ⟨readyAtEvent, readyExtension, {
    createdAfter := Nat.le_refl _
    allocated := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.quantified_at_or_after_entry
      selected.body.resources receipt ready operational.requirements (scope.catalog checked)
      formation canonical operational.backed operational.origins binderRetained extension
    bound := after.quantifiersBelow _ member
    transport := SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
    live := after.privacy _ member
    values := by simp
    older := ?_
    newRows := ?_ }⟩
  · intro type below
    exact ProtectedVariables.LocalHeaderRequirementTiming.Receipt.generalized_type_safe
      selected.body.resources receipt ready operational.requirements (scope.catalog checked)
      formation canonical operational.backed operational.origins binderRetained extension below
  · intro requirement present fresh
    exact False.elim (fresh (sameRequirements ▸ present))

end HeaderLifetime
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledStatementPrivacyResume
/-! Actual statement prefixes in lambda bodies. The expected return type may
contain variables allocated before the body; each new declaration proves its
privacy from its real initializer and the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem statement_operational_return_privacy
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected.toBodySelection))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial expectedReturn)
    (retained : TypingSourceExtends (result.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection))
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial = .ok result) :
    GeneralizedActualStateInvariant result.state (evidenceSource selected.toBodySelection) ∧
      ∀ binder ∈ result.state.localBinders,
        Safe binder.scheme.quantified result.state expectedReturn := by
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  have catalog := scope.catalog checked
  have afterPrivacy : ActiveQuantifiersPrivate result.state := by
    intro binder member
    rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
    · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
        initial ready operational.requirements (operational.quantifiersBelow binder old)
        (operational.privacy binder old) catalog formation canonical returnBelow
        (returnSafe binder old) result accepted).2.2.1
    · rw [mono]
      exact liveBindersSafe_nil _
    · obtain ⟨initializerFuel, receipt, rfl⟩ := created
      have after := operational.ofInitializer receipt selected.body.resources ready catalog formation canonical
        retained.nodes_prefix retained extension
      exact after.privacy _ member
  obtain ⟨pending, ledger⟩ := operational.ledger
  have after : GeneralizedActualStateInvariant result.state (evidenceSource selected.toBodySelection) := {
    ledger := ⟨pending, (actualLedgerFamily childFuel).statements.statement accepted ledger⟩
    origins := inferStatementFuel_captureOrigins accepted operational.origins retained
    quantifiersBelow := activeQuantifiersBelowNext_inferStatementFuel operational.quantifiersBelow
      ready formation canonical returnBelow accepted
    privacy := afterPrivacy
    backed := operational.backed.inferStatementFuel ready formation canonical returnBelow accepted }
  refine ⟨after,?_⟩
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
  · exact (inferStatementFuel_private binder.scheme.quantified childFuel inferenceContext statement expectedReturn
      initial ready operational.requirements (operational.quantifiersBelow binder old)
      (operational.privacy binder old) catalog formation canonical returnBelow
      (returnSafe binder old) result accepted).1 _ (returnSafe binder old)
  · intro quantified occurs protectedMember
    simp [mono] at protectedMember
  · obtain ⟨initializerFuel, receipt, rfl⟩ := created
    let occurrence := InitializerOccurrence.ofReceipt checked scope receipt ready operational
      (retained.nodes_prefix.subset receipt.recorded) extension
    have safe := occurrence.generalized_type_safe checked scope ready operational returnBelow
    simpa only [occurrence, InitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe

def ResumeEntryInvariant
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel) (expected : Ty) (state : State) : Prop :=
  GeneralizedActualStateInvariant state (evidenceSource selected.toBodySelection) ∧
    (∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state expected) ∧
    state.owner = (evidenceSource selected.toBodySelection).owner

theorem selected_statement_privacy_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (entering : ResumeEntryInvariant selected expectedReturn initial)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (retained : result.state.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementsFuel childFuel inferenceContext sources expectedReturn initial = .ok result)
    (position : sources[index]? = some statement) :
    Nonempty (StatementPrivacyResume inferenceContext statement expectedReturn initial result
      (ResumeEntryInvariant selected expectedReturn)) := by
  apply statementPrivacyResume_of_position_with_invariant ready entering.1.requirements nodesBelow
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    returnBelow accepted position entering
  intro stepFuel source before after beforeReady _ beforeBelow continuation afterRetained executed invariant
  have afterOwner := (Detail.inferStatementFuel_preserves_owner executed).trans invariant.2.2
  have afterSource : TypingSourceExtends (after.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection) :=
    ⟨afterOwner.symm, afterRetained.trans retained⟩
  have afterInvariant := statement_operational_return_privacy checked scope beforeReady invariant.1
    beforeBelow invariant.2.1 afterSource (extension.trans continuation.substitution_extends) executed
  exact ⟨afterInvariant.1,afterInvariant.2,afterOwner⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializedBlockResume
/-! A real initialized statement protects its newly generalized variables
through the rest of a lambda or ordinary function block. The entry state,
generalization, expected-type safety and suffix all come from actual calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

structure InitializedBlockResume
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (initial : State) (result : Detail.BlockResult) (source : Syntax.Statement) where
  actual : InitializerOccurrence selected source
  context : actual.inferenceContext = inferenceContext
  before : initial.InferenceProgress actual.entry
  continuation : actual.result.state.InferenceProgress result.state
  ready : result.state.InferenceReady
  wellFormed : result.state.RequirementsWellFormed
  bound : ∀ q ∈ actual.receipt.binding.1.scheme.quantified, q.index < result.state.inference.next
  transport : SafeTransport actual.receipt.binding.1.scheme.quantified actual.receipt.ready result.state
  resultSafe : Safe actual.receipt.binding.1.scheme.quantified result.state result.type
  expectedSafe : Safe actual.receipt.binding.1.scheme.quantified result.state expectedReturn
  live : LiveBindersSafe actual.receipt.binding.1.scheme.quantified result.state
  olderAtReady : ∀ type, type.VariablesBelow initial.inference.next →
    Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type
  olderSafe : ∀ type, type.VariablesBelow initial.inference.next →
    Safe actual.receipt.binding.1.scheme.quantified result.state type
  newRows : ∀ requirement ∈ result.state.requirements,
    requirement ∉ actual.receipt.ready.requirements →
      PredicateSafe actual.receipt.binding.1.scheme.quantified result.state requirement.predicate

theorem initialized_block_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (entering : ResumeEntryInvariant selected expectedReturn initial)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (retained : result.state.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementsFuel childFuel inferenceContext sources expectedReturn initial = .ok result)
    (position : sources[index]? = some statement)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : statement.value = .letDecl name annotation (some initializer)) :
    Nonempty (InitializedBlockResume selected inferenceContext expectedReturn initial result statement) := by
  obtain ⟨resume⟩ := selected_statement_privacy_resume checked scope ready nodesBelow entering
    returnBelow retained extension accepted position
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  obtain ⟨initializerFuel,receipt,_,_⟩ := resume.toOccurrence.initialized form formation canonical
  have resultExtension := extension.trans resume.continuation.substitution_extends
  have recorded := (resume.retained.trans retained).subset receipt.recorded
  let occurrence := InitializerOccurrence.ofReceipt checked scope receipt resume.ready
    resume.entryInvariant.1 recorded resultExtension
  have afterOwner := (Detail.inferStatementFuel_preserves_owner resume.accepted).trans resume.entryInvariant.2.2
  have afterSource : TypingSourceExtends (resume.result.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection) :=
    ⟨afterOwner.symm, resume.retained.trans retained⟩
  have afterOperational := resume.entryInvariant.1.ofInitializer receipt selected.body.resources resume.ready
    (scope.catalog checked) formation canonical (resume.retained.trans retained) afterSource resultExtension
  have binderMember : receipt.binding.1 ∈ resume.result.state.localBinders := by
    rw [receipt.result_binders]
    exact List.mem_cons_self
  have live := afterOperational.privacy _ binderMember
  have bound := afterOperational.quantifiersBelow _ binderMember
  have older : ∀ type, type.VariablesBelow resume.entry.inference.next →
      Safe receipt.binding.1.scheme.quantified resume.result.state type := by
    intro type below
    have safe := occurrence.generalized_type_safe checked scope resume.ready resume.entryInvariant.1 below
    simpa only [occurrence, InitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe
  have expectedSafe := older expectedReturn (returnBelow.weaken resume.before.next_le)
  have resultSafe : Safe receipt.binding.1.scheme.quantified resume.result.state resume.result.type := by
    have resultType : resume.result.type = .unit :=
      congrArg Detail.StatementResult.type receipt.completed
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  have suffix := resume.resume receipt.binding.1.scheme.quantified bound live expectedSafe resultSafe older
  have properties := Detail.inferStatementsFuel_inferenceProperties ready formation canonical returnBelow accepted
  refine ⟨{
    actual := occurrence, context := rfl, before := resume.before, continuation := resume.continuation,
    ready := properties.2.1,
    wellFormed := (Detail.inferStatementsFuel_direct_progress accepted).wellFormed entering.1.requirements,
    bound := fun q present => Nat.lt_of_lt_of_le (bound q present) resume.continuation.next_le,
    transport := (SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)).trans suffix.1,
    resultSafe := suffix.2.1, expectedSafe := suffix.1 _ expectedSafe,
    live := suffix.2.2.1,
    olderAtReady := fun type below => occurrence.generalized_type_safe checked scope resume.ready
      resume.entryInvariant.1 (below.weaken resume.before.next_le),
    olderSafe := fun type below => suffix.1 type (older type (below.weaken resume.before.next_le)),
    newRows := ?_ }⟩
  intro requirement present fresh
  apply suffix.2.2.2 requirement present
  have same : resume.result.state.requirements = receipt.ready.requirements :=
    congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
  simpa only [same, occurrence, InitializerOccurrence.ofReceipt] using fresh

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNestedTemplatePrivacy
/-! Actual selected template scope closes the requirements of a new outer
binder while preserving an inner binder's private quantified variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledNestedTemplatePrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization

private theorem predicate_image {substitution : Substitution} {predicate : ProgramPredicate}
    {type : Ty} (member : type ∈ predicate.subject :: predicate.arguments)
    {v q : TypeVarId} (occurs : v ∈ type.freeVariables)
    (image : q ∈ (substitution.apply (.variable v)).freeVariables) :
    q ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  have inside := MonomorphicGeneralization.replacement_occurs substitution type occurs image
  rcases List.mem_cons.mp member with rfl | member
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr (.inl inside)
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply type, List.mem_map.mpr ⟨type, member, rfl⟩, inside⟩)

/-- The inner binder's real finalizer check keeps each protected variable
fixed. The actual outer template then excludes those variables from every
live requirement, using the same source owner after finalization. -/
theorem outer_binder_safe {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) {fuel : Nat}
    {selected : Selected compiled row fuel} {outerSource innerSource : Syntax.Statement}
    (outer : InitializerOccurrence selected outerSource)
    (inner : InitializerOccurrence selected innerSource)
    (bodySafe : Safe inner.receipt.binding.1.scheme.quantified
      outer.receipt.ready outer.receipt.value.type) :
    BinderSafe inner.receipt.binding.1.scheme.quantified outer.result.state
      outer.receipt.binding.1 := by
  have bodyEq : outer.receipt.binding.1.scheme.body =
      outer.receipt.ready.resolve outer.receipt.value.type := by
    exact Detail.generalizeValue_scheme_body _ _ _ _
  have innerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained inner)
  have outerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained outer)
  have fixed : ∀ q ∈ inner.receipt.binding.1.scheme.quantified,
      selected.body.finalized.substitution.apply (.variable q) = .variable q := by
    intro q quantified
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (innerCapture.quantified_fresh q quantified), Option.getD_none]
  have resultResolve : ∀ type, outer.result.state.resolve type = outer.receipt.ready.resolve type := by
    intro type
    simp only [State.resolve, InferState.resolve, outer.receipt.inference_eq]
  constructor
  · intro v occurs q image privateMember
    rw [resultResolve] at image
    have inBody := (List.mem_filter.mp occurs).1
    have inResolved := MonomorphicGeneralization.replacement_occurs
      outer.receipt.ready.inference.substitution outer.receipt.binding.1.scheme.body inBody image
    rw [bodyEq] at inResolved
    exact safe_resolved outer.ready bodySafe q inResolved privateMember
  · intro requirement owned type typeMember v occurs _unbound q image privateMember
    rw [resultResolve] at image
    have finalImage := fixed_variable_occurs_at_final outer.extension (fixed q privateMember) image
    have predicateOccurs := predicate_image typeMember occurs finalImage
    let owner : LocalSchemeTemplateOwner :=
      ⟨outer.receipt.binding.1, .expression outer.receipt.value.id, requirement⟩
    have initialized : ({binder := outer.receipt.binding.1, initializer := .expression outer.receipt.value.id} :
        InitializedLetBinding) ∈ initializedLetBindings (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) :=
      List.mem_flatMap.mpr ⟨_, outer.recorded, List.mem_singleton_self _⟩
    have contains : ContainsLocalSchemeTemplate (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) owner :=
      List.mem_flatMap.mpr ⟨_, initialized, List.mem_map.mpr ⟨requirement, owned, rfl⟩⟩
    have finalizedContains := FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      selected.body.finalized.substitution contains
    simp only [SourceCompiledGeneralizedSoundness.evidenceSource,
      SourceCompiledGeneralizedSoundness.bodyRoots, Selected.toBodySelection] at finalizedContains
    rw [← selected.body.resources.source_eq] at finalizedContains
    have restricted : selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ outerCapture.quantified_fresh
    have finalizedOccurs : q ∈ TypedTraitResolution.predicateVariables
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution owner).requirement.predicate := by
      change q ∈ TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution
          (selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified) requirement.predicate)
      rw [restricted]
      exact predicateOccurs
    have quantified := SourceCompiledGeneralizedBarrierConnection.original_template_scoped
      accepted member selected finalizedContains q finalizedOccurs
    have outerOccurs : q ∈ (outer.receipt.ready.resolve outer.receipt.value.type).freeVariables :=
      (List.mem_filter.mp quantified).1
    exact bodySafe q outerOccurs privateMember

end Solcore.SourceSemantics.SourceCompiledNestedTemplatePrivacy
end
