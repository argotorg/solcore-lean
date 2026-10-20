import Solcore.Frontend.SourceInference.LocalGeneralizationInferenceReceipts
import Solcore.SourceSemantics.SourceInferenceSelectedLocalSchemePrivacy

/-! Active local-scheme predicates retain an actual raw ledger witness.
The invariant follows executable scope preservation and generalization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def LiveTemplatesBacked (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, ∀ requirement ∈ binder.schemeRequirements,
    ∃ raw ∈ state.requirements,
      applyPredicate state requirement.predicate = applyPredicate state raw.predicate

private theorem predicate_extends {before after : State}
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution)
    (predicate : ProgramPredicate) :
    applyPredicate after (applyPredicate before predicate) = applyPredicate after predicate :=
  TypedTraitResolution.applySubstitution_semanticallyExtends extension predicate

theorem LiveTemplatesBacked.transport {before after : State}
    (backed : LiveTemplatesBacked before)
    (binders : after.localBinders ⊆ before.localBinders)
    (rows : before.requirements ⊆ after.requirements)
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution) :
    LiveTemplatesBacked after := by
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (binders member) requirement retained
  refine ⟨raw, rows present, ?_⟩
  have transported := congrArg (applyPredicate after) same
  simpa only [predicate_extends extension] using transported

theorem LiveTemplatesBacked.congr {before after : State}
    (backed : LiveTemplatesBacked before)
    (binders : after.localBinders = before.localBinders)
    (rows : after.requirements = before.requirements)
    (inference : after.inference.substitution = before.inference.substitution) :
    LiveTemplatesBacked after := by
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (binders ▸ member) requirement retained
  exact ⟨raw,rows.symm ▸ present,by simpa only [applyPredicate, inference] using same⟩

theorem LiveTemplatesBacked.initial
    (owner : Resolved.DeclarationId) (locals : Environment) (comptime : List Bool) :
    LiveTemplatesBacked (State.initial owner locals comptime) := by
  intro binder member requirement retained
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, below, same⟩ := List.exists_of_mem_mapIdx member
  subst binder
  simp at retained

theorem LiveTemplatesBacked.inferExprFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {expected : Option Ty}
    {initial : State} {result : InferredExpression × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  have properties := inferExprFuel_inferenceProperties ready validated canonical expectedBelow accepted
  have same := congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
  change result.2.localBinders = initial.localBinders at same
  exact backed.transport (by intro _ member; exact same ▸ member)
    (inferExprFuel_requirements_subset accepted) properties.1.substitution_extends

theorem LiveTemplatesBacked.generalized
    {state : State} (backed : LiveTemplatesBacked state) (solved : state.inference.Solved)
    (locals : Environment) (cutoff : Nat) (type : Ty) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    let generalized := generalizeValue state locals cutoff type
    LiveTemplatesBacked ((state.withLocals locals).allocateBinder name generalized.scheme span
      comptime generalized.requirements).2 := by
  intro generalized binder member requirement retained
  change binder ∈ ((state.withLocals locals).allocateBinder name generalized.scheme span
    comptime generalized.requirements).1 :: state.localBinders at member
  rcases List.mem_cons.mp member with rfl | old
  · change requirement ∈ generalized.requirements at retained
    obtain ⟨raw, present, _, same⟩ :=
      generalizeValue_requirement_source state locals cutoff type requirement retained
    refine ⟨raw,present,?_⟩
    change applyPredicate state requirement.predicate = applyPredicate state raw.predicate
    rw [same]
    exact predicate_extends solved.apply_idempotent _
  · exact backed binder old requirement retained

theorem LocalLetRequirementTiming.Receipt.templates_ready
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked receipt.ready :=
  (backed.congr (after := initial.allocateStatementId.2) rfl rfl rfl).inferExprFuel ready.allocateStatementId validated canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child

theorem LocalLetRequirementTiming.Receipt.templates_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    LiveTemplatesBacked result.state := by
  have readyBacked := LocalLetRequirementTiming.Receipt.templates_ready receipt backed ready validated canonical
  have readyProperties := receipt.initializer_inference ready validated canonical
  have allocated := readyBacked.generalized readyProperties.2.1.solved receipt.locals
    initial.nextRequirement (receipt.ready.resolve receipt.value.type) receipt.name.value
    (some receipt.name.span) false
  rw [receipt.completed]
  exact allocated.congr rfl rfl rfl

theorem LocalLetRequirementTiming.Receipt.templates_before
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (wellFormed : initial.RequirementsWellFormed)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∀ binder ∈ receipt.ready.localBinders, ∀ requirement ∈ binder.schemeRequirements,
      ∃ raw ∈ receipt.ready.requirements.take initial.nextRequirement,
        applyPredicate receipt.ready requirement.predicate = applyPredicate receipt.ready raw.predicate := by
  have properties := receipt.initializer_inference ready validated canonical
  have readyWellFormed := (inferExprFuel_direct_progress receipt.child).wellFormed wellFormed
  have rows : initial.requirements ⊆ receipt.ready.requirements := inferExprFuel_requirements_subset receipt.child
  intro binder member requirement retained
  obtain ⟨raw, present, same⟩ := backed binder (receipt.ready_binders ▸ member) requirement retained
  refine ⟨raw, (State.mem_take_prior_requirements_iff initial receipt.ready wellFormed readyWellFormed
    rows raw).mpr present, ?_⟩
  have transported := congrArg (applyPredicate receipt.ready) same
  simpa only [predicate_extends properties.1.substitution_extends] using transported

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
