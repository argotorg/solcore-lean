import Solcore.SourceSemantics.SourceInferenceNormalizedContracts

/-! The recursive initializer result and its exact executable allocation
compose at the real initialized-let boundary, including for-header metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail

theorem annotation_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {source : Option Syntax.TypeExpr} {expected : Option Ty}
    (formation : InferenceFormationContext semantic context outer)
    (annotation : LocalLetRequirementTiming.Annotation context source expected) (next : Nat) :
    (∀ type ∈ expected, type.VariablesBelow next) ∧
      ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type) := by
  cases annotation with
  | none => simp
  | @some syntaxType type accepted =>
    constructor
    · intro selected member
      cases Option.mem_some_iff.mp member
      exact resolveSourceType_success_variablesBelow accepted next
    · intro selected member
      cases Option.mem_some_iff.mp member
      rw [resolveSourceType_success_apply_eq_self outer accepted]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed formation.canonical
          formation.signatures formation.scope.parameters formation.scope.owner accepted)

theorem uninitialized_binding_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {source : Syntax.TypeExpr} {type : Ty}
    {state : State} (name : Syntax.Identifier)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : resolveSourceType context source = .ok type)
    (continuation : outer.SemanticallyExtends state.inference.substitution) :
    let locals := state.binderEnvironment.apply state.inference.substitution
    let generalized := generalizeValue state locals state.nextRequirement (state.resolve type)
    NormalizedStateFormation semantic outer
      ((state.withLocals locals).allocateBinder name.value generalized.scheme
        (some name.span) false generalized.requirements).2 := by
  dsimp only
  let locals := state.binderEnvironment.apply state.inference.substitution
  have resolvedEq : state.resolve type = type :=
    resolveSourceType_success_apply_eq_self state.inference.substitution accepted
  have closed : type.freeVariables = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro metavariable member
    exact Nat.not_lt_zero _ (resolveSourceType_success_variablesBelow accepted 0 metavariable member)
  have quantifiedEmpty :
      (generalizeValue state locals state.nextRequirement (state.resolve type)).scheme.quantified = [] := by
    rw [generalizeValue_scheme_quantified, resolvedEq, closed]
    rfl
  have typeFormed : TypeAdmissible semantic (outer.apply (state.resolve type)) := by
    rw [resolvedEq, resolveSourceType_success_apply_eq_self outer accepted]
    exact TypeAdmissible.ofWellFormed
      (resolveSourceType_success_typeWellFormed formation.canonical
        formation.signatures formation.scope.parameters formation.scope.owner accepted)
  have localsFormed : NormalizedStateFormation semantic outer (state.withLocals locals) :=
    formed.congr rfl rfl
  apply NormalizedStateFormation.allocate localsFormed
  apply NormalizedBinderFormation.generalized locals state.nextRequirement name.value
    (some name.span) false continuation typeFormed formed.requirements
  exact LocalBinderInstantiationNoCapture.of_quantified_eq_nil quantifiedEmpty

theorem initialized_statement_receipt_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (child : InferExprFuelFormation semantic outer fuel context receipt.initializer
      receipt.expected initial.allocateStatementId.2)
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial)
    (formation : InferenceFormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (captures : NoCaptureNodes outer result.state.nodes) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  have sameInference : result.state.inference = receipt.ready.inference :=
    congrArg (fun value : StatementResult => value.state.inference) receipt.completed
  have childContinuation : outer.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [sameInference] at continuation
  have childCaptures : NoCaptureNodes outer receipt.ready.nodes :=
    captures.mono (by intro node member; rw [receipt.completed]; exact List.mem_append_left _ member)
  have expected := annotation_normalized_formation formation receipt.annotationAccepted
    initial.allocateStatementId.2.inference.next
  have childFormation := child (State.InferenceReady.allocateStatementId ready)
    (State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodes)
    (formed.congr rfl rfl) formation expected.1 expected.2
    (receipt.value, receipt.ready) receipt.child childContinuation childCaptures
  have newCapture : LocalBinderInstantiationNoCapture outer receipt.binding.1 :=
    captures.at_statement receipt.recorded _ (List.mem_singleton_self _)
  have installed := initialized_statement_normalized_formation receipt childFormation.2 childFormation.1
    childContinuation newCapture
  refine ⟨?_, installed.2⟩
  rw [receipt.completed]
  exact .unit formation.scope.binders

theorem initialized_header_receipt_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (child : InferExprFuelFormation semantic outer fuel context receipt.initializer receipt.expected initial)
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial)
    (formation : InferenceFormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (captures : NoCaptureNodes outer result.2.nodes)
    (headerCaptures : NoCaptureItems outer [result.1]) :
    NormalizedStateFormation semantic outer result.2 := by
  have sameInference : result.2.inference = receipt.ready.inference :=
    congrArg (fun value : ForItemForm × State => value.2.inference) receipt.completed
  have childContinuation : outer.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [sameInference] at continuation
  have childCaptures : NoCaptureNodes outer receipt.ready.nodes := by
    rw [receipt.completed] at captures
    exact captures
  have expected := annotation_normalized_formation formation receipt.annotationAccepted initial.inference.next
  have childFormation := child ready nodes formed formation expected.1 expected.2
    (receipt.value, receipt.ready) receipt.child childContinuation childCaptures
  have newCapture : LocalBinderInstantiationNoCapture outer receipt.binding.1 := by
    apply headerCaptures
    rw [receipt.recorded]
    exact List.mem_flatMap.mpr ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩
  exact (initialized_header_normalized_formation receipt childFormation.2 childFormation.1
    childContinuation newCapture).2

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
