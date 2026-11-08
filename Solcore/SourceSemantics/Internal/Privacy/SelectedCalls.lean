import Solcore.SourceSemantics.Internal.Privacy.SelectedReferences
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Privacy of calls and matches

Declarations, builtins, patterns, finalization and the call and match continuations.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyDeclarations
/-! Named declaration parameters and predicates are instantiated from the
actual allocator and the checked signature catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_below {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) (next : Nat) : type.VariablesBelow next := by
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

/-- The real rigid-parameter allocator cannot expose any older protected
metavariable. No privacy of an arbitrary substitution range is assumed. -/
theorem declaration_instantiation_private {protectedVars : List TypeVarId} {state : State}
    (scheme : ConstrainedDeclarationScheme)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) :
    let instantiated := scheme.instantiate state.inference.next
    let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
    ∀ parameter replacement, (parameter,replacement) ∈ instantiated.parameterSubstitution →
      Safe protectedVars advanced replacement := by
  dsimp only
  intro parameter replacement member
  obtain ⟨metavariable, rfl, lower, _⟩ :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_fresh scheme state.inference.next member
  change Avoids protectedVars (state.resolve (.variable metavariable))
  rw [resolve_fresh_variable ready metavariable lower]
  intro candidate occurs protectedMember
  have same : candidate = metavariable := by simpa [Ty.freeVariables] using occurs
  subst candidate
  exact (Nat.not_lt.mpr lower) (bound metavariable protectedMember)

private theorem predicate_parameters_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) (substitution : ParameterSubstitution)
    (range : ∀ parameter replacement, (parameter,replacement) ∈ substitution →
      Safe protectedVars state replacement) :
    PredicateSafe protectedVars state (predicate.applyParameters substitution) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_parameterApply range (safe_closed _ _ (formed_below formed.subject 0))
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_parameterApply range
      (safe_closed _ _ (formed_below (formed.arguments _ originalMember) 0))

private theorem candidate_fit {context : SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty} {result : Detail.ExpectationResult}
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    Detail.withExpected context state actual expected = .ok result := by
  unfold Detail.candidateWithExpected at accepted
  cases fitted : Detail.withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    cases accepted
    rfl
  | error error =>
    cases error <;> simp [fitted] at accepted
    all_goals cases ‹Unification.Error› <;> simp_all

/-- Actual signature selection, argument fitting, result fitting and the
final declaration batch jointly establish privacy for a retained candidate. -/
theorem tryFunctionCandidate_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature =
      .ok (some result)) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  have signatureFormed := catalog.functions_semantic signature member
  have nextLe := ConstrainedDeclarationScheme.instantiate_next_le signature.scheme state.inference.next
  have advanceProgress : state.InferenceProgress advanced :=
    State.InferenceProgress.of_substitution_eq ready.solved nextLe rfl
  have advancedReady := State.InferenceReady.of_progress_of_binderEnvironment_eq ready advanceProgress rfl
  have advancePrivacy : SafeTransport protectedVars state advanced := .of_substitution_eq rfl
  have rangeSafe := declaration_instantiation_private signature.scheme ready bound
  have rangeBelow : ∀ {parameter replacement}, (parameter, replacement) ∈ instantiated.parameterSubstitution →
      replacement.VariablesBelow advanced.inference.next :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_variablesBelow
      signature.scheme state.inference.next
  have parametersSafe : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      Safe protectedVars advanced type := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact safe_parameterApply rangeSafe
      (safe_closed _ _ (formed_below (signatureFormed.parameter_types _ originalMember) 0))
  have parametersBelow : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      type.VariablesBelow advanced.inference.next := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact ParameterSubstitution.apply_variables_below rangeBelow
      (formed_below (signatureFormed.parameter_types _ originalMember) _)
  have returnsClosed : (Ty.productMany signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany (fun type member => formed_below (signatureFormed.return_types type member) 0)
  have resultSafe : Safe protectedVars advanced
      (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)) :=
    safe_parameterApply rangeSafe (safe_closed _ _ returnsClosed)
  have resultBelow : (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)).VariablesBelow
      advanced.inference.next :=
    ParameterSubstitution.apply_variables_below rangeBelow (returnsClosed.weaken (Nat.zero_le _))
  have predicatesSafe : ∀ predicate ∈ instantiated.predicates, PredicateSafe protectedVars advanced predicate := by
    intro predicate predicateMember
    rw [ConstrainedDeclarationScheme.instantiate_predicates] at predicateMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp predicateMember
    exact predicate_parameters_private (signatureFormed.predicates _ originalMember) _ rangeSafe
  obtain ⟨fittedArguments, fittedResult, trace, fitResult, _, resultEq, _, _, _, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness signatureFormed.scheme_body accepted
  have argumentAccepted := trace.fitArguments_eq
  have argumentProgress := Detail.fitArguments_some_inferenceProperties advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le)
    parametersBelow argumentAccepted
  have argumentPrivacy := fitArguments_private catalog advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) argumentAccepted
  have fitAccepted := candidate_fit fitResult
  have beforeFit := advancePrivacy.trans argumentPrivacy.1
  have totalNext := (advanceProgress.trans argumentProgress.1).next_le
  have fittedPrivacy := withExpected_private argumentProgress.2
    (resultBelow.weaken argumentProgress.1.next_le)
    (fun type member => (expectedBelow type member).weaken totalNext)
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => beforeFit _ (expectedSafe type member)) argumentPrivacy.2.1 fitAccepted
  have fittedRows := withExpected_new_requirements_private catalog argumentProgress.2
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => beforeFit _ (expectedSafe type member)) fitAccepted
  have fittedReady := (Detail.withExpected_inferenceProperties argumentProgress.2
    (resultBelow.weaken argumentProgress.1.next_le)
    (fun type member => (expectedBelow type member).weaken totalNext) fitAccepted).2.1
  have sameInference : result.state.inference = fittedResult.state.inference := by
    rw [stateEq]
    exact requirementBatch_inference _ _
  have sameBinders : result.state.localBinders = fittedResult.state.localBinders := by
    rw [stateEq]
    exact requirementBatch_binders _ _
  have completion : SafeTransport protectedVars fittedResult.state result.state :=
    .of_substitution_eq (congrArg InferState.substitution sameInference)
  refine ⟨beforeFit.trans (fittedPrivacy.1.trans completion), ?_,
    fittedPrivacy.2.2.transport sameBinders completion, ?_⟩
  · rw [resultEq]
    have safe := safe_resolved fittedReady fittedPrivacy.2.1
    have batchInference := requirementBatch_inference fittedResult.state (signature.scheme.instantiate state.inference.next).predicates
    simpa only [Safe, State.resolve, InferState.resolve, sameInference, State.markDirectCallRequirements, batchInference] using safe
  · intro row rowMember fresh
    have batchMember : row ∈ (fittedResult.state.addRequirementsWithIds instantiated.predicates).2.requirements := by
      simpa only [stateEq, State.markDirectCallRequirements] using rowMember
    rcases requirementBatch_row_origin _ _ batchMember with old | issued
    · have beforeRows : ∀ row ∈ fittedResult.state.requirements, row ∉ state.requirements →
          PredicateSafe protectedVars fittedResult.state row.predicate := by
        have combined := new_requirements_trans argumentPrivacy.2.2 fittedRows fittedPrivacy.1
        exact combined
      intro type typeMember
      exact completion _ (beforeRows row old fresh type typeMember)
    · intro type typeMember
      exact completion _ (fittedPrivacy.1 _
        (argumentPrivacy.1 _ (predicatesSafe row.predicate issued type typeMember)))

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyGeneralization
/-! A new binder inherits privacy from its actual initializer and the new
requirement rows selected by executable generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem safe_variable_member {protectedVars : List TypeVarId} {state : State}
    {type : Ty} (safe : Safe protectedVars state type) {metavariable : TypeVarId}
    (member : metavariable ∈ type.freeVariables) :
    Safe protectedVars state (.variable metavariable) := by
  induction type with
  | «variable» actual =>
    have same : metavariable = actual := by simpa [Ty.freeVariables] using member
    subst metavariable
    exact safe
  | parameter _ => simp [Ty.freeVariables] at member
  | constructor _ => simp [Ty.freeVariables] at member
  | error => simp [Ty.freeVariables] at member
  | proxy _ ih => exact ih safe member
  | comptime _ ih => exact ih safe member
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_application_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_application_iff _ _ _ _).mp safe).2 member
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_function_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_function_iff _ _ _ _).mp safe).2 member
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_product_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_product_iff _ _ _ _).mp safe).2 member
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_mapping_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_mapping_iff _ _ _ _).mp safe).2 member

private theorem generalized_requirement_new_source (state : State)
    (locals : Environment) (cutoff : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    ∃ raw, raw ∈ state.requirements.drop cutoff ∧
      template.predicate = Detail.applyPredicate state raw.predicate := by
  unfold Detail.generalizeValue at member
  dsimp only at member
  obtain ⟨raw, eligible, produced⟩ := List.mem_filterMap.mp member
  split at produced
  · cases Option.some.inj produced
    exact ⟨raw, (List.mem_filter.mp eligible).1, rfl⟩
  · cases produced

private theorem predicate_resolved_private {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady) {predicate : ProgramPredicate}
    (safe : PredicateSafe protectedVars state predicate) :
    PredicateSafe protectedVars state (Detail.applyPredicate state predicate) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_resolved ready (safe _ (by simp))
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_resolved ready (safe _ (List.mem_cons.mpr (.inr originalMember)))

/-- The real requirement cutoff separates every selected template from the
old ledger. Only genuinely new rows need privacy; old generalized templates
may still contain their own quantified variables. -/
theorem generalized_binder_private {protectedVars : List TypeVarId}
    {before state : State} {type : Ty} (locals : Environment) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (beforeWellFormed : before.RequirementsWellFormed)
    (wellFormed : state.RequirementsWellFormed)
    (ready : state.InferenceReady)
    (typeSafe : Safe protectedVars state type)
    (newRows : ∀ row ∈ state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars state row.predicate) :
    let generalized := Detail.generalizeValue state locals before.nextRequirement type
    BinderSafe protectedVars state
      (state.allocateBinder name generalized.scheme span comptime generalized.requirements).1 := by
  dsimp only
  constructor
  · intro metavariable member
    have occurs : metavariable ∈ type.freeVariables := by
      exact (List.mem_filter.mp member).1
    exact safe_variable_member typeSafe occurs
  · intro requirement member predicateType typeMember metavariable occurs outside
    obtain ⟨raw, dropped, predicateEq⟩ :=
      generalized_requirement_new_source state locals before.nextRequirement type requirement member
    obtain ⟨rawMember, lower⟩ :=
      (State.mem_drop_requirements_iff state wellFormed _ raw).mp dropped
    have fresh : raw ∉ before.requirements := by
      intro old
      exact (Nat.not_lt.mpr lower)
        (State.requirement_id_lt_nextRequirement before beforeWellFormed old)
    have safe := predicate_resolved_private ready (newRows raw rawMember fresh)
    rw [predicateEq] at typeMember
    exact safe_variable_member (safe predicateType typeMember) occurs

/-- Executable binder allocation preserves existing live privacy and enters
its actual generalized binder with the inherited initializer certificate. -/
theorem allocate_generalized_private {protectedVars : List TypeVarId}
    {before state : State} {type : Ty} (locals : Environment) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (beforeWellFormed : before.RequirementsWellFormed)
    (wellFormed : state.RequirementsWellFormed) (ready : state.InferenceReady)
    (typeSafe : Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (newRows : ∀ row ∈ state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars state row.predicate) :
    let generalized := Detail.generalizeValue state locals before.nextRequirement type
    let allocated := (state.allocateBinder name generalized.scheme span comptime generalized.requirements).2
    SafeTransport protectedVars state allocated ∧ LiveBindersSafe protectedVars allocated := by
  dsimp only
  have transport : SafeTransport protectedVars state
      (state.allocateBinder name (Detail.generalizeValue state locals before.nextRequirement type).scheme
        span comptime (Detail.generalizeValue state locals before.nextRequirement type).requirements).2 :=
    .of_substitution_eq rfl
  refine ⟨transport, ?_⟩
  intro binder member
  rcases List.mem_cons.mp member with rfl | old
  · exact (generalized_binder_private locals name span comptime beforeWellFormed
      wellFormed ready typeSafe newRows).transport transport
  · exact (live binder old).transport transport

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacySignatureReferences
/-! A named function value is instantiated and recorded from its real catalog
signature, including the predicates emitted by that exact allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_closed {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) : type.VariablesBelow 0 := by
  intro metavariable member
  simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed] at member

private theorem instantiated_predicates_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {signature : ProgramFunctionSignature}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) :
    let instantiated := signature.scheme.instantiate state.inference.next
    let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
    ∀ predicate ∈ instantiated.predicates, PredicateSafe protectedVars advanced predicate := by
  dsimp only
  intro predicate memberPredicate type memberType
  rw [ConstrainedDeclarationScheme.instantiate_predicates] at memberPredicate
  obtain ⟨original, memberOriginal, rfl⟩ := List.mem_map.mp memberPredicate
  have formed := (catalog.functions_semantic signature member).predicates original memberOriginal
  have range := declaration_instantiation_private signature.scheme ready bound
  rcases List.mem_cons.mp memberType with rfl | memberType
  · exact safe_parameterApply range (safe_closed _ _ (formed_closed formed.subject))
  · obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp memberType
    exact safe_parameterApply range (safe_closed _ _ (formed_closed (formed.arguments argument argumentMember)))

/-- The state and obligation batch are the exact executable declaration
instantiation. Its successful expected fitting is retained in the conclusion. -/
theorem declaration_reference_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {signature : ProgramFunctionSignature}
    {source : Syntax.Expr} {id : ExpressionId} {name : String} {expected : Option Ty}
    {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted :
      let instantiated := signature.scheme.instantiate state.inference.next
      let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
      let batch := advanced.addRequirementsWithIds instantiated.predicates
      Detail.recordExpressionWithExpected context source id instantiated.body
        (.reference name (.declaration (DeclarationInstantiation.ofInstantiated signature instantiated)))
        batch.1 expected batch.2 = .ok result) :
    SafeTransport protectedVars state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧
      ∀ row ∈ result.2.requirements, row ∉ state.requirements →
        PredicateSafe protectedVars result.2 row.predicate := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  let batch := advanced.addRequirementsWithIds instantiated.predicates
  have formed := catalog.functions_semantic signature member
  have nextLe := ConstrainedDeclarationScheme.instantiate_next_le signature.scheme state.inference.next
  have progress : state.InferenceProgress advanced := .of_substitution_eq ready.solved nextLe rfl
  have advancedReady := State.InferenceReady.of_progress_of_binderEnvironment_eq ready progress rfl
  have batchInference : batch.2.inference = advanced.inference := requirementBatch_inference _ _
  have batchBinders : batch.2.localBinders = advanced.localBinders := requirementBatch_binders _ _
  have batchProgress := State.InferenceProgress.of_inference_eq advancedReady.solved batchInference
  have batchReady := State.InferenceReady.of_progress_of_binderEnvironment_eq advancedReady
    batchProgress (by simp only [State.binderEnvironment, batchBinders])
  have initialTransport : SafeTransport protectedVars state batch.2 :=
    .of_substitution_eq (by simpa only [advanced] using congrArg InferState.substitution batchInference)
  have bodyClosed : signature.scheme.body.VariablesBelow 0 := by
    rw [formed.scheme_body]
    intro metavariable occurs
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with occurs | occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.parameter_types type member)) metavariable occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.return_types type member)) metavariable occurs
  have bodySafe : Safe protectedVars advanced instantiated.body :=
    safe_parameterApply (declaration_instantiation_private signature.scheme ready bound)
      (safe_closed _ _ bodyClosed)
  have bodyBelow := ConstrainedDeclarationScheme.instantiate_body_variablesBelow signature.scheme
    state.inference.next (bodyClosed.weaken (Nat.zero_le _))
  have totalProgress := progress.trans batchProgress
  have completion : SafeTransport protectedVars advanced batch.2 :=
    .of_substitution_eq (congrArg InferState.substitution batchInference)
  have recordPrivacy := recordExpressionWithExpected_private catalog batchReady
    (by simpa only [batchInference] using bodyBelow)
    (fun type member => (expectedBelow type member).weaken totalProgress.next_le)
    (completion _ bodySafe) (fun type member => initialTransport _ (expectedSafe type member))
    (live.transport batchBinders initialTransport) accepted
  refine ⟨initialTransport.trans recordPrivacy.1, recordPrivacy.2.1, recordPrivacy.2.2.1, ?_⟩
  have batchRows : ∀ row ∈ batch.2.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars batch.2 row.predicate := by
    intro row rowMember fresh
    rcases requirementBatch_row_origin _ _ rowMember with old | issued
    · exact False.elim (fresh old)
    · intro type typeMember
      exact completion _ (instantiated_predicates_private catalog member ready bound _ issued type typeMember)
  exact new_requirements_trans batchRows recordPrivacy.2.2.2 recordPrivacy.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyBuiltins
/-! Fixed builtin calls use their actual equal-argument unifications and
expected-result unification. They issue no requirement rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem equal_arguments_private {protectedVars : List TypeVarId}
    {arguments : List InferredExpression} {parameters : List Ty} {state result : State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    SafeTransport protectedVars state result ∧ LiveBindersSafe protectedVars result ∧
      result.requirements = state.requirements := by
  induction arguments generalizing parameters state result with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, live, rfl⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      subst result
      exact ⟨.refl _ _, live, rfl⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
      | ok middle =>
        simp only [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
        have argSafe := argumentsSafe argument List.mem_cons_self
        have paramSafe := parametersSafe parameter List.mem_cons_self
        have transport := ProtectedVariables.unify argSafe paramSafe unified
        have child := ih
          (fun arg member => transport _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
          (fun param member => transport _ (parametersSafe param (List.mem_cons_of_mem _ member)))
          (live.unify argSafe paramSafe unified) accepted
        exact ⟨transport.trans child.1, child.2.1, child.2.2.trans (unify_requirements unified)⟩

private theorem builtin_parameters_closed (function : BuiltinFunctionId) :
    ∀ type ∈ function.parameterTypes, type.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word]

private theorem builtin_return_closed (function : BuiltinFunctionId) :
    function.returnType.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

private def builtin_finish (source callee : Syntax.Expr) (name : String)
    (function : BuiltinFunctionId) (arguments : List InferredExpression) (call : ExpressionId)
    (state : State) : InferredExpression × State :=
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {id := calleeId, type := function.type}
  let (_, state) := Detail.recordExpression callee calleeExpression
    (.reference name (.builtinFunction function)) [] [] state
  let result : InferredExpression := {id := call, type := state.resolve function.returnType}
  Detail.recordExpression source result
    (.call calleeId (arguments.map (·.id)) (.builtinFunction function)) [] [] state

private theorem builtin_finish_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (function : BuiltinFunctionId)
    (arguments : List InferredExpression) (call : ExpressionId) (state : State)
    (live : LiveBindersSafe protectedVars state) :
    let result := builtin_finish source callee name function arguments call state
    SafeTransport protectedVars state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = state.requirements := by
  dsimp only
  have transport : SafeTransport protectedVars state
      (builtin_finish source callee name function arguments call state).2 := .of_substitution_eq rfl
  refine ⟨transport, ?_, live.transport rfl transport, rfl⟩
  have fixed : state.resolve function.returnType = function.returnType :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables _ _ (by
      intro metavariable _ occurs
      exact Nat.not_lt_zero _ (builtin_return_closed function metavariable occurs))
  change Safe protectedVars (builtin_finish source callee name function arguments call state).2
    (state.resolve function.returnType)
  rw [fixed]
  exact safe_closed _ _ (builtin_return_closed function)

/-- The actual builtin call checks introduce no fresh requirement identities
and preserve privacy through every performed unification. -/
theorem recordBuiltinFunctionCall_private {protectedVars : List TypeVarId}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    SafeTransport protectedVars state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = state.requirements := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases argumentsRun : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentsRun] at accepted
    | ok argumentState =>
      simp only [argumentsRun] at accepted
      have argumentPrivacy := equal_arguments_private argumentsSafe
        (fun type member => safe_closed _ _ (builtin_parameters_closed function type member)) live argumentsRun
      cases expected with
      | none =>
        have same : builtin_finish source callee name function arguments call argumentState = result := by
          simpa only [builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
        subst result
        have complete := builtin_finish_private source callee name function arguments call argumentState argumentPrivacy.2.1
        exact ⟨argumentPrivacy.1.trans complete.1, complete.2.1, complete.2.2.1,
          complete.2.2.2.trans argumentPrivacy.2.2⟩
      | some expected =>
        cases resultRun : Detail.unify argumentState function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok finalState =>
          have same : builtin_finish source callee name function arguments call finalState = result := by
            simpa only [resultRun, builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
          subst result
          have returnsSafe : Safe protectedVars argumentState function.returnType :=
            safe_closed _ _ (builtin_return_closed function)
          have expectedSafe := argumentPrivacy.1 _ (expectedSafe expected rfl)
          have transport := ProtectedVariables.unify returnsSafe expectedSafe resultRun
          have finalLive := argumentPrivacy.2.1.unify returnsSafe expectedSafe resultRun
          have complete := builtin_finish_private source callee name function arguments call finalState finalLive
          exact ⟨argumentPrivacy.1.trans (transport.trans complete.1), complete.2.1, complete.2.2.1,
            complete.2.2.2.trans ((unify_requirements resultRun).trans argumentPrivacy.2.2)⟩
  · simp [arity, bind, Except.bind] at accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLambdaParameters
/-! Actual lambda parameter allocation preserves older protected variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem allocate_mono_private {protectedVars : List TypeVarId} {state : State}
    {type : Ty} (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool)
    (safe : Safe protectedVars state type) (live : LiveBindersSafe protectedVars state) :
    LiveBindersSafe protectedVars (state.allocateBinder name (.mono type) span comptime []).2 := by
  have transport : SafeTransport protectedVars state
      (state.allocateBinder name (.mono type) span comptime []).2 := .of_substitution_eq rfl
  intro binder member
  rcases List.mem_cons.mp member with rfl | member
  · constructor
    · intro metavariable occurs
      exact transport _ (safe_variable_member safe (List.mem_filter.mp occurs).1)
    · intro requirement occurs
      cases occurs
  · exact (live binder member).transport transport

theorem LiveBindersSafe.restore {protectedVars : List TypeVarId} {before after : State}
    (live : LiveBindersSafe protectedVars before)
    (transport : SafeTransport protectedVars before after) :
    LiveBindersSafe protectedVars (after.restoreLexicalScope before.lexicalScope) := by
  intro binder member
  exact (live binder member).transport transport

/-- Both inferred and annotated parameters follow the real fresh allocator,
annotation resolver, duplicate check and recursive binder-entry sequence. -/
theorem bindLambdaParameters_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    SafeTransport protectedVars state result.2.2 ∧
      (∀ type ∈ result.2.1, Safe protectedVars result.2.2 type) ∧
      LiveBindersSafe protectedVars result.2.2 ∧ result.2.2.requirements = state.requirements := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, by simp, live, rfl⟩
  | cons parameter rest ih =>
    cases parameterValue : parameter.value with
    | error =>
      simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    | inferred name =>
      by_cases duplicate : name.value ∈ seen
      · simp [Detail.bindLambdaParameters, parameterValue, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · let type := state.fresh.1
        let freshState := state.fresh.2
        let binderState := (freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).2
        cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
        | error error =>
          simp [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
            binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        | ok tail =>
          rcases tail with ⟨binders, types, finalState⟩
          have same : ((freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).1 :: binders,
              type :: types, finalState) = result := by
            simpa [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
          subst result
          have typeSafe : Safe protectedVars freshState type := fresh_type ready bound
          have binderReady : binderState.InferenceReady :=
            State.InferenceReady.allocateBinder _ _ _ _ _ ready.fresh
              ((Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _))
          have allocated : SafeTransport protectedVars freshState binderState := .of_substitution_eq rfl
          have entered : LiveBindersSafe protectedVars binderState :=
            allocate_mono_private _ _ _ typeSafe (live.transport rfl fresh)
          have child := ih binderReady
            (by intro metavariable member; exact Nat.lt_trans (bound metavariable member) (Nat.lt_succ_self _))
            entered tailRun
          refine ⟨fresh.trans (allocated.trans child.1), ?_, child.2.2.1, child.2.2.2⟩
          intro actual member
          rcases List.mem_cons.mp member with rfl | member
          · exact child.1 _ (allocated _ typeSafe)
          · exact child.2.1 actual member
    | typed marker name sourceType =>
      cases resolved : Detail.resolveSourceType context sourceType with
      | error error =>
        simp [Detail.bindLambdaParameters, parameterValue, resolved, bind, Except.bind] at accepted
      | ok type =>
        by_cases duplicate : name.value ∈ seen
        · simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        · let binderState := (state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).2
          cases tailRun : Detail.bindLambdaParameters context rest (index + 1) (name.value :: seen) binderState with
          | error error =>
            simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
              binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          | ok tail =>
            rcases tail with ⟨binders, types, finalState⟩
            have same : ((state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).1 :: binders,
                type :: types, finalState) = result := by
              simpa [Detail.bindLambdaParameters, parameterValue, resolved, duplicate,
                binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
            subst result
            have typeSafe : Safe protectedVars state type :=
              safe_closed _ _ (Detail.resolveSourceType_success_variablesBelow resolved 0)
            have binderReady : binderState.InferenceReady :=
              State.InferenceReady.allocateBinder _ _ _ _ _ ready
                (Detail.resolveSourceType_success_variablesBelow resolved _)
            have allocated : SafeTransport protectedVars state binderState := .of_substitution_eq rfl
            have entered : LiveBindersSafe protectedVars binderState := allocate_mono_private _ _ _ typeSafe live
            have child := ih binderReady bound entered tailRun
            refine ⟨allocated.trans child.1, ?_, child.2.2.1, child.2.2.2⟩
            intro actual member
            rcases List.mem_cons.mp member with rfl | member
            · exact child.1 _ (allocated _ typeSafe)
            · exact child.2.1 actual member

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCallRecording
/-! Actual overload selection and call-node recording preserve the privacy
proved for the retained candidate and its real requirement batch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem selectFunctionCandidateFrom_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  obtain ⟨signature, member, tried⟩ := Detail.selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_private catalog (cataloged member) ready bound argumentsBelow expectedBelow
    argumentsSafe expectedSafe live tried

private theorem attach_fields (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).inference = state.inference ∧
      (Detail.attachExpressionCoercions state entries).localBinders = state.localBinders ∧
      (Detail.attachExpressionCoercions state entries).requirements = state.requirements := by
  induction entries generalizing state with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => Detail.appendExpressionCoercions node entry.coercions))

/-- The real recording fold modifies only occurrence/node metadata; it
retains the candidate's inferred type and exact requirement ledger. -/
theorem recordSelectedCall_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult)
    (safe : Safe protectedVars attempt.state attempt.result.type)
    (live : LiveBindersSafe protectedVars attempt.state) :
    let result := Detail.recordSelectedCall source callee name arguments attempt
    SafeTransport protectedVars attempt.state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = attempt.state.requirements := by
  dsimp only
  have fields := attach_fields attempt.state attempt.argumentCoercions
  have inference : (Detail.recordSelectedCall source callee name arguments attempt).2.inference = attempt.state.inference := fields.1
  have binders : (Detail.recordSelectedCall source callee name arguments attempt).2.localBinders = attempt.state.localBinders := fields.2.1
  have transport : SafeTransport protectedVars attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  exact ⟨transport, transport _ safe, live.transport binders transport, fields.2.2⟩

/-- Indirect-call recording similarly retains the accepted application's
state and output type, including its already committed coercion requirements. -/
theorem recordIndirectCall_private {protectedVars : List TypeVarId}
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : Detail.IndirectApplicationResult)
    (safe : Safe protectedVars application.state application.result.type)
    (live : LiveBindersSafe protectedVars application.state) :
    let result := Detail.recordIndirectCall source callee arguments application
    SafeTransport protectedVars application.state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = application.state.requirements := by
  dsimp only
  have transport : SafeTransport protectedVars application.state (Detail.recordIndirectCall source callee arguments application).2 :=
    .of_substitution_eq rfl
  exact ⟨transport, transport _ safe, live.transport rfl transport, rfl⟩

/-- Binary overloads may fit the candidate output once more. Recording
preserves this actual fitted state and output, including its new requirements. -/
theorem recordSelectedCallResult_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State)
    (safe : Safe protectedVars state result.type)
    (live : LiveBindersSafe protectedVars state) :
    let recorded := Detail.recordSelectedCallResult source callee name arguments attempt result coercions state
    SafeTransport protectedVars state recorded.2 ∧ Safe protectedVars recorded.2 recorded.1.type ∧
      LiveBindersSafe protectedVars recorded.2 ∧ recorded.2.requirements = state.requirements := by
  dsimp only
  have fields := attach_fields state attempt.argumentCoercions
  have inference : (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2.inference = state.inference := fields.1
  have binders : (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2.localBinders = state.localBinders := fields.2.1
  have transport : SafeTransport protectedVars state (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2 :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  exact ⟨transport, transport _ safe, live.transport binders transport, fields.2.2⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyPatterns
/-! Privacy of the actual recursive pattern checker, including fresh numeric
requirements, constructor payloads, and entered pattern binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem freshTypes_fields (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders ∧
      (Detail.freshTypes count state).2.requirements = state.requirements := by
  induction count generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih => exact ih state.fresh.2

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

private def PatternPrivacy (protectedVars : List TypeVarId) (initial final : State) : Prop :=
  SafeTransport protectedVars initial final ∧ LiveBindersSafe protectedVars final ∧
    ∀ row ∈ final.requirements, row ∉ initial.requirements → PredicateSafe protectedVars final row.predicate

private theorem PatternPrivacy.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : PatternPrivacy protectedVars first second) (right : PatternPrivacy protectedVars second third) :
    PatternPrivacy protectedVars first third :=
  ⟨left.1.trans right.1, right.2.1, new_requirements_trans left.2.2 right.2.2 right.1⟩

private theorem PatternPrivacy.of_unchanged {protectedVars : List TypeVarId} {initial final : State}
    (transport : SafeTransport protectedVars initial final) (live : LiveBindersSafe protectedVars final)
    (requirements : final.requirements = initial.requirements) : PatternPrivacy protectedVars initial final := by
  refine ⟨transport, live, ?_⟩
  intro row member fresh
  exact False.elim (fresh (requirements ▸ member))

private theorem integer_prefix_private {protectedVars : List TypeVarId} {state recorded final : State}
    {expected : Ty} {metavariable : TypeVarId} {normalized : Ty} {requirement : RequirementId}
    (ready : state.InferenceReady)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (freshType : state.fresh.1 = .variable metavariable)
    (unified : Detail.unify recorded (.variable metavariable) normalized = .ok final)
    (normalization : recorded.resolve expected = normalized)
    (inference : recorded.inference = state.fresh.2.inference)
    (binders : recorded.localBinders = state.localBinders)
    (requirements : recorded.requirements = state.requirements ++
      [{id := requirement, predicate := ProgramSignatures.builtinIntPredicate (.variable metavariable)}]) :
    PatternPrivacy protectedVars state final := by
  have stage : SafeTransport protectedVars state.fresh.2 recorded :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  have initialStage : SafeTransport protectedVars state recorded := fresh.trans stage
  have targetSafe : Safe protectedVars recorded (.variable metavariable) :=
    freshType ▸ stage _ (fresh_type ready bound)
  have recordedReady : recorded.InferenceReady := by
    apply State.InferenceReady.of_progress_of_binderEnvironment_eq ready.fresh
      (State.InferenceProgress.of_inference_eq ready.fresh.solved inference)
    simp only [State.binderEnvironment, binders]
    rfl
  have normalizedSafe : Safe protectedVars recorded normalized :=
    normalization ▸ safe_resolved recordedReady (initialStage _ expectedSafe)
  have transport := ProtectedVariables.unify targetSafe normalizedSafe unified
  refine ⟨initialStage.trans transport,
    (live.transport binders initialStage).unify targetSafe normalizedSafe unified, ?_⟩
  intro row member fresh
  rw [unify_requirements unified, requirements] at member
  rcases List.mem_append.mp member with old | issued
  · exact False.elim (fresh old)
  · have same := List.mem_singleton.mp issued
    subst row
    intro type member
    have typeEq : type = .variable metavariable := by
      simpa [ProgramSignatures.builtinIntPredicate] using member
    subst type
    exact transport _ targetSafe

private theorem contextual_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state final : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.contextualConstructorCandidate context state (some expected) name = .ok (dataType,constructor,arguments))
    (unified : Detail.unify state (Detail.instantiateDataConstructor dataType constructor arguments).resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
        type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := contextual_constructor ready formation safe selected
  obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts selected
  cases Option.some.inj expectedEq
  have resolvedBelow : (state.resolve expected).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedBelow
  rw [nominalEq] at resolvedBelow
  have argumentsBelow := ((Ty.variablesBelow_applyMany_iff state.inference.next
    (.constructor (.declaration dataType.id)) arguments).mp
      (by simpa only [Ty.nominal] using resolvedBelow)).2
  have bounds := Detail.instantiateDataConstructor_types_variablesBelow (dataType := dataType) argumentsBelow
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember state.inference.next)
  have progress := Detail.unify_inferenceProgress ready.solved bounds.2 expectedBelow unified
  have finalReady := Detail.unify_preserves_inferenceReady ready bounds.2 expectedBelow unified
  have transport := ProtectedVariables.unify privacy.2 safe unified
  exact ⟨PatternPrivacy.of_unchanged transport (live.unify privacy.2 safe unified) (unify_requirements unified),
    progress, finalReady, fun type member => ⟨(bounds.1 type member).weaken progress.next_le, transport _ (privacy.1 type member)⟩⟩

private theorem explicit_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state allocated final : State} {expected : Ty}
    {qualifiers : List String} {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.explicitConstructorCandidate context qualifiers name = .ok (dataType,constructor))
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  obtain ⟨dataMember, constructorMember, _⟩ := Detail.explicitConstructorCandidate_success_facts selected
  have payloadClosed := formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  have privacy := fresh_constructor (dataType := dataType) ready bound payloadClosed
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor state ready
    (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
  have lexical := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  have requirements := freshConstructor_requirements dataType constructor state
  rw [allocation] at privacy properties lexical requirements
  have allocatedBinders := congrArg LexicalScope.binders lexical
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have expectedSafe := privacy.1 _ safe
  have transport := ProtectedVariables.unify privacy.2.2 expectedSafe unified
  have progress := Detail.unify_inferenceProgress properties.2.1.solved properties.2.2.2.2 expectedBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 properties.2.2.2.2 expectedBound unified
  have finalLive := (live.transport allocatedBinders privacy.1).unify privacy.2.2 expectedSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans requirements),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2.2.1 type member).weaken progress.next_le,
      transport _ (privacy.2.1 type member)⟩⟩

private theorem tuple_prefix_private {protectedVars : List TypeVarId} {state allocated final : State}
    {expected : Ty} {types : List Ty} {count : Nat}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ types, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := freshTypes count ready bound
  have properties := Detail.freshTypes_inferenceProperties count state ready
  have fields := freshTypes_fields count state
  rw [allocation] at privacy properties fields
  have expectedSafe := privacy.1 _ safe
  have argumentsSafe := safe_productMany protectedVars allocated types privacy.2
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have productBound := Ty.variablesBelow_productMany properties.2.2
  have progress := Detail.unify_inferenceProgress properties.2.1.solved expectedBound productBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 expectedBound productBound unified
  have transport := ProtectedVariables.unify expectedSafe argumentsSafe unified
  have finalLive := (live.transport fields.1 privacy.1).unify expectedSafe argumentsSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans fields.2),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2 type member).weaken progress.next_le, transport _ (privacy.2 type member)⟩⟩


private def PatternCallPrivacy (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    Safe protectedVars state expected → LiveBindersSafe protectedVars state →
    Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    PatternPrivacy protectedVars state result.state

private def PatternsCallPrivacy (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    (∀ type ∈ expected, Safe protectedVars state type) → LiveBindersSafe protectedVars state →
    Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    PatternPrivacy protectedVars state result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_private (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallPrivacy protectedVars fuel context pattern expected seen state := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallPrivacy protectedVars fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallPrivacy protectedVars fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live (by assumption) unified
        (by assumption) rfl rfl rfl
  case case5 =>
    intros
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live (by assumption) unified
        (by assumption) rfl rfl rfl
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (Detail.freshTypes sources.length inputState).1 = argumentTypes :=
      congrArg Prod.fst freshEq
    have allocatedStateEq : (Detail.freshTypes sources.length inputState).2 = allocatedState :=
      congrArg Prod.snd freshEq
    have beforeChildren := tuple_prefix_private (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow bound expectedSafe live freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have child := childrenIH _ _ beforeChildren.2.2.1
      (fun type member => (beforeChildren.2.2.2 type member).1) formation
      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
      (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by
        rw [← argumentTypesEq]
        simpa only [sources] using (by assumption))
    exact beforeChildren.1.trans child
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallPrivacy
    unfold PatternCallPrivacy at ihHead
    unfold PatternsCallPrivacy at ihTail
    intro result ready expectedBelow formation bound expectedSafe live success
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headRun : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headRun, bind, Except.bind] at success
      cases tailRun : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headPrivacy := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation
          bound (expectedSafe _ List.mem_cons_self) live headRun
        have headProperties := Detail.inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation headRun
        have tailPrivacy := ihTail inferredHead inferredTail headProperties.2
          (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
          formation (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
          (fun type member => headPrivacy.1 _ (expectedSafe type (List.mem_cons_of_mem _ member)))
          headPrivacy.2.1 tailRun
        exact headPrivacy.trans tailPrivacy
  all_goals
    intros
    first | unfold PatternCallPrivacy at * | unfold PatternsCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact PatternPrivacy.of_unchanged (.refl _ _) live rfl
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation bound expectedSafe live (by assumption))
    all_goals
      try
        exact PatternPrivacy.of_unchanged (.of_substitution_eq rfl)
          (allocate_mono_private _ _ _ (safe_resolved ready expectedSafe) live) rfl

/-- The actual recursive flat pattern computation transports private live
variables, including every requirement row newly issued by nested children. -/
theorem inferMatchPatternFlatFuel_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State}
    {result : Detail.InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result) :
    SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate :=
  pattern_call_private protectedVars fuel context pattern expected seen state result
    ready expectedBelow formation bound expectedSafe live accepted

/-- Public pattern checking keeps the exact continuation state returned by
its recursive pattern computation. -/
theorem inferMatchPatternFuel_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State}
    {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    SafeTransport protectedVars state result.2 ∧ LiveBindersSafe protectedVars result.2 ∧
      ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases actual : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_private ready expectedBelow formation bound expectedSafe live actual

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts
/-! Privacy through the actual mutually recursive source inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def InferExprFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferConstructorApplicationFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    (∀ payload ∈ instantiation.payloadTypes, Safe protectedVars state payload) →
    instantiation.resultType.VariablesBelow state.inference.next →
    Safe protectedVars state instantiation.resultType →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferConstructorArgumentsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expectedTypes, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      SafeTransport protectedVars state result.2 ∧
        (∀ expression ∈ result.1, Safe protectedVars result.2 expression.type) ∧
        LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferStatementsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      SafeTransport protectedVars state result.state ∧
        Safe protectedVars result.state result.type ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferStatementFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      SafeTransport protectedVars state result.state ∧
        Safe protectedVars result.state result.type ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferForItemsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

def InferForItemFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      SafeTransport protectedVars state result.2 ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferPlaceFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        Safe protectedVars result.2 result.1.type ∧ LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferAssignedValueFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      SafeTransport protectedVars state result.2.2 ∧
        Safe protectedVars result.2.2 result.1.target.type ∧
        Safe protectedVars result.2.2 result.2.1.type ∧ LiveBindersSafe protectedVars result.2.2 ∧
        ∀ row ∈ result.2.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2.2 row.predicate

def InferExprsFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      SafeTransport protectedVars state result.2 ∧
        (∀ expression ∈ result.1, Safe protectedVars result.2 expression.type) ∧
        LiveBindersSafe protectedVars result.2 ∧
        ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate

def InferMatchCasesFuelPrivacy
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    scrutineeType.VariablesBelow state.inference.next →
    Safe protectedVars state scrutineeType →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
        ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCallContinuation
/-! The actual call branch preserves private scheme variables through
constructor dispatch, argument inference, overload selection, builtins and
indirect application. Recursive premises are exactly smaller-fuel cases. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem freshDataConstructorInstantiation_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

theorem inferExprFuel_call_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression callee : Syntax.Expr} {sourceArguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (expressionEq : expression.value = .call callee sourceArguments)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelPrivacy protectedVars fuel context expression
        initial.allocateExpressionId.1 instantiation sourceArguments.elements expected state)
    (argumentsInduction : InferExprsFuelPrivacy protectedVars fuel context
      sourceArguments.elements initial.allocateExpressionId.2)
    (calleeInduction : ∀ state, InferExprFuelPrivacy protectedVars fuel context callee none state) :
    InferExprFuelPrivacy protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocatedPrivacy
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated callee with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType, constructor⟩
        let freshResult := freshDataConstructorInstantiation dataType constructor allocated
        have candidateFacts := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
        have freshPrivacy := fresh_constructor (dataType := dataType) allocatedReady bound payloadClosed
        have freshLive := allocatedLive.transport
          (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
        have freshWellFormed := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wellFormed
        have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) freshProperties.1.next_le)
          freshLive catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
          freshProperties.2.2.2.2 freshPrivacy.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          (fun type member => freshPrivacy.1 _ (expectedSafe type member)) result success
        refine ⟨allocatedPrivacy.trans (freshPrivacy.1.trans finished.1), finished.2.1, finished.2.2.1, ?_⟩
        intro row member fresh
        apply finished.2.2.2 row member
        change row ∉ allocated.requirements at fresh
        simpa only [freshResult, freshDataConstructorInstantiation_requirements] using fresh
    | nil =>
      simp only at success
      split at success
      · cases success
      · next _ missing _ =>
        cases missing with
        | some missing => rcases missing with ⟨qualifiers,name⟩; simp at success
        | none =>
          cases argumentsResult : inferExprsFuel fuel context sourceArguments.elements allocated with
          | error error => simp [argumentsResult] at success
          | ok argumentsPair =>
            rcases argumentsPair with ⟨arguments, argumentState⟩
            simp only [argumentsResult] at success
            have argumentsProperties := inferExprsFuel_inferenceProperties allocatedReady validated canonical argumentsResult
            have argumentsPrivacy := argumentsInduction allocatedReady wellFormed bound allocatedLive catalog validated canonical
              (arguments,argumentState) argumentsResult
            have prefixPrivacy := allocatedPrivacy.trans argumentsPrivacy.1
            have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
              fun type member => (expectedBelow type member).weaken argumentsProperties.1.next_le
            have expectedSafeAtArguments : ∀ type ∈ expected, Safe protectedVars argumentState type :=
              fun type member => argumentsPrivacy.1 _ (expectedSafe type member)
            have argumentBound : ∀ v ∈ protectedVars, v.index < argumentState.inference.next :=
              fun v member => Nat.lt_of_lt_of_le (bound v member) argumentsProperties.1.next_le
            have finishSelected (name : String) (candidates : List ProgramFunctionSignature)
                (subset : candidates ⊆ context.signatures.functions) (attempt : CandidateAttemptResult)
                (selectionSuccess : selectFunctionCandidateFrom context name candidates arguments
                  (relevantIntegerLiterals argumentState allocated.integerLiterals.length arguments) id expected argumentState = .ok attempt)
                (resultEq : recordSelectedCall expression callee name arguments attempt = result) :
                SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
                  LiveBindersSafe protectedVars result.2 ∧
                  ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
              have selected := selectFunctionCandidateFrom_private catalog subset argumentsProperties.2.1 argumentBound
                argumentsProperties.2.2 expectedAtArguments argumentsPrivacy.2.1 expectedSafeAtArguments argumentsPrivacy.2.2.1 selectionSuccess
              have recorded := recordSelectedCall_private expression callee name arguments attempt selected.2.1 selected.2.2.1
              rw [← resultEq]
              refine ⟨prefixPrivacy.trans (selected.1.trans recorded.1), recorded.2.1, recorded.2.2.1, ?_⟩
              have rows := new_requirements_trans argumentsPrivacy.2.2.2 selected.2.2.2 selected.1
              intro row member fresh type typeMember
              exact recorded.1 _ (rows row (recorded.2.2.2 ▸ member) fresh type typeMember)
            have finishIndirect (calleeResult : InferredExpression) (calleeState : State)
                (calleeSuccess : inferExprFuel fuel context callee none argumentState = .ok (calleeResult,calleeState))
                (application : IndirectApplicationResult)
                (applicationSuccess : applyFunctionType context id calleeResult.type arguments expected calleeState = .ok application)
                (resultEq : recordIndirectCall expression calleeResult arguments application = result) :
                SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
                  LiveBindersSafe protectedVars result.2 ∧
                  ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
              have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1 validated canonical (by simp) calleeSuccess
              have calleePrivacy := calleeInduction argumentState argumentsProperties.2.1
                ((inferExprsFuel_direct_progress argumentsResult).wellFormed wellFormed) argumentBound argumentsPrivacy.2.2.1
                catalog validated canonical (by simp) (by simp) (calleeResult,calleeState) calleeSuccess
              have applied := applyFunctionType_private catalog calleeProperties.2.1
                (fun v member => Nat.lt_of_lt_of_le (argumentBound v member) calleeProperties.1.next_le)
                calleeProperties.2.2
                (fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le)
                (fun type member => (expectedAtArguments type member).weaken calleeProperties.1.next_le)
                calleePrivacy.2.1 (fun argument member => calleePrivacy.1 _ (argumentsPrivacy.2.1 argument member))
                (fun type member => calleePrivacy.1 _ (expectedSafeAtArguments type member)) calleePrivacy.2.2.1 applicationSuccess
              have recorded := recordIndirectCall_private expression calleeResult arguments application applied.2.1 applied.2.2.1
              rw [← resultEq]
              refine ⟨prefixPrivacy.trans (calleePrivacy.1.trans (applied.1.trans recorded.1)), recorded.2.1, recorded.2.2.1, ?_⟩
              have rows := new_requirements_trans
                (new_requirements_trans argumentsPrivacy.2.2.2 calleePrivacy.2.2.2 calleePrivacy.1) applied.2.2.2 applied.1
              intro row member fresh type typeMember
              exact recorded.1 _ (rows row (recorded.2.2.2 ▸ member) fresh type typeMember)
            cases qualifiedEq : calleeQualifiedIdentifier? callee with
            | some qualified =>
                rcases qualified with ⟨namespacePath, name⟩
                simp only [qualifiedEq] at success
                cases binderEq :
                    argumentState.lookupBinder? namespacePath.head! with
                | some binder =>
                    simp only [binderEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | none =>
                    simp only [binderEq] at success
                    cases functionsResult : qualifiedFunctionsNamed
                        context namespacePath name with
                    | error error =>
                        simp [functionsResult]
                          at success
                    | ok candidatesOption =>
                        simp only [functionsResult]
                          at success
                        cases candidatesOption with
                        | some candidates =>
                            cases selectionResult :
                                selectFunctionCandidateFrom context
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates arguments
                                  (relevantIntegerLiterals
                                    argumentState
                                    allocated.integerLiterals.length
                                    arguments)
                                  id expected argumentState with
                            | error error =>
                                simp [selectionResult] at success
                            | ok attempt =>
                                simp only [selectionResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishSelected
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates
                                  (qualifiedFunctionsNamed_success_subset_catalog
                                    functionsResult)
                                  attempt selectionResult resultEq
                        | none =>
                            cases calleeResult : inferExprFuel fuel
                                context callee none argumentState with
                            | error error =>
                                simp [calleeResult]
                                  at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult] at success
                                cases applicationResult :
                                    applyFunctionType context id
                                      inferredCallee.type arguments
                                      expected calleeState with
                                | error error =>
                                    simp [applicationResult] at success
                                | ok application =>
                                    simp only [applicationResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult
                                      application applicationResult
                                      resultEq
            | none =>
                simp only [qualifiedEq] at success
                cases identifierEq : calleeIdentifier? callee with
                | none =>
                    simp only [identifierEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | some name =>
                    simp only [identifierEq] at success
                    cases binderEq : argumentState.lookupBinder? name with
                    | some binder =>
                        simp only [binderEq] at success
                        cases calleeResult : inferExprFuel fuel context
                            callee none argumentState with
                        | error error =>
                            simp [calleeResult]
                              at success
                        | ok calleePair =>
                            rcases calleePair with
                              ⟨inferredCallee, calleeState⟩
                            simp only [calleeResult] at success
                            cases applicationResult : applyFunctionType
                                context id inferredCallee.type arguments
                                expected calleeState with
                            | error error =>
                                simp [applicationResult] at success
                            | ok application =>
                                simp only [applicationResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishIndirect inferredCallee
                                  calleeState calleeResult application
                                  applicationResult resultEq
                    | none =>
                        simp only [binderEq] at success
                        cases functionsResult : functionsNamed context
                            name with
                        | error error =>
                            simp [functionsResult]
                              at success
                        | ok candidates =>
                            simp only [functionsResult] at success
                            cases candidates with
                            | nil =>
                                cases builtinEq :
                                    builtinFunctionNamed? name with
                                | none =>
                                    simp [builtinEq] at success
                                | some function =>
                                    simp only [builtinEq] at success
                                    have builtinPrivacy := recordBuiltinFunctionCall_private
                                      argumentsPrivacy.2.1 expectedSafeAtArguments argumentsPrivacy.2.2.1 success
                                    refine ⟨prefixPrivacy.trans builtinPrivacy.1, builtinPrivacy.2.1,
                                      builtinPrivacy.2.2.1, ?_⟩
                                    intro row member fresh
                                    have inArguments := builtinPrivacy.2.2.2 ▸ member
                                    exact fun type typeMember => builtinPrivacy.1 _
                                      (argumentsPrivacy.2.2.2 row inArguments fresh type typeMember)
                            | cons candidate rest =>
                                cases selectionResult :
                                    selectFunctionCandidateFrom context
                                      name (candidate :: rest) arguments
                                      (relevantIntegerLiterals
                                        argumentState
                                        allocated.integerLiterals.length
                                        arguments)
                                      id expected argumentState with
                                | error error =>
                                    simp [selectionResult] at success
                                | ok attempt =>
                                    simp only [selectionResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishSelected name
                                      (candidate :: rest)
                                      (functionsNamed_success_subset_catalog
                                        functionsResult)
                                      attempt selectionResult resultEq

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyFinalization
/-! Numeric defaulting removes flexible variables. Its real finalization
receipt therefore preserves privacy without requiring the defaulted variable
to be private before defaulting. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem default_unifier (v : TypeVarId) :
    Unification.unifyTypes (.variable v) .word = .ok [(v,.word)] := by
  exact Unification.unifyWithFuel_variable_constructor 14 v (.builtin .word)

private theorem unify_word_private {protectedVars : List TypeVarId}
    {before after : State} {original resolved : TypeVarId}
    (normal : before.resolve (.variable original) = .variable resolved)
    (accepted : Detail.unify before (.variable original) .word = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  have unifyEq : before.inference.unify (.variable original) .word =
      .ok { before.inference with substitution := Substitution.compose [(resolved,Ty.word)] before.inference.substitution } := by
    unfold InferState.unify
    change (do
      let update ← Unification.unifyTypes (before.resolve (.variable original)) .word
      pure { before.inference with substitution := update.compose before.inference.substitution }) = _
    simp only [normal,default_unifier,bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [unifyEq,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
  subst after
  have range : Substitution.RangeAvoidsDomain [(resolved,Ty.word)] (guard protectedVars) := by
    intro v type member
    have same : (v,type) = (resolved,Ty.word) := List.mem_singleton.mp member
    cases same
    intro candidate occurs
    simp only [Ty.word,Ty.freeVariables,List.not_mem_nil] at occurs
  intro type safe
  simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

theorem defaultIntegerPatternTarget_private {protectedVars : List TypeVarId}
    {before after : State} {origin : IntegerPatternOrigin}
    (accepted : Detail.defaultIntegerPatternTarget before origin = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.defaultIntegerPatternTarget at accepted
  split at accepted
  · exact unify_word_private (by assumption) accepted
  · have same : before = after := Except.ok.inj accepted
    subst after
    exact .refl _ _

theorem defaultIntegerLiteralTarget_private {protectedVars : List TypeVarId}
    {before after : State} {origin : IntegerLiteralOrigin}
    (accepted : Detail.defaultIntegerLiteralTarget before origin = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.defaultIntegerLiteralTarget at accepted
  split at accepted
  · exact unify_word_private (by assumption) accepted
  · have same : before = after := Except.ok.inj accepted
    subst after
    exact .refl _ _

theorem defaultIntegerPatternTargets_private {protectedVars : List TypeVarId}
    {before after : State} {origins : List IntegerPatternOrigin}
    (accepted : Detail.defaultIntegerPatternTargets origins before = .ok after) :
    SafeTransport protectedVars before after := by
  induction origins generalizing before with
  | nil =>
    cases Except.ok.inj accepted
    exact .refl _ _
  | cons origin rest ih =>
    unfold Detail.defaultIntegerPatternTargets at accepted
    cases head : Detail.defaultIntegerPatternTarget before origin with
    | error error => simp [head,bind,Except.bind] at accepted
    | ok next =>
      simp only [head,bind,Except.bind] at accepted
      exact (defaultIntegerPatternTarget_private head).trans (ih accepted)

theorem defaultIntegerLiteralTargets_private {protectedVars : List TypeVarId}
    {before after : State} {origins : List IntegerLiteralOrigin}
    (accepted : Detail.defaultIntegerLiteralTargets origins before = .ok after) :
    SafeTransport protectedVars before after := by
  induction origins generalizing before with
  | nil =>
    cases Except.ok.inj accepted
    exact .refl _ _
  | cons origin rest ih =>
    unfold Detail.defaultIntegerLiteralTargets at accepted
    cases head : Detail.defaultIntegerLiteralTarget before origin with
    | error error => simp [head,bind,Except.bind] at accepted
    | ok next =>
      simp only [head,bind,Except.bind] at accepted
      exact (defaultIntegerLiteralTarget_private head).trans (ih accepted)

/-- The exact public finalization result preserves every previously private
type. This follows from its two successful defaulting passes. -/
theorem finalize_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : SourceInference.Result}
    (accepted : Detail.finalize context type state roots = .ok result) :
    ∀ value, Safe protectedVars state value → Avoids protectedVars (result.substitution.apply value) := by
  let witness := Detail.finalize_success_witness accepted
  have through : SafeTransport protectedVars state witness.finalState := (defaultIntegerPatternTargets_private witness.patternDefault).trans
    (defaultIntegerLiteralTargets_private witness.literalDefault)
  intro value safe
  have finalSafe := through value safe
  have substEq : result.substitution = witness.finalState.inference.substitution :=
    congrArg SourceInference.Result.substitution witness.result_eq
  rw [substEq]
  exact finalSafe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyForContinuation
/-! The real for initializer, condition, body and post sequence preserves
private scheme variables, including both lexical-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferStatementFuel_for_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (initializerIH : InferForItemsFuelPrivacy protectedVars fuel context initializer initial.allocateStatementId.2)
    (conditionIH : ∀ initialized : InferredForItems,
      InferExprFuelPrivacy protectedVars fuel context condition (some .bool) initialized.state)
    (bodyIH : ∀ state, InferStatementsFuelPrivacy protectedVars fuel
      {context with loopDepth := context.loopDepth + 1} body.value expectedReturn state)
    (postIH : ∀ (initialized : InferredForItems) (checkedBody : BlockResult),
      InferForItemsFuelPrivacy protectedVars fuel {context with loopDepth := context.loopDepth + 1} post
        (checkedBody.state.restoreLexicalScope initialized.state.lexicalScope)) :
    InferStatementFuelPrivacy protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
  let id := initial.allocateStatementId.1
  let allocated := initial.allocateStatementId.2
  let loopContext := {context with loopDepth := context.loopDepth + 1}
  have allocationEq : initial.allocateStatementId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocatedPrivacy
  unfold inferStatementFuel at success
  simp only [allocationEq, form, bind, Except.bind] at success
  cases initializerRun : inferForItemsFuel fuel context initializer allocated with
  | error error => simp [initializerRun] at success
  | ok initialized =>
    simp only [initializerRun] at success
    have initProperties := inferForItemsFuel_inferenceProperties allocatedReady validated canonical initializerRun
    have initPrivacy := initializerIH allocatedReady wellFormed bound allocatedLive catalog validated canonical initialized initializerRun
    have initWellFormed := (inferForItemsFuel_direct_progress initializerRun).wellFormed wellFormed
    cases conditionRun : inferExprFuel fuel context condition (some .bool) initialized.state with
    | error error => simp [conditionRun] at success
    | ok conditionPair =>
      rcases conditionPair with ⟨checkedCondition, conditionState⟩
      simp only [conditionRun] at success
      have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow initialized.state.inference.next := by
        intro type member
        cases Option.mem_def.mp member
        exact Ty.variablesBelow_constructor _ _
      have boolSafe : ∀ type ∈ some Ty.bool, Safe protectedVars initialized.state type := by
        intro type member
        cases Option.mem_def.mp member
        exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
      have conditionProperties := inferExprFuel_inferenceProperties initProperties.2 validated canonical boolBelow conditionRun
      have conditionPrivacy := conditionIH initialized initProperties.2 initWellFormed
        (fun v member => Nat.lt_of_lt_of_le (bound v member) initProperties.1.next_le)
        initPrivacy.2.1 catalog validated canonical boolBelow boolSafe (checkedCondition,conditionState) conditionRun
      have conditionWellFormed := (inferExprFuel_direct_progress conditionRun).wellFormed initWellFormed
      have throughCondition := initProperties.1.trans conditionProperties.1
      have privacyThroughCondition := initPrivacy.1.trans conditionPrivacy.1
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expectedReturn conditionState with
      | error error => simp [loopContext,bodyRun] at success
      | ok checkedBody =>
        simp only [loopContext,bodyRun] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext)
          conditionProperties.2.1 validated (fun signature member => canonical signature member)
          (returnBelow.weaken throughCondition.next_le) bodyRun
        have bodyPrivacy := bodyIH conditionState conditionProperties.2.1 conditionWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) throughCondition.next_le)
          conditionPrivacy.2.2.1 catalog validated (fun signature member => canonical signature member)
          (returnBelow.weaken throughCondition.next_le)
          (privacyThroughCondition _ returnSafe) checkedBody bodyRun
        let afterBody := checkedBody.state.restoreLexicalScope initialized.state.lexicalScope
        have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
          (conditionProperties.1.trans bodyProperties.1)
        have restoredPrivacy : SafeTransport protectedVars checkedBody.state afterBody := .of_substitution_eq rfl
        have conditionBodyPrivacy := conditionPrivacy.1.trans bodyPrivacy.1
        have afterBodyLive : LiveBindersSafe protectedVars afterBody := initPrivacy.2.1.restore conditionBodyPrivacy
        have afterBodyWellFormed : afterBody.RequirementsWellFormed :=
          State.restoreLexicalScope_preserves_requirementsWellFormed _ _
            ((inferStatementsFuel_direct_progress bodyRun).wellFormed conditionWellFormed)
        have throughBody := initProperties.1.trans restoredProperties.1
        cases postRun : inferForItemsFuel fuel loopContext post afterBody with
        | error error => simp [loopContext,afterBody,postRun] at success
        | ok checkedPost =>
          simp only [loopContext,afterBody,postRun,pure,Pure.pure,Except.pure,Except.ok.injEq] at success
          subst result
          have postPrivacy := postIH initialized checkedBody restoredProperties.2 afterBodyWellFormed
            (fun v member => Nat.lt_of_lt_of_le (bound v member) throughBody.next_le)
            afterBodyLive catalog validated (fun signature member => canonical signature member) checkedPost postRun
          have privacyThroughPost := privacyThroughCondition.trans (bodyPrivacy.1.trans (restoredPrivacy.trans postPrivacy.1))
          let restored := checkedPost.state.restoreLexicalScope allocated.lexicalScope
          let node : Node := .statement {
            id,span := statement.span,type := .unit,
            form := .forLoop initialized.items checkedCondition.id checkedPost.items checkedBody.statements }
          have finalPrivacy : SafeTransport protectedVars checkedPost.state (restored.recordNode node) := .of_substitution_eq rfl
          have finalLive : LiveBindersSafe protectedVars (restored.recordNode node) :=
            (allocatedLive.restore privacyThroughPost).transport rfl (.of_substitution_eq rfl)
          refine ⟨allocatedPrivacy.trans (privacyThroughPost.trans finalPrivacy), safe_closed _ _ (Ty.variablesBelow_constructor _ _), finalLive, ?_⟩
          have bodyRows := new_requirements_trans
            (new_requirements_trans initPrivacy.2.2 conditionPrivacy.2.2.2 conditionPrivacy.1)
            bodyPrivacy.2.2.2 bodyPrivacy.1
          have restoredRows : ∀ row ∈ afterBody.requirements, row ∉ allocated.requirements → PredicateSafe protectedVars afterBody row.predicate := by
            intro row member fresh type typeMember
            exact restoredPrivacy _ (bodyRows row member fresh type typeMember)
          have postRows := new_requirements_trans restoredRows postPrivacy.2.2 postPrivacy.1
          intro row member fresh type typeMember
          exact finalPrivacy _ (postRows row member fresh type typeMember)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyMatchContinuation
/-! A match arm follows its real pattern and body calls, restores the saved
lexical scope, and passes the reached state to the remaining arms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferMatchCasesFuel_cons_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial : State}
    (bodyIH : ∀ state, InferStatementsFuelPrivacy protectedVars fuel context
      arm.value.body.value expectedReturn state)
    (tailIH : ∀ body : BlockResult, InferMatchCasesFuelPrivacy protectedVars fuel
      context scrutineeType expectedReturn outerScope rest
      (body.state.restoreLexicalScope outerScope)) :
    InferMatchCasesFuelPrivacy protectedVars (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial := by
  intro ready wellFormed bound live catalog validated canonical scrutineeBelow
    scrutineeSafe returnBelow returnSafe scopeEq result accepted
  subst outerScope
  unfold inferMatchCasesFuel at accepted
  simp only [bind, Except.bind] at accepted
  cases patternRun : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial with
  | error error => simp [patternRun] at accepted
  | ok patternPair =>
    rcases patternPair with ⟨pattern, patternState⟩
    simp only [patternRun] at accepted
    cases bodyRun : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState with
    | error error => simp [bodyRun] at accepted
    | ok body =>
      simp only [bodyRun] at accepted
      cases tailRun : inferMatchCasesFuel fuel context scrutineeType expectedReturn initial.lexicalScope
          rest (body.state.restoreLexicalScope initial.lexicalScope) with
      | error error => simp [tailRun] at accepted
      | ok tail =>
        simp only [tailRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have patternProperties := inferMatchPatternFuel_inferenceProperties ready
          scrutineeBelow validated patternRun
        have patternPrivacy := inferMatchPatternFuel_private ready scrutineeBelow validated
          bound scrutineeSafe live patternRun
        have patternWellFormed := (inferMatchPatternFuel_direct_progress patternRun).wellFormed wellFormed
        have returnAtPattern := returnBelow.weaken patternProperties.1.next_le
        have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
          validated canonical returnAtPattern bodyRun
        have bodyPrivacy := bodyIH patternState patternProperties.2.1 patternWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) patternProperties.1.next_le)
          patternPrivacy.2.1 catalog validated canonical returnAtPattern
          (patternPrivacy.1 _ returnSafe) body bodyRun
        have throughBody := patternProperties.1.trans bodyProperties.1
        have privacyThroughBody := patternPrivacy.1.trans bodyPrivacy.1
        have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
        let restored := body.state.restoreLexicalScope initial.lexicalScope
        have restoredPrivacy : SafeTransport protectedVars body.state restored := .of_substitution_eq rfl
        have privacyThroughRestored := privacyThroughBody.trans restoredPrivacy
        have restoredLive : LiveBindersSafe protectedVars restored := live.restore privacyThroughBody
        have restoredWellFormed : restored.RequirementsWellFormed :=
          State.restoreLexicalScope_preserves_requirementsWellFormed body.state initial.lexicalScope
            ((inferStatementsFuel_direct_progress bodyRun).wellFormed patternWellFormed)
        have tailPrivacy := tailIH body restoredProperties.2 restoredWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) restoredProperties.1.next_le)
          restoredLive catalog validated canonical
          (scrutineeBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ scrutineeSafe)
          (returnBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ returnSafe) (by simp) tail tailRun
        refine ⟨privacyThroughRestored.trans tailPrivacy.1, tailPrivacy.2.1, ?_⟩
        have bodyRows := new_requirements_trans patternPrivacy.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
        have restoredRows : ∀ row ∈ restored.requirements, row ∉ initial.requirements →
            PredicateSafe protectedVars restored row.predicate := by
          intro row member fresh type typeMember
          exact restoredPrivacy _ (bodyRows row member fresh type typeMember)
        exact new_requirements_trans restoredRows tailPrivacy.2.2 tailPrivacy.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyMatchStatement
/-! Real match statement inference preserves scheme privacy through ordered
scrutinees, all arms, optional default inference and actual scope restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private def finishMatch (fuel : Nat) (context : SourceInference.Context)
    (statement : Syntax.Statement) (id : StatementId) (hidden : Resolved.LocalId)
    (scrutinee : InferredExpression) (arms : Syntax.Located Syntax.MatchArmsValue)
    (expectedReturn : Ty) (state : State) : Except Error StatementResult := do
  let outerScope := state.lexicalScope
  let checked ← inferMatchCasesFuel fuel context scrutinee.type expectedReturn outerScope arms.value.cases state
  let (defaultBody,state) ← match arms.value.defaultBody with
    | none => pure (none,checked.state)
    | some body => do
      let inferred ← inferStatementsFuel fuel context body.value expectedReturn checked.state
      pure (some (inferred.statements,inferred.sawReturn),inferred.state.restoreLexicalScope outerScope)
  let exhaustive := checked.hasWildcard || defaultBody.isSome ||
    exhaustsNominalConstructors context state scrutinee.type checked.cases
  if !exhaustive then throw (.nonExhaustiveMatch statement.span) else
    let requirements := checked.cases.flatMap fun arm => arm.pattern.requirements
    let defaultStatements := defaultBody.map (·.1)
    let defaultReturns := defaultBody.map (·.2) |>.getD true
    let sawReturn := checked.allReturn && defaultReturns
    let type := if sawReturn then state.resolve expectedReturn else .unit
    let state := state.recordNode (.statement {
      id := id
      span := statement.span
      type := type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee := hidden
        cases := checked.cases
        defaultBody := defaultStatements
        requirements := requirements
      }
    })
    pure {
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := state
    }


private theorem finishMatch_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (bound : ∀ v ∈ protectedVars, v.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (scrutineeSafe : Safe protectedVars state scrutinee.type)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnSafe : Safe protectedVars state expectedReturn)
    (casesIH : InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    {result : StatementResult}
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready validated canonical scrutineeBelow returnBelow rfl casesRun
    have casesPrivacy := casesIH ready wellFormed bound live catalog validated canonical
      scrutineeBelow scrutineeSafe returnBelow returnSafe rfl checked casesRun
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        refine ⟨casesPrivacy.1, ?_, casesPrivacy.2.1.transport rfl (.of_substitution_eq rfl), casesPrivacy.2.2⟩
        split
        · exact safe_resolved (state := checked.state) casesProperties.2.1 (casesPrivacy.1 _ returnSafe)
        · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 validated canonical
          (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrivacy := bodyIH checked body casesProperties.2.1
          ((inferMatchCasesFuel_direct_progress casesRun).wellFormed wellFormed)
          (fun v member => Nat.lt_of_lt_of_le (bound v member) casesProperties.1.next_le)
          casesPrivacy.2.1 catalog validated canonical (returnBelow.weaken casesProperties.1.next_le)
          (casesPrivacy.1 _ returnSafe) checkedBody bodyRun
        have through := casesPrivacy.1.trans bodyPrivacy.1
        have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
          (casesProperties.1.trans bodyProperties.1)).2
        have restoredLive := live.restore through
        have rows := new_requirements_trans casesPrivacy.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
        split at success
        · cases success
        · injection success with resultEq
          subst result
          refine ⟨through, ?_, restoredLive.transport rfl (.of_substitution_eq rfl), rows⟩
          split
          · exact safe_resolved (state := checkedBody.state.restoreLexicalScope state.lexicalScope) restoredReady (through _ returnSafe)
          · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

theorem inferStatementFuel_match_single_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {source : Syntax.Expr} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (single : scrutinees.elements.toList = [source])
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    (sourceIH : InferExprFuelPrivacy protectedVars fuel context source none initial.allocateStatementId.2) :
    InferStatementFuelPrivacy protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form,single,bind,Except.bind] at success
  cases sourceRun : inferExprFuel fuel context source none allocated with
  | error error => simp [allocated,sourceRun] at success
  | ok pair =>
    rcases pair with ⟨scrutinee,sourceState⟩
    simp only [allocated,sourceRun] at success
    have sourceProperties := inferExprFuel_inferenceProperties allocatedReady validated canonical (by simp) sourceRun
    have sourcePrivacy := sourceIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (by simp) (by simp) (scrutinee,sourceState) sourceRun
    let hiddenState := sourceState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal sourceProperties.2.1
    have hiddenPrivacy : SafeTransport protectedVars sourceState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 sourceState.allocateHiddenLocal.1
        scrutinee arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_private hiddenReady
      ((inferExprFuel_direct_progress sourceRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) sourceProperties.1.next_le)
      (sourcePrivacy.2.2.1.transport rfl hiddenPrivacy) catalog validated canonical sourceProperties.2.2
      (hiddenPrivacy _ sourcePrivacy.2.1) (returnBelow.weaken sourceProperties.1.next_le)
      (sourcePrivacy.1 _ returnSafe) (casesIH scrutinee hiddenState) bodyIH finishRun
    exact ⟨allocatedPrivacy.trans (sourcePrivacy.1.trans (hiddenPrivacy.trans finished.1)),finished.2.1,finished.2.2.1,
      new_requirements_trans sourcePrivacy.2.2.2 finished.2.2.2 finished.1⟩


theorem inferStatementFuel_match_many_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (notSingleton : ∀ source, scrutinees.elements.toList = [source] → False)
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    (sourcesIH : InferExprsFuelPrivacy protectedVars fuel context scrutinees.elements.toList initial.allocateStatementId.2) :
    InferStatementFuelPrivacy protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form] at success
  simp only [bind,Except.bind] at success
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList initial.allocateStatementId.2 with
  | error error => simp [sourcesRun] at success
  | ok pair =>
    rcases pair with ⟨elements,elementState⟩
    simp only [sourcesRun,pure,Pure.pure,Except.pure] at success
    have properties := inferExprsFuel_inferenceProperties allocatedReady validated canonical sourcesRun
    have privacy := sourcesIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (elements,elementState) sourcesRun
    let tuple : InferredExpression := {id := elementState.allocateExpressionId.1,type := Ty.productMany (elements.map (·.type))}
    let tupleState := elementState.allocateExpressionId.2.recordNode (.expression {
      id := tuple.id
      span := statement.span
      type := tuple.type
      form := .tuple (elements.map (·.id)) })
    have tupleReady : tupleState.InferenceReady := State.InferenceReady.recordNode _
      (State.InferenceReady.allocateExpressionId properties.2.1)
    have tuplePrivacy : SafeTransport protectedVars elementState tupleState := .of_substitution_eq rfl
    have tupleBelow : tuple.type.VariablesBelow tupleState.inference.next := by
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember
    have tupleSafe : Safe protectedVars tupleState tuple.type := by
      apply safe_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact tuplePrivacy _ (privacy.2.1 element elementMember)
    let hiddenState := tupleState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal tupleReady
    have hiddenPrivacy : SafeTransport protectedVars tupleState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 tupleState.allocateHiddenLocal.1
        tuple arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_private hiddenReady
      ((inferExprsFuel_direct_progress sourcesRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) properties.1.next_le)
      ((privacy.2.2.1.transport rfl tuplePrivacy).transport rfl hiddenPrivacy) catalog validated canonical tupleBelow
      (hiddenPrivacy _ tupleSafe) (returnBelow.weaken properties.1.next_le)
      (privacy.1 _ returnSafe) (casesIH tuple hiddenState) bodyIH finishRun
    exact ⟨allocatedPrivacy.trans (privacy.1.trans (tuplePrivacy.trans (hiddenPrivacy.trans finished.1))),finished.2.1,finished.2.2.1,
      new_requirements_trans privacy.2.2.2 finished.2.2.2 finished.1⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
