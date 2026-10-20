import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyGeneralization

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
