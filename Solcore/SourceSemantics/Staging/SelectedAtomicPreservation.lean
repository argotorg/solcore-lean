import Solcore.SourceSemantics.Staging.SelectedPreservationContracts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- Atomic evaluation performs no nested call. Captures use the original source and environment. -/
theorem atomic_value
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {value : Value}
    {rawType : Ty} {plan : ExpressionRequirementPlan}
    (runtime : SourceRuntimeValid program context source)
    (evidence_covers : evidence.Covers context)
    (environment_agrees : EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (occurrence : ∃ id node, ContainsExpression source id node ∧ node.form = form ∧ node.rawType = rawType)
    (typing : ExpressionFormHasRawType source context form rawType plan)
    (atomic : AtomicForm form)
    (evaluation : ExpressionFormEvaluates program context evidence source environment before
      form requirements coercions value after) :
    ExpressionEvaluationPreserved context before after value rawType := by
  cases atomic with
  | unit =>
    cases evaluation with
    | tuple layout elements pack =>
      cases elements
      cases pack
      cases typing with
      | tuple types => cases types; exact ⟨.unit, before_typed, .refl _⟩
  | literal literal =>
    cases evaluation with
    | literal layout constructs =>
      cases typing with
      | literal valid => exact ⟨constructs.hasType, before_typed, .refl _⟩
  | integerLiteral source resolution =>
    cases evaluation with
    | integerLiteral layout constructs =>
      cases typing with
      | integerLiteral valid => exact ⟨constructs.hasType, before_typed, .refl _⟩
  | reference name resolution =>
    obtain ⟨valueTyped, heapTyped, extended⟩ := evaluation.referencePreserves environment_agrees before_typed typing
    exact ⟨valueTyped, heapTyped, extended⟩
  | proxy inner =>
    cases evaluation with
    | proxy layout =>
      cases typing with
      | proxy valid => exact ⟨.proxy _, before_typed, .refl _⟩
  | lambda parameters returnType body =>
    cases evaluation with
    | lambda layout =>
      cases typing with
      | @lambda _ lambdaContext finalContext parameters parameterTypes returnType
          body bodyFacts names_unique parameters_extend body_type body_completes =>
        rcases occurrence with ⟨id, node, contains, node_form, node_raw⟩
        have body_types := MonoBindersExtend.bodyTypes_eq parameters_extend
        have form_typed := ExpressionFormHasRawType.lambda names_unique parameters_extend body_type body_completes
        have code : ClosureCodeValid context {
            parameters := parameters, resultType := returnType, body := body,
            source := source, captured := environment, context := context, evidence := evidence } := {
          owner := runtime.owner
          closed := runtime.closed
          variables_closed := runtime.variables_closed
          residual_variables_open := runtime.residual_variables_open
          graph := runtime.graph
          requirement_ledger := runtime.requirements
          occurrence := ⟨id, node, contains, node_form, by simpa [body_types] using node_raw, by
            rw [node_form]; simpa [body_types] using form_typed⟩ }
        exact ⟨by
          simpa [body_types] using (ValueHasType.closure (context := context) (heap := before)
            (function := {
              parameters := parameters
              resultType := returnType
              body := body
              source := source
              captured := environment
              context := context
              evidence := evidence })
            rfl code evidence_covers environment_agrees), before_typed, .refl _⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
