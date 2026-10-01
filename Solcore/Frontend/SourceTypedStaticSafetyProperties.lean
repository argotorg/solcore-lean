import Solcore.Frontend.SourceRuntimeDeepValidation

/-!
Static lookup provenance for source-typed runtime lambdas.

These lemmas identify the exact checked specialization and occurrence table
from which a lambda node was selected. They intentionally do not infer body
typing from an arbitrary `CheckedFunction` record: that stronger claim needs a
separate source-checker soundness certificate.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem SourceCompilationPlan

/-- A successful exact runtime lookup selects a member of the finite plan
whose key is precisely the requested key. -/
theorem exactSpecialization_member_and_key
    (plan : Plan) (key : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (selected : exactSpecialization plan key = .ok specialized) :
    specialized ∈ plan.specializations ∧ specialized.key = key := by
  unfold exactSpecialization at selected
  cases filtered : plan.specializations.filter (fun candidate =>
      decide (candidate.key = key)) with
  | nil =>
      rw [filtered] at selected
      cases selected
  | cons first rest =>
      cases rest with
      | nil =>
          rw [filtered] at selected
          cases selected
          have member : specialized ∈ plan.specializations.filter (fun candidate =>
              decide (candidate.key = key)) := by
            rw [filtered]
            simp
          obtain ⟨inPlan, matching⟩ := List.mem_filter.mp member
          exact ⟨inPlan, of_decide_eq_true matching⟩
      | cons second tail =>
          rw [filtered] at selected
          cases selected

/-- A successful typed expression lookup really returns a node in the
function's heterogeneous occurrence table, at the queried occurrence. -/
theorem lookupExpression_member_and_occurrence
    (source : TypedSource) (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node) :
    Node.expression node ∈ source.nodes ∧
      node.id.occurrence = id.occurrence := by
  unfold TypedSource.lookupExpression? at found
  cases lookup : source.lookupNode? id.occurrence with
  | none =>
      rw [lookup] at found
      cases found
  | some selected =>
      rw [lookup] at found
      cases selected with
      | statement statement => cases found
      | expression expression =>
          cases found
          unfold TypedSource.lookupNode? at lookup
          have member : Node.expression node ∈ source.nodes :=
            List.mem_of_find?_eq_some lookup
          have sameOccurrence :
              decide ((Node.expression node).occurrenceId =
                id.occurrence) = true := by
            exact List.find?_some (p := fun selected : Node =>
              decide (selected.occurrenceId = id.occurrence)) lookup
          exact ⟨member, of_decide_eq_true sameOccurrence⟩

/-- The smallest static lambda-annotation contract needed by the evaluator.
It is deliberately a separate certificate: an arbitrary `CheckedFunction`
record, or the runtime's executable-profile preflight, does not establish it.
The source inference soundness proof should eventually produce this for every
specialization in the canonical plan. -/
def Plan.LambdaAnnotationsAgree (plan : Plan) : Prop :=
  ∀ specialized, specialized ∈ plan.specializations →
    ∀ node, Node.expression node ∈ specialized.function.typedBody.nodes →
      ∀ parameters resultType body,
        node.form = .lambda parameters resultType body →
          node.type = .function
            (Ty.productMany (parameters.map (·.scheme.body))) resultType

/-- A plan-level lambda annotation certificate discharges the node-type
premise used when the typed evaluator creates a closure. -/
theorem exactLambdaNode_hasFunctionType
    (plan : Plan) (owner : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId)
    (annotations : plan.LambdaAnnotationsAgree)
    (selected : exactSpecialization plan owner = .ok specialized)
    (found : specialized.function.typedBody.lookupExpression? id = some node)
    (shape : node.form = .lambda parameters resultType body) :
    node.type = .function
      (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  have inPlan := (exactSpecialization_member_and_key plan owner specialized
    selected).1
  have inSource := (lookupExpression_member_and_occurrence
    specialized.function.typedBody id node found).1
  exact annotations specialized inPlan node inSource parameters resultType
    body shape

/-- The static component of a runtime lambda certificate: its selected owner
and annotated function type come from one node in that checked function's
source table. The annotation equality is an explicit premise, not a theorem
of arbitrary, constructible checked IR. -/
theorem checkedLambdaNode_provenance
    (plan : Plan) (owner : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId)
    (selected : exactSpecialization plan owner = .ok specialized)
    (found : specialized.function.typedBody.lookupExpression? id = some node)
    (shape : node.form = .lambda parameters resultType body)
    (annotation : node.type = .function
      (Ty.productMany (parameters.map (·.scheme.body))) resultType) :
    specialized ∈ plan.specializations ∧
      specialized.key = owner ∧
      Node.expression node ∈ specialized.function.typedBody.nodes ∧
      node.id.occurrence = id.occurrence ∧
      node.form = .lambda parameters resultType body ∧
      node.type = .function
        (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  obtain ⟨inPlan, matchingKey⟩ :=
    exactSpecialization_member_and_key plan owner specialized selected
  obtain ⟨inSource, matchingOccurrence⟩ :=
    lookupExpression_member_and_occurrence specialized.function.typedBody
      id node found
  exact ⟨inPlan, matchingKey, inSource, matchingOccurrence, shape,
    annotation⟩

/-- A runtime closure's code-provenance invariant yields a concrete checked
lambda node in the selected specialization's source table, including its
annotated function type. This still does not certify the lambda *body's*
typing derivation. -/
theorem closure_hasPlanCode_checkedLambdaNode
    (plan : Plan) (owner : Key) (source : TypedSource)
    (environment : Environment) (parameters : List TypedBinder)
    (evidence : RuntimeEvidenceEnvironment)
    (resultType : Ty) (body : List StatementId)
    (code : (Value.closure parameters resultType body source owner
      environment evidence).HasPlanCode plan) :
    ∃ (specialized : SourceSpecialization.SpecializedFunction)
      (id : ExpressionId) (node : ExpressionNode),
      validateExecutablePlan plan = .ok () ∧
      exactSpecialization plan owner = .ok specialized ∧
      specialized.function.typedBody = source ∧
      specialized ∈ plan.specializations ∧
      specialized.key = owner ∧
      Node.expression node ∈ source.nodes ∧
      node.id.occurrence = id.occurrence ∧
      node.form = .lambda parameters resultType body ∧
      node.type = .function
        (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  have first := code 1
  change validateExecutablePlan plan = .ok () ∧
    ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
      specialized.function.typedBody = source ∧
      ∃ id node, source.lookupExpression? id = some node ∧
        node.form = .lambda parameters resultType body ∧
        node.type = .function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType at first
  obtain ⟨validated, specialized, selected, sameSource,
    id, node, found, shape, annotation⟩ := first
  have foundInSpecialization :
      specialized.function.typedBody.lookupExpression? id = some node := by
    rw [sameSource]
    exact found
  obtain ⟨inPlan, matchingKey, inSpecialization, matchingOccurrence,
    _, _⟩ := checkedLambdaNode_provenance plan owner specialized id node
      parameters resultType body selected foundInSpecialization shape annotation
  refine ⟨specialized, id, node, validated, selected, sameSource, inPlan,
    matchingKey, ?_, matchingOccurrence, shape, annotation⟩
  simpa [sameSource] using inSpecialization

end Solcore.Frontend.SourceTypedRuntime
