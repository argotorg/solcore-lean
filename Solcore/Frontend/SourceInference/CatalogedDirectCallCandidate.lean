import Solcore.Frontend.SourceInference.CatalogedDirectCallProgress

/-! The actual selected candidate supplies the ordinary catalog declaration
before its newly issued requirement batch is recorded on the source call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
open TypeSystem Detail DirectCallEvents
variable {catalog : List Resolved.DeclarationId}

/-- Recording discharges the exact pending batch together with its actual
selected declaration. No typing judgment is used to identify that declaration. -/
theorem recordSelectedCallResult_pending
    {before state : State} {attempt : CandidateAttemptResult}
    (nodes : state.nodes = before.nodes)
    (direct : state.directCallRequirements = before.directCallRequirements ++ attempt.signatureRequirements)
    (cataloged : attempt.instantiation.declaration ∈ catalog)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (result : InferredExpression) (trailing : List CoercionStep) :
    Progress catalog before (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  rw [recordSelectedCallResult_direct_unchanged, direct] at member
  rcases List.mem_append.mp member with prior | fresh
  · have original : HasCall catalog state.nodes requirement := by
      rw [nodes]
      exact origins requirement prior
    apply (original.attachExpressionCoercions attempt.argumentCoercions).mono
    intro node present
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · let calleeId := (Detail.attachExpressionCoercions state attempt.argumentCoercions).allocateExpressionId.1
    let callNode : ExpressionNode := {
      id := result.id, span := source.span, type := result.type
      form := .call calleeId (arguments.map (·.id)) (.declaration attempt.instantiation)
      requirements := coercionRequirements attempt.callCoercions ++ attempt.signatureRequirements ++
        coercionRequirements trailing
      coercions := attempt.callCoercions ++ trailing }
    refine ⟨callNode, ?_, calleeId, arguments.map (·.id), attempt.instantiation, rfl, ?_, cataloged⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ fresh)

theorem selected_catalog
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions) :
    attempt.instantiation.declaration ∈ context.signatures.functions.map (·.id) := by
  obtain ⟨signature, present, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  rw [tryFunctionCandidate_some_instantiation selected]
  exact List.mem_map.mpr ⟨signature, cataloged present, rfl⟩

namespace Progress

theorem selectAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_pending (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_batch accepted) (selected_catalog accepted cataloged)
    source callee name arguments _ _

theorem selectFitAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected selectedExpected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {fitted : ExpectationResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call selectedExpected state = .ok attempt)
    (fit : Detail.withExpected context attempt.state attempt.result expected = .ok fitted)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCallResult source callee name arguments attempt
        fitted.expression fitted.coercions fitted.state).2 :=
  recordSelectedCallResult_pending
    ((withExpected_occurrenceState_eq fit).1.trans (selectFunctionCandidateFrom_occurrenceState_eq accepted).1)
    ((withExpected_direct_eq fit).trans (selectFunctionCandidateFrom_direct_batch accepted))
    (selected_catalog accepted cataloged) source callee name arguments _ _

end Progress
end Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
