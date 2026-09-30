import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.Dynamic.Control

/-!
The final step from a declaratively typed list of inferred statement roots to
the whole-body typing judgment.  This isolates the control-completion argument
from the recursive inference-soundness proof.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

private theorem statementRoots_filterMap (statements : List StatementId) :
    (statements.map NodeId.statement).filterMap (fun root =>
      match root with
      | .statement statement => some statement
      | .expression _ => none) = statements := by
  induction statements with
  | nil => rfl
  | cons statement rest induction => simp [induction]

/-- A typed statement list with the checker's exact root layout and result
annotation satisfies the complete declaration-body judgment. -/
theorem bodyHasType_of_statementRoots
    {source : TypedSource} {context finalContext : SourceSemantics.Context}
    {statements : List StatementId} {expected : Ty} {facts : BodyFacts}
    (roots : source.roots = statements.map NodeId.statement)
    (typing : StatementsHaveType source { returnType := expected } context
      statements finalContext facts)
    (resultType : facts.type = expected) :
    BodyHasType source context expected facts := by
  refine ⟨finalContext, ?_, ?_, ?_⟩
  · have selected :
        source.roots.filterMap (fun root =>
          match root with
          | .statement statement => some statement
          | .expression _ => none) = statements := by
        rw [roots]
        exact statementRoots_filterMap statements
    exact selected.symm ▸ typing
  · intro expression member
    simp [roots] at member
  · exact typing.bodyCompletes_of_closed rfl resultType

/-- Finalization leaves the statement-root list unchanged.  In particular,
the checker cannot emit an expression root for a top-level body. -/
theorem finalize_statementRoots
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : Frontend.SourceInference.State}
    {statements : List StatementId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state
      (statements.map NodeId.statement) = .ok result) :
    result.typedSource.roots = statements.map NodeId.statement := by
  rw [Detail.finalize_typedSource success]
  simp [Frontend.SourceInference.State.toTypedSource]

/-- A successful whole-body check retains precisely the roots produced by
statement inference, with no expression roots inserted by finalization. -/
theorem checkFunctionBody_success_statementRoots
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ body : Detail.BlockResult,
      checked.typedBody.roots = body.statements.map NodeId.statement := by
  obtain ⟨_, body, _, result, _, _, _, finalized, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact ⟨body, finalize_statementRoots finalized⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
