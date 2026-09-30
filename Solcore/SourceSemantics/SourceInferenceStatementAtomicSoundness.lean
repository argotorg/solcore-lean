import Solcore.SourceSemantics.SourceInferenceStatementLocalBound

/-!
Closed typing branches for source statements with no recursively inferred
child.  Each theorem consumes an actual successful frontend trace and returns
the exact result shape expected by the recursive statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A bare return is sound after its actual unit/return-type unification. -/
theorem inferStatementFuel_returnUnit_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_returnUnit_sound statementEq
    allocationEq success invariant outerExtension roots⟩

/-- The successful loop-depth guard supplies precisely the declarative
`break` premise. -/
theorem inferStatementFuel_break_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_break_sound statementEq
    allocationEq success invariant roots⟩

/-- Successful `continue` uses the same loop-depth guard while preserving its
distinct control outcome. -/
theorem inferStatementFuel_continue_atomicBranch
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {roots : List NodeId}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  exact ⟨target, _, inferStatementFuel_success_continue_sound statementEq
    allocationEq success invariant roots⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
