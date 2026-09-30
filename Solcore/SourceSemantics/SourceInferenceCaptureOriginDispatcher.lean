import Solcore.SourceSemantics.SourceInferenceCaptureOrigins

/-!
Complete one-statement preservation of raw initialized-binder capture origins.
Unlike semantic typing, this invariant follows from the actual executable
statement result alone: initialized lets record their binder, ordinary
statements preserve the lexical stack, and scoped constructs restore it.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Every successful source statement preserves capture provenance relative
to the one raw source which will be passed to finalization. -/
theorem inferStatementFuel_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial evidenceState : State} {result : Detail.StatementResult}
    {roots : List NodeId}
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ fuel =>
      cases allocationEq : initial.allocateStatementId with
      | mk id allocated =>
          cases statementEq : statement.value with
          | letDecl name sourceType initializer =>
              cases sourceType with
              | none =>
                  cases initializer with
                  | none =>
                      simp [Detail.inferStatementFuel, allocationEq,
                        statementEq] at success
                      change (Except.error (.missingInitializer name.value) :
                        Except Frontend.SourceInference.Error
                          Detail.StatementResult) = .ok result at success
                      cases success
                  | some initializer =>
                      exact inferStatementFuel_letUnannotatedInitialized_captureOrigins
                        statementEq allocationEq success origins
                        resultToEvidence
              | some sourceType =>
                  cases initializer with
                  | none =>
                      exact inferStatementFuel_letAnnotatedUninitialized_captureOrigins
                        statementEq allocationEq success origins
                  | some initializer =>
                      exact inferStatementFuel_letAnnotatedInitialized_captureOrigins
                        statementEq allocationEq success origins
                        resultToEvidence
          | returnStmt value =>
              cases value with
              | none =>
                  exact inferStatementFuel_returnUnit_captureOrigins
                    statementEq allocationEq success origins
              | some value =>
                  exact inferStatementFuel_returnValue_captureOrigins
                    statementEq allocationEq success origins
          | expression expression trailingSemicolon =>
              exact inferStatementFuel_expression_captureOrigins
                statementEq allocationEq success origins
          | assignValue target operator value =>
              exact inferStatementFuel_assignValue_captureOrigins
                statementEq allocationEq success origins
          | assignBitNot target operatorSpan =>
              exact inferStatementFuel_assignBitNot_captureOrigins
                statementEq allocationEq success origins
          | matchWith scrutinees arms =>
              cases defaultEq : arms.value.defaultBody with
              | none =>
                  exact inferStatementFuel_matchWithoutDefault_captureOrigins
                    statementEq defaultEq allocationEq success origins
              | some defaultBody =>
                  exact inferStatementFuel_matchWithDefault_captureOrigins
                    statementEq defaultEq allocationEq success origins
          | forLoop headerSpan initializer condition post body =>
              exact inferStatementFuel_forLoop_captureOrigins statementEq
                allocationEq success origins
          | whileLoop condition body =>
              exact inferStatementFuel_whileLoop_captureOrigins statementEq
                allocationEq success origins
          | ifThen condition thenBody elseBody =>
              cases elseBody with
              | none =>
                  exact inferStatementFuel_ifWithoutElse_captureOrigins
                    statementEq allocationEq success origins
              | some elseBody =>
                  exact inferStatementFuel_ifWithElse_captureOrigins
                    statementEq allocationEq success origins
          | block body =>
              exact inferStatementFuel_block_captureOrigins statementEq
                allocationEq success origins
          | assembly body =>
              simp [Detail.inferStatementFuel, statementEq]
                at success
          | breakStmt =>
              exact inferStatementFuel_break_captureOrigins statementEq
                allocationEq success origins
          | continueStmt =>
              exact inferStatementFuel_continue_captureOrigins statementEq
                allocationEq success origins
          | error =>
              simp [Detail.inferStatementFuel, statementEq]
                at success

/-- The one-statement theorem composes over the executable statement-list
traversal.  Each prefix result is retained in the final raw evidence source,
so an initialized binder remains certified at every later lookup. -/
theorem inferStatementsFuel_captureOrigins
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {initial evidenceState : State} {result : Detail.BlockResult}
    {roots : List NodeId}
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn initial = .ok result)
    (below : initial.NodesBelowNextOccurrence)
    (origins : ActiveBinderCaptureOrigins initial
      (evidenceState.toTypedSource roots))
    (resultToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots)) :
    ActiveBinderCaptureOrigins result.state
      (evidenceState.toTypedSource roots) := by
  induction fuel generalizing statements initial result with
  | zero => simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          simp [Detail.inferStatementsFuel] at success
          subst result
          exact origins
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              have headToEvidence : TypingSourceExtends
                  (head.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                simpa only [resultEq] using resultToEvidence
              have headOrigins := inferStatementFuel_captureOrigins
                headSuccess origins headToEvidence
              simpa only [resultEq] using headOrigins
          | cons next tail =>
              obtain ⟨head, restResult, headSuccess, tailSuccess,
                  resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              have headBelow : head.state.NodesBelowNextOccurrence :=
                (Detail.inferStatementFuel_occurrenceBoundExtends
                  headSuccess).nodesBelowNextOccurrence below
              have tailToEvidence : TypingSourceExtends
                  (restResult.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) := by
                simpa only [resultEq] using resultToEvidence
              have headToEvidence : TypingSourceExtends
                  (head.state.toTypedSource roots)
                  (evidenceState.toTypedSource roots) :=
                (inferStatementsFuel_success_typingSourceExtends tailSuccess
                  headBelow roots).trans tailToEvidence
              have headOrigins := inferStatementFuel_captureOrigins
                headSuccess origins headToEvidence
              have restOrigins := induction tailSuccess headBelow headOrigins
                tailToEvidence
              simpa only [resultEq] using restOrigins

end Solcore.SourceSemantics.SourceInferenceSoundness
