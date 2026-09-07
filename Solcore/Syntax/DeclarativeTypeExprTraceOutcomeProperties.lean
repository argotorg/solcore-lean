import Solcore.Syntax.DeclarativeTypeExprTraceInductionProperties
import Solcore.Syntax.DeclarativeTypeDispatchTraceAgreementProperties

/-! Recursive trace exactness follows by simultaneous strong induction on the
left derivation. Left children carry the least derivation and its induction
property; right children are arbitrary least derivations. Only the right root
is unrolled. No uniform recursive uniqueness or outcome existence is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private def agreesWithLeast : TypeTraceQuery → Prop
  | .success source endByte input value output trace =>
      (∀ {other after events}, TypeExprTraceParses source endByte input other after events →
        value = other ∧ output = after ∧ trace = events) ∧
      (∀ {rejected report events}, TypeExprTraceRejects source endByte input rejected report events → False)
  | .rejection source endByte input rejected report trace =>
      (∀ {after diagnostic events}, TypeExprTraceRejects source endByte input after diagnostic events →
        rejected = after ∧ report = diagnostic ∧ trace = events) ∧
      (∀ {value output events}, TypeExprTraceParses source endByte input value output events → False)

private def knownSuccess (source : SourceId) (endByte : Nat) (input : Remainder)
    (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  TypeExprTraceParses source endByte input value output trace ∧
    agreesWithLeast (.success source endByte input value output trace)

private def knownRejection (source : SourceId) (endByte : Nat) (input rejected : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  TypeExprTraceRejects source endByte input rejected report trace ∧
    agreesWithLeast (.rejection source endByte input rejected report trace)

private theorem knownChildren_agree (source : SourceId) (endByte : Nat) :
    TraceOutcomeAgreement knownSuccess knownRejection TypeExprTraceParses TypeExprTraceRejects source endByte where
  successResultAgree left right := left.2.1 right
  rejectResultAgree left right := left.2.1 right
  successRejectDisjoint left right := left.2.2 right
  rejectSuccessDisjoint left right := left.2.2 right

private theorem agreesWithLeast_closed (query : TypeTraceQuery)
    (step : TypeTraceLayer (fun query => TypeTraceLeast query ∧ agreesWithLeast query) query) :
    agreesWithLeast query := by
  cases query with
  | success source endByte input value output trace =>
      have agreement := typeDispatchTraceOutcomeAgreement (knownChildren_agree source endByte)
      constructor
      · intro other after events right
        exact agreement.successResultAgree step (TypeExprTraceParses.unroll_iff.mp right)
      · intro rejected report events right
        exact agreement.successRejectDisjoint step (TypeExprTraceRejects.unroll_iff.mp right)
  | rejection source endByte input rejected report trace =>
      have agreement := typeDispatchTraceOutcomeAgreement (knownChildren_agree source endByte)
      constructor
      · intro after diagnostic events right
        exact agreement.rejectResultAgree step (TypeExprTraceRejects.unroll_iff.mp right)
      · intro value output events right
        exact agreement.rejectSuccessDisjoint step (TypeExprTraceParses.unroll_iff.mp right)

theorem TypeExprTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : Syntax.TypeExpr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TypeExprTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : TypeExprTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  (TypeTraceLeast.strong_induction agreesWithLeast_closed leftParsed).1 rightParsed

theorem TypeExprTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftReport rightReport : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : TypeExprTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : TypeExprTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  (TypeTraceLeast.strong_induction agreesWithLeast_closed leftRejected).1 rightRejected

theorem TypeExprTraceParses.disjoint_rejection
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    ¬ ∃ rejected report events, TypeExprTraceRejects source endByte input rejected report events := by
  rintro ⟨rejected, report, events, rejection⟩
  exact (TypeTraceLeast.strong_induction agreesWithLeast_closed parsed).2 rejection

theorem TypeExprTraceRejects.disjoint_success
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TypeExprTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact (TypeTraceLeast.strong_induction agreesWithLeast_closed rejection).2 parsed

theorem typeExprTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec TypeExprTraceParses TypeExprTraceRejects source endByte where
  successResultUnique := TypeExprTraceParses.result_unique
  rejectResultUnique := TypeExprTraceRejects.result_unique
  successRejectDisjoint := TypeExprTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
