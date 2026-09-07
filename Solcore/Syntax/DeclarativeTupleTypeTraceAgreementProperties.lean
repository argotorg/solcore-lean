import Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceAgreementProperties

/-! Pairwise child outcome agreement lifts through the raw tuple list. Neither
child relation needs its own functionality, existence, or carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem tupleTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (TupleTypeTraceParses leftParses) (TupleTypeTraceRejects leftParses leftRejects)
      (TupleTypeTraceParses rightParses) (TupleTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed elements =>
        cases right with
        | parsed other =>
            rcases elements.result_agree children.successResultAgree other with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := left.result_agree children right
  successRejectDisjoint parsed rejected := by
    cases parsed with
    | parsed elements => exact elements.disjoint_rejection_of_agreement children rejected
  rejectSuccessDisjoint rejected parsed := by
    cases parsed with
    | parsed elements => exact rejected.disjoint_success_of_agreement children elements

end Solcore.Syntax.DeclarativeGrammar
