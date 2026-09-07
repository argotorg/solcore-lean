import Solcore.Syntax.DeclarativeFunctionReturnsTraceGrammar
import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceAgreementProperties

/-! Distinct child relations agree through optional returns. Exact contextual
marker presence separates the silent absent success from every rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem functionReturnsTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (FunctionReturnsTraceParses leftParses)
      (FunctionReturnsTraceRejects leftParses leftRejects)
      (FunctionReturnsTraceParses rightParses)
      (FunctionReturnsTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | absent absent =>
        cases right with
        | absent => exact ⟨rfl, rfl, rfl⟩
        | present span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
    | present span marker values =>
        cases right with
        | absent absent => exact False.elim (absent ⟨span, marker.1⟩)
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases values.result_agree children.successResultAgree otherValues with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | present _ marker values =>
        cases right with
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact values.result_agree children otherValues
  successRejectDisjoint parsed rejected := by
    cases rejected with
    | present span marker values =>
        cases parsed with
        | absent absent => exact absent ⟨span, marker.1⟩
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact otherValues.disjoint_rejection_of_agreement children values
  rejectSuccessDisjoint rejected parsed := by
    cases rejected with
    | present span marker values =>
        cases parsed with
        | absent absent => exact absent ⟨span, marker.1⟩
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact values.disjoint_success_of_agreement children otherValues

end Solcore.Syntax.DeclarativeGrammar
