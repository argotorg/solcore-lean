import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceAgreementProperties
import Solcore.Syntax.DeclarativeNamedTypeTraceOutcomeProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceOutcomeProperties

/-! Distinct child relations agree through optional arguments and raw named
types. Name checks and finishing events stay in their original order. No
functionality of either child relation by itself is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem namedTypeArgumentsTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (NamedTypeArgumentsTraceParses leftParses)
      (NamedTypeArgumentsTraceRejects leftParses leftRejects)
      (NamedTypeArgumentsTraceParses rightParses)
      (NamedTypeArgumentsTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | absent absent =>
        cases right with
        | absent => exact ⟨rfl, rfl, rfl⟩
        | present parsed => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
    | present parsed =>
        cases right with
        | absent absent => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
        | present other =>
            rename_i left right
            rcases parsed.result_agree children.successResultAgree other with ⟨same, rfl, rfl⟩
            have valuesEq : left = right := by
              cases left with
              | mk leftSpan leftValues =>
                  cases right with
                  | mk rightSpan rightValues =>
                      cases leftValues
                      cases rightValues
                      simp only [NonemptyList.toList, DelimitedList.mk.injEq, List.cons.injEq] at same
                      rcases same with ⟨rfl, rfl, rfl⟩
                      rfl
            exact ⟨congrArg some valuesEq, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | present _ _ left =>
        cases right with
        | present _ _ right => exact left.result_agree children right
  successRejectDisjoint parsed rejection := by
    cases rejection with
    | present span opening rejection =>
        cases parsed with
        | absent absent => exact absent ⟨span, opening⟩
        | present parsed => exact parsed.disjoint_rejection_of_agreement children rejection
  rejectSuccessDisjoint rejection parsed := by
    cases rejection with
    | present span opening rejection =>
        cases parsed with
        | absent absent => exact absent ⟨span, opening⟩
        | present parsed => exact rejection.disjoint_success_of_agreement children parsed

theorem namedTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (NamedTypeTraceParses leftParses)
      (NamedTypeTraceRejects leftParses leftRejects)
      (NamedTypeTraceParses rightParses)
      (NamedTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed name arguments finished =>
        cases right with
        | parsed otherName otherArguments otherFinished =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            rcases (namedTypeArgumentsTraceOutcomeAgreement children).successResultAgree
              arguments otherArguments with ⟨rfl, rfl, rfl⟩
            cases finished.trace_unique otherFinished
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | nameRejected name =>
        cases right with
        | nameRejected other => exact name.result_unique other
        | argumentsRejected other _ => exact False.elim (name.disjoint_success ⟨_, _, _, other⟩)
    | argumentsRejected name arguments =>
        cases right with
        | nameRejected other => exact False.elim (other.disjoint_success ⟨_, _, _, name⟩)
        | argumentsRejected otherName otherArguments =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            rcases (namedTypeArgumentsTraceOutcomeAgreement children).rejectResultAgree
              arguments otherArguments with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  successRejectDisjoint parsed rejection := by
    cases parsed with
    | parsed name arguments _ =>
        cases rejection with
        | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
        | argumentsRejected otherName rejected =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            exact (namedTypeArgumentsTraceOutcomeAgreement children).successRejectDisjoint arguments rejected
  rejectSuccessDisjoint rejection parsed := by
    cases parsed with
    | parsed name arguments _ =>
        cases rejection with
        | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
        | argumentsRejected otherName rejected =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            exact (namedTypeArgumentsTraceOutcomeAgreement children).rejectSuccessDisjoint rejected arguments

end Solcore.Syntax.DeclarativeGrammar
