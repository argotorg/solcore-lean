import Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar
import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeFunctionReturnsTraceAgreementProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Heterogeneous child agreement lifts through raw function parameters and
optional returns. Raw missing-keyword failures remain first failures, and
parameter events precede return events on both sides of every comparison. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem functionTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (FunctionTypeTraceParses leftParses) (FunctionTypeTraceRejects leftParses leftRejects)
      (FunctionTypeTraceParses rightParses) (FunctionTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed _ marker parameters returns =>
        cases right with
        | parsed _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            rcases (functionReturnsTraceOutcomeAgreement children).successResultAgree returns otherReturns with
              ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | markerMissing absent reported =>
        cases right with
        | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
        | parametersRejected span marker _ | returnsRejected span marker _ _ =>
            exact False.elim (absent ⟨span, marker.1⟩)
    | parametersRejected span marker parameters =>
        cases right with
        | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact parameters.result_agree children otherParameters
        | returnsRejected _ otherMarker otherParameters _ =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact False.elim (parameters.disjoint_success_of_agreement children otherParameters)
    | returnsRejected span marker parameters returns =>
        cases right with
        | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact False.elim (parameters.disjoint_rejection_of_agreement children otherParameters)
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            rcases (functionReturnsTraceOutcomeAgreement children).rejectResultAgree returns otherReturns with
              ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  successRejectDisjoint parsed rejected := by
    cases parsed with
    | parsed span marker parameters returns =>
        cases rejected with
        | markerMissing absent _ => exact absent ⟨span, marker.1⟩
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact parameters.disjoint_rejection_of_agreement children otherParameters
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            exact (functionReturnsTraceOutcomeAgreement children).successRejectDisjoint returns otherReturns
  rejectSuccessDisjoint rejected parsed := by
    cases parsed with
    | parsed span marker parameters returns =>
        cases rejected with
        | markerMissing absent _ => exact absent ⟨span, marker.1⟩
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact otherParameters.disjoint_success_of_agreement children parameters
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases otherParameters.result_agree children.successResultAgree parameters with ⟨rfl, rfl, rfl⟩
            exact (functionReturnsTraceOutcomeAgreement children).rejectSuccessDisjoint otherReturns returns

end Solcore.Syntax.DeclarativeGrammar
