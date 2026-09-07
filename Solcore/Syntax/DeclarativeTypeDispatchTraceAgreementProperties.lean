import Solcore.Syntax.DeclarativeTypeDispatchTraceOutcomeProperties
import Solcore.Syntax.DeclarativeSimpleTypeTraceAgreementProperties
import Solcore.Syntax.DeclarativeMappingTypeTraceAgreementProperties
import Solcore.Syntax.DeclarativeNamedTypeTraceAgreementProperties
import Solcore.Syntax.DeclarativeTupleTypeTraceAgreementProperties
import Solcore.Syntax.DeclarativeFunctionTypeTraceAgreementProperties

/-! Heterogeneous raw agreement lifts through the exact ordered selector.
The two child relations may differ and need not be internally functional.
Final rejection stays a silent, non-consuming independent terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem typeDispatchTraceOutcomeAgreement_of_raw
    (raw : ∀ branch,
      TraceOutcomeAgreement (TypeDispatchRawTraceParses leftParses branch)
        (TypeDispatchRawTraceRejects leftParses leftRejects branch)
        (TypeDispatchRawTraceParses rightParses branch)
        (TypeDispatchRawTraceRejects rightParses rightRejects branch) source endByte) :
    TraceOutcomeAgreement (TypeDispatchTraceParses leftParses) (TypeDispatchTraceRejects leftParses leftRejects)
      (TypeDispatchTraceParses rightParses) (TypeDispatchTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | selected branch selection parsed =>
        exact (raw branch).successResultAgree parsed (right.raw_of_selected selection)
  rejectResultAgree left right := by
    cases left with
    | selected branch selection rejection =>
        exact (raw branch).rejectResultAgree rejection (right.raw_of_selected selection)
  successRejectDisjoint left right := by
    cases left with
    | selected branch selection parsed =>
        exact (raw branch).successRejectDisjoint parsed (right.raw_of_selected selection)
  rejectSuccessDisjoint left right := by
    cases left with
    | selected branch selection rejection =>
        exact (raw branch).rejectSuccessDisjoint rejection (right.raw_of_selected selection)

theorem typeDispatchRawTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte)
    (branch : TypeDispatchBranch) :
    TraceOutcomeAgreement (TypeDispatchRawTraceParses leftParses branch)
      (TypeDispatchRawTraceRejects leftParses leftRejects branch)
      (TypeDispatchRawTraceParses rightParses branch)
      (TypeDispatchRawTraceRejects rightParses rightRejects branch) source endByte := by
  cases branch with
  | function => exact functionTypeTraceOutcomeAgreement children
  | comptime => exact comptimeTypeTraceOutcomeAgreement children
  | mapping => exact mappingTypeTraceOutcomeAgreement children
  | proxy => exact proxyTypeTraceOutcomeAgreement children
  | tuple => exact tupleTypeTraceOutcomeAgreement children
  | named => exact namedTypeTraceOutcomeAgreement children
  | final =>
      exact {
        successResultAgree := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
        rejectResultAgree := TypeDispatchFinalTraceRejects.result_unique
        successRejectDisjoint := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
        rejectSuccessDisjoint := by intro _ _ _ _ _ _ _ _ impossible; exact False.elim impossible
      }

theorem typeDispatchTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (TypeDispatchTraceParses leftParses) (TypeDispatchTraceRejects leftParses leftRejects)
      (TypeDispatchTraceParses rightParses) (TypeDispatchTraceRejects rightParses rightRejects) source endByte :=
  typeDispatchTraceOutcomeAgreement_of_raw (typeDispatchRawTraceOutcomeAgreement children)

end Solcore.Syntax.DeclarativeGrammar
