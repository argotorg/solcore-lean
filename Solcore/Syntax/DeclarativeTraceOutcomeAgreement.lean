import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Pairwise diagnostic outcome agreement between distinct child relations.
Neither side is assumed to be functional internally, inhabited, or executable. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure TraceOutcomeAgreement {α : Type}
    (leftParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (leftRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultAgree : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    leftParses source endByte input left afterLeft leftTrace →
    rightParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultAgree : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    leftRejects source endByte input afterLeft leftReport leftTrace →
    rightRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input value output events rejected report trace},
    leftParses source endByte input value output events →
    rightRejects source endByte input rejected report trace → False
  rejectSuccessDisjoint : ∀ {input rejected report trace value output events},
    leftRejects source endByte input rejected report trace →
    rightParses source endByte input value output events → False

variable {α : Type}
  {leftParses rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TraceOutcomeAgreement.symm
    (agreement : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement rightParses rightRejects leftParses leftRejects source endByte where
  successResultAgree left right := by
    rcases agreement.successResultAgree right left with ⟨value, remainder, events⟩
    exact ⟨value.symm, remainder.symm, events.symm⟩
  rejectResultAgree left right := by
    rcases agreement.rejectResultAgree right left with ⟨remainder, report, events⟩
    exact ⟨remainder.symm, report.symm, events.symm⟩
  successRejectDisjoint left right := agreement.rejectSuccessDisjoint right left
  rejectSuccessDisjoint left right := agreement.successRejectDisjoint right left

theorem TraceExactOutcomeSpec.toTraceOutcomeAgreement
    (exactness : TraceExactOutcomeSpec leftParses leftRejects source endByte) :
    TraceOutcomeAgreement leftParses leftRejects leftParses leftRejects source endByte where
  successResultAgree := exactness.successResultUnique
  rejectResultAgree := exactness.rejectResultUnique
  successRejectDisjoint parsed rejected := exactness.successRejectDisjoint rejected ⟨_, _, _, parsed⟩
  rejectSuccessDisjoint rejected parsed := exactness.successRejectDisjoint rejected ⟨_, _, _, parsed⟩

theorem TraceOutcomeAgreement.toTraceExactOutcomeSpec
    (agreement : TraceOutcomeAgreement leftParses leftRejects leftParses leftRejects source endByte) :
    TraceExactOutcomeSpec leftParses leftRejects source endByte where
  successResultUnique := agreement.successResultAgree
  rejectResultUnique := agreement.rejectResultAgree
  successRejectDisjoint rejected := by
    rintro ⟨_, _, _, parsed⟩
    exact agreement.rejectSuccessDisjoint rejected parsed

end Solcore.Syntax.DeclarativeGrammar
