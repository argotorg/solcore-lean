import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables

/-! The actual callable diagnostic producer starts at its requested minimum.
This finite receipt exposes the original checked unknown token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Allocation uses the actual checked word conversion of the computed start;
no property of the later decision traversal is assumed. -/
theorem prepare_unknown {plan : SourceCoreStageCodebook.Plan}
    {contracts : SourceCoreStageCodebook.Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program) :
    0 < program.unknown.val ∧ minimum ≤ program.unknown.val := by
  unfold SourceCoreCallableFaultSites.prepare at accepted
  obtain ⟨unknown, issued, accepted⟩ := bind_ok accepted
  obtain ⟨sites, _traversed, finished⟩ := bind_ok accepted
  have same : unknown = program.unknown := congrArg (·.unknown) (Except.ok.inj finished)
  rw [← same]
  change (match Word.ofNat? _ with
    | some value => Except.ok value
    | none => Except.error SourceCoreCallableFaultSites.Error.reasonSpaceExhausted) = .ok unknown at issued
  split at issued
  · rename_i value converted
    cases issued
    unfold Word.ofNat? at converted
    split at converted
    · have number := congrArg Fin.val (Option.some.inj converted).symm
      rw [number]
      exact ⟨Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    · cases converted
  · cases issued

/-- A retained token below the actual requested minimum is below the genuine
unknown-token boundary used by the public callable append. -/
theorem below_unknown {plan : SourceCoreStageCodebook.Plan}
    {contracts : SourceCoreStageCodebook.Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program} {token : Word}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    (below : token.val < minimum) : token.val < program.unknown.val := by
  exact Nat.lt_of_lt_of_le below (prepare_unknown accepted).2

/-- The public receiver uses this same callable producer. Its filtered append
therefore preserves the base table's result for the retained earlier token. -/
theorem append_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {plan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {issuedBase table : SourceCoreFaultSites.Table} {minimum : Nat}
    {callable : SourceCoreCallableFaultSites.Program} {token : Word}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts issuedBase minimum = .ok callable)
    (present : prepared.base.callableDiagnostics = some callable)
    (below : token.val < minimum) :
    (CallableIndexedOwnedPublicFaultReceiverTables.appendCallable prepared table).diagnostic? token =
      table.diagnostic? token := by
  exact CallableIndexedOwnedPublicFaultReceiverTables.appendCallable_diagnostic present
    (below_unknown accepted below)

end Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds
