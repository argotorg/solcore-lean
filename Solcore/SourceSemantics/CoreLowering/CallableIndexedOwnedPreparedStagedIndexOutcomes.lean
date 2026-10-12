import Solcore.SourceSemantics.Staging.RecursiveTrace
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTerminal

/-! The existing mapping helper and independent staged Source lookup use the
same terminal decision after both argument heaps have been reached. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
open Core Frontend SourceInference Staging.Recursive

def liftOutcome : Dynamic.ExpressionOutcome → Outcome
  | .value value => .value value
  | .fault reason => .fault (.semantic reason)

theorem of_terminal {base key : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (terminal : CompatibleExpressionIndices.Terminal base key outcome) :
    IndexOutcome base key (liftOutcome outcome) := by
  cases terminal with
  | found shape located => exact .found shape located
  | default shape absent defaulted => exact .default shape absent defaulted
  | shape invalid => exact .shape invalid
  | keyType shape typed mismatch => exact .keyType shape typed mismatch
  | unavailable shape typed absent missing => exact .unavailable shape typed absent missing

theorem to_terminal {base key : Dynamic.Value} {outcome : Outcome}
    (result : IndexOutcome base key outcome) :
    ∃ plain, outcome = liftOutcome plain ∧ CompatibleExpressionIndices.Terminal base key plain := by
  cases result with
  | found shape located => exact ⟨_, rfl, .found shape located⟩
  | default shape absent defaulted => exact ⟨_, rfl, .default shape absent defaulted⟩
  | shape invalid => exact ⟨_, rfl, .shape invalid⟩
  | keyType shape typed mismatch => exact ⟨_, rfl, .keyType shape typed mismatch⟩
  | unavailable shape typed absent missing => exact ⟨_, rfl, .unavailable shape typed absent missing⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
