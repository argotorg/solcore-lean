import Solcore.Semantics.HostDriverResumptionProperties
import Solcore.Semantics.WordReturnedFrameCompletionProperties

/-! Typed branch exclusion and terminal resumption for Word completion. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostDriverResult

universe u v

/-- A typed Word projection fails only at exhaustion or a policy boundary. -/
theorem toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (typing : result.outcome.HasType .word definitions) :
    result.toWordReturnedFrameCompletion? = none ↔
      (∃ context state,
        result = ⟨context, .outOfFuel state⟩) ∨
      ∃ context suspension remainingFuel,
        result = ⟨context, .unsupported suspension remainingFuel⟩ := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          obtain ⟨world, _storeTyping, valueTyping⟩ := typing
          obtain ⟨word, rfl⟩ := valueTyping.word_shape
          simp
      | outOfFuel state =>
          simp
      | fault error state =>
          exact False.elim typing
      | unsupported suspension remainingFuel => simp

/-- A successful projection is unchanged by any later fuel offer. -/
theorem toWordReturnedFrameCompletion?_resumeWithFuel_of_some
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (handler :
      HostHandler (HostStorageDriver.Context RollbackState TraceState))
    (additional : Nat)
    (completion : WordReturnedFrameCompletion RollbackState TraceState)
    (completed :
      result.toWordReturnedFrameCompletion? = some completion) :
    toWordReturnedFrameCompletion?
        (result.resumeWithFuel handler additional) = some completion := by
  rw [(toWordReturnedFrameCompletion?_eq_some_iff
    result completion).mp completed]
  rfl

end Solcore.Semantics.HostDriverResult
