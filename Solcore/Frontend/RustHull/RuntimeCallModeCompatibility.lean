import Solcore.Frontend.RustHull.RuntimeCallModeSemantics

/-! Existing ordinary and static-call proofs also apply to the extended source
semantics: their guards, message arguments and callback modes are unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeSemantics
open Core

section
variable {children : State → AccountCallSemantics.Children}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {state final : State} {result : Semantics.Result Semantics.Value}

theorem ordinary_call
    (computed : Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final) :
    RuntimeCallEffectsSemantics.Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final := by
  cases computed with
  | staticValue _ isStatic nonzero => exact .staticValue _ rfl isStatic nonzero
  | gasOverflow _ permitted nonzero overflow =>
      have notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false := permitted.resolve_left (by simp)
      exact .gasOverflow _ rfl notStatic nonzero overflow
  | invoked permitted stipend executed =>
      apply RuntimeCallEffectsSemantics.Call.invoked
      · exact .inr (permitted.resolve_left (by simp))
      · intro _ nonzero
        exact stipend rfl nonzero
      · simpa only [arguments, RuntimeCallEffectsSemantics.arguments, Operation.hasStipend,
          Operation.mode, reduceCtorEq, ↓reduceIte, and_true, true_and] using executed

theorem static_call
    (computed : Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final) :
    RuntimeCallEffectsSemantics.Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final := by
  cases computed with
  | staticValue ordinary _ _ => cases ordinary
  | gasOverflow stipend _ _ _ => cases stipend
  | invoked _ _ executed =>
      apply RuntimeCallEffectsSemantics.Call.invoked (.inl rfl)
      · intro impossible
        cases impossible
      · simpa only [arguments, RuntimeCallEffectsSemantics.arguments, Operation.hasStipend,
          Operation.mode, reduceCtorEq, ↓reduceIte, ne_eq, not_true_eq_false, and_false] using executed

end
end Solcore.Frontend.RustHull.RuntimeCallModeSemantics
