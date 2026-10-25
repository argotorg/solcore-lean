import Solcore.Frontend.RustHull.MemoryGuardSemantics
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! The real builtin compiler implements the independent memory guard by
returning its evaluated word, without changing the resulting argument store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

private theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "memoryguard" arguments = .ok lowered) :
    arguments.length = 1 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem inner_components {scope : Scope} {value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "memoryguard" [value] = .ok lowered) :
    lowered = ⟨.word, LanguageResult.success value⟩ := by
  change Except.ok (Lowered.mk .word (LanguageResult.success value)) = .ok lowered at compiled
  exact (Except.ok.inj compiled).symm

/-- Successful lowering and the evaluated arguments give the same source word.
The builtin uses no effect slots and performs no store writes or allocations. -/
theorem preserves {scope : Scope} {name : String} {sourceType : Ty} {expected : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {result : Semantics.Result Semantics.Value}
    (called : MemoryGuardSemantics.Builtin name sourceType sources result)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {mapping : Renaming} {environment : Environment} {initial store : Store}
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target, ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target store := by
  cases called with
  | @guarded _ value =>
      obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components rfl compiled
      have arity : arguments.length = 1 := by
        simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
      obtain ⟨expression, input, rfl, same, rfl⟩ := one_word related words arity
      have same : value = input := by simpa only [List.cons.injEq, Semantics.Value.word.injEq, true_and, and_true] using same
      subst input
      obtain rfl := inner_components rawCompiled
      cases typed
      cases loweredEqual
      refine ⟨.inRight .word (.word value), .value (.word _), ?_⟩
      apply LanguageResult.bind_success .word packed
      exact .inRight (.var rfl)

end Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence
