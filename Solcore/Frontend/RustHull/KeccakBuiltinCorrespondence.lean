import Solcore.Frontend.RustHull.KeccakHashCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! Keccak source derivations pass through the actual outer builtin compiler,
including its word-argument checks and initialized memory references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "keccak256" arguments = .ok lowered) :
    arguments.length = 2 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem components {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "keccak256" [offset, length] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Keccak.hash memory size offset length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Keccak.hash memory size offset length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem preserves
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "keccak256" expected arguments = .ok lowered)
    {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : KeccakSemantics.Builtin "keccak256" sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 2 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨offsetExpr, lengthExpr, offset, length, rfl, rfl, rfl⟩ := two_words related words arity
  cases called with
  | hash executed =>
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := components rawCompiled
      cases typed
      cases loweredEqual
      have runtime' := runtime.temporary (.product .word .word) (.pair (.word offset) (.word length))
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
        KeccakHashCorrespondence.hash_preserves executed stateRelated
          (reference_evaluates runtime' memoryMember memoryCompiled store)
          (reference_evaluates runtime' sizeMember sizeCompiled store)
          (.first (.var (index := 0) rfl)) (.second (.var (index := 0) rfl))
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [KeccakHashCorrespondence.hash_rename]
      exact evaluated

end Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence
