import Solcore.Frontend.RustHull.MemoryCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! Memory effects through the actual Hull builtin compiler. Successful
compilation supplies the argument constraints and runtime references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence MemoryCorrespondence EffectBuiltinCorrespondence

inductive Operation where
  | load | store | store8 | size
  deriving DecidableEq

def Operation.name : Operation → String
  | .load => "mload" | .store => "mstore" | .store8 => "mstore8" | .size => "msize"

def Operation.arity : Operation → Nat
  | .load => 1 | .store | .store8 => 2 | .size => 0

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem load_components {scope : Scope} {offset : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mload" [offset] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Memory.mload memory size offset⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Memory.mload memory size offset)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem store_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem store8_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore8" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore8 memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore8 memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem size_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "msize" [] = .ok lowered) :
    ∃ size, Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell size)⟩ := by
  change (do
    let raw ← (do
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (LanguageResult.success (.loadCell size))) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨size, sizeCompiled, (Except.ok.inj returned).symm⟩

/-- The compiler, argument relation and actual runtime references determine
the source memory result. No premise supplies a computed source outcome. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      MemorySemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | size =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      cases related
      obtain ⟨size, sizeCompiled, rfl⟩ := size_components rawCompiled
      cases typed
      cases loweredEqual
      refine ⟨.value (.word state.size), state, .inRight .word (.word state.size), store,
        rfl, .value (.word _), ?_, stateRelated, Frame.refl _ _ _⟩
      apply LanguageResult.bind_success .word packed
      exact .inRight (.loadCell
        (reference_evaluates (runtime.temporary .unit .unit) sizeMember sizeCompiled store) stateRelated.size)
  | load =>
      obtain ⟨offsetExpr, offset, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := load_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ := mload_preserves stateRelated offset (.word offset :: environment)
      refine ⟨(MemorySemantics.mload state offset).1, (MemorySemantics.mload state offset).2,
        mloadResult state offset, mloadStore store memoryLocation sizeLocation state offset (.word offset :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .word packed
      rw [mload_rename]
      exact mload_evaluates state offset
        (reference_evaluates (runtime.temporary .word (.word offset)) memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary .word (.word offset)) sizeMember sizeCompiled store)
        (.var rfl) stateRelated.memory stateRelated.size stateRelated.distinct
  | store =>
      obtain ⟨offsetExpr, valueExpr, offset, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ :=
        mstore_preserves stateRelated offset value (.pair (.word offset) (.word value) :: environment)
      refine ⟨(MemorySemantics.mstore state offset value).1, (MemorySemantics.mstore state offset value).2,
        mstoreResult state offset, mstoreStore store memoryLocation sizeLocation state offset value
          (.pair (.word offset) (.word value) :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .unit packed
      rw [mstore_rename]
      exact mstore_evaluates state offset value
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          sizeMember sizeCompiled store)
        (.first (.var rfl)) (.second (.var rfl)) stateRelated.memory stateRelated.size stateRelated.distinct
  | store8 =>
      obtain ⟨offsetExpr, valueExpr, offset, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store8_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ :=
        mstore8_preserves stateRelated offset value (.pair (.word offset) (.word value) :: environment)
      refine ⟨(MemorySemantics.mstore8 state offset value).1, (MemorySemantics.mstore8 state offset value).2,
        mstore8Result state offset, mstore8Store store memoryLocation sizeLocation state offset value
          (.pair (.word offset) (.word value) :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .unit packed
      rw [mstore8_rename]
      exact mstore8_evaluates state offset value
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          sizeMember sizeCompiled store)
        (.first (.var rfl)) (.second (.var rfl)) stateRelated.memory stateRelated.size stateRelated.distinct

end Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
