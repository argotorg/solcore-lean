import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! The outer Hull builtin compiler determines word arguments and resolves
the memory and calldata references used by copying. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open MemoryCopySemantics (Operation)

theorem three_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 3) :
    ∃ first second third left middle right,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] ∧
      sources = [.word left, .word middle, .word right] ∧
      targets = [.word left, .word middle, .word right] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, middle, right, rfl, rfl, rfl⟩ := two_words tail
        (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, second, third, left, middle, right, rfl, rfl, rfl⟩

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = 3 := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem move_components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mcopy" [destination, source, length] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mcopy memory size destination source length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mcopy memory size destination source length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem calldata_components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldatacopy" [destination, source, length] = .ok lowered) :
    ∃ memory size calldata, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "calldata" WordMapping.type = .ok calldata ∧
      lowered = ⟨.unit, Memory.copyPackedFrom memory size destination (.loadCell calldata) source length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      let calldata ← Effects.reference scope "calldata" WordMapping.type
      pure (Lowered.mk .unit (Memory.copyPackedFrom memory size destination (.loadCell calldata) source length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨calldata, calldataCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, calldata, memoryCompiled, sizeCompiled, calldataCompiled, (Except.ok.inj returned).symm⟩

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {calldata : MemorySemantics.Entries} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : MemoryCopySemantics.Builtin calldata operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (available : operation = .calldata → ∃ location, ⟨"calldata", WordMapping.type, location⟩ ∈ slots)
    (calldataRead : ∀ location, ⟨"calldata", WordMapping.type, location⟩ ∈ slots →
      store.read? location = some (WordMapping.encode calldata))
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    three_words related words arity
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  cases operation with
  | move =>
      generalize named : Operation.move.name = actualName at called
      cases called with
      | move executed =>
          obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := move_components rawCompiled
          cases typed
          cases loweredEqual
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.mcopy_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl)) (.first (.second (.var (index := 0) rfl))) (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          rw [MemoryCopyCorrespondence.mcopy_rename]
          exact evaluated
      | calldata _ => exact False.elim ((by decide : ("mcopy" : String) ≠ "calldatacopy") named)
  | calldata =>
      generalize named : Operation.calldata.name = actualName at called
      cases called with
      | calldata executed =>
          obtain ⟨location, member⟩ := available rfl
          obtain ⟨memory, size, inputRef, memoryCompiled, sizeCompiled, inputCompiled, rfl⟩ :=
            calldata_components rawCompiled
          cases typed
          cases loweredEqual
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' member inputCompiled store) (calldataRead location member))
              (.first (.second (.var (index := 0) rfl))) (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

      | move _ => exact False.elim ((by decide : ("calldatacopy" : String) ≠ "mcopy") named)

end Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
