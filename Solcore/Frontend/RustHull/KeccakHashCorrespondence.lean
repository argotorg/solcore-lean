import Solcore.Frontend.RustHull.KeccakAbsorptionCorrespondence
import Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
import Solcore.Frontend.RustHull.LogsCorrespondence

/-! Independent block absorption drives the emitted recursive helper and
hash expression. Padding allocations preserve the actual memory cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakHashCorrespondence
open Core MemoryCorrespondence KeccakPermutationCorrespondence KeccakAbsorptionCorrespondence

def input (words : MemorySemantics.Entries) (offset remaining : Word) (state : KeccakSemantics.State) : Value :=
  .pair (WordMapping.encode words) (.pair (.word offset) (.pair (.word remaining) (stateValue state)))

theorem absorbBody_evaluates {words : MemorySemantics.Entries} {offset remaining result : Word}
    {state : KeccakSemantics.State} (absorbed : KeccakSemantics.Absorb words offset remaining state result)
    (length : state.length = 25) (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Keccak.parameterType .word Keccak.absorbBody location captured) :
    ∃ suffix, Evaluates
      (input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured)
      store Keccak.absorbBody (.inRight .word (.word result)) (store ++ suffix) := by
  induction absorbed generalizing store with
  | last offset remaining state short =>
      let environment := input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := absorbBlock_evaluates (environment := environment) (store := store)
        (mapping := Keccak.field 0 4 (.var 0)) (offsetExpr := Keccak.field 1 4 (.var 0))
        (remainingExpr := Keccak.field 2 4 (.var 0)) (stateExpr := Keccak.field 3 4 (.var 0))
        length (LogsCorrespondence.Stable.var rfl).first (LogsCorrespondence.Stable.var rfl).second.first
        (LogsCorrespondence.Stable.var rfl).second.second.first (LogsCorrespondence.Stable.var rfl).second.second.second
      refine ⟨suffix, ?_⟩
      apply LanguageResult.bind_success .word blockEvaluated
      apply Evaluates.letE (permute_var_evaluates (absorbBlock_length words offset remaining state) rfl)
      apply Evaluates.ifTrue
      · exact .binary .word (.first (.second (.second (.var rfl)))) (by simp [BinaryOp.apply, short])
      · exact .inRight (digest_evaluates (permute_length _ (absorbBlock_length words offset remaining state)) (.var rfl))
  | @more offset remaining state result full rest ih =>
      let environment := input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := absorbBlock_evaluates (environment := environment) (store := store)
        (mapping := Keccak.field 0 4 (.var 0)) (offsetExpr := Keccak.field 1 4 (.var 0))
        (remainingExpr := Keccak.field 2 4 (.var 0)) (stateExpr := Keccak.field 3 4 (.var 0))
        length (LogsCorrespondence.Stable.var rfl).first (LogsCorrespondence.Stable.var rfl).second.first
        (LogsCorrespondence.Stable.var rfl).second.second.first (LogsCorrespondence.Stable.var rfl).second.second.second
      obtain ⟨tail, bodyEvaluated⟩ := ih (permute_length _ (absorbBlock_length words offset remaining state)) (store ++ suffix)
        (LogsCorrespondence.installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      apply Evaluates.letE (permute_var_evaluates (absorbBlock_length words offset remaining state) rfl)
      apply Evaluates.ifFalse
      · exact .binary .word (.first (.second (.second (.var rfl)))) (by simp [BinaryOp.apply, full])
      · apply LogsCorrespondence.invoke_evaluates (body := Keccak.absorbBody) (captured := captured)
          (input := input words (offset.add (Word.ofNatModulo 136)) (remaining.sub (Word.ofNatModulo 136))
            (KeccakSemantics.permute (KeccakSemantics.absorbBlock words offset remaining state)))
          (.var rfl) (LogsCorrespondence.installed_append installed suffix)
        · simp [Core.Expr.weakenAt, Keccak.packet, Keccak.field, Keccak.add, Keccak.number]
          exact .pair (.first (.var rfl)) (.pair (.binary (.first (.second (.var rfl))) .word rfl)
            (.pair (.binary (leftValue := .word remaining) (.first (.second (.second (.var rfl)))) .word rfl) (.var rfl)))
        · exact bodyEvaluated

theorem absorb_evaluates {words : MemorySemantics.Entries} {offset remaining result : Word}
    {state : KeccakSemantics.State} (absorbed : KeccakSemantics.Absorb words offset remaining state result)
    (length : state.length = 25)
    {environment : Environment} {store : Store} {mapping offsetExpr remainingExpr stateExpr : Core.Expr}
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode words) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (remainingEvaluated : Evaluates environment store remainingExpr (.word remaining) store)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store) :
    ∃ suffix, Evaluates environment store
      (WordMapping.runHelper Keccak.parameterType .word Keccak.absorbBody
        (Keccak.packet [mapping, offsetExpr, remainingExpr, stateExpr]))
      (.inRight .word (.word result)) (store ++ suffix) := by
  let argument := input words offset remaining state
  let closure := WordMapping.closure Keccak.parameterType .word Keccak.absorbBody store.length (argument :: environment)
  obtain ⟨suffix, body⟩ := absorbBody_evaluates absorbed length
    (store ++ [.inRight .unit closure]) store.length (argument :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  exact LogsCorrespondence.runHelper_evaluates
    (.pair mappingEvaluated (.pair offsetEvaluated (.pair remainingEvaluated stateEvaluated))) body

theorem hash_preserves {offset length : Word}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (hashed : KeccakSemantics.Hash offset length state result finalState)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, Correspondence.ResultRel .word result target ∧
      Evaluates environment store (Keccak.hash memoryRef sizeRef offsetExpr lengthExpr) target final ∧
      StateRel memoryLocation sizeLocation finalState final ∧ Frame memoryLocation sizeLocation store final := by
  let argument := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word offset) (.word length)))
  have touched := touch_evaluates (environment := argument :: environment)
    (reference := Keccak.field 1 4 (.var 0)) (offsetExpr := Keccak.field 2 4 (.var 0)) (lengthExpr := Keccak.field 3 4 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.var rfl)))) related.size
  cases hashed with
  | overflow overflow =>
      simp only [touchResult, overflow, touchStore_failure overflow] at touched
      refine ⟨.inLeft .word (.word Memory.overflowReason), store, .language _, ?_, related, Frame.refl _ _ _⟩
      exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
        (LanguageResult.bind_failure .word touched)
  | @done size result touchedSize absorbed =>
      simp only [touchResult, touchedSize] at touched
      have touchedRelated := related.touch touchedSize
      obtain ⟨suffix, evaluated⟩ := absorb_evaluates absorbed (by simp)
        (environment := .unit :: argument :: environment)
        (mapping := .loadCell (Keccak.field 0 4 (.var 1))) (offsetExpr := Keccak.field 2 4 (.var 1))
        (remainingExpr := Keccak.field 3 4 (.var 1)) (stateExpr := Keccak.zeroState)
        (.loadCell (.first (.var rfl)) touchedRelated.memory)
        (.first (.second (.second (.var rfl)))) (.second (.second (.second (.var rfl))))
        (zeroState_evaluates _ _)
      refine ⟨.inRight .word (.word result), _, .value (.word result), ?_, touchedRelated.append suffix,
        (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ suffix)⟩
      exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
        (LanguageResult.bind_success .word touched evaluated)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem hash_rename (memory size offset length : Core.Expr) (mapping : Renaming) :
    (Keccak.hash memory size offset length).rename mapping =
      Keccak.hash (memory.rename mapping) (size.rename mapping) (offset.rename mapping) (length.rename mapping) := by
  simp only [Keccak.hash, Keccak.packet, Core.Expr.rename]
  congr 1
  simp [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.add, Memory.number, Memory.packet, Memory.field,
    Keccak.field, Keccak.absorbBody, Keccak.absorbBlock, Keccak.readLane, Keccak.paddedByte,
    Keccak.digest, Keccak.permute, Keccak.roundCalls, Keccak.roundBody,
    Keccak.constants, Keccak.rotations, Keccak.source, Keccak.destination,
    Keccak.packet, Keccak.number, Keccak.xor, Keccak.add, Keccak.shift,
    Keccak.move, Keccak.lane, Keccak.zeroState, Keccak.rotate,
    Memory.readMemoryByte, List.range_succ,
    WordMapping.lookup, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end Solcore.Frontend.RustHull.KeccakHashCorrespondence
