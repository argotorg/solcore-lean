import Solcore.Frontend.RustHull.Sha256BlockCorrespondence
import Solcore.Frontend.RustHull.Sha256CompressCorrespondence

/-! The independent SHA-256 block sequence drives the actual recursive helper
and hash expression. Lookup allocations preserve the actual memory cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256HashCorrespondence
open Core MemoryCorrespondence LogsCorrespondence Sha256BlockCorrespondence

abbrev helperReference (location : Nat) : Value :=
  .cellRef (OptionalCell.cellType (WordMapping.helperType Sha256Implementation.parameterType .word)) location

theorem absorbBody_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Sha256Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 8) (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Sha256Implementation.parameterType .word
      Sha256Implementation.absorbBody location captured) :
    ∃ suffix, Evaluates (parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured)
      store Sha256Implementation.absorbBody (.inRight .word (.word result)) (store ++ suffix) := by
  induction absorbed generalizing store with
  | @last offset remaining state markerUsed short fits =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      refine ⟨suffix, ?_⟩
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, fits, decide_false]))
      exact .inRight (Sha256CompressCorrespondence.digest_evaluates
        (environment := wordsValue (Sha256Semantics.compress state block) :: wordsValue block :: environment)
        (stateExpr := .var 0) (Sha256CompressCorrespondence.compress_length state block) (fun _ => .var rfl) _)
  | @spill offset remaining state markerUsed result short spills rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      let next := Sha256Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Sha256CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, spills, decide_true]))
      apply invoke_evaluates (body := Sha256Implementation.absorbBody) (captured := captured)
        (input := parametersValue words offset (Word.ofNatModulo 0) bits next true)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number]
        exact .pair (.first (.var rfl)) (.pair (.first (.second (.var rfl))) (.pair .word
          (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated
  | @more offset remaining state markerUsed result full rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      let next := Sha256Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Sha256CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, full, decide_true]))
      apply invoke_evaluates (body := Sha256Implementation.absorbBody) (captured := captured)
        (input := parametersValue words (offset.add (Word.ofNatModulo 64)) (remaining.sub (Word.ofNatModulo 64))
          bits next false)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number, HashBlocks.add]
        exact .pair (.first (.var rfl)) (.pair (.binary (.first (.second (.var rfl))) .word rfl)
          (.pair (.binary (.first (.second (.second (.var rfl)))) .word rfl)
            (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated

theorem absorb_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Sha256Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 8) {environment : Environment} {store : Store}
    {argument : Core.Expr}
    (argumentEvaluated : Evaluates environment store argument
      (parametersValue words offset remaining bits state markerUsed) store) :
    ∃ suffix, Evaluates environment store
      (WordMapping.runHelper Sha256Implementation.parameterType .word Sha256Implementation.absorbBody argument)
      (.inRight .word (.word result)) (store ++ suffix) := by
  let input := parametersValue words offset remaining bits state markerUsed
  let closure := WordMapping.closure Sha256Implementation.parameterType .word Sha256Implementation.absorbBody
    store.length (input :: environment)
  obtain ⟨suffix, body⟩ := absorbBody_evaluates absorbed length
    (store ++ [.inRight .unit closure]) store.length (input :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  exact runHelper_evaluates argumentEvaluated body

/-- The actual SHA-256 expression touches the input range, then digests it with
the independent block sequence. Only the memory size cell changes. -/
theorem hash_preserves {offset length size result : Word} {state : MemorySemantics.State}
    (touched : MemorySemantics.touchSize? state.size offset length = some size)
    (digested : Sha256Semantics.Digest state.words offset length result)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ final, Evaluates environment store (Sha256.hash memoryRef sizeRef offsetExpr lengthExpr)
        (.inRight .word (.word result)) final ∧
      StateRel memoryLocation sizeLocation {state with size := size} final ∧
      Frame memoryLocation sizeLocation store final := by
  rw [Sha256Implementation.hash_eq]
  let argument := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word offset) (.word length)))
  have touchedEvaluated := touch_evaluates (environment := argument :: environment)
    (reference := HashBlocks.field 1 4 (.var 0)) (offsetExpr := HashBlocks.field 2 4 (.var 0))
    (lengthExpr := HashBlocks.field 3 4 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.var rfl)))) related.size
  simp only [touchResult, touched] at touchedEvaluated
  have touchedRelated := related.touch touched
  obtain ⟨suffix, evaluated⟩ := absorb_evaluates digested Sha256CompressCorrespondence.initial_length
    (environment := .unit :: argument :: environment)
    (argument := HashBlocks.packet [.loadCell (HashBlocks.field 0 4 (.var 1)), HashBlocks.field 2 4 (.var 1),
      HashBlocks.field 3 4 (.var 1),
      .binary .wordAnd (.binary .wordMul (HashBlocks.field 3 4 (.var 1)) (HashBlocks.number 8))
        (HashBlocks.number (2 ^ 64 - 1)),
      Sha256Implementation.initial, .bool false])
    (.pair (.loadCell (.first (.var rfl)) touchedRelated.memory) (.pair (.first (.second (.second (.var rfl))))
      (.pair (.second (.second (.second (.var rfl))))
        (.pair (.binary (.binary (.second (.second (.second (.var rfl)))) .word rfl) .word rfl)
          (.pair (Sha256CompressCorrespondence.initial_evaluates _ _) .bool)))))
  refine ⟨_, ?_, touchedRelated.append suffix, (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ suffix)⟩
  exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
    (LanguageResult.bind_success .word touchedEvaluated evaluated)

end Solcore.Frontend.RustHull.Sha256HashCorrespondence
