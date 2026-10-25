import Solcore.Frontend.RustHull.MemorySnapshotSemantics
import Solcore.Frontend.RustHull.MemorySnapshot
import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence

/-! The aligned traversal retains the source entry order and installs one
ordinary recursive helper. Its recursive calls leave the store unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

def alignedInput (entries : MemorySemantics.Entries) (start last shift : Word) : Value :=
  bundleValues [WordMapping.encode entries, .word start, .word last, .word shift]

theorem alignedBody_evaluates (entries : MemorySemantics.Entries) (start last shift : Word)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody location captured) :
    Evaluates (alignedInput entries start last shift ::
      .cellRef (OptionalCell.cellType (WordMapping.helperType MemorySnapshot.parameter WordMapping.type)) location :: captured)
      store MemorySnapshot.alignedBody (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift entries))) store := by
  induction entries with
  | nil => exact .matchData (.first (.var rfl)) rfl rfl (.inRight (.construct .unit))
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      let payload : Value := .pair (.pair (.word key) (.word value)) (WordMapping.encode rest)
      let input := alignedInput ((key, value) :: rest) start last shift
      let reference : Value := .cellRef (OptionalCell.cellType (WordMapping.helperType MemorySnapshot.parameter WordMapping.type)) location
      let oldEnvironment := payload :: input :: reference :: captured
      let args := bundleValues [payload, input, reference]
      let environment := args :: oldEnvironment
      let argsCode : Code := fun here => .var (here - 0 - 1)
      have argsRelated : CodeValue 1 environment argsCode (bundleValues [payload, input, reference]) :=
        CodeValue.bound 0 oldEnvironment args
      have entryRelated := argsRelated.part (index := 0) rfl
      have pairRelated := entryRelated.part (values := [.pair (.word key) (.word value), WordMapping.encode rest]) (index := 0) rfl
      have keyRelated := pairRelated.part (values := [.word key, .word value]) (index := 0) rfl
      have valueRelated := pairRelated.part (values := [.word key, .word value]) (index := 1) rfl
      have tailRelated := entryRelated.part (values := [.pair (.word key) (.word value), WordMapping.encode rest]) (index := 1) rfl
      have inputRelated := argsRelated.part (index := 1) rfl
      have startRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 1) rfl
      have lastRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 2) rfl
      have shiftRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 3) rfl
      have referenceRelated := argsRelated.part (index := 2) rfl
      let recurse : Code := fun depth => WordMapping.invoke MemorySnapshot.parameter WordMapping.type
        (part 2 3 argsCode depth)
        (packet [part 1 2 (part 0 3 argsCode), part 1 4 (part 1 3 argsCode),
          part 2 4 (part 1 3 argsCode), part 3 4 (part 1 3 argsCode)] depth)
      have recursed (extra : Environment) : Evaluates (extra ++ environment) store (recurse (1 + extra.length))
          (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest))) store := by
        apply WordMapping.invoke_evaluates ((referenceRelated.prepend extra).evaluates store) installed
        · have argument := (CodeValue.packet (.cons tailRelated (.cons startRelated (.cons lastRelated (.cons shiftRelated .nil))))).prepend
            (WordMapping.closure MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody location captured :: extra)
          simpa [Core.Expr.weakenAt, CodeBuilder.packet, CodeBuilder.part, argsCode, projectArgument, bundle,
            List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, environment]
            using argument.evaluates store
        · exact ih
      unfold MemorySnapshot.alignedBody
      apply Evaluates.matchData (constructor := WordMapping.consConstructor) (.first (.var rfl)) rfl rfl
      apply Evaluates.letE (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
      by_cases before : start > key
      · simp only [MemorySnapshotSemantics.retain, before, ↓reduceIte]
        exact .ifTrue (.binary (startRelated.evaluates store) (keyRelated.evaluates store) (by simp [BinaryOp.apply, before])) (recursed [])
      · apply Evaluates.ifFalse (.binary (startRelated.evaluates store) (keyRelated.evaluates store) (by simp [BinaryOp.apply, before]))
        by_cases outside : key > Word.ofNatModulo ((wordModulus - 1) / 32)
        · simp only [MemorySnapshotSemantics.retain, before, outside, ↓reduceIte]
          exact .ifTrue (.binary (keyRelated.evaluates store) .word (by simp [BinaryOp.apply, outside])) (recursed [])
        · apply Evaluates.ifFalse (.binary (keyRelated.evaluates store) .word (by simp [BinaryOp.apply, outside]))
          apply Evaluates.letE (.binary (keyRelated.evaluates store) (startRelated.evaluates store) rfl)
          have last' := lastRelated.prepend [.word (key.sub start)]
          by_cases after : key.sub start > last
          · simp only [MemorySnapshotSemantics.retain, before, outside, after, ↓reduceIte]
            exact .ifTrue (.binary (.var rfl) (last'.evaluates store) (by simp [BinaryOp.apply, after])) (recursed [.word (key.sub start)])
          · simp only [MemorySnapshotSemantics.retain, before, outside, after, ↓reduceIte]
            apply Evaluates.ifFalse (.binary (.var rfl) (last'.evaluates store) (by simp [BinaryOp.apply, after]))
            apply LanguageResult.bind_success WordMapping.type (recursed [.word (key.sub start)])
            apply Evaluates.inRight
            apply Evaluates.construct
            apply Evaluates.pair
            · apply Evaluates.pair (.var rfl)
              have value' := valueRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              have shift' := shiftRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              have last'' := lastRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              by_cases finalWord : key.sub start == last
              · simp only [finalWord, ↓reduceIte]
                exact .ifTrue (.binary (.var rfl) (last''.evaluates store) (by simp [BinaryOp.apply, finalWord]))
                  (.binary (.binary (value'.evaluates store) (shift'.evaluates store) rfl) (shift'.evaluates store) rfl)
              · simp only [finalWord, Bool.false_eq_true, ↓reduceIte]
                exact .ifFalse (.binary (.var rfl) (last''.evaluates store) (by simp [BinaryOp.apply, finalWord])) (value'.evaluates store)
            · exact .var rfl

theorem aligned_evaluates {environment : Environment} {initial store : Store}
    {argument : Core.Expr} {entries : MemorySemantics.Entries} {start last shift : Word}
    (evaluated : Evaluates environment initial argument (alignedInput entries start last shift) store) :
    Evaluates environment initial (WordMapping.runHelper MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody argument)
      (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift entries)))
      (WordMapping.installedStore store MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
        (alignedInput entries start last shift) environment) := by
  apply WordMapping.runHelper_evaluates evaluated
  apply alignedBody_evaluates
  simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]

end Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
