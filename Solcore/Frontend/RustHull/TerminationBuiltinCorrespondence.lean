import Solcore.Frontend.RustHull.TerminationSemantics
import Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! Message termination through the actual effect compiler. Both the memory
range check and the ordered writes use the concrete runtime reference cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence ScalarExecution
open TerminationSemantics

def finishStore (locations : StorageBuiltinCorrespondence.Locations) (kind : Nat)
    (offset length : Word) (store : Store) : Store :=
  ((store.set locations.returnOffset (.word offset)).set locations.returnSize (.word length)).set locations.exit (.word (Word.ofNatModulo kind))

def finalStore (locations : StorageBuiltinCorrespondence.Locations) (state : RuntimeEffectsSemantics.State)
    (kind : Nat) (offset length : Word) (store : Store) : Store :=
  match MemorySemantics.touchSize? state.memory.size offset length with
  | none => store
  | some _ => finishStore locations kind offset length
      (MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length)

def target (state : RuntimeEffectsSemantics.State) (offset length : Word) : Core.Value :=
  match MemorySemantics.touchSize? state.memory.size offset length with
  | none => .inLeft .unit (.word (Word.ofNatModulo 6))
  | some _ => .inLeft .unit (.word Word.maximum)

def StableWord (environment : Environment) (mapping : Renaming) (expression : Core.Expr) (value : Word) : Prop :=
  ∀ (extra : Environment) (store : Store),
    Evaluates (extra ++ environment) store (expression.rename (fun index => extra.length + mapping index)) (.word value) store

private theorem components {scope : Scope} {kind : Nat} {offset length compiled : Core.Expr}
    (accepted : Effects.terminate scope kind offset length = .ok compiled) :
    ∃ memorySize exit returnOffset returnSize,
      Effects.reference scope "memorySize" .word = .ok memorySize ∧
      Effects.reference scope "exit" .word = .ok exit ∧
      Effects.reference scope "returnOffset" .word = .ok returnOffset ∧
      Effects.reference scope "returnSize" .word = .ok returnSize ∧
      compiled = LocalSequence.discard .unit (Memory.touch memorySize offset length)
        ([Core.Expr.storeCell returnOffset offset, .storeCell returnSize length,
          .storeCell exit (.word (Word.ofNatModulo kind))].foldr (fun store next => .letE store (next.weakenAt 0))
          (LanguageResult.failure .unit (.word Word.maximum))) := by
  unfold Effects.terminate at accepted
  obtain ⟨memorySize, memoryCompiled, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨exit, exitCompiled, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨returnOffset, offsetCompiled, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨returnSize, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp accepted
  exact ⟨memorySize, exit, returnOffset, returnSize, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled,
    (Except.ok.inj returned).symm⟩

theorem touch_rename (reference offset length : Core.Expr) (mapping : Renaming) :
    (Memory.touch reference offset length).rename mapping =
      Memory.touch (reference.rename mapping) (offset.rename mapping) (length.rename mapping) := by
  rfl

private theorem rename_weaken_one (expression : Core.Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = expression.rename (fun index => mapping index + 1) := by
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  congr 1

private theorem rename_weaken_two (expression : Core.Expr) (mapping : Renaming) :
    ((expression.weakenAt 0).weakenAt 1).rename mapping.lift.lift =
      expression.rename (fun index => mapping index + 2) := by
  rw [← Core.Expr.rename_insertion, ← Core.Expr.rename_insertion, Core.Expr.rename_comp, Core.Expr.rename_comp]
  congr 1

private theorem rename_weaken_three (expression : Core.Expr) (mapping : Renaming) :
    (((expression.weakenAt 0).weakenAt 1).weakenAt 2).rename mapping.lift.lift.lift =
      expression.rename (fun index => mapping index + 3) := by
  rw [← Core.Expr.rename_insertion, ← Core.Expr.rename_insertion, ← Core.Expr.rename_insertion,
    Core.Expr.rename_comp, Core.Expr.rename_comp, Core.Expr.rename_comp]
  congr 1

theorem terminate_evaluates {scope : Scope} {kind : Nat} {offsetExpr lengthExpr compiled : Core.Expr}
    (accepted : Effects.terminate scope kind offsetExpr lengthExpr = .ok compiled)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : StorageBuiltinCorrespondence.Locations} {state : RuntimeEffectsSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (related : StorageBuiltinCorrespondence.StateRel locations state.storage store)
    (memorySize : store.read? locations.memorySize = some (.word state.memory.size))
    (offset length : Word)
    (offsetStable : StableWord environment mapping offsetExpr offset)
    (lengthStable : StableWord environment mapping lengthExpr length) :
    Evaluates environment store (compiled.rename mapping) (target state offset length)
      (finalStore locations state kind offset length store) := by
  obtain ⟨memory, exit, returnOffset, returnSize, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled, rfl⟩ := components accepted
  have touched := MemoryCorrespondence.touch_evaluates
    (reference_evaluates runtime memorySizeMember memoryCompiled store)
    (by simpa only [List.length_nil, Nat.zero_add, List.nil_append] using offsetStable [] store)
    (by simpa only [List.length_nil, Nat.zero_add, List.nil_append] using lengthStable [] store) memorySize
  have distinct := related.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  cases checked : MemorySemantics.touchSize? state.memory.size offset length with
  | none =>
      simp only [MemoryCorrespondence.touchResult, checked, MemoryCorrespondence.touchStore_failure checked] at touched
      simp only [target, finalStore, checked]
      simp only [LocalSequence.discard, LanguageResult.bind, Core.Expr.rename]
      apply Evaluates.caseLeft (by rw [touch_rename]; exact touched)
      exact .inLeft (.var rfl)
  | some size =>
      simp only [MemoryCorrespondence.touchResult, checked] at touched
      let touchedStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length
      let offsetStore : Store := touchedStore.set locations.returnOffset (.word offset)
      let sizeStore : Store := offsetStore.set locations.returnSize (.word length)
      have offsetRead : touchedStore.read? locations.returnOffset = some (.word state.storage.returnOffset) := by
        exact (MemoryCorrespondence.touchStore_other store (by intro same; simp_all) _ _ _).trans related.returnOffset
      have offsetWritten : touchedStore.write? locations.returnOffset (.word offset) =
          some (touchedStore.set locations.returnOffset (.word offset)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp offsetRead).1, rfl⟩
      have sizeRead : offsetStore.read? locations.returnSize =
          some (.word state.storage.returnSize) := by
        rw [Store.write?_preserves_other offsetWritten (by intro same; simp_all)]
        exact (MemoryCorrespondence.touchStore_other store (by intro same; simp_all) _ _ _).trans related.returnSize
      have sizeWritten : offsetStore.write? locations.returnSize (.word length) =
          some ((touchedStore.set locations.returnOffset (.word offset)).set locations.returnSize (.word length)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeRead).1, rfl⟩
      have exitRead : sizeStore.read?
          locations.exit = some (.word state.storage.exit) := by
        rw [Store.write?_preserves_other sizeWritten (by intro same; simp_all),
          Store.write?_preserves_other offsetWritten (by intro same; simp_all)]
        exact (MemoryCorrespondence.touchStore_other store (by intro same; simp_all) _ _ _).trans related.exit
      have exitWritten : sizeStore.write?
          locations.exit (.word (Word.ofNatModulo kind)) = some (finishStore locations kind offset length touchedStore) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp exitRead).1, rfl⟩
      simp only [target, finalStore, checked, LocalSequence.discard, LanguageResult.bind, List.foldr_cons,
        List.foldr_nil, Core.Expr.rename, Core.Expr.weakenAt, Renaming.lift, LanguageResult.failure]
      apply Evaluates.caseRight (by rw [touch_rename]; exact touched)
      apply Evaluates.letE (boundValue := .unit) (bodyStore := touchedStore.set locations.returnOffset (.word offset))
      · simpa only [rename_weaken_one, List.length_cons, List.length_nil, List.cons_append,
          List.nil_append, Nat.add_comm, Nat.zero_add] using
          (Evaluates.storeCell (reference_evaluates (runtime.prepend [.unit]) offsetMember offsetCompiled touchedStore)
            offsetRead (offsetStable [.unit] touchedStore) offsetWritten)
      · apply Evaluates.letE (boundValue := .unit)
          (bodyStore := (touchedStore.set locations.returnOffset (.word offset)).set locations.returnSize (.word length))
        · simpa [rename_weaken_two, Nat.add_comm] using Evaluates.storeCell
            (reference_evaluates (runtime.prepend [.unit, .unit]) sizeMember sizeCompiled _)
            sizeRead (lengthStable [.unit, .unit] _) sizeWritten
        · apply Evaluates.letE (boundValue := .unit) (bodyStore := finishStore locations kind offset length touchedStore)
          · simpa [rename_weaken_three, Nat.add_comm] using Evaluates.storeCell
              (reference_evaluates (runtime.prepend [.unit, .unit, .unit]) exitMember exitCompiled _)
              exitRead .word exitWritten
          · exact .inLeft .word

theorem finishStore_other {locations : StorageBuiltinCorrespondence.Locations} {store : Store}
    {kind : Nat} {offset length : Word} {location : Nat} {value : Core.Value}
    (exit : location ≠ locations.exit) (returnOffset : location ≠ locations.returnOffset)
    (returnSize : location ≠ locations.returnSize) (found : store.read? location = some value) :
    (finishStore locations kind offset length store).read? location = some value := by
  simp only [finishStore, Store.read?, List.getElem?_set_ne (Ne.symm exit),
    List.getElem?_set_ne (Ne.symm returnOffset), List.getElem?_set_ne (Ne.symm returnSize)]
  exact found

theorem finishStore_frame (locations : StorageBuiltinCorrespondence.Locations) (store : Store)
    (kind : Nat) (offset length : Word) :
    StorageBuiltinCorrespondence.Frame locations store (finishStore locations kind offset length store) := by
  refine ⟨by simp [finishStore], ?_⟩
  intro location value outside found
  simp only [StorageBuiltinCorrespondence.Locations.mutable, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at outside
  exact finishStore_other outside.2.1 outside.2.2.1 outside.2.2.2 found

theorem finish_storage {locations : StorageBuiltinCorrespondence.Locations}
    {state : StorageSemantics.State} {store : Store}
    (related : StorageBuiltinCorrespondence.StateRel locations state store)
    (kind : Nat) (offset length : Word) :
    StorageBuiltinCorrespondence.StateRel locations
      {state with exit := Word.ofNatModulo kind, returnOffset := offset, returnSize := length}
      (finishStore locations kind offset length store) := by
  have distinct := related.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  have offsetBound := (List.getElem?_eq_some_iff.mp related.returnOffset).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.returnSize).1
  have exitBound := (List.getElem?_eq_some_iff.mp related.exit).1
  constructor
  · obtain ⟨accounts, source, found⟩ := related.world
    exact ⟨accounts, source, finishStore_other (locations := locations) (location := locations.world)
      (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) found⟩
  · exact finishStore_other (locations := locations) (location := locations.address)
      (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.address
  · exact finishStore_other (locations := locations) (location := locations.complete)
      (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.complete
  · exact finishStore_other (locations := locations) (location := locations.isStatic)
      (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.isStatic
  · simp [finishStore, Store.read?, exitBound]
  · simp only [finishStore, Store.read?, List.getElem?_set_ne
        (by intro same; simp_all : locations.exit ≠ locations.returnOffset),
      List.getElem?_set_ne (by intro same; simp_all : locations.returnSize ≠ locations.returnOffset)]
    simp [offsetBound]
  · simp only [finishStore, Store.read?, List.getElem?_set_ne
      (by intro same; simp_all : locations.exit ≠ locations.returnSize)]
    simp [sizeBound]
  · exact related.distinct

theorem terminate_state {layout : RuntimeEffectsCorrespondence.Layout}
    {state : RuntimeEffectsSemantics.State} {store : Store}
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (kind : Nat) (offset length : Word) :
    ResultRel .unit (terminate state kind offset length).1 (target state offset length) ∧
    MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      (terminate state kind offset length).2.memory (finalStore layout.storage state kind offset length store) ∧
    StorageBuiltinCorrespondence.StateRel layout.storage (terminate state kind offset length).2.storage
      (finalStore layout.storage state kind offset length store) ∧
    RuntimeEffectsCorrespondence.Frame layout store (finalStore layout.storage state kind offset length store) := by
  cases checked : MemorySemantics.touchSize? state.memory.size offset length with
  | none =>
      simp only [terminate, finalStore, target, checked]
      exact ⟨.language _, memory, storage, ⟨Nat.le_refl _, fun _ _ _ found => found⟩⟩
  | some size =>
      simp only [terminate, finalStore, target, checked]
      have touchFrame := MemoryCorrespondence.Frame.touch layout.memory layout.storage.memorySize
        store state.memory.size offset length
      have finishFrame := finishStore_frame layout.storage
        (MemoryCorrespondence.touchStore store layout.storage.memorySize state.memory.size offset length) kind offset length
      have first := RuntimeEffectsCorrespondence.Frame.of_memory (layout := layout) touchFrame
      have second := RuntimeEffectsCorrespondence.Frame.of_storage (layout := layout) finishFrame
      exact ⟨.language _, RuntimeEffectsCorrespondence.storage_preserves_memory (memory.touch checked) finishFrame,
        finish_storage (RuntimeEffectsCorrespondence.memory_preserves_storage storage touchFrame) kind offset length,
        ⟨Nat.le_trans first.length_le second.length_le,
          fun location value outside found => second.read location value outside (first.read location value outside found)⟩⟩

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

theorem terminate_closures {layout : RuntimeEffectsCorrespondence.Layout}
    {state : RuntimeEffectsSemantics.State} {store : Store}
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (kind : Nat) (offset length : Word) :
    ClosuresPreserved store (finalStore layout.storage state kind offset length store) := by
  cases checked : MemorySemantics.touchSize? state.memory.size offset length with
  | none =>
      simp only [finalStore, checked]
      intro location parameter result body environment found
      exact found
  | some size =>
      simp only [finalStore, checked]
      have touchFrame := MemoryCorrespondence.Frame.touch layout.memory layout.storage.memorySize
        store state.memory.size offset length
      intro location parameter result body environment found
      have first := MemoryEffectCorrespondence.closures_preserved memory touchFrame found
      exact StorageEffectCorrespondence.closures_preserved
        (RuntimeEffectsCorrespondence.memory_preserves_storage storage touchFrame)
        (finishStore_frame layout.storage _ kind offset length) first

private theorem zero_components (operation : Operation) (zero : operation.arity = 0)
    {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero) = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero)
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases zero
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

private theorem two_components (operation : Operation) (two : operation.arity = 2)
    {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind offset length = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases two
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

/-- Argument typing and arity are derived from the accepted outer compiler.
The range and exit registers, including overflow and zero-length behavior,
correspond to the independent source operation at the final actual store. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {state : RuntimeEffectsSemantics.State} {layout : RuntimeEffectsCorrespondence.Layout}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) (sourceType : Ty) :
    ∃ result finalState target final,
      builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ :=
    outer_components (by cases operation <;> rfl) compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  by_cases zero : operation.arity = 0
  · have empty : arguments = [] := List.eq_nil_of_length_eq_zero (arity.trans zero)
    subst arguments
    cases related
    obtain ⟨expression, terminated, rfl⟩ := zero_components operation zero rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind Word.zero Word.zero
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind Word.zero Word.zero⟩
    · cases operation <;> first | rfl | cases zero
    · apply LanguageResult.bind_success .unit packed
      exact terminate_evaluates terminated (runtime.temporary .unit .unit)
        memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
        (fun _ _ => .word) (fun _ _ => .word)
  · have two : operation.arity = 2 := by cases operation <;> simp_all [Operation.arity]
    obtain ⟨offsetExpr, lengthExpr, offset, length, rfl, rfl, rfl⟩ := two_words related words (arity.trans two)
    obtain ⟨expression, terminated, rfl⟩ := two_components operation two rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind offset length
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind offset length⟩
    · cases operation <;> first | rfl | cases two
    · apply LanguageResult.bind_success .unit packed
      apply terminate_evaluates terminated
        (runtime.temporary (.product .word .word) (.pair (.word offset) (.word length)))
        memorySizeMember exitMember offsetMember sizeMember storage memory.size offset length
      · intro extra store
        exact .first (rightValue := .word length) (.var (by simp [Renaming.lift]))
      · intro extra store
        exact .second (leftValue := .word offset) (.var (by simp [Renaming.lift]))

end Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence
