import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Internal.EffectLayers
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.EffectBuiltins

/-!
# Effect layers: termination, copies, hashing

The frame and message proofs of the termination, copy and hash layers.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.TerminationEffectCorrespondence
/-! Concrete termination discharges the external-call obligation and reaches
actual recursive assembly using the existing memory/storage resource model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.TerminationEffectCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution
open RuntimeEffectsCorrespondence (Layout model memory_related storage_related frame_above resources_preserved)

def supported (name : String) : Prop := ∃ operation : TerminationSemantics.Operation, operation.name = name

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots TerminationSemantics.effects := by
  intro functions name type sources initial final result available notFunction called
  obtain ⟨operation, rfl⟩ := available
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed =>
      cases operation <;> simp [TerminationSemantics.Operation.name, Semantics.primitive?] at computed
  | external absent notPrimitive computed =>
      intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
      obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained⟩ :=
        TerminationBuiltinCorrespondence.preserves operation compiled related runtime
          memorySizeMember exitMember offsetMember sizeMember (memory_related state) (storage_related state) packed type
      have same := Option.some.inj (computed.symm.trans meaning)
      cases same
      exact ⟨target, finalStore, resultRelated, evaluated,
        state.cutoff_effect (frame_above frame)
          (resources_preserved state.external.1 state.external.2.2 memoryFinal storageFinal frame),
        installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions TerminationSemantics.effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


theorem terminate_context (state : RuntimeEffectsSemantics.State) (kind : Nat) (offset length : Core.Word) :
    RuntimeEffectsProjectionPreservation.context (TerminationSemantics.terminate state kind offset length).2 =
      RuntimeEffectsProjectionPreservation.context state := by
  unfold TerminationSemantics.terminate
  split <;> rfl

private theorem terminated_context {state final : RuntimeEffectsSemantics.State}
    {kind : Nat} {offset length : Core.Word} {result : Semantics.Result Semantics.Value}
    (called : some (TerminationSemantics.terminate state kind offset length) = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context state := by
  have changed : (TerminationSemantics.terminate state kind offset length).2 = final :=
    congrArg Prod.snd (Option.some.inj called)
  exact (congrArg RuntimeEffectsProjectionPreservation.context changed).symm.trans
    (terminate_context state kind offset length)

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : TerminationSemantics.builtin name type arguments initial = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context initial := by
  by_cases returned : name = "return"
  · subst name
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals try cases first
    all_goals try cases second
    all_goals try contradiction
    rename_i offset length
    exact terminated_context (kind := 1) (offset := offset) (length := length) called
  by_cases reverted : name = "revert"
  · subst name
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals try cases first
    all_goals try cases second
    all_goals try contradiction
    rename_i offset length
    exact terminated_context (kind := 2) (offset := offset) (length := length) called
  by_cases stopped : name = "stop"
  · subst name
    cases arguments with
    | nil => exact terminated_context (kind := 1) (offset := Core.Word.zero) (length := Core.Word.zero) called
    | cons first rest => cases first <;> contradiction
  by_cases invalid : name = "invalid"
  · subst name
    cases arguments with
    | nil => exact terminated_context (kind := 3) (offset := Core.Word.zero) (length := Core.Word.zero) called
    | cons first rest => cases first <;> contradiction
  simp [TerminationSemantics.builtin, returned, reverted, stopped, invalid] at called

theorem context_preserves : EffectProjectionPreservation.Preserves TerminationSemantics.effects
    RuntimeEffectsProjectionPreservation.context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions TerminationSemantics.effects function arguments initial result final) :
    RuntimeEffectsProjectionPreservation.context final.external = RuntimeEffectsProjectionPreservation.context initial.external :=
  EffectProjectionPreservation.function_preserves context_preserves evaluated

end Solcore.Frontend.RustHull.TerminationEffectCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
/-! Message termination uses the established concrete memory/storage model;
its surrounding environment and event cells retain their source observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeLogEffectsCorrespondence.supported slots name ∨ TerminationEffectCorrespondence.supported name

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((memory | storage) | environment) | logs) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem termination_unsupported {slots : List EffectSlot} {name : String}
    (enabled : RuntimeLogEffectsCorrespondence.supported slots name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    TerminationSemantics.builtin name type arguments state = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem runtime_unsupported (operation : TerminationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeLogEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeLogEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
        cases operation <;> rfl
      rw [missing] at computed
      contradiction
  | logs computed =>
      obtain ⟨log, named⟩ := log_named computed
      cases log <;> cases operation <;> simp [LogsSemantics.Operation.name, TerminationSemantics.Operation.name] at named

theorem external_preserves (layout : RuntimeLogEffectsCorrespondence.Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeFullEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeLogEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeLogEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact RuntimeLogEffectsCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember runtimeEnabled notFunction call typeCompiled
      | @termination finalRuntime computed =>
          have terminationEnabled : TerminationEffectCorrespondence.supported name := by
            rcases enabled with runtime | termination
            · rw [termination_unsupported runtime] at computed
              contradiction
            · exact termination
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          let projected : Semantics.State RuntimeEffectsSemantics.State := ⟨initial.heap, initial.external.runtime.runtime⟩
          have call : Semantics.EvalCall functions TerminationSemantics.effects name type sources projected result
              {projected with external := finalRuntime} := .external absent notPrimitive computed
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            TerminationEffectCorrespondence.external_preserves layout.toLayout
              (RuntimeLogEffectsCorrespondence.patched layout baseline initial.external) slots
              memorySizeMember exitMember offsetMember sizeMember terminationEnabled notFunction call typeCompiled
              compiled related packed runtime (RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment) installed
          have afterEnvironment := RuntimeEnvironmentEffectsCorrespondence.runtime_updated
            (RuntimeLogEffectsCorrespondence.passive_runtime passive) beforeEnvironment finalState
          exact ⟨target, finalStore, resultRelated, evaluated, RuntimeLogEffectsCorrespondence.runtime_updated afterEnvironment,
            installedFinal, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeLogEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeFullEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeFullEffectsFrameCorrespondence
/-! Explicit termination reaches actual frame compilation, captured calls,
final resource snapshots, and account lookup using the existing runtime layout. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeFullEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive runtime_related logs_related)
open RuntimeFullEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
abbrev PassiveCell := RuntimeLogEffectsFrameCorrespondence.PassiveCell
abbrev passiveSnapshotNames := RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames
abbrev snapshotValues := RuntimeLogEffectsFrameCorrespondence.snapshotValues
abbrev passive_observed := @RuntimeLogEffectsFrameCorrespondence.passive_observed

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and explicit termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeFullEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeFullEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related state))
  have finalLogs := logs_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeFullEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeFullEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeFullEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeFullEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember initialRelated passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeFullEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractFullCorrespondence
/-! Explicit termination reaches the actual message finalizer, together with
all memory, storage and event observations preceding termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractFullCorrespondence
open Correspondence ScalarExecution CodeBuilder
abbrev resultValue := ContractLogCorrespondence.resultValue
abbrev succeeded := ContractLogCorrespondence.succeeded
abbrev passiveValues := ContractLogCorrespondence.passiveValues
abbrev snapshotValues := ContractLogCorrespondence.snapshotValues
abbrev messageValue := ContractLogCorrespondence.messageValue
abbrev MessageRel := ContractLogCorrespondence.MessageRel
abbrev message_evaluates := @ContractLogCorrespondence.message_evaluates

def supported (name : String) : Prop :=
  ContractLogCorrespondence.supported name ∨ TerminationEffectCorrespondence.supported name

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeFullEffectsCorrespondence.supported slots = supported := by
  funext name
  simp only [RuntimeFullEffectsCorrespondence.supported, supported, ContractLogCorrespondence.supported_actual signature]

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeFullEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeLogEffectsCorrespondence.Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeLogEffectsFrameCorrespondence.PassiveCell layout slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesBound : balancesLocation < layout.boundary)
    (balancesOutside : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable layout) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeFullEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated (passiveValues balances) snapshotObserved
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := RuntimeLogEffectsCorrespondence.other_related related balancesOutside
    simpa only [prefixRead, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractFullCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCopyEffectsCorrespondence
/-! Snapshot copies preserve the surrounding storage, event and immutable
observation cells while updating the shared memory model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCopyEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

def Available (slots : List EffectSlot) (operation : MemoryCopySemantics.Operation) : Prop :=
  operation = .calldata → ∃ location, ⟨"calldata", Core.WordMapping.type, location⟩ ∈ slots

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeFullEffectsCorrespondence.supported slots name ∨
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name ∧ Available slots operation

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((((memory | storage) | environment) | logs) | termination) | ⟨operation, rfl, _⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem runtime_unsupported (operation : MemoryCopySemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeFullEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeFullEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
            cases operation <;> rfl
          rw [missing] at computed
          contradiction
      | logs computed =>
          obtain ⟨log, named⟩ := log_named computed
          cases log <;> cases operation <;> simp [LogsSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | termination computed =>
      have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
        cases operation <;> rfl
      rw [missing] at computed
      contradiction

private theorem name_separate {slots : List EffectSlot} {name : String}
    (enabled : RuntimeFullEffectsCorrespondence.supported slots name) (operation : MemoryCopySemantics.Operation) :
    operation.name ≠ name := by
  rcases enabled with (((memory | storage) | environment) | logs) | termination
  · obtain ⟨op, rfl⟩ := memory
    cases op <;> cases operation <;> decide
  · obtain ⟨op, rfl⟩ := storage
    cases op with | load transient | store transient => cases transient <;> cases operation <;> decide
  · obtain ⟨op, rfl, _⟩ := environment
    cases op <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals cases operation <;> decide
  · obtain ⟨op, rfl⟩ := logs
    cases op <;> cases operation <;> decide
  · obtain ⟨op, rfl⟩ := termination
    cases op <;> cases operation <;> decide

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : Passive layout slots) {world : World} {state : Semantics.State RuntimeCopyEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots) world
      {state with external := RuntimeCopyEffectsSemantics.withMemory state.external memory} final := by
  have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related before
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
  have afterRuntime := beforeRuntime.cutoff_effect
    (RuntimeEffectsCorrespondence.frame_above (RuntimeEffectsCorrespondence.Frame.of_memory frame))
    (RuntimeEffectsCorrespondence.resources_preserved (after := {state.external.runtime.runtime with memory := memory})
      beforeRuntime.external.1 beforeRuntime.external.2.2 memoryAfter
      (RuntimeEffectsCorrespondence.memory_preserves_storage (RuntimeEffectsCorrespondence.storage_related beforeRuntime) frame)
      (RuntimeEffectsCorrespondence.Frame.of_memory frame))
  exact RuntimeLogEffectsCorrespondence.runtime_updated
    (RuntimeEnvironmentEffectsCorrespondence.runtime_updated
      (RuntimeLogEffectsCorrespondence.passive_runtime passive) beforeEnvironment afterRuntime)

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeCopyEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeFullEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl, _⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeFullEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact RuntimeFullEffectsCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember runtimeEnabled notFunction call typeCompiled
      | @copy finalMemory computed =>
          have copyEnabled : ∃ operation : MemoryCopySemantics.Operation, operation.name = name ∧ Available slots operation := by
            rcases enabled with runtime | copy
            · obtain ⟨operation, named⟩ := copy_named computed
              exact False.elim (name_separate runtime operation named)
            · exact copy
          obtain ⟨operation, rfl, available⟩ := copyEnabled
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          have calldataRead : ∀ location, ⟨"calldata", Core.WordMapping.type, location⟩ ∈ slots →
              argumentStore.read? location = some (Core.WordMapping.encode initial.external.runtime.environment.calldata) := by
            intro location member
            exact RuntimeEnvironmentEffectsCorrespondence.observations_related beforeEnvironment _ member _ rfl
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            MemoryCopyBuiltinCorrespondence.preserves operation compiled computed related runtime memoryMember memorySizeMember
              available calldataRead memoryRelated packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated, memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeLogEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeCopyEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeCopyEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCopyEffectsFrameCorrespondence
/-! Memory copies and explicit termination reach actual frame compilation, captured calls,
final resource snapshots, and account lookup using the existing runtime layout. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCopyEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive runtime_related logs_related)
open RuntimeCopyEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
abbrev PassiveCell := RuntimeLogEffectsFrameCorrespondence.PassiveCell
abbrev passiveSnapshotNames := RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames
abbrev snapshotValues := RuntimeLogEffectsFrameCorrespondence.snapshotValues
abbrev passive_observed := @RuntimeLogEffectsFrameCorrespondence.passive_observed

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
memory copies and explicit termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeCopyEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related state))
  have finalLogs := logs_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeCopyEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeCopyEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember initialRelated passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeCopyEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCopyCorrespondence
/-! Copied memory reaches the actual message finalizer together with the
source storage, event and termination observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCopyCorrespondence
open Correspondence ScalarExecution CodeBuilder
abbrev resultValue := ContractLogCorrespondence.resultValue
abbrev succeeded := ContractLogCorrespondence.succeeded
abbrev passiveValues := ContractLogCorrespondence.passiveValues
abbrev snapshotValues := ContractLogCorrespondence.snapshotValues
abbrev messageValue := ContractLogCorrespondence.messageValue
abbrev MessageRel := ContractLogCorrespondence.MessageRel
abbrev message_evaluates := @ContractLogCorrespondence.message_evaluates

def supported (name : String) : Prop := ContractFullCorrespondence.supported name ∨
  ∃ operation : MemoryCopySemantics.Operation, operation.name = name

theorem available_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots)
    (operation : MemoryCopySemantics.Operation) : RuntimeCopyEffectsCorrespondence.Available slots operation := by
  intro _
  have present : ("calldata", Core.WordMapping.type) ∈ RuntimeEffectsFrameCorrespondence.slotTypes slots := by
    rw [signature]
    simp [Effects.slots]
  obtain ⟨slot, member, same⟩ := List.mem_map.mp present
  rcases slot with ⟨name, type, location⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨location, member⟩

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeCopyEffectsCorrespondence.supported slots = supported := by
  funext name
  apply propext
  constructor
  · intro enabled
    rcases enabled with runtime | ⟨operation, named, _⟩
    · exact .inl ((congrFun (ContractFullCorrespondence.supported_actual signature) name) ▸ runtime)
    · exact .inr ⟨operation, named⟩
  · intro enabled
    rcases enabled with runtime | ⟨operation, named⟩
    · exact .inl ((congrFun (ContractFullCorrespondence.supported_actual signature) name).symm ▸ runtime)
    · exact .inr ⟨operation, named, available_actual signature operation⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCopyEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeLogEffectsCorrespondence.Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeLogEffectsFrameCorrespondence.PassiveCell layout slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesBound : balancesLocation < layout.boundary)
    (balancesOutside : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable layout) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeCopyEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated (passiveValues balances) snapshotObserved
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := RuntimeLogEffectsCorrespondence.other_related related balancesOutside
    simpa only [prefixRead, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCopyCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence
/-! Hashing extends the concrete runtime while preserving memory contents,
account state, event snapshots and immutable observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeCopyEffectsCorrespondence.supported slots name ∨ name = "keccak256"

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((memory | storage) | environment) | logs) | termination) | copy) | rfl
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem runtime_unsupported {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : RuntimeCopyEffectsSemantics.Builtin "keccak256" type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed => contradiction
          | logs computed =>
              obtain ⟨operation, named⟩ := log_named computed
              cases operation <;> simp [LogsSemantics.Operation.name] at named
      | termination computed => contradiction
  | copy computed =>
      obtain ⟨operation, named⟩ := copy_named computed
      cases operation <;> simp [MemoryCopySemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeHashEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeCopyEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | rfl
            · exact runtime
            · exact False.elim (runtime_unsupported computed)
          have call : Semantics.EvalCall functions RuntimeCopyEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact RuntimeCopyEffectsCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember runtimeEnabled notFunction call typeCompiled
      | hash computed =>
          have named := hash_named computed
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            KeccakBuiltinCorrespondence.preserves compiled computed related runtime memoryMember memorySizeMember memoryRelated packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated,
            RuntimeCopyEffectsCorrespondence.memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeLogEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeHashEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeHashEffectsFrameCorrespondence
/-! Hashing and explicit termination reach actual frame compilation, captured calls,
final resource snapshots, and account lookup using the existing runtime layout. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeHashEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive runtime_related logs_related)
open RuntimeHashEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
abbrev PassiveCell := RuntimeLogEffectsFrameCorrespondence.PassiveCell
abbrev passiveSnapshotNames := RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames
abbrev snapshotValues := RuntimeLogEffectsFrameCorrespondence.snapshotValues
abbrev passive_observed := @RuntimeLogEffectsFrameCorrespondence.passive_observed

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
memory hashing and explicit termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeHashEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeHashEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related state))
  have finalLogs := logs_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeHashEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeHashEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeHashEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeHashEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember initialRelated passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeHashEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractHashCorrespondence
/-! Hashed memory reaches the actual message finalizer together with the
source storage, event and termination observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractHashCorrespondence
open Correspondence ScalarExecution CodeBuilder
abbrev resultValue := ContractLogCorrespondence.resultValue
abbrev succeeded := ContractLogCorrespondence.succeeded
abbrev passiveValues := ContractLogCorrespondence.passiveValues
abbrev snapshotValues := ContractLogCorrespondence.snapshotValues
abbrev messageValue := ContractLogCorrespondence.messageValue
abbrev MessageRel := ContractLogCorrespondence.MessageRel
abbrev message_evaluates := @ContractLogCorrespondence.message_evaluates

def supported (name : String) : Prop := ContractCopyCorrespondence.supported name ∨ name = "keccak256"

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeHashEffectsCorrespondence.supported slots = supported := by
  funext name
  unfold RuntimeHashEffectsCorrespondence.supported supported
  rw [ContractCopyCorrespondence.supported_actual signature]

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeHashEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeLogEffectsCorrespondence.Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeLogEffectsFrameCorrespondence.PassiveCell layout slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesBound : balancesLocation < layout.boundary)
    (balancesOutside : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable layout) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeHashEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated (passiveValues balances) snapshotObserved
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := RuntimeLogEffectsCorrespondence.other_related related balancesOutside
    simpa only [prefixRead, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractHashCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
/-! The actual return-data source guards preserve their order before copying.
Both invalid-source branches use the existing termination proof, while a valid
source reaches packed copying and retains unrelated cells and closures. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

private theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" arguments = .ok lowered) :
    arguments.length = 3 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" [destination, source, length] = .ok lowered) :
    ∃ dataSize invalid memory size data,
      Effects.reference scope "returnDataSize" .word = .ok dataSize ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "returnData" WordMapping.type = .ok data ∧
      lowered = ⟨.unit, .ifE (.binary .wordGt source (.loadCell dataSize)) invalid
        (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
          (Memory.copyPackedFrom memory size destination (.loadCell data) source length))⟩ := by
  have expanded : (do
      let raw ← (do
        let dataSize ← Effects.reference scope "returnDataSize" .word
        let invalid ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let memory ← Effects.reference scope "memory" WordMapping.type
        let size ← Effects.reference scope "memorySize" .word
        let data ← Effects.reference scope "returnData" WordMapping.type
        pure (Lowered.mk .unit (.ifE (.binary .wordGt source (.loadCell dataSize)) invalid
          (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
            (Memory.copyPackedFrom memory size destination (.loadCell data) source length)))) : LowerM Lowered)
      pure raw) = .ok lowered := compiled
  obtain ⟨dataSize, dataSizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨invalid, invalidCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨memory, memoryCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨size, sizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨data, dataCompiled, returned⟩ := lower_bind_eq_ok.mp expanded
  exact ⟨dataSize, invalid, memory, size, data, dataSizeCompiled, invalidCompiled,
    memoryCompiled, sizeCompiled, dataCompiled, (Except.ok.inj returned).symm⟩

theorem preserves {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "returndatacopy" expected arguments = .ok lowered)
    {entries : MemorySemantics.Entries} {dataSize : Word} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : ReturnDataSemantics.Builtin entries dataSize "returndatacopy" sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {layout : RuntimeEffectsCorrespondence.Layout} {dataLocation dataSizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, dataLocation⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, dataSizeLocation⟩ ∈ slots)
    (dataRead : store.read? dataLocation = some (WordMapping.encode entries))
    (dataSizeRead : store.read? dataSizeLocation = some (.word dataSize))
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target final,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  obtain ⟨dataSizeRef, invalid, memoryRef, sizeRef, dataRef,
    dataSizeCompiled, invalidCompiled, memoryCompiled, sizeCompiled, dataCompiled, rfl⟩ := components rawCompiled
  cases typed
  cases loweredEqual
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime'
    memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
    (fun _ _ => .word) (fun _ _ => .word)
  have terminatedState := TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
  have terminatedClosures : ClosuresPreserved store
      (TerminationBuiltinCorrespondence.finalStore layout.storage state 3 Word.zero Word.zero store) :=
    TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero
  have sourceEvaluated : Evaluates (input :: environment) store
      ((projectArgument 1 3 (.var 0)).rename mapping.lift) (.word source) store :=
    .first (.second (.var rfl))
  have lengthEvaluated : Evaluates (input :: environment) store
      ((projectArgument 2 3 (.var 0)).rename mapping.lift) (.word length) store :=
    .second (.second (.var rfl))
  have dataSizeEvaluated := Evaluates.loadCell (reference_evaluates runtime' dataSizeMember dataSizeCompiled store) dataSizeRead
  cases called with
  | copy executed =>
      cases executed with
      | sourceOverflow invalidSource =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifTrue (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, invalidSource])) terminated
      | lengthOverflow validSource invalidLength =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
          exact .ifTrue (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
            (by simp [BinaryOp.apply, invalidLength])) terminated
      | copied validSource validLength executed =>
          obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed memory
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' memorySizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' dataMember dataCompiled store) dataRead)
              sourceEvaluated lengthEvaluated
          refine ⟨target, final, resultRelated, ?_, finalRelated,
            RuntimeEffectsCorrespondence.memory_preserves_storage storage frame,
            RuntimeEffectsCorrespondence.Frame.of_memory frame,
            MemoryEffectCorrespondence.closures_preserved memory frame⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
          apply Evaluates.ifFalse (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
            (by simp [BinaryOp.apply, validLength]))
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

end Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeControlEffectsCorrespondence
/-! Termination reuses the concrete memory/storage layout and its resource
model. No external implementation assumption remains at recursive assembly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeControlEffectsCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution
open RuntimeEffectsCorrespondence (Layout model)

def supported (name : String) : Prop :=
  RuntimeEffectsCorrespondence.supported name ∨ TerminationEffectCorrespondence.supported name

private theorem termination_unsupported {name : String}
    (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    TerminationSemantics.builtin name type arguments state = none := by
  rcases available with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
  · cases operation <;> rfl
  · cases operation with | load transient | store transient => cases transient <;> rfl

private theorem runtime_unsupported (operation : TerminationSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> rfl

theorem runtime_builtin {name : String} (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeControlEffectsSemantics.builtin name type arguments state =
      RuntimeEffectsSemantics.builtin name type arguments state := by
  unfold RuntimeControlEffectsSemantics.builtin
  cases computed : RuntimeEffectsSemantics.builtin name type arguments state with
  | some output => rfl
  | none => exact termination_unsupported available type arguments state

theorem termination_builtin (operation : TerminationSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeControlEffectsSemantics.builtin operation.name type arguments state =
      TerminationSemantics.builtin operation.name type arguments state := by
  simp only [RuntimeControlEffectsSemantics.builtin, runtime_unsupported]

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots RuntimeControlEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  rcases enabled with runtimeEnabled | ⟨operation, rfl⟩
  · have call : Semantics.EvalCall functions RuntimeEffectsSemantics.effects name type sources initial result final := by
      cases called with
      | function selected called => rw [notFunction] at selected; contradiction
      | primitive absent computed => exact .primitive absent computed
      | external absent notPrimitive computed =>
          exact .external absent notPrimitive ((runtime_builtin runtimeEnabled type sources initial.external).symm.trans computed)
    intro typeFuel expected typeCompiled
    exact RuntimeEffectsCorrespondence.external_preserves layout baseline slots memoryMember worldMember
      addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      runtimeEnabled notFunction call typeCompiled
  · have call : Semantics.EvalCall functions TerminationSemantics.effects operation.name type sources initial result final := by
      cases called with
      | function selected called => rw [notFunction] at selected; contradiction
      | primitive absent computed => exact .primitive absent computed
      | external absent notPrimitive computed =>
          exact .external absent notPrimitive ((termination_builtin operation type sources initial.external).symm.trans computed)
    intro typeFuel expected typeCompiled
    exact TerminationEffectCorrespondence.external_preserves layout baseline slots
      memorySizeMember exitMember offsetMember sizeMember ⟨operation, rfl⟩ notFunction call typeCompiled

/-- Memory, storage, and explicit termination preserve their independent
meaning through actual recursive assembly. -/
theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeControlEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context initial := by
  unfold RuntimeControlEffectsSemantics.builtin at called
  split at called
  · rename_i output runtime
    exact RuntimeEffectsProjectionPreservation.builtin_context (runtime.trans called)
  · exact TerminationEffectCorrespondence.builtin_context called

theorem context_preserves : EffectProjectionPreservation.Preserves RuntimeControlEffectsSemantics.effects
    RuntimeEffectsProjectionPreservation.context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function arguments initial result final) :
    RuntimeEffectsProjectionPreservation.context final.external = RuntimeEffectsProjectionPreservation.context initial.external :=
  EffectProjectionPreservation.function_preserves context_preserves evaluated

theorem function_observations {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function arguments initial result final) :
    final.external.storage.address = initial.external.storage.address ∧
    final.external.storage.complete = initial.external.storage.complete ∧
    final.external.storage.isStatic = initial.external.storage.isStatic :=
  ⟨congrArg RuntimeEffectsProjectionPreservation.Context.address (function_context evaluated),
   congrArg RuntimeEffectsProjectionPreservation.Context.complete (function_context evaluated),
   congrArg RuntimeEffectsProjectionPreservation.Context.isStatic (function_context evaluated)⟩

end Solcore.Frontend.RustHull.RuntimeControlEffectsCorrespondence
end
