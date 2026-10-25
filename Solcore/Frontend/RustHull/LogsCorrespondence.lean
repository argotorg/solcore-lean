import Solcore.Frontend.RustHull.LogsSemantics
import Solcore.Frontend.RustHull.Logs
import Solcore.Frontend.RustHull.MemoryCorrespondence

/-! Event payload snapshots execute through the emitted mapping helpers.
All helper allocations remain in the resulting Core store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogsCorrespondence
open Core

theorem invoke_evaluates {environment captured : Environment} {store final : Store}
    {parameter result : Core.Ty} {body reference argument : Core.Expr} {location : Nat} {input output : Value}
    (referenceEvaluated : Evaluates environment store reference
      (.cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location) store)
    (installed : WordMapping.Installed store parameter result body location captured)
    (argumentEvaluated : Evaluates (WordMapping.closure parameter result body location captured :: environment)
      store (argument.weakenAt 0) input store)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location :: captured)
      store body output final) :
    Evaluates environment store (WordMapping.invoke parameter result reference argument) output final :=
  .caseRight (OptionalCell.read_success Word.zero referenceEvaluated installed)
    (.apply (.var rfl) argumentEvaluated bodyEvaluated)

theorem runHelper_evaluates {environment : Environment} {initial store final : Store}
    {parameter result : Core.Ty} {body argument : Core.Expr} {input output : Value}
    (argumentEvaluated : Evaluates environment initial argument input store)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) store.length :: input :: environment)
      (WordMapping.installedStore store parameter result body input environment) body output final) :
    Evaluates environment initial (WordMapping.runHelper parameter result body argument) output final := by
  apply Evaluates.letE argumentEvaluated
  apply Evaluates.letE (OptionalCell.allocate_evaluates _ _ _)
  apply Evaluates.letE (bodyStore := WordMapping.installedStore store parameter result body input environment)
  · apply Evaluates.storeCell (oldValue := .inLeft (WordMapping.helperType parameter result) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, WordMapping.installedStore, WordMapping.closure]
  · apply invoke_evaluates (body := body) (captured := input :: environment) (.var rfl)
    · simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]
    · simpa [Core.Expr.weakenAt] using (Evaluates.var (by rfl))
    · exact bodyEvaluated

theorem installed_append {store : Store} {parameter result : Core.Ty} {body : Core.Expr}
    {location : Nat} {captured : Environment}
    (installed : WordMapping.Installed store parameter result body location captured) (suffix : Store) :
    WordMapping.Installed (store ++ suffix) parameter result body location captured := by
  have bound := (List.getElem?_eq_some_iff.mp installed).1
  simpa only [WordMapping.Installed, Store.read?, List.getElem?_append_left bound] using installed

def copyInput (memory : LogsSemantics.Words) (offset length : Word)
    (mapping : LogsSemantics.Words) (cursor : Word) : Value :=
  .pair (WordMapping.encode memory) (.pair (.word offset) (.pair (.word length)
    (.pair (WordMapping.encode mapping) (.word cursor))))

theorem copyBody_evaluates {memory : LogsSemantics.Words} {offset length cursor : Word}
    {mapping result : LogsSemantics.Words} (copied : LogsSemantics.Copy memory offset length mapping cursor result)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Logs.copyType WordMapping.type Logs.copyBody location captured) :
    ∃ suffix, Evaluates
      (copyInput memory offset length mapping cursor ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Logs.copyType WordMapping.type)) location :: captured)
      store Logs.copyBody (.inRight .word (WordMapping.encode result)) (store ++ suffix) := by
  induction copied generalizing store with
  | empty offset cursor mapping =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact .ifTrue (.binary (.first (.second (.second (.var rfl)))) .word rfl)
        (.inRight (.first (.second (.second (.second (.var rfl))))))
  | @step offset length cursor mapping result nonempty rest ih =>
      let input := copyInput memory offset length mapping cursor
      let environment := input :: .cellRef (OptionalCell.cellType (WordMapping.helperType Logs.copyType WordMapping.type)) location :: captured
      let readStore := MemoryCorrespondence.readWordStore store memory offset environment
      obtain ⟨readSuffix, readExtended⟩ := MemoryCorrespondence.readWordStore_extension store memory offset environment
      have readEvaluated := MemoryCorrespondence.readMemoryWord_evaluates
        (environment := environment) (initial := store)
        (mapping := Logs.field 0 5 (.var 0)) (offsetExpr := Logs.field 1 5 (.var 0)) memory offset
        (.first (.var rfl)) (.first (.second (.var rfl)))
      let word := MemorySemantics.readWord memory offset
      let count := LogsSemantics.chunk length
      let distance := LogsSemantics.padding length
      let updated := MemorySemantics.insert cursor (LogsSemantics.paddedWord memory offset length) mapping
      let insertEnvironment := Value.word distance :: .word count :: .word word :: environment
      let inserted := MemoryCorrespondence.insertStore readStore mapping cursor
        (LogsSemantics.paddedWord memory offset length) insertEnvironment
      have insertedInstalled : WordMapping.Installed inserted Logs.copyType WordMapping.type Logs.copyBody location captured := by
        apply installed_append (suffix := [_])
        rw [show readStore = store ++ readSuffix from readExtended]
        exact installed_append installed readSuffix
      obtain ⟨suffix, evaluated⟩ := ih inserted insertedInstalled
      refine ⟨readSuffix ++ [.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody readStore.length
        (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word (LogsSemantics.paddedWord memory offset length))) :: insertEnvironment))] ++ suffix, ?_⟩
      have finalStore : inserted ++ suffix = store ++
          (readSuffix ++ [.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody readStore.length
            (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word (LogsSemantics.paddedWord memory offset length))) :: insertEnvironment))] ++ suffix) := by
        change (readStore ++ [_]) ++ suffix = _
        rw [show readStore = store ++ readSuffix from readExtended]
        simp only [List.append_assoc]
      rw [← finalStore]
      apply Evaluates.ifFalse
      · apply Evaluates.binary (.first (.second (.second (.var rfl)))) .word
        change some (Value.bool (length == Word.zero)) = some (Value.bool false)
        exact congrArg (fun value => some (Value.bool value)) (beq_eq_false_iff_ne.mpr nonempty)
      · apply LanguageResult.bind_success WordMapping.type readEvaluated
        have countEvaluated : Evaluates (.word word :: environment) readStore
            (.ifE (.binary .wordGt (Logs.field 2 5 (.var 1)) (Logs.number 31)) (Logs.number 32) (Logs.field 2 5 (.var 1)))
            (.word count) readStore := by
          by_cases enough : length > Word.ofNatModulo 31
          · simp only [count, LogsSemantics.chunk, enough, ↓reduceIte]
            exact .ifTrue (.binary (.first (.second (.second (.var rfl)))) .word (by simp [BinaryOp.apply, enough])) .word
          · simp only [count, LogsSemantics.chunk, enough, ↓reduceIte]
            exact .ifFalse (.binary (.first (.second (.second (.var rfl)))) .word (by simp [BinaryOp.apply, enough]))
              (.first (.second (.second (.var rfl))))
        apply Evaluates.letE countEvaluated
        apply Evaluates.letE (.binary (.binary .word (.var rfl) rfl) .word rfl)
        apply LanguageResult.bind_success WordMapping.type
        · have insertedEvaluated := WordMapping.insert_evaluates mapping cursor
            (LogsSemantics.paddedWord memory offset length)
            (environment := insertEnvironment) (initialStore := readStore)
            (mapping := Logs.field 3 5 (.var 3)) (keyExpr := Logs.field 4 5 (.var 3))
            (valueExpr := .binary .wordShl (.binary .wordShr (.var 2) (.var 0)) (.var 0))
            (.first (.second (.second (.second (.var rfl))))) (.second (.second (.second (.second (.var rfl)))))
            (.binary (.binary (.var rfl) (.var rfl) rfl) (.var rfl) rfl)
          simpa only [← MemoryCorrespondence.insert_eq, insertEnvironment, distance, LogsSemantics.padding, count] using insertedEvaluated
        · apply invoke_evaluates (body := Logs.copyBody) (captured := captured)
            (input := copyInput memory (offset.add count) (length.sub count) updated (cursor.add (Word.ofNatModulo 1)))
            (.var rfl) insertedInstalled
          · simp [Core.Expr.weakenAt, Logs.packet, Logs.field, Logs.add, Logs.number]
            exact .pair (.first (.var rfl)) (.pair
              (.binary (.first (.second (.var rfl))) (.var rfl) rfl)
              (.pair (.binary (.first (.second (.second (.var rfl)))) (.var rfl) rfl)
                (.pair (.var rfl) (.binary (leftValue := .word cursor) (.second (.second (.second (.second (.var rfl))))) .word rfl))))
          · exact evaluated

theorem copyPayload_evaluates {memory : LogsSemantics.Words} {offset length cursor : Word}
    {mapping result : LogsSemantics.Words} (copied : LogsSemantics.Copy memory offset length mapping cursor result)
    {environment : Environment} {store : Store} {memoryExpr offsetExpr lengthExpr mappingExpr cursorExpr : Core.Expr}
    (memoryEvaluated : Evaluates environment store memoryExpr (WordMapping.encode memory) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (mappingEvaluated : Evaluates environment store mappingExpr (WordMapping.encode mapping) store)
    (cursorEvaluated : Evaluates environment store cursorExpr (.word cursor) store) :
    ∃ suffix, Evaluates environment store (Logs.copyPayload memoryExpr offsetExpr lengthExpr mappingExpr cursorExpr)
      (.inRight .word (WordMapping.encode result)) (store ++ suffix) := by
  let input := copyInput memory offset length mapping cursor
  let closure := WordMapping.closure Logs.copyType WordMapping.type Logs.copyBody store.length (input :: environment)
  obtain ⟨suffix, body⟩ := copyBody_evaluates copied (store ++ [.inRight .unit closure]) store.length (input :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  apply runHelper_evaluates (.pair memoryEvaluated (.pair offsetEvaluated (.pair lengthEvaluated (.pair mappingEvaluated cursorEvaluated))))
  exact body

/-- Header expressions contain immutable frame arguments. Their evaluation is
stable under the binders and helper allocations used by sequential insertion. -/
def Stable (environment : Environment) (expression : Core.Expr) (value : Value) : Prop :=
  ∀ extra store, Evaluates (extra ++ environment) store
    (expression.rename (fun index => index + extra.length)) value store

theorem Stable.evaluates {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (store : Store) :
    Evaluates environment store expression value store := by
  have evaluated := stable [] store
  change Evaluates environment store (expression.rename Renaming.id) value store at evaluated
  simpa only [Core.Expr.rename_id] using evaluated

theorem Stable.prepend {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (inserted : Value) :
    Stable (inserted :: environment) (expression.weakenAt 0) value := by
  intro extra store
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  have renamed : Renaming.comp (fun index => index + extra.length) (Renaming.insertion 0) =
      (fun index => index + (extra ++ [inserted]).length) := by
    funext index
    simp only [Renaming.comp, Renaming.insertion, Nat.zero_le, ↓reduceIte, List.length_append, List.length_singleton]
    omega
  rw [renamed]
  simpa only [List.append_assoc, List.singleton_append] using stable (extra ++ [inserted]) store

theorem Stable.var {environment : Environment} {index : Nat} {value : Value}
    (found : environment[index]? = some value) : Stable environment (.var index) value := by
  intro extra store
  apply Evaluates.var
  simpa only [Nat.add_comm index, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using found

theorem Stable.word (environment : Environment) (value : Word) : Stable environment (.word value) (.word value) :=
  fun _ _ => .word

theorem Stable.first {environment : Environment} {expression : Core.Expr} {first second : Value}
    (stable : Stable environment expression (.pair first second)) : Stable environment (.first expression) first :=
  fun extra store => .first (stable extra store)

theorem Stable.second {environment : Environment} {expression : Core.Expr} {first second : Value}
    (stable : Stable environment expression (.pair first second)) : Stable environment (.second expression) second :=
  fun extra store => .second (stable extra store)

theorem Stable.addOne {environment : Environment} {expression : Core.Expr} {value : Word}
    (stable : Stable environment expression (.word value)) :
    Stable environment (Logs.add expression (Logs.number 1)) (.word (value.add (Word.ofNatModulo 1))) :=
  fun extra store => .binary (stable extra store) .word rfl

inductive WordExpressions (environment : Environment) : List Core.Expr → List Word → Prop where
  | nil : WordExpressions environment [] []
  | cons {expression expressions value values}
      (head : Stable environment expression (.word value))
      (tail : WordExpressions environment expressions values) :
      WordExpressions environment (expression :: expressions) (value :: values)

theorem WordExpressions.prepend {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) (inserted : Value) :
    WordExpressions (inserted :: environment) (expressions.map (·.weakenAt 0)) values := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.prepend inserted) ih

theorem insertWords_evaluates {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values)
    (mapping : LogsSemantics.Words) (cursor : Word) {mappingExpr cursorExpr : Core.Expr}
    (store : Store) (mappingEvaluated : Evaluates environment store mappingExpr (WordMapping.encode mapping) store)
    (cursorStable : Stable environment cursorExpr (.word cursor)) :
    ∃ suffix, Evaluates environment store (Logs.insertWords mappingExpr cursorExpr expressions)
      (.inRight .word (WordMapping.encode (LogsSemantics.insertWords mapping cursor values))) (store ++ suffix) := by
  induction values generalizing environment expressions mapping cursor mappingExpr cursorExpr store with
  | nil =>
      cases related
      exact ⟨[], by simpa only [List.append_nil, Logs.insertWords, LogsSemantics.insertWords, LanguageResult.success] using Evaluates.inRight (leftType := .word) mappingEvaluated⟩
  | cons value values ih =>
      cases related with
      | @cons expression expressions _ _ head tail =>
          let updated := MemorySemantics.insert cursor value mapping
          let inserted := MemoryCorrespondence.insertStore store mapping cursor value environment
          obtain ⟨suffix, rest⟩ := ih (tail.prepend (WordMapping.encode updated)) updated
            (cursor.add (Word.ofNatModulo 1)) inserted (mappingExpr := .var 0)
            (cursorExpr := Logs.add (cursorExpr.weakenAt 0) (Logs.number 1)) (.var rfl)
            ((cursorStable.prepend (WordMapping.encode updated)).addOne)
          refine ⟨[.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody store.length
            (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word value)) :: environment))] ++ suffix, ?_⟩
          rw [← List.append_assoc, Logs.insertWords, LogsSemantics.insertWords]
          apply LanguageResult.bind_success WordMapping.type
          · simpa only [← MemoryCorrespondence.insert_eq] using WordMapping.insert_evaluates mapping cursor value
              mappingEvaluated (cursorStable.evaluates store) (head.evaluates store)
          · exact rest

def wordPacket : List Word → Value
  | [] => .unit
  | [value] => .word value
  | value :: rest => .pair (.word value) (wordPacket rest)

theorem WordExpressions.length {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) : expressions.length = values.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

theorem WordExpressions.packet {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) :
    Stable environment (Logs.packet expressions) (wordPacket values) := by
  induction related with
  | nil => exact fun _ _ => .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head
      | cons next rest => exact fun extra store => .pair (head extra store) (ih extra store)

theorem Stable.field {environment : Environment} {expression : Core.Expr} {values : List Word}
    (stable : Stable environment expression (wordPacket values)) {index : Nat} {value : Word}
    (found : values[index]? = some value) :
    Stable environment (Logs.field index values.length expression) (.word value) := by
  induction values generalizing expression index with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => cases Option.some.inj found; exact stable
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero => cases Option.some.inj found; exact stable.first
          | succ index =>
              simpa [Logs.field] using ih stable.second found

theorem WordExpressions.of_getElem? {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (length : expressions.length = values.length)
    (related : ∀ (index : Nat) expression value, expressions[index]? = some expression → values[index]? = some value →
      Stable environment expression (.word value)) : WordExpressions environment expressions values := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => exact .nil
      | cons value values => simp at length
  | cons expression expressions ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          exact .cons (related 0 expression value rfl rfl)
            (ih (Nat.succ.inj length) (fun index expression value codeFound valueFound =>
              related (index + 1) expression value codeFound valueFound))

theorem Stable.fields {environment : Environment} {expression : Core.Expr} {values : List Word}
    (stable : Stable environment expression (wordPacket values)) :
    WordExpressions environment ((List.range values.length).map (fun index => Logs.field index values.length expression)) values := by
  apply WordExpressions.of_getElem? (by simp)
  intro index code value codeFound valueFound
  have bound := (List.getElem?_eq_some_iff.mp valueFound).1
  simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some] at codeFound
  cases Option.some.inj codeFound
  exact stable.field valueFound

theorem WordExpressions.append {environment : Environment} {first second : List Core.Expr} {left right : List Word}
    (heads : WordExpressions environment first left) (tails : WordExpressions environment second right) :
    WordExpressions environment (first ++ second) (left ++ right) := by
  induction heads with
  | nil => exact tails
  | cons head tail ih => exact .cons head ih

structure Locations where
  memory : Nat
  memorySize : Nat
  logs : Nat
  logSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.memory, locations.memorySize, locations.logs, locations.logSize]

structure StateRel (locations : Locations) (state : LogsSemantics.State) (store : Store) : Prop where
  distinct : locations.all.Nodup
  memory : store.read? locations.memory = some (WordMapping.encode state.memory.words)
  memorySize : store.read? locations.memorySize = some (.word state.memory.size)
  logs : store.read? locations.logs = some (WordMapping.encode state.words)
  logSize : store.read? locations.logSize = some (.word state.cursor)

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length : initial.length ≤ final.length
  read : ∀ location value, location ∉ locations.all → initial.read? location = some value → final.read? location = some value

theorem Frame.refl (locations : Locations) (store : Store) : Frame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.trans {locations : Locations} {initial middle final : Store}
    (first : Frame locations initial middle) (second : Frame locations middle final) : Frame locations initial final :=
  ⟨Nat.le_trans first.length second.length, fun location value outside found =>
    second.read location value outside (first.read location value outside found)⟩

theorem Frame.append (locations : Locations) (store suffix : Store) : Frame locations store (store ++ suffix) where
  length := by simp
  read := by
    intro location value _ found
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

theorem Frame.set (locations : Locations) (store : Store) (location : Nat) (value : Value)
    (member : location ∈ locations.all) : Frame locations store (store.set location value) where
  length := by simp
  read := by
    intro other old outside found
    have different : location ≠ other := fun equal => outside (equal ▸ member)
    simpa [Store.read?, different] using found

theorem Frame.touch (locations : Locations) (store : Store) (size offset length : Word) :
    Frame locations store (MemoryCorrespondence.touchStore store locations.memorySize size offset length) where
  length := by rw [MemoryCorrespondence.touchStore_length]; exact Nat.le_refl _
  read := by
    intro location value outside found
    exact (MemoryCorrespondence.touchStore_other store
      (by intro equal; exact outside (by simp [Locations.all, equal])) size offset length).trans found

theorem StateRel.append {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) (suffix : Store) : StateRel locations state (store ++ suffix) where
  distinct := related.distinct
  memory := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.memory).1] using related.memory
  memorySize := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.memorySize).1] using related.memorySize
  logs := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.logs).1] using related.logs
  logSize := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.logSize).1] using related.logSize

theorem StateRel.touch {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) {offset length size : Word}
    (expanded : MemorySemantics.touchSize? state.memory.size offset length = some size) :
    StateRel locations {state with memory := {state.memory with size := size}}
      (MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  refine ⟨related.distinct, ?_, MemoryCorrespondence.touchStore_read related.memorySize expanded, ?_, ?_⟩
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.memory
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.logs
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.logSize

def publishStore (locations : Locations) (store : Store) (words : LogsSemantics.Words) (cursor : Word) : Store :=
  (store.set locations.logs (WordMapping.encode words)).set locations.logSize (.word cursor)

theorem StateRel.publish {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) (words : LogsSemantics.Words) (cursor : Word) :
    StateRel locations {state with words := words, cursor := cursor} (publishStore locations store words cursor) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  have logsBound := (List.getElem?_eq_some_iff.mp related.logs).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.logSize).1
  refine ⟨related.distinct, ?_, ?_, ?_, ?_⟩
  · simpa [publishStore, Store.read?, show locations.logSize ≠ locations.memory by intro equal; simp_all,
      show locations.logs ≠ locations.memory by intro equal; simp_all] using related.memory
  · simpa [publishStore, Store.read?, show locations.logSize ≠ locations.memorySize by intro equal; simp_all,
      show locations.logs ≠ locations.memorySize by intro equal; simp_all] using related.memorySize
  · simp [publishStore, Store.read?, show locations.logSize ≠ locations.logs by intro equal; simp_all, logsBound]
  · simp [publishStore, Store.read?, sizeBound]

theorem Frame.publish (locations : Locations) (store : Store) (words : LogsSemantics.Words) (cursor : Word) :
    Frame locations store (publishStore locations store words cursor) :=
  (Frame.set locations store locations.logs (WordMapping.encode words) (by simp [Locations.all])).trans
    (Frame.set locations _ locations.logSize (.word cursor) (by simp [Locations.all]))

def appendInput (locations : Locations) (address offset length : Word) (topics : List Word) : Value :=
  .pair (.cellRef WordMapping.type locations.memory)
    (.pair (.cellRef .word locations.memorySize) (.pair (.cellRef WordMapping.type locations.logs)
      (.pair (.cellRef .word locations.logSize) (.pair (.word address)
        (.pair (.word offset) (.pair (.word length) (wordPacket topics)))))))

def appendTail (count : Nat) : Core.Expr :=
  .ifE (.binary .wordGt (.var 1) (.var 0))
    (LanguageResult.failure .unit (.word Logs.capacityReason))
    (LanguageResult.bind .unit
      (Memory.touch (Logs.field 1 8 (.var 2)) (Logs.field 5 8 (.var 2)) (Logs.field 6 8 (.var 2)))
      (.letE (.loadCell (Logs.field 0 8 (.var 3)))
        (let headers := [Logs.field 4 8 (.var 4), Logs.number count, Logs.field 6 8 (.var 4)] ++
           (List.range count).map (fun index => Logs.field index count (Logs.field 7 8 (.var 4)))
         LanguageResult.bind .unit
           (Logs.insertWords (.loadCell (Logs.field 2 8 (.var 4))) (.var 3) headers)
           (LanguageResult.bind .unit
             (Logs.copyPayload (.var 1) (Logs.field 5 8 (.var 5)) (Logs.field 6 8 (.var 5))
               (.var 0) (Logs.add (.var 4) (Logs.number (3 + count))))
             (LanguageResult.success
               (.letE (.storeCell (Logs.field 2 8 (.var 6)) (.var 0))
                 (.storeCell (Logs.field 3 8 (.var 7)) (.var 5))))))))

theorem wordCount_evaluates {environment : Environment} {store : Store} {expression : Core.Expr} {length : Word}
    (stable : Stable environment expression (.word length)) :
    Evaluates environment store (Logs.wordCount expression) (.word (LogsSemantics.wordCount length)) store := by
  unfold Logs.wordCount LogsSemantics.wordCount
  apply Evaluates.binary (rightValue := .word (if length.umod (Word.ofNatModulo 32) == Word.zero then Word.zero else Word.ofNatModulo 1))
    (.binary (stable.evaluates store) .word rfl)
  · by_cases multiple : length.umod (Word.ofNatModulo 32) == Word.zero
    · simp only [multiple, ↓reduceIte]
      exact .ifTrue (.binary (.binary (stable.evaluates store) .word rfl) .word
        (by change some (Value.bool (length.umod (Word.ofNatModulo 32) == Word.zero)) = _; rw [multiple])) .word
    · simp only [multiple]
      exact .ifFalse (.binary (.binary (stable.evaluates store) .word rfl) .word
        (by change some (Value.bool (length.umod (Word.ofNatModulo 32) == Word.zero)) = _; rw [Bool.eq_false_iff.mpr multiple])) .word
  · rfl

theorem append_enter {environment : Environment} {store final : Store} {locations : Locations} {state : LogsSemantics.State}
    {memoryRef sizeRef logsRef cursorRef addressExpr offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr}
    {offset length : Word} {topics : List Word} {result : Value}
    (related : StateRel locations state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type locations.memory) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word locations.memorySize) store)
    (logsEvaluated : Evaluates environment store logsRef (.cellRef WordMapping.type locations.logs) store)
    (cursorEvaluated : Evaluates environment store cursorRef (.cellRef .word locations.logSize) store)
    (addressEvaluated : Evaluates environment store addressExpr (.word state.address) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (topicsRelated : WordExpressions environment topicExprs topics) (allowed : topics.length ≤ 4)
    (continued : Evaluates
      (.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor ::
        appendInput locations state.address offset length topics :: environment)
      store (appendTail topics.length) result final) :
    Evaluates environment store (Logs.append memoryRef sizeRef logsRef cursorRef addressExpr topicExprs offsetExpr lengthExpr) result final := by
  have count := topicsRelated.length
  simp only [Logs.append, count, show ¬topics.length > 4 from Nat.not_lt.mpr allowed, ↓reduceIte]
  apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair logsEvaluated (.pair cursorEvaluated
    (.pair addressEvaluated (.pair offsetEvaluated (.pair lengthEvaluated (topicsRelated.packet.evaluates store))))))))
  apply Evaluates.letE (.loadCell (.first (.second (.second (.second (.var rfl))))) related.logSize)
  apply Evaluates.letE
    (.binary (.var rfl) (.binary .word (wordCount_evaluates
      (Stable.first (Stable.second (Stable.second (Stable.second (Stable.second (Stable.second (Stable.second (Stable.var (by rfl)))))))))) rfl) rfl)
  exact continued

theorem appendTail_preserves {locations : Locations} {state finalState : LogsSemantics.State}
    {offset length : Word} {topics : List Word} {result : Semantics.Result Semantics.Value}
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (allowed : topics.length ≤ 4) (environment : Environment) (store : Store)
    (related : StateRel locations state store) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates (.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor ::
        appendInput locations state.address offset length topics :: environment)
        store (appendTail topics.length) target final ∧ StateRel locations finalState final ∧ Frame locations store final := by
  let input := appendInput locations state.address offset length topics
  let entered := Value.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor :: input :: environment
  have touched := MemoryCorrespondence.touch_evaluates (environment := entered)
    (reference := Logs.field 1 8 (.var 2)) (offsetExpr := Logs.field 5 8 (.var 2))
    (lengthExpr := Logs.field 6 8 (.var 2))
    (.first (.second (.var rfl)))
    (.first (.second (.second (.second (.second (.second (.var rfl)))))))
    (.first (.second (.second (.second (.second (.second (.second (.var rfl)))))))) related.memorySize
  cases appended with
  | topics tooMany => omega
  | capacity allowed overflow =>
      refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
      exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, overflow])) (.inLeft .word)
  | memory allowed capacity overflow =>
      simp only [MemoryCorrespondence.touchResult, overflow, MemoryCorrespondence.touchStore_failure overflow] at touched
      refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
      exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, capacity]))
        (LanguageResult.bind_failure .unit touched)
  | @done size words allowed capacity expanded copied =>
      simp only [MemoryCorrespondence.touchResult, expanded] at touched
      let touchedStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length
      have touchedRelated := related.touch expanded
      let headerEnvironment := WordMapping.encode state.memory.words :: Value.unit :: entered
      let headerExprs := [Logs.field 4 8 (.var 4), Logs.number topics.length, Logs.field 6 8 (.var 4)] ++
        (List.range topics.length).map (fun index => Logs.field index topics.length (Logs.field 7 8 (.var 4)))
      have inputStable : Stable headerEnvironment (.var 4) input := Stable.var rfl
      have headerRelated : WordExpressions headerEnvironment headerExprs (LogsSemantics.headers state.address length topics) := by
        apply WordExpressions.append
          (.cons inputStable.second.second.second.second.first
            (.cons (Stable.word _ _) (.cons inputStable.second.second.second.second.second.second.first .nil)))
        exact inputStable.second.second.second.second.second.second.second.fields
      let headerWords := LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address length topics)
      obtain ⟨headerSuffix, inserted⟩ := insertWords_evaluates headerRelated state.words state.cursor touchedStore
        (mappingExpr := .loadCell (Logs.field 2 8 (.var 4))) (cursorExpr := .var 3)
        (.loadCell (.first (.second (.second (.var rfl)))) touchedRelated.logs) (Stable.var rfl)
      let headerStore := touchedStore ++ headerSuffix
      have headerStored := touchedRelated.append headerSuffix
      let payloadEnvironment := WordMapping.encode headerWords :: headerEnvironment
      obtain ⟨payloadSuffix, payload⟩ := copyPayload_evaluates copied
        (environment := payloadEnvironment) (store := headerStore)
        (memoryExpr := .var 1) (offsetExpr := Logs.field 5 8 (.var 5)) (lengthExpr := Logs.field 6 8 (.var 5))
        (mappingExpr := .var 0) (cursorExpr := Logs.add (.var 4) (Logs.number (3 + topics.length)))
        (.var rfl) (.first (.second (.second (.second (.second (.second (.var rfl)))))))
        (.first (.second (.second (.second (.second (.second (.second (.var rfl))))))))
        (.var rfl) (.binary (.var rfl) .word rfl)
      let copiedStore := headerStore ++ payloadSuffix
      have copiedRelated := headerStored.append payloadSuffix
      have distinct := related.distinct
      simp [Locations.all] at distinct
      have logsWritten : copiedStore.write? locations.logs (WordMapping.encode words) =
          some (copiedStore.set locations.logs (WordMapping.encode words)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp copiedRelated.logs).1, rfl⟩
      have cursorRead : Store.read? (copiedStore.set locations.logs (WordMapping.encode words)) locations.logSize = some (.word state.cursor) := by
        rw [Store.write?_preserves_other logsWritten (by intro equal; simp_all)]
        exact copiedRelated.logSize
      have cursorWritten : Store.write? (copiedStore.set locations.logs (WordMapping.encode words)) locations.logSize
          (.word (LogsSemantics.nextCursor state.cursor length topics)) =
          some (publishStore locations copiedStore words (LogsSemantics.nextCursor state.cursor length topics)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp cursorRead).1, rfl⟩
      refine ⟨_, _, .value .unit, ?_, copiedRelated.publish words _,
        ((Frame.touch locations store state.memory.size offset length).trans
          ((Frame.append locations touchedStore headerSuffix).trans
            (Frame.append locations headerStore payloadSuffix))).trans (Frame.publish locations copiedStore words _)⟩
      apply Evaluates.ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, capacity]))
      apply LanguageResult.bind_success .unit touched
      apply Evaluates.letE (.loadCell (.first (.var rfl)) touchedRelated.memory)
      apply LanguageResult.bind_success .unit inserted
      apply LanguageResult.bind_success .unit payload
      apply Evaluates.inRight
      apply Evaluates.letE
        (.storeCell (.first (.second (.second (.var rfl)))) copiedRelated.logs (.var rfl) logsWritten)
      exact .storeCell (.first (.second (.second (.second (.var rfl))))) cursorRead (.var rfl) cursorWritten

theorem append_preserves {environment : Environment} {store : Store} {locations : Locations}
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    {memoryRef sizeRef logsRef cursorRef addressExpr offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr}
    {offset length : Word} {topics : List Word}
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (related : StateRel locations state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type locations.memory) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word locations.memorySize) store)
    (logsEvaluated : Evaluates environment store logsRef (.cellRef WordMapping.type locations.logs) store)
    (cursorEvaluated : Evaluates environment store cursorRef (.cellRef .word locations.logSize) store)
    (addressEvaluated : Evaluates environment store addressExpr (.word state.address) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (topicsRelated : WordExpressions environment topicExprs topics) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates environment store (Logs.append memoryRef sizeRef logsRef cursorRef addressExpr topicExprs offsetExpr lengthExpr)
        target final ∧ StateRel locations finalState final ∧ Frame locations store final := by
  by_cases allowed : topics.length ≤ 4
  · obtain ⟨target, final, resultRelated, evaluated, stateRelated, frame⟩ := appendTail_preserves appended allowed environment store related
    exact ⟨target, final, resultRelated, append_enter related memoryEvaluated sizeEvaluated logsEvaluated cursorEvaluated
      addressEvaluated offsetEvaluated lengthEvaluated topicsRelated allowed evaluated, stateRelated, frame⟩
  · cases appended with
    | topics tooMany =>
        refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
        simpa only [Logs.append, topicsRelated.length, show topics.length > 4 from Nat.lt_of_not_ge allowed,
          ↓reduceIte, LanguageResult.failure, Logs.topicReason] using (Evaluates.inLeft (rightType := .unit) (Evaluates.word (value := Word.ofNatModulo 11)))
    | capacity possible _ => contradiction
    | memory possible _ _ => contradiction
    | done possible _ _ _ => contradiction

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem append_rename (memory size logs cursor address : Core.Expr) (topics : List Core.Expr)
    (offset length : Core.Expr) (mapping : Renaming) (allowed : topics.length ≤ 4) :
    (Logs.append memory size logs cursor address topics offset length).rename mapping =
      Logs.append (memory.rename mapping) (size.rename mapping) (logs.rename mapping) (cursor.rename mapping)
        (address.rename mapping) (topics.map (·.rename mapping)) (offset.rename mapping) (length.rename mapping) := by
  rcases topics with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals try (have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at allowed; omega); subst rest)
  all_goals
    simp [Logs.append, List.range_succ, Logs.packet, Logs.field, Logs.wordCount, Logs.add, Logs.number,
      Logs.insertWords, Logs.copyPayload, Logs.copyBody,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      Memory.touch, Memory.readMemoryWord, WordMapping.lookup, WordMapping.insert,
      WordMapping.runHelper, WordMapping.lookupBody, WordMapping.insertBody, WordMapping.invoke,
      OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
      Renaming.lift, Core.Expr.weakenAt, WordMapping.cons, WordMapping.empty]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end Solcore.Frontend.RustHull.LogsCorrespondence
