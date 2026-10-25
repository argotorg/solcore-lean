import Solcore.Frontend.RustHull.EnvironmentSemantics
import Solcore.Frontend.RustHull.MemoryCorrespondence
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! Concrete environment observations through the actual Hull effect compiler.
Optional transaction data, absent gas and unknown code retain their distinct
language faults. Read helpers may allocate closures but retain existing cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence EnvironmentSemantics ScalarExecution

abbrev optionalWord := Core.Ty.sum .unit .word
abbrev optionalHashes := Core.Ty.sum .unit Core.WordMapping.type

def wordOption : Option Word → Core.Value
  | none => .inLeft .word .unit | some value => .inRight .unit (.word value)

def hashesOption : Option MemorySemantics.Entries → Core.Value
  | none => .inLeft WordMapping.type .unit | some values => .inRight .unit (WordMapping.encode values)

def observation (state : EnvironmentSemantics.State) (name : String) (type : Core.Ty) : Option Core.Value :=
  match name, type with
  | "address", .word => some (.word (state.direct .address))
  | "caller", .word => some (.word (state.direct .caller))
  | "callvalue", .word => some (.word (state.direct .callvalue))
  | "calldataSize", .word => some (.word (state.direct .calldataSize))
  | "returnDataSize", .word => some (.word (state.direct .returnDataSize))
  | "origin", .sum .unit .word => some (wordOption (state.ambient .origin))
  | "gasprice", .sum .unit .word => some (wordOption (state.ambient .gasprice))
  | "coinbase", .sum .unit .word => some (wordOption (state.ambient .coinbase))
  | "timestamp", .sum .unit .word => some (wordOption (state.ambient .timestamp))
  | "number", .sum .unit .word => some (wordOption (state.ambient .number))
  | "prevrandao", .sum .unit .word => some (wordOption (state.ambient .prevrandao))
  | "gaslimit", .sum .unit .word => some (wordOption (state.ambient .gaslimit))
  | "chainid", .sum .unit .word => some (wordOption (state.ambient .chainid))
  | "basefee", .sum .unit .word => some (wordOption (state.ambient .basefee))
  | "blobbasefee", .sum .unit .word => some (wordOption (state.ambient .blobbasefee))
  | "availableGas", .sum .unit .word => some (wordOption state.gas)
  | "codeSize", .word => some (.word state.codeSize)
  | "codeKnown", .bool => some (.bool state.codeKnown)
  | "calldata", type => if type = WordMapping.type then some (WordMapping.encode state.calldata) else none
  | "blockHashes", type => if type = optionalHashes then some (hashesOption state.blockHashes) else none
  | "blobHashes", type => if type = optionalHashes then some (hashesOption state.blobHashes) else none
  | _, _ => none

/-- Only slots present in the compiled runtime scope are observed. This does
not require optional linked-code slots when the selected code does not use them. -/
def StateRel (slots : List EffectSlot) (state : EnvironmentSemantics.State) (store : Store) : Prop :=
  ∀ slot ∈ slots, ∀ value, observation state slot.name slot.type = some value →
    store.read? slot.location = some value

def inputs : Operation → List (String × Core.Ty)
  | .direct operation => [(operation.slot, .word)]
  | .ambient operation => [(operation.name, optionalWord)]
  | .gas => [("availableGas", optionalWord)]
  | .codeSize => [("codeSize", .word), ("codeKnown", .bool)]
  | .calldataLoad => [("calldata", WordMapping.type)]
  | .blockHash => [("number", optionalWord), ("blockHashes", optionalHashes)]
  | .blobHash => [("blobHashes", optionalHashes)]

def Available (slots : List EffectSlot) (operation : Operation) : Prop :=
  ∀ name type, (name, type) ∈ inputs operation → ∃ location, ⟨name, type, location⟩ ∈ slots

theorem StateRel.retained {slots : List EffectSlot} {state : EnvironmentSemantics.State} {initial final : Store}
    (related : StateRel slots state initial) (retained : StoreRetains initial final) :
    StateRel slots state final := by
  intro slot member value represented
  have found := related slot member value represented
  rw [retained.read slot.location (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem direct_observation (state : EnvironmentSemantics.State) (operation : Direct) :
    observation state operation.slot .word = some (.word (state.direct operation)) := by
  cases operation <;> rfl

private theorem ambient_observation (state : EnvironmentSemantics.State) (operation : AmbientWord) :
    observation state operation.name optionalWord = some (wordOption (state.ambient operation)) := by
  cases operation <;> rfl

private theorem direct_components (operation : Direct) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ reference, Effects.reference scope operation.slot .word = .ok reference ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell reference)⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let reference ← Effects.reference scope operation.slot .word
      pure ⟨.word, LanguageResult.success (.loadCell reference)⟩) := by
    cases operation <;> rfl
  rw [expanded] at compiled
  obtain ⟨reference, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, compiled, (Except.ok.inj returned).symm⟩

def ambientBody (operation : AmbientWord) : Core.Expr :=
  LanguageResult.success (if operation.isAddress then
    .binary .wordAnd (.var 0) (.word (Word.ofNatModulo (2 ^ 160 - 1))) else .var 0)

private theorem ambient_read_components {scope : Scope} {name : String} {type : Core.Ty} {value : Core.Expr}
    (compiled : Ambient.read scope name type = .ok value) :
    ∃ reference, Effects.reference scope name type = .ok reference ∧ value = .loadCell reference := by
  unfold Ambient.read at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, typed, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  refine ⟨.var index, ?_, (Except.ok.inj returned).symm⟩
  simp only [Effects.reference, Effects.slotName, Effects.reservedPrefix, looked, typed,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem ambient_components (operation : AmbientWord) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ reference, Effects.reference scope operation.name optionalWord = .ok reference ∧
      lowered = ⟨.word, .caseE (.loadCell reference)
        (LanguageResult.failure .word (.word (Word.ofNatModulo 14))) (ambientBody operation)⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let value ← Ambient.read scope operation.name optionalWord
      pure ⟨.word, .caseE (value.rename (· + 0))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 14))) (ambientBody operation)⟩) := by
    cases operation <;> rfl
  rw [expanded] at compiled
  obtain ⟨value, readCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_read_components readCompiled
  refine ⟨reference, referenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem gas_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "gas" [] = .ok lowered) :
    ∃ reference, Effects.reference scope "availableGas" optionalWord = .ok reference ∧
      lowered = ⟨.word, .caseE (.loadCell reference)
        (LanguageResult.failure .word (.word (Word.ofNatModulo 9))) (LanguageResult.success (.var 0))⟩ := by
  change (do
    let reference ← Effects.reference scope "availableGas" optionalWord
    pure (Lowered.mk .word (.caseE (.loadCell reference)
      (LanguageResult.failure .word (.word (Word.ofNatModulo 9))) (LanguageResult.success (.var 0))))) = .ok lowered at compiled
  obtain ⟨reference, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, compiled, (Except.ok.inj returned).symm⟩

private theorem codeSize_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "codesize" [] = .ok lowered) :
    ∃ size known, Effects.reference scope "codeSize" .word = .ok size ∧
      Effects.reference scope "codeKnown" .bool = .ok known ∧
      lowered = ⟨.word, .ifE (.loadCell known) (LanguageResult.success (.loadCell size))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 15)))⟩ := by
  change (do
    let size ← Effects.reference scope "codeSize" .word
    let expression ← (do
      let known ← Effects.reference scope "codeKnown" .bool
      pure (.ifE (.loadCell known) (LanguageResult.success (.loadCell size))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 15)))) : LowerM Core.Expr)
    pure (Lowered.mk .word expression)) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨expression, guarded, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨known, knownCompiled, guardedEqual⟩ := lower_bind_eq_ok.mp guarded
  cases guardedEqual
  exact ⟨size, known, sizeCompiled, knownCompiled, (Except.ok.inj returned).symm⟩

theorem direct_preserves (operation : Direct) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots (.direct operation)) (related : StateRel slots state store) :
    ResultRel lowered.type (.value (.word (state.direct operation))) (.inRight .word (.word (state.direct operation))) ∧
      Evaluates environment store (lowered.expression.rename mapping) (.inRight .word (.word (state.direct operation))) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := direct_components operation compiled
  obtain ⟨location, member⟩ := available operation.slot .word (by simp [inputs])
  exact ⟨.value (.word _), .inRight (.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (direct_observation state operation)))⟩

def wordResult : Semantics.Result Semantics.Value → Core.Value
  | .value (.word value) => .inRight .word (.word value)
  | .fault (.language reason) => .inLeft .word (.word reason)
  | _ => .inLeft .word (.word Word.zero)

theorem ambient_preserves (operation : AmbientWord) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots (.ambient operation)) (related : StateRel slots state store) :
    ResultRel lowered.type (ambientWord state operation) (wordResult (ambientWord state operation)) ∧
      Evaluates environment store (lowered.expression.rename mapping) (wordResult (ambientWord state operation)) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_components operation compiled
  obtain ⟨location, member⟩ := available operation.name optionalWord (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (ambient_observation state operation))
  cases found : state.ambient operation with
  | none =>
      simp only [ambientWord, found, Option.map_none, EnvironmentSemantics.available, wordResult]
      exact ⟨.language _, .caseLeft (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inLeft .word)⟩
  | some value =>
      simp only [ambientWord, found, Option.map_some, EnvironmentSemantics.available, wordResult]
      refine ⟨.value (.word _), .caseRight (by simpa only [found, wordOption, Core.Expr.rename] using read) ?_⟩
      cases masked : operation.isAddress
      · simpa [ambientBody, masked, LanguageResult.success, Core.Expr.rename, Renaming.lift] using
          (Evaluates.inRight (leftType := .word) (Evaluates.var (by rfl) :
            Evaluates (.word value :: environment) store (.var 0) (.word value) store))
      · simpa [ambientBody, masked, LanguageResult.success, Core.Expr.rename, Renaming.lift,
          EnvironmentSemantics.address] using
          (Evaluates.inRight (leftType := .word) (Evaluates.binary (Evaluates.var (by rfl)) Evaluates.word rfl :
            Evaluates (.word value :: environment) store
              (.binary .wordAnd (.var 0) (.word (Word.ofNatModulo (2 ^ 160 - 1))))
              (.word (EnvironmentSemantics.address value)) store))

theorem gas_preserves {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "gas" [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .gas) (related : StateRel slots state store) :
    ResultRel lowered.type (EnvironmentSemantics.available 9 state.gas) (wordResult (EnvironmentSemantics.available 9 state.gas)) ∧
      Evaluates environment store (lowered.expression.rename mapping) (wordResult (EnvironmentSemantics.available 9 state.gas)) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := gas_components compiled
  obtain ⟨location, member⟩ := available "availableGas" optionalWord (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (show observation state "availableGas" optionalWord = some (wordOption state.gas) from rfl))
  cases found : state.gas with
  | none =>
      simp only [EnvironmentSemantics.available, wordResult]
      exact ⟨.language _, .caseLeft (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inLeft .word)⟩
  | some value =>
      simp only [EnvironmentSemantics.available, wordResult]
      exact ⟨.value (.word _), .caseRight (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inRight (.var rfl))⟩

theorem codeSize_preserves {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "codesize" [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .codeSize) (related : StateRel slots state store) :
    ∃ result target, observe state .codeSize [] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target store := by
  obtain ⟨size, known, sizeCompiled, knownCompiled, rfl⟩ := codeSize_components compiled
  obtain ⟨sizeLocation, sizeMember⟩ := available "codeSize" .word (by simp [inputs])
  obtain ⟨knownLocation, knownMember⟩ := available "codeKnown" .bool (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime knownMember knownCompiled store)
    (related _ knownMember _ (show observation state "codeKnown" .bool = some (.bool state.codeKnown) from rfl))
  cases found : state.codeKnown with
  | false =>
      exact ⟨.fault (.language (Word.ofNatModulo 15)), .inLeft .word (.word (Word.ofNatModulo 15)),
        by simp [observe, found], .language _, .ifFalse (by simpa only [found, Core.Expr.rename] using read) (.inLeft .word)⟩
  | true =>
      exact ⟨.value (.word state.codeSize), .inRight .word (.word state.codeSize),
        by simp [observe, found], .value (.word _),
        .ifTrue (by simpa only [found, Core.Expr.rename] using read) (.inRight (.loadCell (reference_evaluates runtime sizeMember sizeCompiled store)
          (related _ sizeMember _ rfl)))⟩


private theorem reference_position {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (runtime : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) :
    ∃ index, reference = .var index ∧ environment[mapping index]? = some (.cellRef slot.type slot.location) := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact ⟨index, rfl, runtime slot member binding index looked⟩

set_option linter.unusedSimpArgs false in
theorem readMemoryWord_rename (entries index : Core.Expr) (mapping : Renaming) :
    (Memory.readMemoryWord entries index).rename mapping =
      Memory.readMemoryWord (entries.rename mapping) (index.rename mapping) := by
  simp only [Memory.readMemoryWord, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    WordMapping.lookup, WordMapping.runHelper, WordMapping.lookupBody, WordMapping.invoke,
    OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  rfl

set_option linter.unusedSimpArgs false in
theorem lookup_rename (entries index : Core.Expr) (mapping : Renaming) :
    (WordMapping.lookup entries index).rename mapping =
      WordMapping.lookup (entries.rename mapping) (index.rename mapping) := by
  simp only [WordMapping.lookup, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    WordMapping.runHelper, WordMapping.lookupBody, WordMapping.invoke,
    OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  rfl

private theorem calldata_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldataload" [index] = .ok lowered) :
    ∃ reference, Effects.reference scope "calldata" WordMapping.type = .ok reference ∧
      lowered = ⟨.word, Memory.readMemoryWord (.loadCell reference) index⟩ := by
  change (do
    let reference ← Effects.reference scope "calldata" WordMapping.type
    pure (Lowered.mk .word (Memory.readMemoryWord (.loadCell reference) index))) = .ok lowered at compiled
  obtain ⟨reference, referenceCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, referenceCompiled, (Except.ok.inj returned).symm⟩

theorem calldata_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldataload" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .calldataLoad) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ final, ResultRel lowered.type (.value (.word (MemorySemantics.readWord state.calldata index)))
        (.inRight .word (.word (MemorySemantics.readWord state.calldata index))) ∧
      Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word (.word (MemorySemantics.readWord state.calldata index))) final ∧ StoreRetains store final := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := calldata_components compiled
  obtain ⟨location, member⟩ := available "calldata" WordMapping.type (by simp [inputs])
  obtain ⟨suffix, extended⟩ := MemoryCorrespondence.readWordStore_extension store state.calldata index environment
  refine ⟨MemoryCorrespondence.readWordStore store state.calldata index environment, .value (.word _), ?_, ?_⟩
  · rw [readMemoryWord_rename]
    exact MemoryCorrespondence.readMemoryWord_evaluates state.calldata index
      (.loadCell (reference_evaluates runtime member referenceCompiled store)
        (related _ member _ (by simp [observation]))) evaluated
  · rw [extended]; exact StoreRetains.append store suffix

def blobCode (hashes index : Core.Expr) : Core.Expr :=
  .letE index (.caseE (hashes.rename (· + 1))
    (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
    (WordMapping.lookup (.var 0) (.var 1)))

def blockCode (current hashes index : Core.Expr) : Core.Expr :=
  .letE index (.caseE (current.rename (· + 1))
    (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
    (.caseE (hashes.rename (· + 2))
      (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
      (.ifE (.binary .wordGt (.var 1) (.var 2))
        (.ifE (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (.word (Word.ofNatModulo 256)))
          (LanguageResult.success (.word Word.zero)) (WordMapping.lookup (.var 0) (.var 2)))
        (LanguageResult.success (.word Word.zero)))))

private theorem blob_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blobhash" [index] = .ok lowered) :
    ∃ reference, Effects.reference scope "blobHashes" optionalHashes = .ok reference ∧
      lowered = ⟨.word, blobCode (.loadCell reference) index⟩ := by
  have expanded : Effects.lowerBuiltin scope "blobhash" [index] = (do
      let hashes ← Ambient.read scope "blobHashes" optionalHashes
      pure ⟨.word, blobCode hashes (index.rename (· + 0))⟩) := rfl
  rw [expanded] at compiled
  obtain ⟨hashes, readCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_read_components readCompiled
  refine ⟨reference, referenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem block_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blockhash" [index] = .ok lowered) :
    ∃ current hashes, Effects.reference scope "number" optionalWord = .ok current ∧
      Effects.reference scope "blockHashes" optionalHashes = .ok hashes ∧
      lowered = ⟨.word, blockCode (.loadCell current) (.loadCell hashes) index⟩ := by
  have expanded : Effects.lowerBuiltin scope "blockhash" [index] = (do
      let current ← Ambient.read scope "number" optionalWord
      let hashes ← Ambient.read scope "blockHashes" optionalHashes
      pure ⟨.word, blockCode current hashes (index.rename (· + 0))⟩) := rfl
  rw [expanded] at compiled
  obtain ⟨current, currentCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨hashes, hashesCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨currentRef, currentReferenceCompiled, rfl⟩ := ambient_read_components currentCompiled
  obtain ⟨hashesRef, hashesReferenceCompiled, rfl⟩ := ambient_read_components hashesCompiled
  refine ⟨currentRef, hashesRef, currentReferenceCompiled, hashesReferenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem lookup_retains (entries : MemorySemantics.Entries) (index : Word)
    (environment : Environment) (store : Store) :
    StoreRetains store (MemoryCorrespondence.lookupStore store entries index environment) :=
  StoreRetains.append store [_]

theorem blob_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blobhash" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .blobHash) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ target final, ResultRel lowered.type (blobHash state index) target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := blob_components compiled
  obtain ⟨location, member⟩ := available "blobHashes" optionalHashes (by simp [inputs])
  obtain ⟨position, rfl, found⟩ := reference_position runtime member referenceCompiled
  have read := related _ member _ (show observation state "blobHashes" optionalHashes = some (hashesOption state.blobHashes) by simp [observation])
  simp only [blobCode, Core.Expr.rename, Renaming.lift, lookup_rename, LanguageResult.failure]
  cases hashes : state.blobHashes with
  | none =>
      have missing : store.read? location = some (.inLeft WordMapping.type .unit) := by
        simpa only [hashes, hashesOption] using read
      refine ⟨_, store, ?_, .letE evaluated (.caseLeft (.loadCell (elementType := optionalHashes) (.var ?_) missing) (.inLeft .word)), StoreRetains.refl _⟩
      · simp only [blobHash, hashes, Option.map_none, EnvironmentSemantics.available]; exact .language _
      · simpa using found
  | some entries =>
      have historyRead : store.read? location = some (.inRight .unit (WordMapping.encode entries)) := by
        simpa only [hashes, hashesOption] using read
      refine ⟨.inRight .word (.word (WordMapping.lookupEntries index entries)),
        MemoryCorrespondence.lookupStore store entries index (WordMapping.encode entries :: .word index :: environment),
        ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) ?_),
        lookup_retains entries index (WordMapping.encode entries :: .word index :: environment) store⟩
      · simpa only [blobHash, hashes, Option.map_some, EnvironmentSemantics.available, MemoryCorrespondence.lookup_eq] using
          (ResultRel.value (ValueRel.word (WordMapping.lookupEntries index entries)))
      · simpa using found
      · exact WordMapping.lookup_evaluates entries index (.var rfl) (.var rfl)

theorem block_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blockhash" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .blockHash) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ target final, ResultRel lowered.type (blockHash state index) target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  obtain ⟨currentRef, hashesRef, currentCompiled, hashesCompiled, rfl⟩ := block_components compiled
  obtain ⟨currentLocation, currentMember⟩ := available "number" optionalWord (by simp [inputs])
  obtain ⟨hashesLocation, hashesMember⟩ := available "blockHashes" optionalHashes (by simp [inputs])
  obtain ⟨currentPosition, rfl, currentFound⟩ := reference_position runtime currentMember currentCompiled
  obtain ⟨hashesPosition, rfl, hashesFound⟩ := reference_position runtime hashesMember hashesCompiled
  have currentRead := related _ currentMember _ (ambient_observation state .number)
  have hashesRead := related _ hashesMember _ (show observation state "blockHashes" optionalHashes = some (hashesOption state.blockHashes) by simp [observation])
  simp only [blockCode, Core.Expr.rename, Renaming.lift, lookup_rename, LanguageResult.failure, LanguageResult.success]
  cases current : state.ambient .number with
  | none =>
      have missing : store.read? currentLocation = some (.inLeft .word .unit) := by
        simpa only [current, wordOption] using currentRead
      refine ⟨_, store, ?_, .letE evaluated (.caseLeft (.loadCell (elementType := optionalWord) (.var ?_) missing) (.inLeft .word)), StoreRetains.refl _⟩
      · simp only [blockHash, current]; exact .language _
      · simpa using currentFound
  | some number =>
      have numberRead : store.read? currentLocation = some (.inRight .unit (.word number)) := by
        simpa only [current, wordOption] using currentRead
      cases hashes : state.blockHashes with
      | none =>
          have missing : store.read? hashesLocation = some (.inLeft WordMapping.type .unit) := by
            simpa only [hashes, hashesOption] using hashesRead
          refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
            (.caseLeft (.loadCell (elementType := optionalHashes) (.var ?_) missing) (.inLeft .word))), StoreRetains.refl _⟩
          · simp only [blockHash, current, hashes]; exact .language _
          · simpa using currentFound
          · simpa [Nat.add_assoc] using hashesFound
      | some entries =>
          have historyRead : store.read? hashesLocation = some (.inRight .unit (WordMapping.encode entries)) := by
            simpa only [hashes, hashesOption] using hashesRead
          by_cases past : number > index
          · by_cases old : number.sub index > Word.ofNatModulo 256
            · refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
                (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifTrue (.binary (.var rfl) (.var rfl) ?_)
                  (.ifTrue (.binary (.binary (.var rfl) (.var rfl) rfl) .word ?_) (.inRight .word))))), StoreRetains.refl _⟩
              · simp only [blockHash, current, hashes, past, old, ↓reduceIte]; exact .value (.word _)
              · simpa using currentFound
              · simpa [Nat.add_assoc] using hashesFound
              · simp [BinaryOp.apply, past]
              · simp [BinaryOp.apply, old]
            · refine ⟨.inRight .word (.word (WordMapping.lookupEntries index entries)),
                MemoryCorrespondence.lookupStore store entries index
                  (WordMapping.encode entries :: .word number :: .word index :: environment),
                ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
                (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifTrue (.binary (.var rfl) (.var rfl) ?_)
                  (.ifFalse (.binary (.binary (.var rfl) (.var rfl) rfl) .word ?_) ?_)))), lookup_retains entries index
                  (WordMapping.encode entries :: .word number :: .word index :: environment) store⟩
              · simp only [blockHash, current, hashes, past, old, ↓reduceIte, MemoryCorrespondence.lookup_eq]; exact .value (.word _)
              · simpa using currentFound
              · simpa [Nat.add_assoc] using hashesFound
              · simp [BinaryOp.apply, past]
              · simp [BinaryOp.apply, old]
              · exact WordMapping.lookup_evaluates entries index (.var rfl) (.var rfl)
          · refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
              (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifFalse (.binary (.var rfl) (.var rfl) ?_) (.inRight .word)))), StoreRetains.refl _⟩
            · simp only [blockHash, current, hashes, past, ↓reduceIte]; exact .value (.word _)
            · simpa using currentFound
            · simpa [Nat.add_assoc] using hashesFound
            · simp [BinaryOp.apply, past]


private theorem operation_supported (operation : Operation) : Effects.supports operation.name = true := by
  cases operation with
  | direct operation => cases operation <;> rfl
  | ambient operation => cases operation <;> rfl
  | gas | codeSize | calldataLoad | blockHash | blobHash => rfl

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;> (try first | cases ‹Direct› | cases ‹AmbientWord›)
  all_goals rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem builtin_operation (operation : Operation) (type : Ty)
    (arguments : List Semantics.Value) (state : EnvironmentSemantics.State) :
    builtin operation.name type arguments state = (observe state operation arguments).map (fun result => (result, state)) := by
  have selected : operations.find? (fun candidate => candidate.name == operation.name) = some operation := by
    cases operation with
    | direct operation => cases operation <;> decide
    | ambient operation => cases operation <;> decide
    | gas | codeSize | calldataLoad | blockHash | blobHash => decide
  unfold builtin
  rw [selected]
  change (observe state operation arguments).bind (fun result => some (result, state)) = _
  cases observe state operation arguments <;> rfl

private theorem zero_preserves (operation : Operation) (arity : operation.arity = 0)
    {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (related : StateRel slots state store) :
    ∃ result target, observe state operation [] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target store := by
  cases operation with
  | direct operation =>
      obtain ⟨relatedResult, evaluated⟩ := direct_preserves operation compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | ambient operation =>
      obtain ⟨relatedResult, evaluated⟩ := ambient_preserves operation compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | gas =>
      obtain ⟨relatedResult, evaluated⟩ := gas_preserves compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | codeSize => exact codeSize_preserves compiled runtime available related
  | calldataLoad | blockHash | blobHash => cases arity

private theorem one_preserves (operation : Operation) (arity : operation.arity = 1)
    {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ result target final, observe state operation [.word index] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  cases operation with
  | direct | ambient | gas | codeSize => cases arity
  | calldataLoad =>
      obtain ⟨final, relatedResult, executed, retained⟩ := calldata_preserves compiled runtime available related index evaluated
      exact ⟨_, _, final, rfl, relatedResult, executed, retained⟩
  | blockHash =>
      obtain ⟨target, final, relatedResult, executed, retained⟩ := block_preserves compiled runtime available related index evaluated
      exact ⟨_, target, final, rfl, relatedResult, executed, retained⟩
  | blobHash =>
      obtain ⟨target, final, relatedResult, executed, retained⟩ := blob_preserves compiled runtime available related index evaluated
      exact ⟨_, target, final, rfl, relatedResult, executed, retained⟩

/-- All twenty environment operations pass through the actual outer builtin
compiler. Optional failures and mapping-helper allocations preserve the source
observations and every cell that existed before the operation. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (stateRelated : StateRel slots state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) (sourceType : Ty) :
    ∃ result target final,
      builtin operation.name sourceType sources state = some (result, state) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      StateRel slots state final ∧ StoreRetains store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (operation_supported operation) compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  by_cases zero : operation.arity = 0
  · have empty : arguments = [] := List.eq_nil_of_length_eq_zero (arity.trans zero)
    subst arguments
    cases related
    obtain ⟨result, target, observed, relatedResult, executed⟩ :=
      zero_preserves operation zero rawCompiled (runtime.temporary .unit .unit) available stateRelated
    cases typed
    cases loweredEqual
    exact ⟨result, target, store,
      by rw [builtin_operation, observed]; rfl,
      relatedResult, LanguageResult.bind_success _ packed executed, stateRelated, StoreRetains.refl _⟩
  · have one : operation.arity = 1 := by cases operation <;> simp_all [Operation.arity]
    obtain ⟨indexExpr, index, rfl, rfl, rfl⟩ := one_word related words (arity.trans one)
    obtain ⟨result, target, final, observed, relatedResult, executed, retained⟩ :=
      one_preserves operation one rawCompiled (runtime.temporary .word (.word index)) available stateRelated index (.var rfl)
    cases typed
    cases loweredEqual
    exact ⟨result, target, final,
      by rw [builtin_operation, observed]; rfl,
      relatedResult, LanguageResult.bind_success _ packed executed, stateRelated.retained retained, retained⟩

end Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
