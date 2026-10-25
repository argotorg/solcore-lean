import Solcore.Frontend.RustHull.AccountObservationBuiltinCompiler
import Solcore.Frontend.RustHull.AccountInspectionCorrespondence
import Solcore.Frontend.RustHull.AccountInspectionRenamingCorrespondence
import Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
import Solcore.Frontend.RustHull.StorageBuiltinCorrespondence

/-! Independent account observations reach the actual outer builtin compiler
with references obtained from the initialized runtime environment. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountObservationBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open AccountObservationSemantics (Operation)

theorem memory_unchanged {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current : Word} {name : String}
    {sourceType : Ty} {sources : List Semantics.Value} {state finalState : MemorySemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current name sourceType sources state result finalState)
    (readonly : name ≠ "extcodecopy") : finalState = state := by
  cases called <;> first | rfl | exact False.elim (readonly rfl)

private theorem retained_memory {memory size : Nat} {state : MemorySemantics.State} {store final : Store}
    (related : MemoryCorrespondence.StateRel memory size state store) (retained : StoreRetains store final) :
    MemoryCorrespondence.StateRel memory size state final ∧ MemoryCorrespondence.Frame memory size store final := by
  have keep : ∀ location value, store.read? location = some value → final.read? location = some value := by
    intro location value found
    exact (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  exact ⟨⟨related.distinct, keep _ _ related.memory, keep _ _ related.size⟩,
    ⟨retained.length_le, fun location value _ _ found => keep location value found⟩⟩

private theorem lookup_preserves {environment : Environment} {store : Store}
    {entries index : Core.Expr} {balances : StorageSemantics.Words} {key : Word}
    (entriesEvaluated : Evaluates environment store entries (WordMapping.encode balances) store)
    (indexEvaluated : Evaluates environment store index (.word key) store) :
    ∃ final,
      Evaluates environment store (WordMapping.lookup entries index)
        (.inRight .word (.word (StorageSemantics.readWord key balances))) final ∧ StoreRetains store final := by
  have evaluated := WordMapping.lookup_evaluates balances key entriesEvaluated indexEvaluated
  rw [← StorageCorrespondence.readWord_eq] at evaluated
  exact ⟨_, evaluated, StoreRetains.append _ _⟩

private theorem balance_result {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current target : Word} {sourceType : Ty}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current "balance" sourceType
      [.word target] state result finalState) :
    result = .value (.word (StorageSemantics.readWord (AccountObservationSemantics.address target) balances)) := by
  generalize named : "balance" = name at called
  cases called <;> simp only [String.reduceEq] at named
  rfl

private theorem selfbalance_result {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current : Word} {sourceType : Ty}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current "selfbalance" sourceType
      [] state result finalState) : result = .value (.word (StorageSemantics.readWord current balances)) := by
  generalize named : "selfbalance" = name at called
  cases called
  rfl

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {storage : StorageSemantics.State} {balances : StorageSemantics.Words}
    {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin storage.world storage.complete balances storage.address
      operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation balancesLocation : Nat}
    {locations : StorageBuiltinCorrespondence.Locations}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, balancesLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (storageRelated : StorageBuiltinCorrespondence.StateRel locations storage store)
    (balancesRead : store.read? balancesLocation = some (WordMapping.encode balances))
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨accounts, accountsEqual, worldRead⟩ := storageRelated.world
  rw [← accountsEqual] at called
  cases operation with
  | balance =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨balancesRef, balancesCompiled, rfl⟩ := balance_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have resultEqual := balance_result called
      cases resultEqual
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨finalStore, evaluated, retained⟩ := lookup_preserves
        (.loadCell (reference_evaluates runtime' balancesMember balancesCompiled store) balancesRead)
        (.binary (op := .wordAnd) (.var (index := 0) rfl) (Evaluates.word (value := Word.ofNatModulo (2 ^ 160 - 1))) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨_, finalStore, .value (.word _), ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [EnvironmentBuiltinCorrespondence.lookup_rename]
      exact evaluated
  | selfbalance =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      cases related
      obtain ⟨balancesRef, addressRef, balancesCompiled, addressCompiled, rfl⟩ := selfbalance_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have resultEqual := selfbalance_result called
      cases resultEqual
      have runtime' := runtime.temporary .unit .unit
      obtain ⟨finalStore, evaluated, retained⟩ := lookup_preserves
        (.loadCell (reference_evaluates runtime' balancesMember balancesCompiled store) balancesRead)
        (.loadCell (reference_evaluates runtime' addressMember addressCompiled store) storageRelated.address)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨_, finalStore, .value (.word _), ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [EnvironmentBuiltinCorrespondence.lookup_rename]
      exact evaluated
  | size =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨worldRef, completeRef, worldCompiled, completeCompiled, rfl⟩ := size_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨target, finalStore, resultRelated, evaluated, retained⟩ :=
        AccountInspectionCorrespondence.size_preserves called worldRead
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (.var (index := 0) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [AccountInspectionCorrespondence.size_rename]
      exact evaluated
  | copy =>
      obtain ⟨targetExpr, destinationExpr, sourceExpr, lengthExpr, targetWord, destination, source, length, rfl, rfl, rfl⟩ :=
        four_words related words arity
      obtain ⟨worldRef, completeRef, memoryRef, sizeRef, worldCompiled, completeCompiled,
        memoryCompiled, sizeCompiled, rfl⟩ := copy_components rawCompiled
      cases typed
      cases loweredEqual
      have runtime' := runtime.temporary (.product .word (.product .word (.product .word .word)))
        (.pair (.word targetWord) (.pair (.word destination) (.pair (.word source) (.word length))))
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
        AccountInspectionCorrespondence.copy_preserves called worldRead stateRelated
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (reference_evaluates runtime' memoryMember memoryCompiled store)
          (reference_evaluates runtime' sizeMember sizeCompiled store)
          (.first (.var (index := 0) rfl)) (.first (.second (.var (index := 0) rfl)))
          (.first (.second (.second (.var (index := 0) rfl)))) (.second (.second (.second (.var (index := 0) rfl))))
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .unit packed
      rw [AccountInspectionCorrespondence.copy_rename]
      exact evaluated
  | hash =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨worldRef, completeRef, balancesRef, worldCompiled, completeCompiled, balancesCompiled, rfl⟩ :=
        hash_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨target, finalStore, resultRelated, evaluated, retained⟩ :=
        AccountInspectionCorrespondence.hash_preserves called worldRead balancesRead
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (reference_evaluates runtime' balancesMember balancesCompiled store)
          (.var (index := 0) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [AccountInspectionCorrespondence.hash_rename]
      exact evaluated

end Solcore.Frontend.RustHull.AccountObservationBuiltinCorrespondence
