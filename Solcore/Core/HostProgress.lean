import Solcore.Core.HostMachineProperties
import Solcore.Core.HostStateSafety

/-! Progress and immediate fault freedom for the host-aware CEK machine. -/

set_option autoImplicit false

namespace Solcore.Core

/-- A well-typed storage-read argument emits the corresponding request. -/
theorem typed_storageRead_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageRead.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageRead :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨slot, rfl⟩ := wordTyping.word_shape
  exact ⟨⟨.storageRead slot, continuation, store⟩, .storageRead⟩

/-- Capability dispatch is kept separate from the general CEK progress proof. -/
theorem typed_hostApplication_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {function : HostFunction} {value : Value}
    {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      function.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply function :: continuation, store⟩
        suspension := by
  cases function
  exact typed_storageRead_emits valueTyping

theorem host_state_progress
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions) :
    (∃ value store, state = State.final value store) ∨
      (∃ next, HostTransition state next) ∨
      ∃ suspension, HostRequestEmission state suspension := by
  cases stateTyping with
  | eval storeTyping environmentTyping exprTyping continuationTyping =>
      cases exprTyping with
      | unit => exact .inr (.inl ⟨_, .core .unit⟩)
      | bool => exact .inr (.inl ⟨_, .core .bool⟩)
      | word => exact .inr (.inl ⟨_, .core .word⟩)
      | var typeLookup =>
          obtain ⟨value, valueLookup, _⟩ := environmentTyping.lookup typeLookup
          exact .inr (.inl ⟨_, .core (.var valueLookup)⟩)
      | pair => exact .inr (.inl ⟨_, .core .enterPair⟩)
      | first => exact .inr (.inl ⟨_, .core .enterFirst⟩)
      | second => exact .inr (.inl ⟨_, .core .enterSecond⟩)
      | lambda => exact .inr (.inl ⟨_, .core .lambda⟩)
      | apply => exact .inr (.inl ⟨_, .core .enterApply⟩)
      | inLeft => exact .inr (.inl ⟨_, .core .enterInLeft⟩)
      | inRight => exact .inr (.inl ⟨_, .core .enterInRight⟩)
      | caseE => exact .inr (.inl ⟨_, .core .enterCase⟩)
      | newCell => exact .inr (.inl ⟨_, .core .enterNewCell⟩)
      | loadCell => exact .inr (.inl ⟨_, .core .enterLoadCell⟩)
      | storeCell => exact .inr (.inl ⟨_, .core .enterStoreCell⟩)
      | construct => exact .inr (.inl ⟨_, .core .enterConstruct⟩)
      | matchData => exact .inr (.inl ⟨_, .core .enterMatchData⟩)
      | unary => exact .inr (.inl ⟨_, .core .enterUnary⟩)
      | binary => exact .inr (.inl ⟨_, .core .enterBinary⟩)
      | ternary => exact .inr (.inl ⟨_, .core .enterTernary⟩)
      | letE => exact .inr (.inl ⟨_, .core .enterLet⟩)
      | ifE => exact .inr (.inl ⟨_, .core .enterIf⟩)
  | @ret _ world value continuation store controlType resultType
      storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact .inl ⟨value, store, rfl⟩
      | cons frameTyping restTyping =>
          cases frameTyping with
          | unaryApply =>
              obtain ⟨result, applied, _⟩ :=
                UnaryOp.apply_total_of_type _ _ valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyUnary applied)⟩)
          | binaryRight => exact .inr (.inl ⟨_, .core .enterBinaryRight⟩)
          | binaryApply leftTyping =>
              obtain ⟨result, applied, _⟩ :=
                BinaryOp.apply_total_of_types _ _ _
                  leftTyping.type_eq valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyBinary applied)⟩)
          | ternarySecond =>
              exact .inr (.inl ⟨_, .core .enterTernarySecond⟩)
          | ternaryThird => exact .inr (.inl ⟨_, .core .enterTernaryThird⟩)
          | ternaryApply firstTyping secondTyping =>
              obtain ⟨result, applied, _⟩ :=
                TernaryOp.apply_total_of_types _ _ _ _
                  firstTyping.type_eq secondTyping.type_eq valueTyping.type_eq
              exact .inr (.inl ⟨_, .core (.applyTernary applied)⟩)
          | pairRight => exact .inr (.inl ⟨_, .core .enterPairRight⟩)
          | pairApply => exact .inr (.inl ⟨_, .core .applyPair⟩)
          | firstApply =>
              cases valueTyping with
              | pair => exact .inr (.inl ⟨_, .core .applyFirst⟩)
          | secondApply =>
              cases valueTyping with
              | pair => exact .inr (.inl ⟨_, .core .applySecond⟩)
          | inLeftApply => exact .inr (.inl ⟨_, .core .applyInLeft⟩)
          | inRightApply => exact .inr (.inl ⟨_, .core .applyInRight⟩)
          | caseBranches =>
              cases valueTyping with
              | inLeft => exact .inr (.inl ⟨_, .core .chooseLeft⟩)
              | inRight => exact .inr (.inl ⟨_, .core .chooseRight⟩)
          | newCellApply _ => exact .inr (.inl ⟨_, .core .applyNewCell⟩)
          | loadCellApply _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨loaded, read, _, _⟩ := storeTyping.lookup found
                  exact .inr (.inl ⟨_, .core (.applyLoadCell read)⟩)
          | storeCellValue _ _ _ =>
              cases valueTyping with
              | cellRef found =>
                  obtain ⟨oldValue, read, _, _⟩ := storeTyping.lookup found
                  exact .inr (.inl ⟨_, .core (.beginStoreCellValue read)⟩)
          | storeCellApply found _ =>
              obtain ⟨updatedStore, written⟩ :=
                storeTyping.write_exists (value := value) found
              exact .inr (.inl ⟨_, .core (.applyStoreCell written)⟩)
          | constructApply _ => exact .inr (.inl ⟨_, .core .applyConstruct⟩)
          | matchDataApply definitionLookup _ branchesTyping =>
              cases valueTyping with
              | constructed constructorLookup payloadTyping =>
                  obtain ⟨runtimeDefinition, runtimeDefinitionLookup,
                    payloadTypeLookup⟩ :=
                      DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp
                        constructorLookup
                  have typedDefinitionLookup :=
                    DataEnvironment.lookupDataType?_eq_some_iff.mp definitionLookup
                  rw [typedDefinitionLookup] at runtimeDefinitionLookup
                  cases runtimeDefinitionLookup
                  obtain ⟨branch, branchLookup⟩ :=
                    branchesTyping.branch_exists payloadTypeLookup
                  exact .inr (.inl ⟨_, .core (.chooseData rfl branchLookup)⟩)
          | applyArgument =>
              cases valueTyping with
              | closure => exact .inr (.inl ⟨_, .core .beginArgument⟩)
              | hostFunction => exact .inr (.inl ⟨_, .beginApplication⟩)
          | applyClosure => exact .inr (.inl ⟨_, .core .invokeClosure⟩)
          | hostApply =>
              exact .inr (.inr (typed_hostApplication_emits valueTyping))
          | letBody => exact .inr (.inl ⟨_, .core .bindLet⟩)
          | ifBranches =>
              cases valueTyping with
              | bool =>
                  rename_i decision
                  cases decision with
                  | false => exact .inr (.inl ⟨_, .core .chooseFalse⟩)
                  | true => exact .inr (.inl ⟨_, .core .chooseTrue⟩)

theorem well_typed_host_state_never_faults
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : HostStateHasType state resultType definitions) :
    hostAdvance state ≠ .fault error := by
  intro faulted
  rcases host_state_progress stateTyping with
    ⟨value, store, rfl⟩ | ⟨next, step⟩ | ⟨suspension, emission⟩
  · simp [hostAdvance, advance, State.final] at faulted
  · rw [hostAdvance_next_iff.mpr step] at faulted
    contradiction
  · rw [hostAdvance_suspended_iff.mpr emission] at faulted
    contradiction

end Solcore.Core
