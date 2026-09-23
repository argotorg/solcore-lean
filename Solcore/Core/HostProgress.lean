import Solcore.Core.HostMachine
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

/-- A well-typed storage-write argument emits the corresponding request. -/
theorem typed_storageWrite_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageWrite.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageWrite :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨slot, writtenValue, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.storageWrite slot writtenValue, continuation, store⟩,
      .storageWrite⟩

/-- A well-typed storage-address observation emits its argument-free request. -/
theorem typed_storageAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.storageAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .storageAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.storageAddress, continuation, store⟩, .storageAddress⟩

/-- A well-typed code-address observation emits its argument-free request. -/
theorem typed_codeAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.codeAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .codeAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.codeAddress, continuation, store⟩, .codeAddress⟩

/-- A well-typed call-value observation emits its argument-free request. -/
theorem typed_callValue_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callValue.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callValue :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.callValue, continuation, store⟩, .callValue⟩

/-- A well-typed caller-address observation emits its argument-free request. -/
theorem typed_callerAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callerAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callerAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.callerAddress, continuation, store⟩, .callerAddress⟩

/-- A well-typed input-data byte offset emits its optional read request. -/
theorem typed_inputDataByte?_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataByte?.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataByte? :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨offset, rfl⟩ := wordTyping.word_shape
  exact ⟨⟨.inputDataByte? offset, continuation, store⟩, .inputDataByte?⟩

/-- A well-typed input-size observation emits its argument-free request. -/
theorem typed_inputDataSize_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataSize.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataSize :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.inputDataSize, continuation, store⟩, .inputDataSize⟩

/-- A well-typed input-data word offset emits its optional read request. -/
theorem typed_inputDataWordBE?_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.inputDataWordBE?.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .inputDataWordBE? :: continuation, store⟩
        suspension := by
  have wordTyping :
      HostRuntimeValueHasType world value .word definitions := by
    simpa using valueTyping
  obtain ⟨offset, rfl⟩ := wordTyping.word_shape
  exact
    ⟨⟨.inputDataWordBE? offset, continuation, store⟩,
      .inputDataWordBE?⟩

/-- A well-typed current-address observation emits its argument-free request. -/
theorem typed_currentAddress_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.currentAddress.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .currentAddress :: continuation, store⟩
        suspension := by
  have unitTyping :
      HostRuntimeValueHasType world value .unit definitions := by
    simpa using valueTyping
  cases unitTyping
  exact ⟨⟨.currentAddress, continuation, store⟩, .currentAddress⟩

/-- A well-typed target/input pair emits one contract-word call request. -/
theorem typed_callContractWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callContractWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .callContractWord :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨target, input, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.callContractWord target input, continuation, store⟩,
      .callContractWord⟩

/-- A well-typed target/value/input tuple emits one value-bearing call. -/
theorem typed_callContractWordWithValue_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.callContractWordWithValue.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value,
          .hostApply .callContractWordWithValue :: continuation, store⟩
        suspension := by
  have tupleTyping :
      HostRuntimeValueHasType world value
        (.product .word (.product .word .word)) definitions := by
    simpa using valueTyping
  obtain ⟨target, transferredValue, input, rfl⟩ :=
    tupleTyping.wordTriple_shape
  exact
    ⟨⟨.callContractWordWithValue target transferredValue input,
        continuation, store⟩,
      .callContractWordWithValue⟩

/-- A well-typed template/value/input tuple emits one creation request. -/
theorem typed_createContractWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.createContractWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value,
          .hostApply .createContractWord :: continuation, store⟩
        suspension := by
  have tupleTyping :
      HostRuntimeValueHasType world value
        (.product .word (.product .word .word)) definitions := by
    simpa using valueTyping
  obtain ⟨templateId, transferredValue, input, rfl⟩ :=
    tupleTyping.wordTriple_shape
  exact
    ⟨⟨.createContractWord templateId transferredValue input,
        continuation, store⟩,
      .createContractWord⟩

/-- A well-typed topic/payload pair emits one log request. -/
theorem typed_emitLogWord_emits
    {definitions : DataEnvironment} {world : StoreTyping}
    {value : Value} {continuation : List Frame} {store : Store}
    (valueTyping : HostRuntimeValueHasType world value
      HostFunction.emitLogWord.parameterType definitions) :
    ∃ suspension,
      HostRequestEmission
        ⟨.ret value, .hostApply .emitLogWord :: continuation, store⟩
        suspension := by
  have pairTyping :
      HostRuntimeValueHasType world value
        (.product .word .word) definitions := by
    simpa using valueTyping
  obtain ⟨topic, payload, rfl⟩ := pairTyping.wordPair_shape
  exact
    ⟨⟨.emitLogWord topic payload, continuation, store⟩,
      .emitLogWord⟩

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
  cases function with
  | storageRead => exact typed_storageRead_emits valueTyping
  | storageWrite => exact typed_storageWrite_emits valueTyping
  | storageAddress => exact typed_storageAddress_emits valueTyping
  | codeAddress => exact typed_codeAddress_emits valueTyping
  | callValue => exact typed_callValue_emits valueTyping
  | callerAddress => exact typed_callerAddress_emits valueTyping
  | inputDataByte? => exact typed_inputDataByte?_emits valueTyping
  | inputDataSize => exact typed_inputDataSize_emits valueTyping
  | inputDataWordBE? => exact typed_inputDataWordBE?_emits valueTyping
  | currentAddress => exact typed_currentAddress_emits valueTyping
  | callContractWord => exact typed_callContractWord_emits valueTyping
  | callContractWordWithValue =>
      exact typed_callContractWordWithValue_emits valueTyping
  | createContractWord =>
      exact typed_createContractWord_emits valueTyping
  | emitLogWord =>
      exact typed_emitLogWord_emits valueTyping

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
