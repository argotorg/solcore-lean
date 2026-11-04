import Solcore.ContractRuntime.Contracts
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState

/-!
# Laws of checked contracts

Word programs, profiles, `CheckedCoreContract`, the two registries, and the environment.
-/

section
-- leanmerge: from Solcore.ContractRuntime.CheckedHostCoreWordProgram
/-! Checker-accepted host-aware Core programs with Word result type. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramProperties`
-/

/-! Admission and projection laws for checked Word-result programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreWordProgram

@[simp] theorem mk_code
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code = code :=
  rfl

@[simp] theorem mk_resultType
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code.program.resultType =
      .word :=
  resultTypeEq

@[simp] theorem ofChecked?_of_word
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    ofChecked? code = some ⟨code, resultTypeEq⟩ := by
  simp [ofChecked?, resultTypeEq]

@[simp] theorem ofChecked?_of_nonword
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    ofChecked? code = none := by
  simp [ofChecked?, resultTypeNe]

@[simp] theorem ofProgram?_of_checked_word
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeEq : program.resultType = .word) :
    ofProgram? program = some ⟨⟨program, checked⟩, resultTypeEq⟩ := by
  simp [ofProgram?, checked, resultTypeEq]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, CheckedHostCoreProgram.ofProgram?, rejected]

@[simp] theorem ofProgram?_of_checked_nonword
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeNe : program.resultType ≠ .word) :
    ofProgram? program = none := by
  simp [ofProgram?, checked, ofChecked?, resultTypeNe]

end Solcore.ContractRuntime.CheckedHostCoreWordProgram

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramExecution`
-/

/-! Storage-backed execution specialized to checked Word-result programs. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreWordProgramExecutionProperties`
-/

/-! Safety, projection, stability, and fuel laws for checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace CheckedHostCoreWordProgram

theorem runWithStorage_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      .word code.code.program.dataDefinitions := by
  have typing := code.code.runWithStorage_hasType context inputs fuel
  rw [code.resultType_eq_word] at typing
  exact typing

theorem runWithStorage_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  simpa only [runWithStorage] using
    code.code.runWithStorage_ne_fault
      context inputs fuel error faultState

/-- Exact raw fault results are impossible for checked Word execution. -/
theorem runWithStorage_ne_fault_result
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    code.runWithStorage context inputs fuel ≠
      ⟨finalContext, .fault error faultState⟩ := by
  intro execution
  apply code.runWithStorage_ne_fault context inputs fuel error faultState
  exact congrArg HostDriverResult.outcome execution

/-- Every completed checked Word execution contains exactly a Word value. -/
theorem runWithStorage_done_word
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩) :
    ∃ word, value = .word word := by
  have outcome :
      (code.code.runWithStorage context inputs fuel).outcome =
        .done value store := by
    simpa only [runWithStorage] using
      congrArg HostDriverResult.outcome execution
  obtain ⟨world, _storeTyping, valueTyping⟩ :=
    code.code.runWithStorage_done_hasType context inputs outcome
  rw [code.resultType_eq_word] at valueTyping
  exact valueTyping.word_shape

theorem runWithStorageReturnedFrameCompletion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion ↔
      code.runWithStorage context inputs fuel =
        completion.toHostDriverResult := by
  exact HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff
    (code.runWithStorage context inputs fuel) completion

/-- A checked Word projection is absent at exhaustion or a policy boundary. -/
theorem runWithStorageReturnedFrameCompletion?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel = none ↔
      (∃ finalContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩) ∨
      ∃ finalContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  exact
    HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
      (code.runWithStorage context inputs fuel)
      (code.runWithStorage_hasType context inputs fuel)

/-- Once a Word completion is available, every larger budget returns it. -/
theorem runWithStorageReturnedFrameCompletion?_some_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {completion : WordReturnedFrameCompletion RollbackState TraceState}
    (completed :
      code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion)
    (more : fuel ≤ largerFuel) :
    code.runWithStorageReturnedFrameCompletion?
        context inputs largerFuel = some completion := by
  have execution :=
    (code.runWithStorageReturnedFrameCompletion?_eq_some_iff
      context inputs fuel completion).mp completed
  have stable := code.code.runWithStorage_done_stable
    context inputs execution more
  exact
    (code.runWithStorageReturnedFrameCompletion?_eq_some_iff
      context inputs largerFuel completion).mpr stable

/-- Raw resumption uses the same immutable inputs and exact summed budget. -/
theorem runWithStorage_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) := by
  simpa only [runWithStorage] using
    code.code.runWithStorage_resumeWithFuel
      context inputs fuel additional

/-- Classifying a resumed raw run agrees with classifying one summed run. -/
theorem toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    ((code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional).toWordReturnedFrameCompletion? =
      code.runWithStorageReturnedFrameCompletion?
        context inputs (fuel + additional) := by
  rw [code.runWithStorage_resumeWithFuel context inputs fuel additional]
  rfl

end CheckedHostCoreWordProgram

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.CoreContractEntryProfile
/-! Typed completion conventions for syntax-independent checked Core contracts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CoreContractEntryProfile

@[simp] theorem ofWordTupleType?_wordTupleType (count : Nat) :
    ofWordTupleType? (wordTupleType count) = some count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [wordTupleType, ofWordTupleType?, ih]

@[simp] theorem wordTupleType_inj {left right : Nat} :
    wordTupleType left = wordTupleType right ↔ left = right := by
  constructor
  · intro equal
    simpa using congrArg ofWordTupleType? equal
  · intro equal
    rw [equal]

@[simp] theorem ofEnumPayloadType?_enumPayloadType (payload : EnumPayload) :
    ofEnumPayloadType? (enumPayloadType payload) = some payload := by
  cases payload <;> rfl

@[simp] theorem enumPayloadType_inj {payload other : EnumPayload} :
    enumPayloadType payload = enumPayloadType other ↔ payload = other := by
  constructor
  · intro equal
    simpa using congrArg ofEnumPayloadType? equal
  · rintro rfl
    rfl

/-- Every constructor's value is a product, never the unit of an empty `bytes`
value. -/
@[simp] theorem enumPayloadType_ne_unit (payload : EnumPayload) :
    enumPayloadType payload ≠ .unit := by
  cases payload <;> simp [enumPayloadType]

@[simp] theorem unit_ne_enumPayloadType (payload : EnumPayload) :
    Core.Ty.unit ≠ enumPayloadType payload :=
  (enumPayloadType_ne_unit payload).symm

@[simp] theorem ofEnumType?_enumType (first : EnumPayload) (rest : List EnumPayload) :
    ofEnumType? (enumType first rest) = some (first, rest) := by
  induction rest generalizing first with
  | nil => cases first <;> rfl
  | cons next rest ih => simp [enumType, ofEnumType?, ih]

@[simp] theorem enumType_inj {first other : EnumPayload} {rest others : List EnumPayload} :
    enumType first rest = enumType other others ↔ first = other ∧ rest = others := by
  constructor
  · intro equal
    simpa using congrArg ofEnumType? equal
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem ofRawBytesType?_rawBytesType (extraWords : Nat) :
    ofRawBytesType? (rawBytesType extraWords) = some extraWords := by
  simp [rawBytesType, ofRawBytesType?]

end CoreContractEntryProfile

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.CheckedCoreContract
/-! Checked Core code with a fixed contract-level completion convention. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCoreContractExtensionality`
-/

/-! Checked contracts are determined by their underlying checked program. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime

theorem CheckedHostCoreProgram.eq_of_program_eq
    {left right : CheckedHostCoreProgram}
    (equal : left.program = right.program) : left = right := by
  cases left
  cases right
  simp only at equal
  subst_vars
  rfl

theorem CoreContractEntryProfile.eq_of_resultType_eq
    {left right : CoreContractEntryProfile}
    (equal : left.resultType = right.resultType) : left = right := by
  cases left <;> cases right <;>
    simp_all [CoreContractEntryProfile.resultType,
      CoreContractEntryProfile.wordTupleType,
      CoreContractEntryProfile.boundedBytesType,
      CoreContractEntryProfile.rawBytesType,
      CoreContractEntryProfile.enumType]

@[ext] theorem CheckedCoreContract.ext
    {left right : CheckedCoreContract}
    (programEq : left.code.program = right.code.program) : left = right := by
  cases left with
  | mk leftCode leftProfile leftType =>
      cases right with
      | mk rightCode rightProfile rightType =>
          change leftCode.program = rightCode.program at programEq
          have codeEq : leftCode = rightCode :=
            CheckedHostCoreProgram.eq_of_program_eq programEq
          subst rightCode
          have profileEq : leftProfile = rightProfile :=
            CoreContractEntryProfile.eq_of_resultType_eq
              (leftType.symm.trans rightType)
          subst rightProfile
          rfl

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.CheckedContractRegistry
/-! Dynamic resolution of registered checked contracts in a WorldState. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedContractRegistryProperties`
-/

/-! Exact laws for current-world checked-contract resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedContractRegistry

@[simp] theorem resolve?_of_lookup_none
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    (absent : registry.lookup target = none) :
    registry.resolve? currentWorld target = none := by
  simp [resolve?, absent]

@[simp] theorem resolve?_of_account_absent
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    (registered : registry.lookup target = some contract)
    (absent : currentWorld.account? target = none) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i account accountEntry
    simp_all

@[simp] theorem resolve?_of_code_absent
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    {account : Account}
    (registered : registry.lookup target = some contract)
    (accountPresent : currentWorld.account? target = some account)
    (absent : account.code? = none) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i selectedAccount accountEntry
    have accountEq : selectedAccount = account :=
      Option.some.inj (accountEntry.symm.trans accountPresent)
    subst account
    split
    · rfl
    · rename_i installedCode codeEntry
      exact False.elim (by simp_all)

@[simp] theorem resolve?_of_code_mismatch
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    {account : Account}
    {installedCode : CheckedHostCoreProgram}
    (registered : registry.lookup target = some contract)
    (accountPresent : currentWorld.account? target = some account)
    (codePresent : account.code? = some installedCode)
    (mismatch : installedCode.program ≠ contract.code.program) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i selectedAccount accountEntry
    have accountEq : selectedAccount = account :=
      Option.some.inj (accountEntry.symm.trans accountPresent)
    subst account
    split
    · rfl
    · rename_i selectedCode selectedCodePresent
      have codeEq : selectedCode = installedCode :=
        Option.some.inj (selectedCodePresent.symm.trans codePresent)
      subst installedCode
      simp [mismatch]

@[simp] theorem resolve?_of_lookup_and_installed
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    (registered : registry.lookup target = some contract)
    (installed :
      InstalledCheckedCoreContract currentWorld target contract) :
    registry.resolve? currentWorld target = some ⟨contract, installed⟩ := by
  cases installed with
  | mk account accountPresent codePresent =>
      unfold resolve?
      simp only [registered]
      split
      · rename_i accountAbsent
        simp_all
      · rename_i selectedAccount accountEntry
        have accountEq : selectedAccount = account :=
          Option.some.inj (accountEntry.symm.trans accountPresent)
        subst account
        split
        · rename_i codeAbsent
          simp_all
        · rename_i installedCode installedCodePresent
          have codeEq : installedCode = contract.code :=
            Option.some.inj (installedCodePresent.symm.trans codePresent)
          subst installedCode
          simp only [dif_pos]

/-- Every successful resolution identifies the registry entry it consumed. -/
theorem lookup_eq_some_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    registry.lookup target = some resolved.1 := by
  unfold resolve? at resolvedEq
  split at resolvedEq
  · simp_all
  · rename_i contract registered
    split at resolvedEq
    · simp_all
    · rename_i account accountPresent
      split at resolvedEq
      · simp_all
      · rename_i installedCode codePresent
        split at resolvedEq
        · have resolutionEq := Option.some.inj resolvedEq
          have contractEq : contract = resolved.1 :=
            congrArg Sigma.fst resolutionEq
          exact registered.trans (congrArg some contractEq)
        · simp_all

/-- Exact pointwise success law; installation evidence supplies world matching. -/
@[simp] theorem resolve?_eq_some_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    (resolved : Resolution currentWorld target) :
    registry.resolve? currentWorld target = some resolved ↔
      registry.lookup target = some resolved.1 := by
  constructor
  · exact lookup_eq_some_of_resolve?_eq_some
      registry currentWorld target
  · intro registered
    exact resolve?_of_lookup_and_installed
      registry currentWorld target registered resolved.2

/-- The account witness returned on success belongs to the queried world now. -/
theorem account_present_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (_resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    currentWorld.account? target = some resolved.2.account :=
  resolved.2.account_present

/-- The successful account contains exactly the resolved checked program. -/
theorem code_present_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (_resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    resolved.2.account.code? = some resolved.1.code :=
  resolved.2.code_present

/-- Existential success is exactly registration plus current-world installation. -/
theorem exists_resolve?_eq_some_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address) :
    (∃ resolved : Resolution currentWorld target,
      registry.resolve? currentWorld target = some resolved) ↔
      ∃ contract account,
        registry.lookup target = some contract ∧
        currentWorld.account? target = some account ∧
        account.code? = some contract.code := by
  constructor
  · rintro ⟨resolved, resolvedEq⟩
    exact ⟨resolved.1, resolved.2.account,
      lookup_eq_some_of_resolve?_eq_some
        registry currentWorld target resolvedEq,
      resolved.2.account_present,
      resolved.2.code_present⟩
  · rintro ⟨contract, account, registered, accountPresent, codePresent⟩
    let installed :
        InstalledCheckedCoreContract currentWorld target contract := {
      account := account
      account_present := accountPresent
      code_present := codePresent
    }
    exact ⟨⟨contract, installed⟩,
      resolve?_of_lookup_and_installed
        registry currentWorld target registered installed⟩

/-- Exact failure law: no registered contract is installed in the current world. -/
@[simp] theorem resolve?_eq_none_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address) :
    registry.resolve? currentWorld target = none ↔
      ¬ ∃ contract account,
        registry.lookup target = some contract ∧
        currentWorld.account? target = some account ∧
        account.code? = some contract.code := by
  rw [← exists_resolve?_eq_some_iff]
  constructor
  · intro resolvedNone resolved
    rcases resolved with ⟨resolved, resolvedEq⟩
    rw [resolvedNone] at resolvedEq
    contradiction
  · intro noResolved
    cases resolvedEq : registry.resolve? currentWorld target with
    | none => rfl
    | some resolved =>
        exact False.elim (noResolved ⟨resolved, resolvedEq⟩)

end Solcore.ContractRuntime.CheckedContractRegistry
end

section
-- leanmerge: from Solcore.ContractRuntime.CheckedCreationTemplateRegistry
/-! Checked initializer/runtime pairs selected by immutable creation identifiers. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationTemplateRegistryProperties`
-/

/-! Projection and empty-registry laws for checked creation templates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCreationTemplate

@[simp] theorem mk_initializer
    (initializer runtime : CheckedCoreContract) :
    (CheckedCreationTemplate.mk initializer runtime).initializer = initializer :=
  rfl

@[simp] theorem mk_runtime
    (initializer runtime : CheckedCoreContract) :
    (CheckedCreationTemplate.mk initializer runtime).runtime = runtime :=
  rfl

end CheckedCreationTemplate

namespace CheckedCreationTemplateRegistry

@[simp] theorem empty_lookup (identifier : Core.Word) :
    empty.lookup identifier = none :=
  rfl

end CheckedCreationTemplateRegistry

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.ExecutionEnvironment
/-! Immutable registries and address derivation fixed for one execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.ExecutionEnvironmentProperties`
-/

/-! Exact projections for the immutable execution environment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ExecutionEnvironment

@[simp] theorem callsOnly_callRegistry
    (registry : CheckedContractRegistry) :
    (callsOnly registry).callRegistry = registry :=
  rfl

@[simp] theorem callsOnly_creationTemplates_lookup
    (registry : CheckedContractRegistry)
    (identifier : Core.Word) :
    (callsOnly registry).creationTemplates.lookup identifier = none :=
  rfl

@[simp] theorem inertCreationAddressPolicy_derive
    (creator : Address) (nonce : Core.Word) :
    inertCreationAddressPolicy.derive creator nonce = ⟨0, by decide⟩ :=
  rfl

@[simp] theorem callsOnly_creationAddressPolicy_derive
    (registry : CheckedContractRegistry)
    (creator : Address) (nonce : Core.Word) :
    (callsOnly registry).creationAddressPolicy.derive creator nonce =
      ⟨0, by decide⟩ :=
  rfl

end Solcore.ContractRuntime.ExecutionEnvironment
end
