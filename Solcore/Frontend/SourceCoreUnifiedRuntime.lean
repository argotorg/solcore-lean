import Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs
import Solcore.Frontend.SourceRuntimeDeepValidation

/-! Compatibility observations from the cached indexed Core pipeline.
The old public source validators and error priority remain at the boundary;
execution and resumption use only the typed Core checkpoint. Initial source
heaps are an inert, validated prefix, never imported as arbitrary Core code.
Decoder/compiler failures are explicit adapter errors, not source faults.
This module does not claim whole source/Core meaning preservation or a common
numeric fuel cost. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedRuntime
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev SourceValue := SourceTypedRuntime.Value
abbrev SourceState := SourceTypedRuntime.RuntimeState
abbrev RunResult := SourceTypedRuntime.RunResult
abbrev RuntimeError := SourceTypedRuntime.RuntimeError

inductive PrepareError where
  | root (error : RuntimeError)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | rootInputMismatch (key : Key)
  | rootResultMismatch (key : Key)
  | nativeResultMismatch (key : Key)
  | output (error : SourceCoreCallableIndexedHeapOutputs.Error)
  deriving Repr

structure Root {checked : Checked} (program : Program checked) where private mk ::
  entry : SourceCoreCallableIndexedPrograms.Entry program.layouts
  member : entry ∈ program.entries
  specialized : SourceSpecialization.SpecializedFunction
  selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan entry.key = .ok specialized
  inputExact : entry.inputs.map (·.scheme.body) = specialized.function.typedBody.inputs.map (·.scheme.body)
  resultExact : entry.sourceResultType = specialized.function.inferredBodyType
  projected : checked.catalog.project specialized.function.inferredBodyType = .ok entry.native.resultType
  evidence : Except RuntimeError SourceTypedRuntime.RuntimeEvidenceEnvironment
  evidencePrepared : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program.base.sourceProgram
    specialized.key specialized.assumptions = evidence

def Root.argumentTypes {checked : Checked} {program : Program checked} (root : Root program) : List Ty :=
  root.specialized.function.typedBody.inputs.map (·.scheme.body)
def Root.expected {checked : Checked} {program : Program checked} (root : Root program) : Ty :=
  root.specialized.function.inferredBodyType

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  planPrepared : SourceCompilationPlan.prepareExecutablePlanEvidence program.base.sourceProgram
    program.base.validationPlan = .ok program.base.plan
  roots : List (Root program)
  output : SourceCoreCallableIndexedHeapOutputs.Prepared program
  outputPrepared : SourceCoreCallableIndexedHeapOutputs.prepare program = .ok output

private def prepareRoot {checked : Checked} (program : Program checked)
    (entry : {entry // entry ∈ program.entries}) : Except PrepareError (Root program) := do
  match selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan entry.val.key with
  | .error error => throw (.root error)
  | .ok specialized =>
    if inputExact : entry.val.inputs.map (·.scheme.body) = specialized.function.typedBody.inputs.map (·.scheme.body) then
      if resultExact : entry.val.sourceResultType = specialized.function.inferredBodyType then
        match projected : checked.catalog.project specialized.function.inferredBodyType with
        | .error error => throw (.projection error)
        | .ok type =>
          if nativeExact : type = entry.val.native.resultType then
            let evidence := SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program.base.sourceProgram
              specialized.key specialized.assumptions
            pure ⟨entry.val, entry.property, specialized, selected, inputExact, resultExact,
              by simpa only [nativeExact] using projected, evidence, rfl⟩
          else throw (.nativeResultMismatch entry.val.key)
      else throw (.rootResultMismatch entry.val.key)
    else throw (.rootInputMismatch entry.val.key)

/-- Called once while preparing the owning artifact. The plan equation is an
actual factory receipt; runtime execution never prepares a source plan. -/
def prepare {checked : Checked} (program : Program checked) : Except PrepareError (Prepared program) := do
  let planPrepared := program.base.planPrepared
  let roots ← program.entries.attach.mapM (prepareRoot program)
  match outputPrepared : SourceCoreCallableIndexedHeapOutputs.prepare program with
  | .error error => throw (.output error)
  | .ok output => pure ⟨planPrepared, roots, output, outputPrepared⟩

def Prepared.root? {checked : Checked} {program : Program checked} (prepared : Prepared program) (key : Key) :
    Option (Root program) := prepared.roots.find? (fun root => decide (root.entry.key = key))

/-- The exact old shallow diagnostics precede prepared-plan deep validation.
This helper performs no source expression/statement evaluation. -/
def boundaryFailure {checked : Checked} {program : Program checked} (_prepared : Prepared program)
    (root : Root program) (arguments : List SourceValue) (validationFuel : Nat) (initial : SourceState) :
    Option RuntimeError :=
  match SourceTypedRuntime.validateInputs program.base.sourceProgram.signatures program.base.validationPlan
      validationFuel root.argumentTypes arguments with
  | some error => some error
  | none =>
    if !initial.isDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan then
      some .deepSafetyInitialStateRejected
    else if !SourceTypedRuntime.valuesDeeplySafe validationFuel program.base.sourceProgram.signatures
        program.base.plan initial arguments root.argumentTypes then
      some .deepSafetyInputsRejected
    else match root.evidence with
      | .error error => some error
      | .ok _ => none

private theorem true_of_not_neg {value : Bool} (accepted : ¬ (!value) = true) : value = true := by
  cases value <;> simp_all

theorem boundaryFailure_none {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {root : Root program} {arguments : List SourceValue} {validationFuel : Nat} {initial : SourceState}
    (accepted : boundaryFailure prepared root arguments validationFuel initial = none) :
    SourceTypedRuntime.validateInputs program.base.sourceProgram.signatures program.base.validationPlan
      validationFuel root.argumentTypes arguments = none ∧
    initial.isDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan = true ∧
    SourceTypedRuntime.valuesDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan
      initial arguments root.argumentTypes = true := by
  unfold boundaryFailure at accepted
  cases shallow : SourceTypedRuntime.validateInputs program.base.sourceProgram.signatures
      program.base.validationPlan validationFuel root.argumentTypes arguments with
  | some error => simp [shallow] at accepted
  | none =>
    simp only [shallow] at accepted
    split at accepted
    · contradiction
    · next initialSafe =>
      split at accepted
      · contradiction
      · next inputsSafe => exact ⟨rfl, true_of_not_neg initialSafe, true_of_not_neg inputsSafe⟩

inductive Error where
  | unavailableRoot (key : Key)
  | native (error : SourceCoreCallableIndexedPrograms.RunError)
  | nativeRootMismatch
  | heap (error : SourceCoreCallableIndexedHeapOutputs.Error)
  | output (error : SourceCoreCallableIndexedOutputs.Error)
  | unknownLanguageReason (reason : Core.Word)
  | internalFault (error : Core.MachineFault)
  | invalidCarrier
  deriving Repr

structure Execution {checked : Checked} {program : Program checked} (prepared : Prepared program) where private mk ::
  root : Root program
  arguments : List SourceValue
  validationFuel : Nat
  initial : SourceState
  boundaryAccepted : boundaryFailure prepared root arguments validationFuel initial = none
  completion : SourceCoreCallableIndexedPrograms.Completion program
  keyExact : completion.entry.key = root.entry.key
  resultExact : completion.entry.native.resultType = root.entry.native.resultType

theorem Execution.projected {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (execution : Execution prepared) :
    checked.catalog.project execution.root.expected = .ok execution.completion.entry.native.resultType := by
  rw [execution.resultExact]
  exact execution.root.projected

def Execution.resume {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (execution : Execution prepared) (fuel : Nat) : Execution prepared := {
  execution with
  completion := execution.completion.resume fuel
  keyExact := by unfold SourceCoreCallableIndexedPrograms.Completion.resume; split <;> exact execution.keyExact
  resultExact := by unfold SourceCoreCallableIndexedPrograms.Completion.resume; split <;> exact execution.resultExact
}

/-- Structural public data cost. Callable code and saved environments are
not recursively decoded by the data codec; their owned receipts are cached. -/
def nativeDataSize : Core.Value → Nat
  | .pair left right => nativeDataSize left + nativeDataSize right + 1
  | .inLeft _ child | .inRight _ child | .constructed _ child => nativeDataSize child + 1
  | _ => 1

private def metadataSize : SourceCoreRawMetadata.Metadata → Nat
  | .proxy type => type.size + 1
  | .mapping key value => key.size + value.size + 1
  | .constructor instantiation => instantiation.resultType.size +
      (instantiation.payloadTypes.foldl (fun total type => total + type.size) 0) +
      (instantiation.parameterSubstitution.foldl (fun total entry => total + entry.2.size) 0) + 1

/-- Codec descent also counts ordered mapping width. Derive its budget from
finite native data instead of imposing an additional public input depth limit.
The explicit override is useful for testing honest adapter budget failures. -/
def Execution.exportFuel {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (execution : Execution prepared) : Nat :=
  let store := SourceCoreCallableIndexedLedger.store execution.completion
  let valueSize := match execution.completion.result.native.observation with
    | .succeeded value _ | .invalidCarrier value _ => nativeDataSize value
    | _ => 0
  store.foldl (fun bound value => max bound (nativeDataSize value)) valueSize +
    (execution.completion.result.context.registry.entries.foldl (fun total entry => total + metadataSize entry) 0) + execution.root.expected.size + 64

def Execution.finalize {checked : Checked} {program : Program checked}
    {prepared : Prepared program} (execution : Execution prepared) (value : SourceValue) (final : SourceState) : RunResult :=
  if value.type? program.base.plan ≠ some (SourceTypedRuntime.runtimeType execution.root.expected) then
    .fault (.resultTypeMismatch execution.root.expected (value.type? program.base.plan)) final
  else if !final.isDeeplySafe execution.validationFuel program.base.sourceProgram.signatures program.base.plan then
    .fault .deepSafetyFinalStateRejected final
  else if !execution.initial.typeLayoutExtends final then
    .fault .deepSafetyFinalStateRejected final
  else if !value.isDeeplySafe execution.validationFuel program.base.sourceProgram.signatures
      program.base.plan final execution.root.expected then
    .fault (.deepSafetyResultRejected execution.root.expected (value.type? program.base.plan)) final
  else .done value final

/-- Recover the same public deep certificate after final source validation.
This proves the boundary checks, not that decoded source data has a separate
whole-program source execution derivation. -/
theorem Execution.finalize_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} (execution : Execution prepared) {value : SourceValue} {final : SourceState}
    (done : execution.finalize value final = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value final := by
  unfold Execution.finalize at done
  split at done
  · contradiction
  · split at done
    · contradiction
    · next finalSafe =>
      split at done
      · contradiction
      · next layoutSafe =>
        split at done
        · contradiction
        · next valueSafe =>
          have boundary := boundaryFailure_none execution.boundaryAccepted
          have planExact : SourceTypedRuntime.preparedDeepExecutablePlan program.base.sourceProgram
              program.base.validationPlan = program.base.plan := by
            simp only [SourceTypedRuntime.preparedDeepExecutablePlan, prepared.planPrepared]
          exact ⟨by simpa only [planExact] using prepared.planPrepared,
            planExact.symm ▸ SourceTypedRuntime.RuntimeState.isDeeplySafe_sound boundary.2.1,
            planExact.symm ▸ SourceTypedRuntime.valuesDeeplySafe_sound boundary.2.2,
            planExact.symm ▸ SourceTypedRuntime.RuntimeState.isDeeplySafe_sound (true_of_not_neg finalSafe),
            SourceTypedRuntime.RuntimeState.typeLayoutExtends_sound (true_of_not_neg layoutSafe),
            planExact.symm ▸ SourceTypedRuntime.Value.isDeeplySafe_sound (true_of_not_neg valueSafe)⟩

/-- Export one genuine Core observation. Source locations are offset by the
inert initial prefix and retain exact allocation order/aliases. -/
def Execution.observe {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (execution : Execution prepared) (exportFuel : Option Nat := none) : Except Error RunResult := do
  let fuel := exportFuel.getD execution.exportFuel
  let heap ← (SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output execution.completion
    execution.initial.heap fuel).mapError Error.heap
  let state : SourceState := ⟨heap.heap⟩
  match execution.completion.result.native.observation with
  | .succeeded _ _ =>
    let decoded ← (SourceCoreCallableIndexedOutputs.decodeSuccess prepared.output.output execution.completion
      execution.root.expected execution.projected execution.initial.heap fuel).mapError Error.output
    pure (execution.finalize decoded.decoded.source state)
  | .failed reason _ =>
    match execution.completion.result.diagnostics.diagnostic? reason with
    | some diagnostic => pure (.fault diagnostic.error state)
    | none => throw (.unknownLanguageReason reason)
  | .outOfFuel _ => pure (.outOfFuel state)
  | .internalFault error _ => throw (.internalFault error)
  | .invalidCarrier _ _ => throw .invalidCarrier

theorem Execution.observe_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} (execution : Execution prepared) {fuel : Option Nat}
    {value : SourceValue} {final : SourceState}
    (done : execution.observe fuel = .ok (.done value final)) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value final := by
  unfold Execution.observe at done
  cases heapEq : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output execution.completion
      execution.initial.heap (fuel.getD execution.exportFuel) with
  | error error => simp [heapEq, Except.mapError, bind, Except.bind] at done
  | ok heap =>
    simp only [heapEq, Except.mapError, bind, Except.bind] at done
    cases observed : execution.completion.result.native.observation with
    | succeeded native store =>
      simp only [observed] at done
      cases decodedEq : SourceCoreCallableIndexedOutputs.decodeSuccess prepared.output.output execution.completion
          execution.root.expected execution.projected execution.initial.heap (fuel.getD execution.exportFuel) with
      | error error => simp [decodedEq] at done
      | ok decoded =>
        simp only [decodedEq, pure, Except.pure,
          Except.ok.injEq] at done
        have values : decoded.decoded.source = value ∧ (⟨heap.heap⟩ : SourceState) = final := by
          unfold Execution.finalize at done
          split at done
          · contradiction
          · split at done
            · contradiction
            · split at done
              · contradiction
              · split at done
                · contradiction
                · cases done; exact ⟨rfl, rfl⟩
        rcases values with ⟨rfl, rfl⟩
        exact execution.finalize_done_certificate done
    | failed reason store =>
      simp only [observed] at done
      split at done <;> simp [pure, Except.pure] at done
    | outOfFuel state => simp [observed, pure, Except.pure] at done
    | internalFault error store => simp [observed] at done
    | invalidCarrier native store => simp [observed] at done

/-- Retain the actual typed checkpoint beside the historical public payload.
Rejected calls retain no native execution and can be resumed harmlessly. -/
structure Result {checked : Checked} {program : Program checked} (prepared : Prepared program) where private mk ::
  observation : RunResult
  execution : Option (Execution prepared)
  observed : match execution with
    | none => ∀ value final, observation ≠ .done value final
    | some execution => execution.observe = .ok observation

/-- An actual public success carries the old prepared deep certificate for
its exact cached root and accepted request. -/
theorem Result.done_certificate {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (result : Result prepared) {value : SourceValue} {final : SourceState}
    (done : result.observation = .done value final) :
    ∃ execution, result.execution = some execution ∧
      SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
        execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value final := by
  cases executionEq : result.execution with
  | none =>
    have impossible : ∀ value final, result.observation ≠ .done value final := by
      simpa only [executionEq] using result.observed
    exact False.elim (impossible value final done)
  | some execution =>
    have observed : execution.observe = .ok result.observation := by
      simpa only [executionEq] using result.observed
    exact ⟨execution, rfl, execution.observe_done_certificate (observed.trans (congrArg Except.ok done))⟩

def run {checked : Checked} {program : Program checked} (prepared : Prepared program) (key : Key)
    (arguments : List SourceValue) (validationFuel executionFuel : Nat) (initial : SourceState := {}) :
    Except Error (Result prepared) := do
  match SourceCompilationPlan.exactSpecialization program.base.validationPlan key with
  | .error error => pure ⟨.fault error initial, none, by intro value final impossible; contradiction⟩
  | .ok _ =>
    let root ← match prepared.root? key with
      | some root => pure root | none => throw (.unavailableRoot key)
    match boundaryAccepted : boundaryFailure prepared root arguments validationFuel initial with
    | some error => pure ⟨.fault error initial, none, by intro value final impossible; contradiction⟩
    | none =>
      let completion ← (program.runSource key arguments executionFuel validationFuel).mapError Error.native
      if keyExact : completion.entry.key = root.entry.key then
        if resultExact : completion.entry.native.resultType = root.entry.native.resultType then
          let execution := Execution.mk root arguments validationFuel initial boundaryAccepted completion keyExact resultExact
          match observed : execution.observe with
          | .error error => throw error
          | .ok observation => pure ⟨observation, some execution, observed⟩
        else throw .nativeRootMismatch
      else throw .nativeRootMismatch

def Result.resume {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (result : Result prepared) (fuel : Nat) : Except Error (Result prepared) := do
  match result.execution with
  | none => pure result
  | some execution =>
    let execution := execution.resume fuel
    match observed : execution.observe with
    | .error error => throw error
    | .ok observation => pure ⟨observation, some execution, observed⟩

end Solcore.Frontend.SourceCoreUnifiedRuntime
