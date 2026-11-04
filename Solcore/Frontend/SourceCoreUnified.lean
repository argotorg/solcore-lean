import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.Frontend.Internal.RuntimeValidation

/-!
# The cached artifact

One reusable source-compatible Core artifact, and its runtime adapter. Main declaration:
`SourceCoreUnifiedCompilation.Compiled`. Main theorems:
`SourceCoreUnifiedPreparationCertificates.run_done_specialization`,
`SourceCoreUnifiedPreparationCertificates.run_resume_done_specialization`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreUnifiedRuntime
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreUnifiedCompilation
/-! Prepare one reusable source-compatible Core artifact. The actual common
compiler, indexed frame program, and source observation caches are prepared
once. Calls and resumptions retain the same native program and typed checkpoint.
This boundary remains separate from the existing compiler facade while its
complete feature admission and source meaning correspondence are established. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedCompilation
open SourceInference
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Key := SourceSpecialization.SpecializationKey

inductive Error where
  | compatible (error : SourceCoreCompatibleFunctions.Error)
  | indexed (error : SourceCoreCallableIndexedPrograms.Error)
  | runtime (error : SourceCoreUnifiedRuntime.PrepareError)
  deriving Repr

structure Compiled where private mk ::
  sourceProgram : CheckedProgram
  validationPlan : Plan
  compilationFuel : Nat
  compatible : SourceCoreCompatibleFunctions.Automatic
  compatiblePrepared : SourceCoreCompatibleFunctions.prepare sourceProgram validationPlan compilationFuel = .ok compatible
  indexed : SourceCoreCallableIndexedPrograms.Prepared compatible.checked
  indexedPrepared : SourceCoreCallableIndexedPrograms.prepare compatible.prepared compilationFuel = .ok indexed
  runtime : SourceCoreUnifiedRuntime.Prepared indexed
  runtimePrepared : SourceCoreUnifiedRuntime.prepare indexed = .ok runtime

/-- All generated code and restoration metadata are cached before the first
invocation. Factory equations retain the actual owning compiler artifacts. -/
def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat) : Except Error Compiled := do
  let compatible ← match accepted : SourceCoreCompatibleFunctions.prepare program plan fuel with
    | .error error => throw (.compatible error)
    | .ok compatible => pure (⟨compatible, accepted⟩ : {compatible //
        SourceCoreCompatibleFunctions.prepare program plan fuel = .ok compatible})
  let indexed ← match accepted : SourceCoreCallableIndexedPrograms.prepare compatible.val.prepared fuel with
    | .error error => throw (.indexed error)
    | .ok indexed => pure (⟨indexed, accepted⟩ : {indexed //
        SourceCoreCallableIndexedPrograms.prepare compatible.val.prepared fuel = .ok indexed})
  let runtime ← match accepted : SourceCoreUnifiedRuntime.prepare indexed.val with
    | .error error => throw (.runtime error)
    | .ok runtime => pure (⟨runtime, accepted⟩ : {runtime //
        SourceCoreUnifiedRuntime.prepare indexed.val = .ok runtime})
  pure ⟨program, plan, fuel, compatible.val, compatible.property, indexed.val, indexed.property,
    runtime.val, runtime.property⟩

def Compiled.keys (compiled : Compiled) : List Key := compiled.indexed.entries.map (·.key)

abbrev Result (compiled : Compiled) := SourceCoreUnifiedRuntime.Result compiled.runtime

def Compiled.run (compiled : Compiled) (key : Key) (arguments : List SourceTypedRuntime.Value)
    (validationFuel executionFuel : Nat) (initial : SourceTypedRuntime.RuntimeState := {}) :
    Except SourceCoreUnifiedRuntime.Error (Result compiled) :=
  SourceCoreUnifiedRuntime.run compiled.runtime key arguments validationFuel executionFuel initial

def Result.resume {compiled : Compiled} (result : Result compiled) (fuel : Nat) :
    Except SourceCoreUnifiedRuntime.Error (Result compiled) := SourceCoreUnifiedRuntime.Result.resume result fuel

end Solcore.Frontend.SourceCoreUnifiedCompilation
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreUnifiedRuntimeCertificates
/-! Request-indexed certificates for the actual public Core-only adapter.
These retain the original source boundary checks and prepared deep certificate;
they do not assert a whole-source execution derivation or equal numeric fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedRuntime

open SourceInference

theorem Prepared.root?_facts {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {root : Root program}
    (found : prepared.root? key = some root) :
    root ∈ prepared.roots ∧ root.entry.key = key := by
  change prepared.roots.find? (fun root => decide (root.entry.key = key)) = some root at found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true (List.find?_some (p := fun candidate : Root program => decide (candidate.entry.key = key)) found)⟩

/-- Every native execution retained by `run` belongs to the exact request. -/
theorem run_execution_request {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    {execution : Execution prepared} (produced : result.execution = some execution) :
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial := by
  unfold run at ran
  split at ran
  · simp only [pure, Except.pure, Except.ok.injEq] at ran
    cases ran
    contradiction
  · simp only [bind, Except.bind] at ran
    split at ran
    · next root found =>
      simp only [pure, Except.pure] at ran
      split at ran
      · simp only [Except.ok.injEq] at ran
        cases ran
        contradiction
      · simp only [Except.mapError] at ran
        split at ran
        · contradiction
        · split at ran
          · split at ran
            · split at ran
              · contradiction
              · simp only [Except.ok.injEq] at ran
                cases ran
                simp only [Option.some.injEq] at produced
                cases produced
                exact ⟨(Prepared.root?_facts found).2, rfl, rfl, rfl⟩
            · contradiction
          · contradiction
    · contradiction

/-- The accepted request retains the old shallow and deep validation decisions
and the authoritative specialization input/result metadata. -/
theorem run_execution_boundary {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    {execution : Execution prepared} (produced : result.execution = some execution) :
    SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok execution.root.specialized ∧
    execution.root.entry.inputs.map (·.scheme.body) = execution.root.argumentTypes ∧
    execution.root.entry.sourceResultType = execution.root.expected ∧
    SourceTypedRuntime.validateInputs program.base.sourceProgram.signatures program.base.validationPlan
      validationFuel execution.root.argumentTypes arguments = none ∧
    initial.isDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan = true ∧
    SourceTypedRuntime.valuesDeeplySafe validationFuel program.base.sourceProgram.signatures program.base.plan
      initial arguments execution.root.argumentTypes = true := by
  rcases run_execution_request ran produced with ⟨keyExact, argumentsExact, fuelExact, initialExact⟩
  have selected := execution.root.selected
  rw [keyExact] at selected
  have boundary := boundaryFailure_none execution.boundaryAccepted
  rw [argumentsExact, fuelExact, initialExact] at boundary
  exact ⟨selected, execution.root.inputExact, execution.root.resultExact, boundary⟩

/-- The request agreement is reusable across any number of native resumptions. -/
def Result.Requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    (result : Result prepared) (key : Key) (arguments : List SourceValue)
    (validationFuel : Nat) (initial : SourceState) : Prop :=
  ∀ execution, result.execution = some execution →
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial

theorem run_requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result) :
    result.Requests key arguments validationFuel initial := fun _ produced => run_execution_request ran produced

theorem Result.resume_requests {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel fuel : Nat} {initial : SourceState}
    {result resumed : Result prepared} (requested : result.Requests key arguments validationFuel initial)
    (continued : result.resume fuel = .ok resumed) :
    resumed.Requests key arguments validationFuel initial := by
  unfold Result.resume at continued
  split at continued
  · simp only [pure, Except.pure, Except.ok.injEq] at continued
    cases continued
    exact requested
  · next previous previousEq =>
    dsimp only at continued
    split at continued
    · contradiction
    · simp only [pure, Except.pure, Except.ok.injEq] at continued
      cases continued
      intro execution produced
      simp only [Option.some.injEq] at produced
      cases produced
      exact requested previous previousEq

/-- Success uses the source input/result metadata of the specialization selected
by the actual request, with the original arguments and initial heap. -/
theorem Result.requested_done_specialization {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState}
    (requested : result.Requests key arguments validationFuel initial)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  rcases result.done_certificate done with ⟨execution, produced, certificate⟩
  rcases requested execution produced with ⟨keyExact, argumentsExact, _, initialExact⟩
  have selected := execution.root.selected
  rw [keyExact] at selected
  refine ⟨execution.root.specialized, selected, ?_⟩
  simpa only [Root.argumentTypes, Root.expected, argumentsExact, initialExact] using certificate

theorem run_done_specialization {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final :=
  Result.requested_done_specialization (run_requests ran) done

theorem Result.requested_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState} {specialized : SourceSpecialization.SpecializedFunction}
    (requested : result.Requests key arguments validationFuel initial)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final := by
  rcases Result.requested_done_specialization requested done with ⟨actual, actualSelected, certificate⟩
  have exactSpecialization : actual = specialized := Except.ok.inj (actualSelected.symm.trans selected)
  cases exactSpecialization
  exact certificate

theorem run_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel : Nat} {initial : SourceState} {result : Result prepared}
    {value : SourceValue} {final : SourceState} {specialized : SourceSpecialization.SpecializedFunction}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  Result.requested_done_certificate (run_requests ran) selected done

theorem run_resume_done_certificate {checked : Checked} {program : Program checked}
    {prepared : Prepared program} {key : Key} {arguments : List SourceValue}
    {validationFuel executionFuel resumeFuel : Nat} {initial : SourceState}
    {result resumed : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : run prepared key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumeFuel = .ok resumed)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : resumed.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  Result.requested_done_certificate (Result.resume_requests (run_requests ran) continued) selected done

end Solcore.Frontend.SourceCoreUnifiedRuntime
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
/-! Actual preparation equations recover source and base ownership. The cached
artifact's native shape does not supply these equalities. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
open SourceInference
abbrev Plan := SourceSpecializationWorklist.Plan

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem compatible_fields {source : CheckedProgram} {plan : Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = source.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (prepared : SourceCoreCompatibleFunctions.prepareWithCatalog source plan checked ownership fuel = .ok base) :
    base.sourceProgram = source ∧ base.validationPlan = plan := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at prepared
  obtain ⟨executable, _, prepared⟩ := bind_ok prepared
  obtain ⟨locals, _, prepared⟩ := bind_ok prepared
  obtain ⟨contexts, _, prepared⟩ := bind_ok prepared
  obtain ⟨functions, _, prepared⟩ := bind_ok prepared
  split at prepared
  · cases prepared; exact ⟨rfl, rfl⟩
  · obtain ⟨diagnostics, _, prepared⟩ := bind_ok prepared
    split at prepared
    · obtain ⟨table, _, prepared⟩ := bind_ok prepared
      obtain ⟨callableDiagnostics, _, prepared⟩ := bind_ok prepared
      simp only [pure, Except.pure, bind, Except.bind] at prepared
      obtain ⟨locals, _, prepared⟩ := bind_ok prepared
      obtain ⟨closures, _, prepared⟩ := bind_ok prepared
      obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
      obtain ⟨entries, _, prepared⟩ := bind_ok prepared
      cases prepared; exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, bind, Except.bind] at prepared
      obtain ⟨closures, _, prepared⟩ := bind_ok prepared
      obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
      obtain ⟨entries, _, prepared⟩ := bind_ok prepared
      cases prepared; exact ⟨rfl, rfl⟩

theorem automatic_fields {source : CheckedProgram} {plan : Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    (prepared : SourceCoreCompatibleFunctions.prepare source plan fuel = .ok automatic) :
    automatic.prepared.sourceProgram = source ∧ automatic.prepared.validationPlan = plan := by
  unfold SourceCoreCompatibleFunctions.prepare at prepared
  obtain ⟨executable, _, prepared⟩ := bind_ok prepared
  obtain ⟨locals, _, prepared⟩ := bind_ok prepared
  dsimp only at prepared
  split at prepared
  · cases prepared
  · obtain ⟨base, accepted, prepared⟩ := bind_ok prepared
    cases prepared
    exact compatible_fields accepted

theorem indexed_base {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    (prepared : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok program) :
    program.base = base := by
  unfold SourceCoreCallableIndexedPrograms.prepare at prepared
  dsimp only at prepared
  split at prepared
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at prepared
  · simp only [pure, Except.pure, bind, Except.bind] at prepared
    split at prepared
    · simp [throw, throwThe, MonadExceptOf.throw] at prepared
    · split at prepared
      · simp [throw, throwThe, MonadExceptOf.throw] at prepared
      · obtain ⟨firstPass, _, prepared⟩ := bind_ok prepared
        split at prepared
        · simp [throw, throwThe, MonadExceptOf.throw] at prepared
        · split at prepared
          · simp [throw, throwThe, MonadExceptOf.throw] at prepared
          · obtain ⟨secondPass, _, prepared⟩ := bind_ok prepared
            obtain ⟨sourceInputs, _, prepared⟩ := bind_ok prepared
            obtain ⟨entries, _, prepared⟩ := bind_ok prepared
            cases prepared
            rfl

theorem compiled_fields (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.base.sourceProgram = compiled.sourceProgram ∧
      compiled.indexed.base.validationPlan = compiled.validationPlan := by
  rw [indexed_base compiled.indexedPrepared]
  exact automatic_fields compiled.compatiblePrepared

theorem compiled_planPrepared (compiled : SourceCoreUnifiedCompilation.Compiled) :
    SourceCompilationPlan.prepareExecutablePlanEvidence compiled.sourceProgram compiled.validationPlan =
      .ok compiled.indexed.base.plan := by
  have prepared := compiled.indexed.base.planPrepared
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rwa [sourceExact, planExact] at prepared

theorem compiled_validation (compiled : SourceCoreUnifiedCompilation.Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.sourceProgram compiled.validationPlan = .ok () := by
  unfold SourceCompilationPlan.validateExecutablePlanEvidence
  rw [compiled_planPrepared compiled]
  rfl

theorem prepare_fields {source : CheckedProgram} {plan : Plan} {fuel : Nat}
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    (prepared : SourceCoreUnifiedCompilation.prepare source plan fuel = .ok compiled) :
    compiled.sourceProgram = source ∧ compiled.validationPlan = plan ∧ compiled.compilationFuel = fuel := by
  unfold SourceCoreUnifiedCompilation.prepare at prepared
  dsimp only at prepared
  split at prepared
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at prepared
  · simp only [pure, Except.pure, bind, Except.bind] at prepared
    split at prepared
    · simp [throw, throwThe, MonadExceptOf.throw] at prepared
    · split at prepared
      · simp [throw, throwThe, MonadExceptOf.throw] at prepared
      · cases prepared
        exact ⟨rfl, rfl, rfl⟩

/-- The cached Core adapter's actual successful request has the original
artifact's public source inputs and result, rather than inferred ownership
from an equal native projection. This is a boundary certificate. -/
theorem run_done_specialization {compiled : SourceCoreUnifiedCompilation.Compiled}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {validationFuel executionFuel : Nat} {initial : SourceTypedRuntime.RuntimeState}
    {result : SourceCoreUnifiedCompilation.Result compiled}
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (ran : compiled.run key arguments validationFuel executionFuel initial = .ok result)
    (done : result.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization compiled.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.sourceProgram compiled.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  obtain ⟨specialized, selected, certificate⟩ := SourceCoreUnifiedRuntime.run_done_specialization ran done
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rw [sourceExact, planExact] at certificate
  rw [planExact] at selected
  exact ⟨specialized, selected, certificate⟩

theorem run_resume_done_specialization {compiled : SourceCoreUnifiedCompilation.Compiled}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {validationFuel executionFuel resumedFuel : Nat} {initial : SourceTypedRuntime.RuntimeState}
    {result resumed : SourceCoreUnifiedCompilation.Result compiled}
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (ran : compiled.run key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumedFuel = .ok resumed)
    (done : resumed.observation = .done value final) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization compiled.validationPlan key = .ok specialized ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.sourceProgram compiled.validationPlan
        (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
        arguments initial value final := by
  obtain ⟨specialized, selected, certificate⟩ := SourceCoreUnifiedRuntime.Result.requested_done_specialization
    (SourceCoreUnifiedRuntime.Result.resume_requests (SourceCoreUnifiedRuntime.run_requests ran) continued) done
  obtain ⟨sourceExact, planExact⟩ := compiled_fields compiled
  rw [sourceExact, planExact] at certificate
  rw [planExact] at selected
  exact ⟨specialized, selected, certificate⟩

end Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
end
