import Solcore.Core.BoundedSafety

/-! Language results represented by ordinary Core sums. Failure is a returned
word reason; the machine continues to distinguish completion, suspension, and
internal faults. These helpers introduce no syntax or evaluation rules. -/

set_option autoImplicit false

namespace Solcore.Core.LanguageResult

def resultType (type : Ty) : Ty := .sum .word type

def success (value : Expr) : Expr := .inRight .word value

def failure (type : Ty) (reason : Expr) : Expr := .inLeft type reason

/-- `body` is already under the success payload binder and returns a language
result. Failure preserves the reason and skips this body. -/
def bind (type : Ty) (computation body : Expr) : Expr :=
  .caseE computation (.inLeft type (.var 0)) body

theorem resultType_wellFormed
    {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) :
    Ty.WellFormed definitions (resultType type) :=
  .sum .word wellFormed

theorem success_hasType
    {definitions : DataEnvironment} {context : Context} {value : Expr} {type : Ty}
    (typed : HasType context value type definitions) :
    HasType context (success value) (resultType type) definitions :=
  .inRight .word typed

theorem failure_hasType
    {definitions : DataEnvironment} {context : Context} {reason : Expr} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context reason .word definitions) :
    HasType context (failure type reason) (resultType type) definitions :=
  .inLeft wellFormed typed

theorem bind_hasType
    {definitions : DataEnvironment} {context : Context}
    {computation body : Expr} {inputType outputType : Ty}
    (wellFormed : Ty.WellFormed definitions outputType)
    (computationTyped : HasType context computation (resultType inputType) definitions)
    (bodyTyped : HasType (inputType :: context) body (resultType outputType) definitions) :
    HasType context (bind outputType computation body) (resultType outputType) definitions :=
  .caseE computationTyped (.inLeft wellFormed (.var rfl)) bodyTyped

theorem success_evaluates
    {environment : Environment} {initialStore finalStore : Store}
    {expression : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expression value finalStore) :
    Evaluates environment initialStore (success expression)
      (.inRight .word value) finalStore :=
  .inRight evaluation

theorem failure_evaluates
    {environment : Environment} {initialStore finalStore : Store}
    {expression : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore expression (.word reason) finalStore) :
    Evaluates environment initialStore (failure type expression)
      (.inLeft type (.word reason)) finalStore :=
  .inLeft evaluation

/-- Only the computation is evaluated. Its resulting store, including any
effects performed before failure, is retained without evaluating `body`. -/
theorem bind_failure
    {environment : Environment} {initialStore finalStore : Store}
    {computation body : Expr} {inputType : Ty} {reason : Word}
    (outputType : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft inputType (.word reason)) finalStore) :
    Evaluates environment initialStore (bind outputType computation body)
      (.inLeft outputType (.word reason)) finalStore :=
  .caseLeft evaluation (.inLeft (.var rfl))

/-- The body receives the successful value and the computation's final store. -/
theorem bind_success
    {environment : Environment} {initialStore bodyStore finalStore : Store}
    {computation body : Expr} {payload result : Value} (outputType : Ty)
    (computationEvaluation : Evaluates environment initialStore computation
      (.inRight .word payload) bodyStore)
    (bodyEvaluation : Evaluates (payload :: environment) bodyStore body result finalStore) :
    Evaluates environment initialStore (bind outputType computation body) result finalStore :=
  .caseRight computationEvaluation bodyEvaluation

/-- A known failure determines both the result and the final store, independently
of the body. No termination or typing premise on the body is needed. -/
theorem bind_failure_iff
    {environment : Environment} {initialStore failureStore finalStore : Store}
    {computation body : Expr} {inputType outputType : Ty} {reason : Word} {result : Value}
    (evaluation : Evaluates environment initialStore computation
      (.inLeft inputType (.word reason)) failureStore) :
    Evaluates environment initialStore (bind outputType computation body) result finalStore ↔
      result = .inLeft outputType (.word reason) ∧ finalStore = failureStore := by
  constructor
  · intro bound
    exact evaluation_deterministic bound (bind_failure outputType evaluation)
  · rintro ⟨rfl, rfl⟩
    exact bind_failure outputType evaluation

theorem bind_success_iff
    {environment : Environment} {initialStore bodyStore finalStore : Store}
    {computation body : Expr} {outputType : Ty} {payload result : Value}
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word payload) bodyStore) :
    Evaluates environment initialStore (bind outputType computation body) result finalStore ↔
      Evaluates (payload :: environment) bodyStore body result finalStore := by
  constructor
  · intro bound
    cases bound with
    | caseLeft other _ =>
        have impossible := (evaluation_deterministic evaluation other).1
        cases impossible
    | caseRight other bodyEvaluation =>
        obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic evaluation other
        cases sameValue
        cases sameStore
        exact bodyEvaluation
  · exact bind_success outputType evaluation

inductive Outcome where
  | succeeded (value : Value)
  | failed (reason : Word)
  deriving Repr, BEq, DecidableEq

/-- Decode the carrier shape. Correct success-payload and result annotations
are guaranteed by the typed interfaces below, not checked by this function. -/
def decode? : Value → Option Outcome
  | .inRight .word value => some (.succeeded value)
  | .inLeft _ (.word reason) => some (.failed reason)
  | _ => none

def Outcome.HasType (outcome : Outcome) (type : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match outcome with
  | .succeeded value => ValueHasType value type definitions
  | .failed _ => True

def Outcome.RuntimeHasType (world : StoreTyping) (outcome : Outcome) (type : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match outcome with
  | .succeeded value => RuntimeValueHasType world value type definitions
  | .failed _ => True

@[simp] theorem decode?_success (value : Value) :
    decode? (.inRight .word value) = some (.succeeded value) := rfl

@[simp] theorem decode?_failure (type : Ty) (reason : Word) :
    decode? (.inLeft type (.word reason)) = some (.failed reason) := rfl

theorem decode?_typed
    {definitions : DataEnvironment} {value : Value} {type : Ty}
    (typed : ValueHasType value (resultType type) definitions) :
    ∃ outcome, decode? value = some outcome ∧ outcome.HasType type definitions := by
  cases typed with
  | inLeft payloadTyped =>
      cases payloadTyped with
      | word => exact ⟨.failed _, rfl, True.intro⟩
  | inRight payloadTyped => exact ⟨.succeeded _, rfl, payloadTyped⟩

theorem decode?_runtime_typed
    {definitions : DataEnvironment} {world : StoreTyping} {value : Value} {type : Ty}
    (typed : RuntimeValueHasType world value (resultType type) definitions) :
    ∃ outcome, decode? value = some outcome ∧ outcome.RuntimeHasType world type definitions := by
  cases typed with
  | inLeft payloadTyped =>
      cases payloadTyped with
      | word => exact ⟨.failed _, rfl, True.intro⟩
  | inRight payloadTyped => exact ⟨.succeeded _, rfl, payloadTyped⟩

theorem decode?_isSome
    {definitions : DataEnvironment} {value : Value} {type : Ty}
    (typed : ValueHasType value (resultType type) definitions) :
    (decode? value).isSome := by
  obtain ⟨outcome, decoded, _⟩ := decode?_typed typed
  simp [decoded]

/-- A total decoder at a statically typed value boundary. The proof supplies
the carrier-shape guarantee and is erased during execution. -/
def decode {definitions : DataEnvironment} {type : Ty} (value : Value)
    (typed : ValueHasType value (resultType type) definitions) : Outcome :=
  (decode? value).get (decode?_isSome typed)

theorem decode_hasType
    {definitions : DataEnvironment} {value : Value} {type : Ty}
    (typed : ValueHasType value (resultType type) definitions) :
    (decode value typed).HasType type definitions := by
  obtain ⟨outcome, decoded, outcomeTyped⟩ := decode?_typed typed
  simpa [decode, decoded] using outcomeTyped

theorem decode_runtime_hasType
    {definitions : DataEnvironment} {world : StoreTyping} {value : Value} {type : Ty}
    (typed : RuntimeValueHasType world value (resultType type) definitions) :
    (decode value typed.erase).RuntimeHasType world type definitions := by
  obtain ⟨outcome, decoded, outcomeTyped⟩ := decode?_runtime_typed typed
  simpa [decode, decoded] using outcomeTyped

/-- Decoding a checked completion preserves the returned store's world and any
successful payload's references. Language failure is still a normal completion. -/
theorem checked_completion_decodes
    {program : Program} {type : Ty} {fuel : Nat} {value : Value} {store : Store}
    (checked : program.check = true)
    (resultTyped : program.resultType = resultType type)
    (completed : program.runStateful fuel = .done value store) :
    ∃ world outcome, RuntimeStoreHasTypes world store program.dataDefinitions ∧
      decode? value = some outcome ∧ outcome.RuntimeHasType world type program.dataDefinitions := by
  obtain ⟨world, storeTyped, valueTyped⟩ :=
    Program.checked_runStateful_preserves_result_type checked completed
  rw [resultTyped] at valueTyped
  obtain ⟨outcome, decoded, outcomeTyped⟩ := decode?_runtime_typed valueTyped
  exact ⟨world, outcome, storeTyped, decoded, outcomeTyped⟩

/-- Observe a finite run without conflating returned language failures,
retained exhaustion checkpoints, internal faults, or malformed carriers. -/
inductive Observation where
  | succeeded (value : Value) (store : Store)
  | failed (reason : Word) (store : Store)
  | outOfFuel (checkpoint : State)
  | internalFault (error : MachineFault) (state : State)
  | invalidCarrier (value : Value) (store : Store)
  deriving Repr, BEq, DecidableEq

def observeResult : StatefulRunResult → Observation
  | .done value store =>
      match decode? value with
      | some (.succeeded payload) => .succeeded payload store
      | some (.failed reason) => .failed reason store
      | none => .invalidCarrier value store
  | .outOfFuel checkpoint => .outOfFuel checkpoint
  | .fault error state => .internalFault error state

def run (program : Program) (fuel : Nat) : Observation :=
  observeResult (program.runStateful fuel)

def Observation.HasType (observation : Observation) (type : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match observation with
  | .succeeded value store =>
      ∃ world, RuntimeStoreHasTypes world store definitions ∧
        RuntimeValueHasType world value type definitions
  | .failed _ store => ∃ world, RuntimeStoreHasTypes world store definitions
  | .outOfFuel checkpoint => StateHasType checkpoint (resultType type) definitions
  | .internalFault _ _ | .invalidCarrier _ _ => False

theorem observeResult_hasType
    {definitions : DataEnvironment} {result : StatefulRunResult} {type : Ty}
    (typed : result.HasType (resultType type) definitions) :
    (observeResult result).HasType type definitions := by
  cases result with
  | done value store =>
      obtain ⟨world, storeTyped, valueTyped⟩ := typed
      obtain ⟨outcome, decoded, outcomeTyped⟩ := decode?_runtime_typed valueTyped
      cases outcome with
      | succeeded payload =>
          simp only [observeResult, decoded, Observation.HasType]
          exact ⟨world, storeTyped, outcomeTyped⟩
      | failed reason =>
          simp only [observeResult, decoded, Observation.HasType]
          exact ⟨world, storeTyped⟩
  | outOfFuel checkpoint => exact typed
  | fault error state => exact typed

theorem checked_run_hasType
    {program : Program} {type : Ty}
    (checked : program.check = true)
    (resultTyped : program.resultType = resultType type) (fuel : Nat) :
    (run program fuel).HasType type program.dataDefinitions := by
  have typed := Program.checked_runStateful_has_type checked fuel
  rw [resultTyped] at typed
  exact observeResult_hasType typed

theorem checked_run_ne_invalidCarrier
    {program : Program} {type : Ty} {fuel : Nat} {value : Value} {store : Store}
    (checked : program.check = true)
    (resultTyped : program.resultType = resultType type) :
    run program fuel ≠ .invalidCarrier value store := by
  intro invalid
  have typed := checked_run_hasType checked resultTyped fuel
  rw [invalid] at typed
  exact typed

theorem checked_run_ne_internalFault
    {program : Program} {type : Ty} {fuel : Nat} {error : MachineFault} {state : State}
    (checked : program.check = true)
    (resultTyped : program.resultType = resultType type) :
    run program fuel ≠ .internalFault error state := by
  intro fault
  have typed := checked_run_hasType checked resultTyped fuel
  rw [fault] at typed
  exact typed

end Solcore.Core.LanguageResult
