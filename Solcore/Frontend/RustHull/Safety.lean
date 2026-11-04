import Solcore.Frontend.RustHull.Effects
import Solcore.Frontend.RustHull.Lowering
import Solcore.Core.BoundedSafety
import Solcore.Frontend.RustHull.LinkedContract
import Solcore.Frontend.RustHull.ScalarExecution

/-!
# Hull safety theorems

Successful preparation gives well-typed Core, and execution has no machine fault. Language failures,
reverts and exhausted fuel stay possible. Main theorems:
`ScalarExecution.prepare_resumes_never_faults`, `ScalarExecution.prepare_resumes_hasType`,
`ScalarExecution.prepare_resumes_checkpoint_hasType`, `Contract.prepare_resumes_safe`,
`LinkedContract.prepare_resumes_safe`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ContextTyping
/-! Typing of the host values used by the public account runtime initializer.
The data environment contains both byte/word mappings and account records.
These results accept arbitrary supplied values; normalization and catalog
selection do not require extra typing premises from the caller. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ContextTyping

theorem wordMappingLiteral_hasType (entries : Core.WordMapping.Entries) (context : Core.Context) :
    Core.HasType context (Core.WordMapping.literal entries) Core.WordMapping.type
      AccountState.definitions := by
  induction entries with
  | nil => exact .construct rfl .unit
  | cons entry rest ih => exact .construct rfl (.pair (.pair .word .word) ih)

theorem optionalWordLiteral_hasType (value : Option Core.Word) (context : Core.Context) :
    Core.HasType context
      (match value with
        | none => .inLeft .word .unit
        | some value => .inRight .unit (.word value))
      Ambient.optionalWord AccountState.definitions := by
  cases value with
  | none => exact .inLeft .word .unit
  | some value => exact .inRight .unit .word

theorem optionalMappingLiteral_hasType (value : Option Core.WordMapping.Entries)
    (context : Core.Context) :
    Core.HasType context
      (match value with
        | none => .inLeft Core.WordMapping.type .unit
        | some entries => .inRight .unit (Core.WordMapping.literal entries))
      Ambient.optionalHashes AccountState.definitions := by
  cases value with
  | none => exact .inLeft (.namedData rfl) .unit
  | some entries => exact .inRight .unit (wordMappingLiteral_hasType entries context)

theorem accountRecordLiteral_hasType (account : AccountState.Account) (identity : Nat)
    (context : Core.Context) :
    Core.HasType context (AccountState.recordLiteral account identity) AccountState.recordType
      AccountState.definitions := by
  simp only [AccountState.recordLiteral, AccountState.recordType, AccountState.fieldTypes,
    bundle, bundleType]
  repeat first
    | exact wordMappingLiteral_hasType _ _
    | exact Core.HasType.word
    | exact Core.HasType.bool
    | apply Core.HasType.pair

theorem accountStateLiteral_hasType (accounts : List (AccountState.Account × Nat))
    (context : Core.Context) :
    Core.HasType context (AccountState.literal accounts) AccountState.type
      AccountState.definitions := by
  induction accounts with
  | nil => exact .construct rfl .unit
  | cons entry rest ih =>
      exact .construct rfl (.pair (.pair .word (accountRecordLiteral_hasType entry.1 entry.2 context)) ih)

theorem ambientContextExpression_hasType (value : Ambient.Context) (context : Core.Context) :
    Core.HasType context (Ambient.contextExpression value) Ambient.contextType
      AccountState.definitions := by
  simp only [Ambient.contextExpression, Ambient.contextType, Ambient.slots,
    List.map, bundle, bundleType]
  repeat first
    | exact optionalWordLiteral_hasType _ _
    | exact optionalMappingLiteral_hasType _ _
    | apply Core.HasType.pair

end Solcore.Frontend.RustHull.ContextTyping
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LoweringSafety
/-! Safety at the checked Hull import boundary. Successful scalar compilation
produces a typed Core function. A typed Core input then has a typed finite
execution outcome, including checkpoints that can be resumed without a machine
fault. These theorems do not assert preservation of an independent Hull meaning.
-/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull

/-- Extract the successful intermediate value of an actual compiler step. -/
theorem lower_bind_eq_ok {α β : Type} {step : LowerM α} {next : α → LowerM β} {value : β} :
    step >>= next = .ok value ↔ ∃ intermediate, step = .ok intermediate ∧ next intermediate = .ok value := by
  cases step <;> simp [Bind.bind, Except.bind]

theorem expectType_eq_of_ok {expected actual : Core.Ty}
    (accepted : expectType expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [expectType, same, fail] at accepted

theorem compile_hasType {program : Program} {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled) :
    Core.HasType [] compiled.expression
      (.function (bundleType compiled.parameters) (Core.LanguageResult.resultType compiled.result)) := by
  by_cases exported : entry ∈ program.entryPoints
  · simp only [compile, exported, ↓reduceIte] at accepted
    obtain ⟨⟨signature, body⟩, _, checked⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨type, inferred, checked⟩ := lower_bind_eq_ok.mp checked
    obtain ⟨value, guarded, returned⟩ := lower_bind_eq_ok.mp checked
    cases value
    have sameType := expectType_eq_of_ok guarded
    cases returned
    cases inferredResult : Core.inferDetailed [] []
        (.lambda (bundleType signature.parameters) (Core.LanguageResult.resultType signature.result) body) with
    | error error => simp [inferredResult, Except.mapError] at inferred
    | ok type =>
        simp only [inferredResult, Except.mapError, Except.ok.injEq] at inferred
        subst type
        apply Core.inferDetailed_iff_typing.mp
        simpa [Signature.functionType, ← sameType] using inferredResult
  · simp [compile, exported, fail, Bind.bind, Except.bind] at accepted

theorem compile_application_hasType {program : Program} {entry : String} {compilationFuel : Nat}
    {compiled : Compiled} {argument : Core.Expr}
    (accepted : compile program entry compilationFuel = .ok compiled)
    (argumentTyped : Core.HasType [] argument (bundleType compiled.parameters)) :
    Core.HasType [] (.apply compiled.expression argument) (Core.LanguageResult.resultType compiled.result) :=
  .apply (compile_hasType accepted) argumentTyped

/-- Completion retains a typed value and store; exhaustion retains a typed
checkpoint. An internal Core fault is excluded for every fuel allowance. -/
theorem compile_run_hasType {program : Program} {entry : String} {compilationFuel : Nat}
    {compiled : Compiled} {argument : Core.Expr}
    (accepted : compile program entry compilationFuel = .ok compiled)
    (argumentTyped : Core.HasType [] argument (bundleType compiled.parameters)) (fuel : Nat) :
    (Core.runStateful fuel (.initial (.apply compiled.expression argument))).HasType
      (Core.LanguageResult.resultType compiled.result) :=
  Core.well_typed_runStateful_has_type
    (Core.initial_state_has_type (compile_application_hasType accepted argumentTyped)) fuel

theorem compile_run_never_faults {program : Program} {entry : String} {compilationFuel fuel : Nat}
    {compiled : Compiled} {argument : Core.Expr} {error : Core.MachineFault} {faultState : Core.State}
    (accepted : compile program entry compilationFuel = .ok compiled)
    (argumentTyped : Core.HasType [] argument (bundleType compiled.parameters)) :
    Core.runStateful fuel (.initial (.apply compiled.expression argument)) ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (Core.initial_state_has_type (compile_application_hasType accepted argumentTyped))

/-- The checkpoint returned by execution is safe to resume. Resuming is the
same Core execution as supplying the combined fuel allowance initially. -/
theorem compile_resume_hasType {program : Program} {entry : String} {compilationFuel spent : Nat}
    {compiled : Compiled} {argument : Core.Expr} {checkpoint : Core.State}
    (accepted : compile program entry compilationFuel = .ok compiled)
    (argumentTyped : Core.HasType [] argument (bundleType compiled.parameters))
    (exhausted : Core.runStateful spent (.initial (.apply compiled.expression argument)) =
      .outOfFuel checkpoint) (additional : Nat) :
    (Core.runStateful additional checkpoint).HasType (Core.LanguageResult.resultType compiled.result) ∧
      Core.runStateful additional checkpoint =
        Core.runStateful (spent + additional) (.initial (.apply compiled.expression argument)) :=
  Core.well_typed_runStateful_resume_has_type
    (Core.initial_state_has_type (compile_application_hasType accepted argumentTyped)) exhausted additional

theorem compile_resume_never_faults {program : Program} {entry : String} {compilationFuel spent additional : Nat}
    {compiled : Compiled} {argument : Core.Expr} {checkpoint faultState : Core.State} {error : Core.MachineFault}
    (accepted : compile program entry compilationFuel = .ok compiled)
    (argumentTyped : Core.HasType [] argument (bundleType compiled.parameters))
    (exhausted : Core.runStateful spent (.initial (.apply compiled.expression argument)) =
      .outOfFuel checkpoint) :
    Core.runStateful additional checkpoint ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (Core.well_typed_runStateful_preserves_checkpoint_type
      (Core.initial_state_has_type (compile_application_hasType accepted argumentTyped)) exhausted)

end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractSafety
/-! Core safety at the public imported-Hull contract boundary.

These results concern the actual Core expression produced by successful
compilation and its public execution checkpoints. They do not establish that
the Rust compiler preserves source meaning, or that Core execution agrees with
EVM gas accounting. Reverts, language failures, export limits and fuel
exhaustion remain possible outcomes.
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

private theorem mapError_eq_ok {α ε δ : Type} {result : Except ε α} {f : ε → δ} {value : α}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result <;> simp_all [Except.mapError]

namespace AccountRuntime

/-- The final public compiler guard checks the complete generated account
runtime, including its recursive callback and shared cells. -/
theorem compileObject_hasType {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List CodeDefinition} {expression : Core.Expr}
    (accepted : compileObject program path fuel codeBytes catalog = .ok expression) :
    Core.HasType [] expression (.function contextType resultType) AccountState.definitions := by
  unfold compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨frame, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨type, inferred, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, guarded, returned⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  have sameType := expectType_eq_of_ok guarded
  cases returned
  apply (Core.inferDetailed_iff_typing (path := [])).mp
  simpa only [← sameType] using mapError_eq_ok inferred

end AccountRuntime

namespace Contract

theorem compileObject_hasType {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {compiled : CompiledObject}
    (accepted : compileObject program path fuel codeBytes catalog = .ok compiled) :
    Core.HasType [] compiled.expression (.function contextType resultType) AccountState.definitions := by
  unfold compileObject at accepted
  obtain ⟨expression, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact AccountRuntime.compileObject_hasType checked

/-- Instantiation constructs typed literals for all host inputs, including the
normalized account world, executable image identities, ambient inputs, packed
calldata and optional gas value. No host account-typing premise is required. -/
theorem CompiledObject.instantiate_hasType
    {compiled : CompiledObject}
    (typing : Core.HasType [] compiled.expression
      (.function contextType resultType) AccountState.definitions)
    (context : Context) :
    Core.HasType [] (compiled.instantiate context).expression resultType AccountState.definitions := by
  cases gas : context.availableGas <;>
    simp only [CompiledObject.instantiate, CompiledObject.contextArgument, normalizeContext, gas, bundle]
  all_goals
    apply Core.HasType.apply typing
    repeat first
      | exact ContextTyping.wordMappingLiteral_hasType _ _
      | exact ContextTyping.accountStateLiteral_hasType _ _
      | exact ContextTyping.ambientContextExpression_hasType _ _
      | constructor

/-- A public receipt carries a typed checkpoint when fuel is exhausted, and
can never contain an internal Core machine fault. Other outcomes are allowed. -/
def Receipt.Safe (receipt : Receipt) : Prop :=
  match receipt.outcome with
  | .outOfFuel checkpoint => Core.StateHasType checkpoint resultType AccountState.definitions
  | .coreFault _ => False
  | _ => True

private theorem completed_safe (value : Core.Value) (store : Core.Store) (maxReturnBytes : Nat) :
    (resumeWithReceipt (Core.State.final value store) 1 maxReturnBytes).Safe := by
  unfold Receipt.Safe resumeWithReceipt
  simp only [Core.runStateful, Core.advance, Core.State.final]
  conv => pattern (Receipt.outcome _); arg 1; whnf
  split <;> try exact True.intro
  all_goals
    rename_i result last equality
    split at equality <;> try cases equality
  all_goals
    dsimp only at equality
    split at equality <;> try cases equality
  all_goals
    try split at equality <;> try cases equality
  all_goals
    conv at equality => lhs; whnf
    dsimp only [Pure.pure, Bind.bind] at equality
  repeat (any_goals (first | cases equality | split at equality))

theorem Receipt.Safe.never_coreFault {receipt : Receipt} (safe : receipt.Safe)
    (error : Core.MachineFault) : receipt.outcome ≠ .coreFault error := by
  intro faulted
  simp only [Receipt.Safe, faulted] at safe

theorem Receipt.Safe.checkpoint_hasType {receipt : Receipt} {checkpoint : Core.State}
    (safe : receipt.Safe) (exhausted : receipt.outcome = .outOfFuel checkpoint) :
    Core.StateHasType checkpoint resultType AccountState.definitions := by
  simpa only [Receipt.Safe, exhausted] using safe

/-- The public result adapter preserves the Core checkpoint safety invariant. -/
theorem resumeWithReceipt_safe {state : Core.State}
    (typing : Core.StateHasType state resultType AccountState.definitions)
    (fuel maxReturnBytes : Nat) : (resumeWithReceipt state fuel maxReturnBytes).Safe := by
  cases executed : Core.runStateful fuel state with
  | done value store =>
      simpa only [resumeWithReceipt, executed, Core.runStateful, Core.advance, Core.State.final]
        using completed_safe value store maxReturnBytes
  | outOfFuel checkpoint =>
      simpa only [Receipt.Safe, resumeWithReceipt, executed] using
        Core.well_typed_runStateful_preserves_checkpoint_type typing executed
  | fault error faultState =>
      exact False.elim (Core.well_typed_runStateful_never_faults typing executed)

theorem runWithReceipt_safe {prepared : Prepared}
    (typing : Core.HasType [] prepared.expression resultType AccountState.definitions)
    (fuel maxReturnBytes : Nat) : (runWithReceipt prepared fuel maxReturnBytes).Safe :=
  resumeWithReceipt_safe (Core.initial_state_has_type typing) fuel maxReturnBytes

/-- Every edge records a genuine public out-of-fuel receipt. The relation
allows any finite number of resumes and any chosen fuel/export allowances. -/
inductive Resumes : Receipt → Receipt → Prop where
  | refl (receipt : Receipt) : Resumes receipt receipt
  | step {first previous : Receipt} {checkpoint : Core.State}
      (path : Resumes first previous)
      (exhausted : previous.outcome = .outOfFuel checkpoint)
      (fuel maxReturnBytes : Nat) :
      Resumes first (resumeWithReceipt checkpoint fuel maxReturnBytes)

theorem Resumes.safe {first last : Receipt} (path : Resumes first last)
    (initialSafe : first.Safe) : last.Safe := by
  induction path with
  | refl => exact initialSafe
  | step _ exhausted fuel maxReturnBytes ih =>
      exact resumeWithReceipt_safe (ih.checkpoint_hasType exhausted) fuel maxReturnBytes

theorem compile_instantiate_hasType {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes catalog = .ok compiled)
    (context : Context) :
    Core.HasType [] (compiled.instantiate context).expression resultType AccountState.definitions :=
  compiled.instantiate_hasType (compileObject_hasType accepted) context

theorem prepare_hasType {program : Program} {path : List String} {compilationFuel : Nat}
    {context : Context} {prepared : Prepared}
    (accepted : prepare program path context compilationFuel = .ok prepared) :
    Core.HasType [] prepared.expression resultType AccountState.definitions := by
  unfold prepare at accepted
  obtain ⟨compiled, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact compile_instantiate_hasType checked context

/-- Successful compilation supplies all typing premises for the actual public
initializer and runner; no independent host-argument typing assumption remains. -/
theorem compile_runWithReceipt_safe {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes catalog = .ok compiled)
    (context : Context) (fuel maxReturnBytes : Nat) :
    (runWithReceipt (compiled.instantiate context) fuel maxReturnBytes).Safe :=
  runWithReceipt_safe (compile_instantiate_hasType accepted context) fuel maxReturnBytes

theorem compile_runWithReceipt_never_coreFault
    {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes catalog = .ok compiled)
    (context : Context) (fuel maxReturnBytes : Nat) (error : Core.MachineFault) :
    (runWithReceipt (compiled.instantiate context) fuel maxReturnBytes).outcome ≠ .coreFault error :=
  (compile_runWithReceipt_safe accepted context fuel maxReturnBytes).never_coreFault error

theorem compile_resumes_never_coreFault {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes catalog = .ok compiled)
    (context : Context) (fuel maxReturnBytes : Nat) {last : Receipt}
    (resumed : Resumes (runWithReceipt (compiled.instantiate context) fuel maxReturnBytes) last)
    (error : Core.MachineFault) : last.outcome ≠ .coreFault error :=
  (resumed.safe (compile_runWithReceipt_safe accepted context fuel maxReturnBytes)).never_coreFault error

theorem prepare_resumes_safe {program : Program} {path : List String} {compilationFuel : Nat}
    {context : Context} {prepared : Prepared}
    (accepted : prepare program path context compilationFuel = .ok prepared)
    (fuel maxReturnBytes : Nat) {last : Receipt}
    (resumed : Resumes (runWithReceipt prepared fuel maxReturnBytes) last) : last.Safe :=
  resumed.safe (runWithReceipt_safe (prepare_hasType accepted) fuel maxReturnBytes)

end Contract

namespace LinkedContract

theorem compileObject_hasType {program : Program} {path : List String} {images : List CodeImage.Image}
    {constructorArguments : List UInt8} {fuel : Nat} {compiled : Contract.CompiledObject}
    (accepted : compileObject program path images constructorArguments fuel = .ok compiled) :
    Core.HasType [] compiled.expression
      (.function Contract.contextType Contract.resultType) AccountState.definitions := by
  unfold compileObject at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  exact Contract.compileObject_hasType accepted

theorem prepare_hasType {program : Program} {path : List String} {images : List CodeImage.Image}
    {constructorArguments : List UInt8} {context : Contract.Context} {fuel : Nat}
    {prepared : Contract.Prepared}
    (accepted : prepare program path images constructorArguments context fuel = .ok prepared) :
    Core.HasType [] prepared.expression Contract.resultType AccountState.definitions := by
  unfold prepare at accepted
  obtain ⟨compiled, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact compiled.instantiate_hasType (compileObject_hasType checked) context

/-- Automatic image catalog construction feeds the same checked initializer,
including arbitrary supplied account worlds and later public checkpoints. -/
theorem compile_resumes_safe {program : Program} {path : List String}
    {images : List CodeImage.Image} {constructorArguments : List UInt8}
    {compilationFuel : Nat} {compiled : Contract.CompiledObject}
    (accepted : compileObject program path images constructorArguments compilationFuel = .ok compiled)
    (context : Contract.Context) (fuel maxReturnBytes : Nat) {last : Contract.Receipt}
    (resumed : Contract.Resumes
      (Contract.runWithReceipt (compiled.instantiate context) fuel maxReturnBytes) last) : last.Safe :=
  resumed.safe (Contract.runWithReceipt_safe
    (compiled.instantiate_hasType (compileObject_hasType accepted) context) fuel maxReturnBytes)

/-- The public deployment guard includes appended constructor arguments. -/
theorem prepareDeployment_initCodeSize {program : Program} {path : List String}
    {images : List CodeImage.Image} {constructorArguments : List UInt8}
    {context : Contract.Context} {fuel : Nat} {prepared : Contract.Prepared}
    (accepted : prepareDeployment program path images constructorArguments context fuel = .ok prepared) :
    ∃ image, CodeImage.select images path = .ok image ∧
      image.bytes.length + constructorArguments.length ≤ 49152 := by
  unfold prepareDeployment at accepted
  obtain ⟨image, selected, accepted⟩ := lower_bind_eq_ok.mp accepted
  split at accepted
  · cases accepted
  · rename_i allowed
    exact ⟨image, mapError_eq_ok selected, Nat.le_of_not_gt allowed⟩

theorem prepareDeployment_hasType {program : Program} {path : List String} {images : List CodeImage.Image}
    {constructorArguments : List UInt8} {context : Contract.Context} {fuel : Nat}
    {prepared : Contract.Prepared}
    (accepted : prepareDeployment program path images constructorArguments context fuel = .ok prepared) :
    Core.HasType [] prepared.expression Contract.resultType AccountState.definitions := by
  unfold prepareDeployment at accepted
  obtain ⟨image, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  split at accepted
  · cases accepted
  · exact prepare_hasType accepted

/-- Exact linked images and constructor arguments use the same checked Core
runtime. This theorem does not validate Rust or the backend image producer. -/
theorem prepareDeployment_resumes_safe {program : Program} {path : List String}
    {images : List CodeImage.Image} {constructorArguments : List UInt8}
    {context : Contract.Context} {compilationFuel : Nat} {prepared : Contract.Prepared}
    (accepted : prepareDeployment program path images constructorArguments context compilationFuel = .ok prepared)
    (fuel maxReturnBytes : Nat) {last : Contract.Receipt}
    (resumed : Contract.Resumes (Contract.runWithReceipt prepared fuel maxReturnBytes) last) : last.Safe :=
  resumed.safe (Contract.runWithReceipt_safe (prepareDeployment_hasType accepted) fuel maxReturnBytes)

theorem prepare_resumes_safe {program : Program} {path : List String}
    {images : List CodeImage.Image} {constructorArguments : List UInt8}
    {context : Contract.Context} {compilationFuel : Nat} {prepared : Contract.Prepared}
    (accepted : prepare program path images constructorArguments context compilationFuel = .ok prepared)
    (fuel maxReturnBytes : Nat) {last : Contract.Receipt}
    (resumed : Contract.Resumes (Contract.runWithReceipt prepared fuel maxReturnBytes) last) : last.Safe :=
  resumed.safe (Contract.runWithReceipt_safe (prepare_hasType accepted) fuel maxReturnBytes)

end LinkedContract
end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EffectsProperties
/-! The pinned Sonatina backend lowers `datacopy` and `codecopy` to the same
instruction. Their Core lowering also agrees, including missing-image errors. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Effects

theorem lowerBuiltin_datacopy_eq_codecopy (scope : Scope)
    (destination source length : Core.Expr) :
    lowerBuiltin scope "datacopy" [destination, source, length] =
      lowerBuiltin scope "codecopy" [destination, source, length] := rfl

end Solcore.Frontend.RustHull.Effects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ScalarExecutionSafety
/-! Safety from actual scalar input preparation. The public preparation result
supplies both the compiler evidence and the typed argument; callers need no
separate argument, environment or heap typing assumption. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ScalarExecution

theorem parseInput_hasType {type : Core.Ty} {input : String} {expression : Core.Expr}
    (parsed : parseInput type input = .ok expression) : Core.HasType [] expression type := by
  cases type <;> try simp [parseInput, fail] at parsed
  case word =>
    obtain ⟨value, _, returned⟩ := lower_bind_eq_ok.mp parsed
    cases returned
    exact .word
  case unit =>
    split at parsed
    · cases parsed; exact .unit
    · contradiction
  case bool =>
    split at parsed
    · cases parsed; exact .bool
    · split at parsed
      · cases parsed; exact .bool
      · contradiction
  case sum left right =>
    cases left <;> cases right <;> simp only at parsed <;> try contradiction
    split at parsed
    · cases parsed; exact .inRight .unit .unit
    · split at parsed
      · cases parsed; exact .inLeft .unit .unit
      · contradiction

theorem parseArguments_hasType {parameters : List Core.Ty} {inputs : List String} {argument : Core.Expr}
    (parsed : parseArguments parameters inputs = .ok argument) :
    Core.HasType [] argument (bundleType parameters) := by
  induction parameters generalizing inputs argument with
  | nil =>
      cases inputs with
      | nil =>
          simp [parseArguments] at parsed
          cases parsed
          exact .unit
      | cons input inputs => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
  | cons type types ih =>
      cases inputs with
      | nil => simp [parseArguments, fail, Bind.bind, Except.bind] at parsed
      | cons input inputs =>
          by_cases length : inputs.length = types.length
          · cases types with
            | nil =>
                have empty : inputs = [] := List.eq_nil_of_length_eq_zero length
                subst inputs
                simp only [parseArguments, List.length_cons, List.length_nil, ↓reduceIte] at parsed
                exact parseInput_hasType parsed
            | cons next rest =>
                have lengths : (input :: inputs).length = (type :: next :: rest).length :=
                  congrArg Nat.succ length
                simp only [parseArguments, lengths, ↓reduceIte] at parsed
                obtain ⟨head, headParsed, tail⟩ := lower_bind_eq_ok.mp parsed
                obtain ⟨tail, tailParsed, returned⟩ := lower_bind_eq_ok.mp tail
                cases returned
                exact .pair (parseInput_hasType headParsed) (ih tailParsed)
          · rw [parseArguments.eq_def] at parsed
            simp [length, fail, Bind.bind, Except.bind] at parsed

theorem prepare_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    Core.HasType [] prepared.expression prepared.resultType := by
  cases compiled : compile program entry compilationFuel with
  | error error => simp [prepare, compiled, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok function =>
      cases parsed : parseArguments function.parameters inputs with
      | error error => simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok argument =>
          simp [prepare, compiled, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
          cases accepted
          exact compile_application_hasType compiled (parseArguments_hasType parsed)

/-- Actual preparation initializes a closed expression, empty environment and
empty heap with the invariant required by every Core transition. -/
theorem prepare_initial_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    Core.StateHasType (.initial prepared.expression) prepared.resultType :=
  Core.initial_state_has_type (prepare_hasType accepted)

theorem prepare_run_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) (fuel : Nat) :
    (run prepared fuel).HasType prepared.resultType :=
  Core.well_typed_runStateful_has_type (prepare_initial_hasType accepted) fuel

theorem prepare_run_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel fuel : Nat} {prepared : Prepared} {error : Core.MachineFault} {faultState : Core.State}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared) :
    run prepared fuel ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults (prepare_initial_hasType accepted)

theorem prepare_resume_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel spent : Nat} {prepared : Prepared} {checkpoint : Core.State}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (exhausted : run prepared spent = .outOfFuel checkpoint) (additional : Nat) :
    (resume checkpoint additional).HasType prepared.resultType ∧
      resume checkpoint additional = run prepared (spent + additional) :=
  Core.well_typed_runStateful_resume_has_type (prepare_initial_hasType accepted) exhausted additional

theorem prepare_resume_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel spent additional : Nat} {prepared : Prepared}
    {checkpoint faultState : Core.State} {error : Core.MachineFault}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (exhausted : run prepared spent = .outOfFuel checkpoint) :
    resume checkpoint additional ≠ .fault error faultState :=
  Core.well_typed_runStateful_never_faults
    (Core.well_typed_runStateful_preserves_checkpoint_type (prepare_initial_hasType accepted) exhausted)

/-- A finite sequence of actual public resumptions. The middle index counts
additional fuel supplied after the first result; zero-fuel resumes are allowed.
Each step retains the checkpoint returned by the previous execution. -/
inductive Resumes : Core.StatefulRunResult → Nat → Core.StatefulRunResult → Prop where
  | refl (result : Core.StatefulRunResult) : Resumes result 0 result
  | step {first previous : Core.StatefulRunResult} {spent : Nat} {checkpoint : Core.State}
      (path : Resumes first spent previous)
      (exhausted : previous = .outOfFuel checkpoint)
      (additional : Nat) :
      Resumes first (spent + additional) (resume checkpoint additional)

/-- Repeated public resumes have exactly the same result, final store and
checkpoint as one public run with the combined fuel allowance. -/
theorem Resumes.eq_combined_run {first last : Core.StatefulRunResult} {additional : Nat}
    (path : Resumes first additional last) (prepared : Prepared) (fuel : Nat)
    (initial : first = run prepared fuel) : last = run prepared (fuel + additional) := by
  induction path with
  | refl => simpa only [Nat.add_zero] using initial
  | @step previous spent checkpoint path exhausted more ih =>
      have stopped : run prepared (fuel + spent) = .outOfFuel checkpoint := ih.symm.trans exhausted
      simpa only [resume, run, Nat.add_assoc] using Core.runStateful_resume stopped more

theorem Resumes.hasType {first last : Core.StatefulRunResult} {additional : Nat}
    {type : Core.Ty} {definitions : Core.DataEnvironment}
    (path : Resumes first additional last) (initial : first.HasType type definitions) :
    last.HasType type definitions := by
  induction path with
  | refl => exact initial
  | step _ exhausted more ih =>
      have checkpointTyped := ih
      rw [exhausted] at checkpointTyped
      exact Core.well_typed_runStateful_has_type checkpointTyped more

/-- Actual scalar preparation proves safety for every finite sequence of
public checkpoints, together with exact combined-fuel execution equality. -/
theorem prepare_resumes_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult}
    (resumed : Resumes (run prepared fuel) additional last) :
    last.HasType prepared.resultType ∧ last = run prepared (fuel + additional) :=
  ⟨resumed.hasType (prepare_run_hasType accepted fuel), resumed.eq_combined_run prepared fuel rfl⟩

theorem prepare_resumes_never_faults {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult}
    (resumed : Resumes (run prepared fuel) additional last)
    (error : Core.MachineFault) (faultState : Core.State) : last ≠ .fault error faultState := by
  have typed := (prepare_resumes_hasType accepted fuel resumed).1
  intro faulted
  simp only [faulted, Core.StatefulRunResult.HasType] at typed

theorem prepare_resumes_checkpoint_hasType {program : Program} {entry : String} {inputs : List String}
    {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (fuel : Nat) {additional : Nat} {last : Core.StatefulRunResult} {checkpoint : Core.State}
    (resumed : Resumes (run prepared fuel) additional last)
    (exhausted : last = .outOfFuel checkpoint) : Core.StateHasType checkpoint prepared.resultType := by
  have typed := (prepare_resumes_hasType accepted fuel resumed).1
  simpa only [exhausted, Core.StatefulRunResult.HasType] using typed

end Solcore.Frontend.RustHull.ScalarExecution
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Safety
/-! Typing and resumable execution safety for the checked Rust Hull boundary. -/
end
