import Solcore.Frontend.RustHull.LinkedContract
import Solcore.Frontend.RustHull.LoweringSafety
import Solcore.Core.BoundedSafety

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
    {codeBytes : Option (List UInt8)} {expression : Core.Expr}
    (accepted : compileObject program path fuel codeBytes = .ok expression) :
    Core.HasType [] expression (.function contextType resultType) Memory.definitions := by
  unfold compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨frame, _, accepted⟩ := lower_bind_eq_ok.mp accepted
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
    {codeBytes : Option (List UInt8)} {compiled : CompiledObject}
    (accepted : compileObject program path fuel codeBytes = .ok compiled) :
    Core.HasType [] compiled.expression (.function contextType resultType) Memory.definitions := by
  unfold compileObject at accepted
  obtain ⟨expression, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact AccountRuntime.compileObject_hasType checked

/-- Instantiation constructs typed literals for all host inputs, including the
normalized address ledger, packed calldata and optional gas value. -/
theorem CompiledObject.instantiate_hasType
    {compiled : CompiledObject}
    (typing : Core.HasType [] compiled.expression
      (.function contextType resultType) Memory.definitions)
    (context : Context) :
    Core.HasType [] (compiled.instantiate context).expression resultType Memory.definitions := by
  cases gas : context.availableGas <;>
    simp only [CompiledObject.instantiate, gas, bundle]
  all_goals
    apply Core.HasType.apply typing
    repeat first
      | exact Core.WordMapping.literal_hasType _ _
      | constructor

/-- A public receipt carries a typed checkpoint when fuel is exhausted, and
can never contain an internal Core machine fault. Other outcomes are allowed. -/
def Receipt.Safe (receipt : Receipt) : Prop :=
  match receipt.outcome with
  | .outOfFuel checkpoint => Core.StateHasType checkpoint resultType Memory.definitions
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
    Core.StateHasType checkpoint resultType Memory.definitions := by
  simpa only [Receipt.Safe, exhausted] using safe

/-- The public result adapter preserves the Core checkpoint safety invariant. -/
theorem resumeWithReceipt_safe {state : Core.State}
    (typing : Core.StateHasType state resultType Memory.definitions)
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
    (typing : Core.HasType [] prepared.expression resultType Memory.definitions)
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
    {codeBytes : Option (List UInt8)} {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes = .ok compiled)
    (context : Context) :
    Core.HasType [] (compiled.instantiate context).expression resultType Memory.definitions :=
  compiled.instantiate_hasType (compileObject_hasType accepted) context

theorem prepare_hasType {program : Program} {path : List String} {compilationFuel : Nat}
    {context : Context} {prepared : Prepared}
    (accepted : prepare program path context compilationFuel = .ok prepared) :
    Core.HasType [] prepared.expression resultType Memory.definitions := by
  unfold prepare at accepted
  obtain ⟨compiled, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact compile_instantiate_hasType checked context

/-- Successful compilation supplies all typing premises for the actual public
initializer and runner; no independent host-argument typing assumption remains. -/
theorem compile_runWithReceipt_safe {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes = .ok compiled)
    (context : Context) (fuel maxReturnBytes : Nat) :
    (runWithReceipt (compiled.instantiate context) fuel maxReturnBytes).Safe :=
  runWithReceipt_safe (compile_instantiate_hasType accepted context) fuel maxReturnBytes

theorem compile_runWithReceipt_never_coreFault
    {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes = .ok compiled)
    (context : Context) (fuel maxReturnBytes : Nat) (error : Core.MachineFault) :
    (runWithReceipt (compiled.instantiate context) fuel maxReturnBytes).outcome ≠ .coreFault error :=
  (compile_runWithReceipt_safe accepted context fuel maxReturnBytes).never_coreFault error

theorem compile_resumes_never_coreFault {program : Program} {path : List String} {compilationFuel : Nat}
    {codeBytes : Option (List UInt8)} {compiled : CompiledObject}
    (accepted : compileObject program path compilationFuel codeBytes = .ok compiled)
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
      (.function Contract.contextType Contract.resultType) Memory.definitions := by
  unfold compileObject at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  exact Contract.compileObject_hasType accepted

theorem prepare_hasType {program : Program} {path : List String} {images : List CodeImage.Image}
    {constructorArguments : List UInt8} {context : Contract.Context} {fuel : Nat}
    {prepared : Contract.Prepared}
    (accepted : prepare program path images constructorArguments context fuel = .ok prepared) :
    Core.HasType [] prepared.expression Contract.resultType Memory.definitions := by
  unfold prepare at accepted
  obtain ⟨compiled, checked, returned⟩ := lower_bind_eq_ok.mp accepted
  cases returned
  exact compiled.instantiate_hasType (compileObject_hasType checked) context

theorem prepareDeployment_hasType {program : Program} {path : List String} {images : List CodeImage.Image}
    {constructorArguments : List UInt8} {context : Contract.Context} {fuel : Nat}
    {prepared : Contract.Prepared}
    (accepted : prepareDeployment program path images constructorArguments context fuel = .ok prepared) :
    Core.HasType [] prepared.expression Contract.resultType Memory.definitions :=
  prepare_hasType accepted

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
