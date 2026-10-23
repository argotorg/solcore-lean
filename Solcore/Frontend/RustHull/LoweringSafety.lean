import Solcore.Frontend.RustHull.Lowering
import Solcore.Core.BoundedSafety

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
