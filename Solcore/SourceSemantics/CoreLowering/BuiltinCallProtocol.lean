import Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
import Solcore.Core.CallableContract

/-! Finite builtin invocation beneath the real tagged/contracted call helpers.
The pure callee and builtin gates cannot fail. Whole completion exposes argument
completion first, so a caller can apply its independent child reflection theorem.
Argument effects occur once and are retained by the actual builtin body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Protocol
open Core Frontend SourceInference BuiltinBodyMeaning

def tagged (function : BuiltinFunctionId) (identity : Word) : Expr :=
  LanguageResult.success (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function))

def taggedValue (function : BuiltinFunctionId) (identity : Word) (captured : Environment) : Value :=
  .pair (.inRight .unit (.word identity))
    (.closure (SourceCoreInteger.builtinParameter function)
      (LanguageResult.resultType (SourceCoreInteger.builtinResult function))
      (LanguageResult.success (SourceCoreInteger.builtinBody function)) captured)

def contracted (function : BuiltinFunctionId) (identity contract : Word) : Expr :=
  LanguageResult.success (CallableContract.wrap contract
    (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)))

def contractedValue (function : BuiltinFunctionId) (identity contract : Word) (captured : Environment) : Value :=
  .pair (taggedValue function identity captured) (.word contract)

theorem tagged_evaluates (function : BuiltinFunctionId) (identity : Word)
    (environment : Environment) (store : Store) :
    Evaluates environment store (tagged function identity)
      (.inRight .word (taggedValue function identity environment)) store :=
  .inRight (.pair (.inRight .word) .lambda)

theorem contracted_evaluates (function : BuiltinFunctionId) (identity contract : Word)
    (environment : Environment) (store : Store) :
    Evaluates environment store (contracted function identity contract)
      (.inRight .word (contractedValue function identity contract environment)) store :=
  .inRight (.pair (.pair (.inRight .word) .lambda) .word)

theorem gates_accept (contract unknown : Word) (phase : CallableContract.Phase) :
    CallableContract.decision [⟨contract, none, none⟩] phase unknown contract = none := by
  cases phase <;> simp [CallableContract.decision, CallableContract.Gate.reason]

theorem tagged_argument_completes {function : BuiltinFunctionId} {identity : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value}
    (completed : Evaluates environment store
      (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
      result finalStore) :
    ∃ argumentValue argumentStore,
      Evaluates (taggedValue function identity environment :: environment) store
        (arguments.weakenAt 0) argumentValue argumentStore := by
  have tail := (LanguageResult.bind_success_iff (tagged_evaluates function identity environment store)).mp completed
  cases tail with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

theorem contracted_argument_completes {function : BuiltinFunctionId} {identity contract unknown : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value}
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ argumentValue argumentStore,
      Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
        ((arguments.weakenAt 0).weakenAt 0) argumentValue argumentStore := by
  have tail := (LanguageResult.bind_success_iff
    (contracted_evaluates function identity contract environment store)).mp completed
  have stage := CallableContract.dispatch_evaluates [⟨contract, none, none⟩] .beforeArguments unknown contract
    (show Evaluates (contractedValue function identity contract environment :: environment) store
      (.second (.var 0)) (.word contract) store from .second (.var rfl))
  rw [gates_accept] at stage
  have argumentsTail := (LanguageResult.bind_success_iff stage).mp tail
  cases argumentsTail with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

theorem tagged_preserves {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity : Word}
    {environment : Environment} {store argumentStore : Store} {arguments : Expr}
    (argumentsEvaluated : Evaluates (taggedValue function identity environment :: environment) store
      (arguments.weakenAt 0) (.inRight .word input) argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment store
        (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := inputs.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related,
    TaggedFunction.call_success (tagged_evaluates function identity environment store) argumentsEvaluated body⟩

theorem contracted_preserves {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity contract unknown : Word}
    {environment : Environment} {store argumentStore : Store} {arguments : Expr}
    (argumentsEvaluated : Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word input) argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment store
        (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
          (contracted function identity contract) arguments)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := inputs.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related,
    CallableContract.call_success [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract environment store)
      (gates_accept contract unknown .beforeArguments) argumentsEvaluated
      (gates_accept contract unknown .beforeApplication) body⟩

theorem tagged_reflects {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity : Word}
    {environment : Environment} {store argumentStore finalStore : Store} {arguments : Expr} {result : Value}
    (argumentsEvaluated : Evaluates (taggedValue function identity environment :: environment) store
      (arguments.weakenAt 0) (.inRight .word input) argumentStore)
    (completed : Evaluates environment store
      (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
      result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := tagged_preserves inputs argumentsEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩

theorem contracted_reflects {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity contract unknown : Word}
    {environment : Environment} {store argumentStore finalStore : Store} {arguments : Expr} {result : Value}
    (argumentsEvaluated : Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word input) argumentStore)
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := contracted_preserves inputs argumentsEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Protocol
