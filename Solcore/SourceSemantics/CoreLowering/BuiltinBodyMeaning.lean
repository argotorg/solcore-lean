import Solcore.Frontend.SourceCoreInteger
import Solcore.SourceSemantics.CoreLowering.IntegerPrimitives

/-! Finite meaning of every actual compiler-provided builtin body. The argument
relation describes scalar source values and their real packed native input.
This is the body boundary: argument effects and callable decoration are handled
by expression and indexed-call adapters. Captures and stores are arbitrary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
open Core Frontend SourceInference

inductive InputRep : BuiltinFunctionId → List Dynamic.Value → Value → Prop where
  | integerSub (left right : Int) : InputRep .integerSub [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | wordFromInteger (value : Int) : InputRep .wordFromInteger [.integer value] (.integer value)
  | integerAdd (left right : Int) : InputRep .integerAdd [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerEq (left right : Int) : InputRep .integerEq [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerLt (left right : Int) : InputRep .integerLt [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerMul (left right : Int) : InputRep .integerMul [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | wordToInteger (value : Word) : InputRep .wordToInteger [.word value] (.word value)

theorem InputRep.runtime_hasType {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    (world : StoreTyping) (definitions : DataEnvironment) :
    RuntimeValueHasType world input (SourceCoreInteger.builtinParameter function) definitions := by
  cases represented <;> first | exact .pair .integer .integer | exact .integer | exact .word

/-- Source builtin application determines a concrete evaluation of the actual
body; no compiler or primitive implementation is placed in the source relation. -/
theorem InputRep.body_meaning {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    (captured : Environment) (store : Store) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates (input :: captured) store (LanguageResult.success (SourceCoreInteger.builtinBody function))
        (.inRight .word nativeResult) store := by
  cases represented with
  | integerSub left right =>
    exact ⟨_, _, .integerSub left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | wordFromInteger value =>
    exact ⟨_, _, .wordFromInteger value, .word _, .inRight (.unary (.var rfl) rfl)⟩
  | integerAdd left right =>
    exact ⟨_, _, .integerAdd left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerEq left right =>
    exact ⟨_, _, .integerEq left right, .bool _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerLt left right =>
    exact ⟨_, _, .integerLt left right, .bool _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerMul left right =>
    exact ⟨_, _, .integerMul left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | wordToInteger value =>
    exact ⟨_, _, .wordToInteger value, .integer _, .inRight (.unary (.var rfl) rfl)⟩

/-- A completed actual builtin body reconstructs its independent source result
and leaves the entire native store unchanged. -/
theorem InputRep.body_reflects {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {captured : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates (input :: captured) store (LanguageResult.success (SourceCoreInteger.builtinBody function)) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = store := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := represented.body_meaning captured store
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩

/-- Invocation uses the exact compiler closure and an already selected packed
input. The selected argument may have produced the store seen by the body. -/
theorem InputRep.closure_preserves {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {environment : Environment} {before argumentStore : Store} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument input argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment before (.apply (SourceCoreInteger.builtinClosure function) argument)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := represented.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related, .apply .lambda argumentEvaluated body⟩

theorem InputRep.closure_reflects {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {environment : Environment} {before argumentStore finalStore : Store} {argument : Expr} {result : Value}
    (argumentEvaluated : Evaluates environment before argument input argumentStore)
    (completed : Evaluates environment before (.apply (SourceCoreInteger.builtinClosure function) argument) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := represented.closure_preserves argumentEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
