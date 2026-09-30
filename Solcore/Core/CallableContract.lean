import Solcore.Core.TaggedFunction

/-! Callable contracts are ordinary product payloads and static word dispatch.
The contract word is distinct from source function identity. Two guards preserve
callee → stage decision → arguments → arity decision → application order.
No syntax, checker, store, or machine rule is added. -/

set_option autoImplicit false

namespace Solcore.Core.CallableContract

def functionType (parameter result : Ty) : Ty :=
  .product (TaggedFunction.functionType parameter result) .word

def wrap (contract : Word) (function : Expr) : Expr :=
  .pair function (.word contract)

inductive Phase where
  | beforeArguments
  | beforeApplication
  deriving Repr, BEq, DecidableEq

structure Gate where
  contract : Word
  beforeArguments : Option Word
  beforeApplication : Option Word
  deriving Repr, BEq, DecidableEq

def Gate.reason (gate : Gate) : Phase → Option Word
  | .beforeArguments => gate.beforeArguments
  | .beforeApplication => gate.beforeApplication

def decision (gates : List Gate) (phase : Phase) (unknown contract : Word) : Option Word :=
  match gates with
  | [] => some unknown
  | gate :: rest => if contract == gate.contract then gate.reason phase
      else decision rest phase unknown contract

def guardResult : Option Word → Expr
  | none => LanguageResult.success .unit
  | some reason => LanguageResult.failure .unit (.word reason)

def dispatch (gates : List Gate) (phase : Phase) (unknown : Word) (contract : Expr) : Expr :=
  match gates with
  | [] => guardResult (some unknown)
  | gate :: rest => .ifE (.binary .wordEq contract (.word gate.contract))
      (guardResult (gate.reason phase)) (dispatch rest phase unknown contract)

def call (gates : List Gate) (unknown : Word) (result : Ty) (callee arguments : Expr) : Expr :=
  LanguageResult.bind result callee
    (LanguageResult.bind result
      (dispatch gates .beforeArguments unknown (.second (.var 0)))
      (LanguageResult.bind result ((arguments.weakenAt 0).weakenAt 0)
        (LanguageResult.bind result
          (dispatch gates .beforeApplication unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1)))))

/-- Equality sees the existing identity tag inside the wrapper. Contract words
can differ without changing named identity; anonymous functions stay unequal. -/
def equalBody : Expr :=
  .letE (.first (.var 1)) (.letE (.first (.var 1)) TaggedFunction.equalBody)

def equal (left right : Expr) : Expr :=
  LocalPrimitiveResults.binaryWith .bool left right equalBody

theorem functionType_wellFormed {definitions : DataEnvironment} {parameter result : Ty}
    (parameterWF : Ty.WellFormed definitions parameter)
    (resultWF : Ty.WellFormed definitions result) :
    Ty.WellFormed definitions (functionType parameter result) :=
  .product (TaggedFunction.functionType_wellFormed parameterWF resultWF) .word

theorem wrap_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr} (contract : Word)
    (typed : HasType context function (TaggedFunction.functionType parameter result) definitions) :
    HasType context (wrap contract function) (functionType parameter result) definitions :=
  .pair typed .word

theorem guardResult_hasType {definitions : DataEnvironment} {context : Context}
    (reason : Option Word) :
    HasType context (guardResult reason) (LanguageResult.resultType .unit) definitions := by
  cases reason with
  | none => exact .inRight .word .unit
  | some reason => exact .inLeft .unit .word

theorem dispatch_hasType {definitions : DataEnvironment} {context : Context}
    (gates : List Gate) (phase : Phase) (unknown : Word) {contract : Expr}
    (typed : HasType context contract .word definitions) :
    HasType context (dispatch gates phase unknown contract)
      (LanguageResult.resultType .unit) definitions := by
  induction gates with
  | nil => exact guardResult_hasType _
  | cons gate rest ih => exact .ifE (.binary typed .word) (guardResult_hasType _) ih

theorem call_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {callee arguments : Expr} (gates : List Gate) (unknown : Word)
    (resultWF : Ty.WellFormed definitions result)
    (calleeTyped : HasType context callee (LanguageResult.resultType (functionType parameter result)) definitions)
    (argumentsTyped : HasType context arguments (LanguageResult.resultType parameter) definitions) :
    HasType context (call gates unknown result callee arguments)
      (LanguageResult.resultType result) definitions := by
  apply LanguageResult.bind_hasType resultWF calleeTyped
  apply LanguageResult.bind_hasType resultWF (dispatch_hasType _ _ _ (.second (.var rfl)))
  apply LanguageResult.bind_hasType resultWF
  · have once := argumentsTyped.weakenAt (inserted := functionType parameter result) 0
    have twice := once.weakenAt (inserted := Ty.unit) 0
    simpa [Context.insertAt] using twice
  apply LanguageResult.bind_hasType resultWF (dispatch_hasType _ _ _ (.second (.var rfl)))
  exact .apply (.second (.first (.var rfl))) (.var rfl)

theorem equalBody_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} :
    HasType (functionType rightParameter rightResult ::
      functionType leftParameter leftResult :: context) equalBody .bool definitions :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_hasType)

theorem equal_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} {left right : Expr}
    (leftTyped : HasType context left
      (LanguageResult.resultType (functionType leftParameter leftResult)) definitions)
    (rightTyped : HasType context right
      (LanguageResult.resultType (functionType rightParameter rightResult)) definitions) :
    HasType context (equal left right) (LanguageResult.resultType .bool) definitions :=
  LocalPrimitiveResults.binaryWith_hasType .bool leftTyped rightTyped equalBody_hasType

theorem equalBody_anonymous_left {environment : Environment} {store : Store}
    {left right rightIdentity : Value} {leftContract rightContract : Word} :
    Evaluates (.pair (.pair rightIdentity right) (.word rightContract) ::
      .pair (.pair (.inLeft .word .unit) left) (.word leftContract) :: environment)
      store equalBody (.bool false) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_anonymous_left)

theorem equalBody_anonymous_right {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity leftContract rightContract : Word} :
    Evaluates (.pair (.pair (.inLeft .word .unit) right) (.word rightContract) ::
      .pair (.pair (.inRight .unit (.word leftIdentity)) left) (.word leftContract) :: environment)
      store equalBody (.bool false) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_anonymous_right)

theorem equalBody_identified {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity rightIdentity leftContract rightContract : Word} :
    Evaluates (.pair (.pair (.inRight .unit (.word rightIdentity)) right) (.word rightContract) ::
      .pair (.pair (.inRight .unit (.word leftIdentity)) left) (.word leftContract) :: environment)
      store equalBody (.bool (leftIdentity == rightIdentity)) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_identified)

def resultValue : Option Word → Value
  | none => .inRight .word .unit
  | some reason => .inLeft .unit (.word reason)

theorem guardResult_evaluates {environment : Environment} {store : Store}
    (reason : Option Word) :
    Evaluates environment store (guardResult reason) (resultValue reason) store := by
  cases reason with
  | none => exact .inRight .unit
  | some reason => exact .inLeft .word

/-- The emitted decision has no store effects. The contract projection is a
pure value read; it can be reused by each branch without evaluating the callee. -/
theorem dispatch_evaluates {environment : Environment} {store : Store}
    (gates : List Gate) (phase : Phase) (unknown contractValue : Word) {contract : Expr}
    (read : Evaluates environment store contract (.word contractValue) store) :
    Evaluates environment store (dispatch gates phase unknown contract)
      (resultValue (decision gates phase unknown contractValue)) store := by
  induction gates with
  | nil => exact guardResult_evaluates _
  | cons gate rest ih =>
      cases sameId : (contractValue == gate.contract) with
      | false =>
          simp only [dispatch, decision, sameId, Bool.false_eq_true, ↓reduceIte]
          apply Evaluates.ifFalse
          · exact .binary read .word (by simp [BinaryOp.apply, sameId])
          · exact ih
      | true =>
          simp only [dispatch, decision, sameId, ↓reduceIte]
          apply Evaluates.ifTrue
          · exact .binary read .word (by simp [BinaryOp.apply, sameId])
          · exact guardResult_evaluates _

theorem dispatch_iff {environment : Environment} {store after : Store}
    (gates : List Gate) (phase : Phase) (unknown contractValue : Word) {contract : Expr} {value : Value}
    (read : Evaluates environment store contract (.word contractValue) store) :
    Evaluates environment store (dispatch gates phase unknown contract) value after ↔
      value = resultValue (decision gates phase unknown contractValue) ∧ after = store := by
  constructor
  · intro evaluation
    exact evaluation_deterministic evaluation (dispatch_evaluates gates phase unknown contractValue read)
  · rintro ⟨rfl, rfl⟩
    exact dispatch_evaluates gates phase unknown contractValue read

theorem wrap_evaluates {environment : Environment} {before after : Store}
    {function : Expr} {value : Value} (contract : Word)
    (evaluation : Evaluates environment before function value after) :
    Evaluates environment before (wrap contract function) (.pair value (.word contract)) after :=
  .pair evaluation .word

theorem call_callee_failure {environment : Environment} {before after : Store}
    {input result : Ty} {callee arguments : Expr} {reason : Word}
    (gates : List Gate) (unknown : Word)
    (evaluation : Evaluates environment before callee (.inLeft input (.word reason)) after) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after :=
  LanguageResult.bind_failure result evaluation

theorem call_stage_failure {environment : Environment} {before after : Store}
    {result : Ty} {callee arguments : Expr} {function : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (evaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) after)
    (rejected : decision gates .beforeArguments unknown contract = some reason) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result evaluation
  apply LanguageResult.bind_failure result
  have gate := dispatch_evaluates gates .beforeArguments unknown contract
    (Evaluates.second (Evaluates.var rfl) : Evaluates
      (.pair function (.word contract) :: environment) after (.second (.var 0)) (.word contract) after)
  simpa [rejected, resultValue] using gate

theorem call_argument_failure {environment : Environment} {before middle after : Store}
    {parameter result : Ty} {callee arguments : Expr} {function : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) middle)
    (accepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit :: .pair function (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inLeft parameter (.word reason)) after) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair function (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [accepted, resultValue] using gate
  exact LanguageResult.bind_failure result argumentsEvaluation

theorem call_arity_failure {environment : Environment} {before middle after : Store}
    {result : Ty} {callee arguments : Expr} {function argument : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) middle)
    (accepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit :: .pair function (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) after)
    (rejected : decision gates .beforeApplication unknown contract = some reason) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair function (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [accepted, resultValue] using gate
  apply LanguageResult.bind_success result argumentsEvaluation
  apply LanguageResult.bind_failure result
  have gate := dispatch_evaluates gates .beforeApplication unknown contract
    (Evaluates.second (Evaluates.var rfl) : Evaluates
      (argument :: .unit :: .pair function (.word contract) :: environment) after
      (.second (.var 2)) (.word contract) after)
  simpa [rejected, resultValue] using gate

theorem call_success {environment captured : Environment} {before middle applied after : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument value : Value} {contract : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract))) middle)
    (stageAccepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit ::
      .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) applied)
    (arityAccepted : decision gates .beforeApplication unknown contract = none)
    (bodyEvaluation : Evaluates (argument :: captured) applied body value after) :
    Evaluates environment before (call gates unknown result callee arguments) value after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
          (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [stageAccepted, resultValue] using gate
  apply LanguageResult.bind_success result argumentsEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeApplication unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (argument :: .unit ::
          .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
            (.word contract) :: environment) applied (.second (.var 2)) (.word contract) applied)
    simpa [arityAccepted, resultValue] using gate
  exact .apply (.second (.first (.var rfl))) (.var rfl) bodyEvaluation

end Solcore.Core.CallableContract
