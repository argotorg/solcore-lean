import Solcore.Core.LocalPrimitiveResults

/-! Ordinary Core functions with a source identity marker. Anonymous closures
carry `left unit` and compare unequal, including against themselves. Named
functions carry `right word`; the compiler must assign distinct words to
distinct declaration/evidence or builtin identities. This module neither
assigns those identities nor adds a primitive for closure equality. -/

set_option autoImplicit false

namespace Solcore.Core.TaggedFunction

def identityType : Ty := .sum .unit .word

def functionType (parameter result : Ty) : Ty :=
  .product identityType (.function parameter (LanguageResult.resultType result))

def anonymous (function : Expr) : Expr :=
  .pair (.inLeft .word .unit) function

def identified (identity : Word) (function : Expr) : Expr :=
  .pair (.inRight .unit (.word identity)) function

/-- The indirect callee runs before its argument bundle. The closure receives
the bundle and the latest shared store; a failure skips the remaining work. -/
def call (result : Ty) (callee arguments : Expr) : Expr :=
  LanguageResult.bind result callee
    (LanguageResult.bind result (arguments.weakenAt 0)
      (.apply (.second (.var 1)) (.var 0)))

/-- A raw comparison under right function, left function, outer context. -/
def equalBody : Expr :=
  .caseE (.first (.var 1)) (.bool false)
    (.caseE (.first (.var 1)) (.bool false)
      (.binary .wordEq (.var 1) (.var 0)))

def equal (left right : Expr) : Expr :=
  LocalPrimitiveResults.binaryWith .bool left right equalBody

theorem identityType_wellFormed {definitions : DataEnvironment} :
    Ty.WellFormed definitions identityType := .sum .unit .word

theorem functionType_wellFormed {definitions : DataEnvironment} {parameter result : Ty}
    (parameterWF : Ty.WellFormed definitions parameter)
    (resultWF : Ty.WellFormed definitions result) :
    Ty.WellFormed definitions (functionType parameter result) :=
  .product identityType_wellFormed
    (.function parameterWF (LanguageResult.resultType_wellFormed resultWF))

theorem anonymous_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr}
    (typed : HasType context function (.function parameter (LanguageResult.resultType result)) definitions) :
    HasType context (anonymous function) (functionType parameter result) definitions :=
  .pair (.inLeft .word .unit) typed

theorem identified_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr} (identity : Word)
    (typed : HasType context function (.function parameter (LanguageResult.resultType result)) definitions) :
    HasType context (identified identity function) (functionType parameter result) definitions :=
  .pair (.inRight .unit .word) typed

theorem call_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {callee arguments : Expr}
    (resultWF : Ty.WellFormed definitions result)
    (calleeTyped : HasType context callee (LanguageResult.resultType (functionType parameter result)) definitions)
    (argumentsTyped : HasType context arguments (LanguageResult.resultType parameter) definitions) :
    HasType context (call result callee arguments) (LanguageResult.resultType result) definitions := by
  apply LanguageResult.bind_hasType resultWF calleeTyped
  apply LanguageResult.bind_hasType resultWF
  · simpa [Context.insertAt] using argumentsTyped.weakenAt
      (inserted := functionType parameter result) 0
  · exact .apply (.second (.var rfl)) (.var rfl)

theorem equalBody_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} :
    HasType (functionType rightParameter rightResult ::
      functionType leftParameter leftResult :: context) equalBody .bool definitions :=
  .caseE (.first (.var rfl)) .bool
    (.caseE (.first (.var rfl)) .bool (.binary (.var rfl) (.var rfl)))

theorem equal_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} {left right : Expr}
    (leftTyped : HasType context left
      (LanguageResult.resultType (functionType leftParameter leftResult)) definitions)
    (rightTyped : HasType context right
      (LanguageResult.resultType (functionType rightParameter rightResult)) definitions) :
    HasType context (equal left right) (LanguageResult.resultType .bool) definitions :=
  LocalPrimitiveResults.binaryWith_hasType .bool leftTyped rightTyped equalBody_hasType

theorem call_callee_failure {environment : Environment} {before after : Store}
    {input result : Ty} {callee arguments : Expr} {reason : Word}
    (evaluation : Evaluates environment before callee (.inLeft input (.word reason)) after) :
    Evaluates environment before (call result callee arguments)
      (.inLeft result (.word reason)) after :=
  LanguageResult.bind_failure result evaluation

theorem call_argument_failure {environment : Environment} {before middle after : Store}
    {parameter result : Ty} {callee arguments : Expr} {function : Value} {reason : Word}
    (calleeEvaluation : Evaluates environment before callee (.inRight .word function) middle)
    (argumentsEvaluation : Evaluates (function :: environment) middle (arguments.weakenAt 0)
      (.inLeft parameter (.word reason)) after) :
    Evaluates environment before (call result callee arguments) (.inLeft result (.word reason)) after :=
  LanguageResult.bind_success result calleeEvaluation
    (LanguageResult.bind_failure result argumentsEvaluation)

theorem call_success {environment captured : Environment} {before middle applied after : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument value : Value}
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))) middle)
    (argumentsEvaluation : Evaluates
      (.pair identity (.closure parameter (LanguageResult.resultType result) body captured) :: environment)
      middle (arguments.weakenAt 0) (.inRight .word argument) applied)
    (bodyEvaluation : Evaluates (argument :: captured) applied body value after) :
    Evaluates environment before (call result callee arguments) value after :=
  LanguageResult.bind_success result calleeEvaluation
    (LanguageResult.bind_success result argumentsEvaluation
      (.apply (.second (.var rfl)) (.var rfl) bodyEvaluation))

/-- Identity comparison examines tags, never closure bodies or captures. -/
theorem equalBody_anonymous_left {environment : Environment} {store : Store}
    {left right : Value} {rightIdentity : Value} :
    Evaluates (.pair rightIdentity right :: .pair (.inLeft .word .unit) left :: environment)
      store equalBody (.bool false) store :=
  .caseLeft (.first (.var rfl)) .bool

theorem equalBody_anonymous_right {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity : Word} :
    Evaluates (.pair (.inLeft .word .unit) right :: .pair (.inRight .unit (.word leftIdentity)) left :: environment)
      store equalBody (.bool false) store :=
  .caseRight (.first (.var rfl)) (.caseLeft (.first (.var rfl)) .bool)

theorem equalBody_identified {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity rightIdentity : Word} :
    Evaluates (.pair (.inRight .unit (.word rightIdentity)) right ::
      .pair (.inRight .unit (.word leftIdentity)) left :: environment)
      store equalBody (.bool (leftIdentity == rightIdentity)) store :=
  .caseRight (.first (.var rfl))
    (.caseRight (.first (.var rfl)) (.binary (.var rfl) (.var rfl) rfl))

end Solcore.Core.TaggedFunction
