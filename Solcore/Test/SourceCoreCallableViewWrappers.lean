import Solcore.SourceSemantics.CoreLowering.CallableViewWrappers

/-! Exact view manifests preserve native identity/contract words and execute
the original closure against the live shared store. Parser tests intentionally
separate structural recognition from external source/view ownership. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableViewWrappers
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableViewWrappers
open Solcore.SourceSemantics.CoreLowering.CallableViewWrappers

private def w (value : Nat) : Word := Word.ofNatModulo value
private def identity : Value := .inRight .unit (.word (w 7))
private def parameter : Ty := .word
private def result : Ty := .word
private def contract : Word := w 11
private def view : Word := w 42
private def carrierType : Ty := CallableContract.functionType parameter result

private def code : Expr :=
  .letE (.storeCell (.var 1) (.var 0))
    (LanguageResult.success (.loadCell (.var 2)))
private def captured : Environment := [.cellRef .word 0]
private def payload : Value := .closure parameter (LanguageResult.resultType result) code captured
private def original : Value := originalValue identity payload contract
private def outer : Environment := [.cellRef .word 0, .closure .unit .unit .unit []]
private def wrapped : Value := wrappedValue parameter result view identity payload contract outer
private def before : Store := [.word (w 5)]
private def after : Store := [.word (w 9)]

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def runExpected (label : String) (expression : Expr) (environment : Environment)
    (store : Store) (value : Value) (finalStore : Store) : IO Unit :=
  match runStateful 500 (.initial expression environment store) with
  | .done actual actualStore =>
    assertTrue (decide (actual = value ∧ actualStore = finalStore)) s!"{label}: {reprStr actual}, {reprStr actualStore}"
  | result => throw (IO.userError s!"{label}: {reprStr result}")

private def rejects (label : String) (value : Value) : IO Unit :=
  assertTrue (parse? parameter result value).isNone s!"{label}: malformed wrapper accepted"

def run : IO Unit := do
  let decoded ← match parse? parameter result wrapped with
    | some parsed => pure parsed | none => throw (IO.userError "actual wrapper did not parse")
  assertTrue (decide (decoded.view = view ∧ decoded.original = original ∧ decoded.outer = outer))
    "parser lost exact original carrier or captured outer environment"
  assertTrue (decide (decoded.identity = identity ∧ decoded.contract = contract)) "parser changed copied tags"
  runExpected "successful read builds only a value"
    (lower parameter result view (LanguageResult.success (.var 0))) [original] before
    (.inRight .word (wrappedValue parameter result view identity payload contract [original])) before
  runExpected "read failure skips wrapper creation"
    (lower parameter result view (LanguageResult.failure carrierType (.word (w 19)))) [] before
    (.inLeft carrierType (.word (w 19))) before
  runExpected "wrapper invokes original code with the live captured cell"
    invoke [wrapped, .word (w 9)] before (.inRight .word (.word (w 9))) after
  runExpected "descriptor projection is unchanged" (.second (.var 0)) [wrapped] before (.word contract) before
  runExpected "identity projection is unchanged" (.first (.first (.var 0))) [wrapped] before identity before
  let failureCode := .letE (.storeCell (.var 1) (.var 0))
    (LanguageResult.failure .word (.word (w 23)))
  let failurePayload := .closure .word (LanguageResult.resultType .word) failureCode captured
  runExpected "language failure preserves original prefix write"
    invoke [wrappedValue .word .word view identity failurePayload contract outer, .word (w 9)] before
    (.inLeft .word (.word (w 23))) after
  let other := wrappedValue parameter result (w 99) identity payload (w 123) []
  runExpected "different views and descriptors preserve named equality"
    CallableContract.equalBody [other, wrapped] before (.bool true) before
  let anonymous := wrappedValue parameter result view (.inLeft .word .unit) payload contract outer
  runExpected "anonymous self equality remains false" CallableContract.equalBody [anonymous, anonymous]
    before (.bool false) before
  runExpected "existing descriptor stage rejection is unchanged"
    (CallableContract.dispatch [⟨contract, some (w 29), none⟩] .beforeArguments (w 31) (.second (.var 0)))
    [wrapped] before (.inLeft .unit (.word (w 29))) before
  let closure := .closure parameter (LanguageResult.resultType result) (body view) (original :: outer)
  rejects "changed copied identity" (.pair (.pair (.inRight .unit (.word (w 8))) closure) (.word contract))
  rejects "changed copied descriptor" (.pair (.pair identity closure) (.word (w 12)))
  rejects "wrong parameter annotation" (.pair (.pair identity
    (.closure .bool (LanguageResult.resultType result) (body view) (original :: outer))) (.word contract))
  rejects "wrong result annotation" (.pair (.pair identity
    (.closure parameter .word (body view) (original :: outer))) (.word contract))
  rejects "changed capture projection" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result)
      (.letE (.word view) (.apply (.second (.first (.var 3))) (.var 1))) (original :: outer))) (.word contract))
  rejects "empty captured environment" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result) (body view) [])) (.word contract))
  rejects "noncarrier captured original" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result) (body view) (.unit :: outer))) (.word contract))
  let differentView := wrappedValue parameter result (w 44) identity payload contract outer
  let parsed ← match parse? parameter result differentView with
    | some parsed => pure parsed | none => throw (IO.userError "another structural manifest failed to parse")
  assertTrue (decide (parsed.view = w 44)) "parser must leave source view ownership to caller"
  assertTrue (Word.ofNat? wordModulus).isNone "out-of-range view IDs must not wrap"

private theorem code_typed : HasType [.word, .cell .word] code (LanguageResult.resultType .word) :=
  .letE (.storeCell (.var rfl) (.var rfl)) (.inRight .word (.loadCell (.var rfl)))

example : HasType [carrierType] (lower parameter result view (LanguageResult.success (.var 0)))
    (LanguageResult.resultType carrierType) := lower_hasType view .word .word (.inRight .word (.var rfl))

private theorem original_typed : RuntimeValueHasType [.word] original carrierType :=
  .pair (.pair (.inRight .word) (.closure (.cons (.cellRef rfl) .nil) code_typed)) .word

example : RuntimeValueHasType [.word] wrapped carrierType :=
  wrapped_runtime_typed view original_typed
    (.cons (.cellRef rfl) (.cons (.closure .nil .unit) .nil))

private theorem writes : Evaluates (.word (w 9) :: captured) before code
    (.inRight .word (.word (w 9))) after :=
  .letE (.storeCell (.var rfl) rfl (.var rfl) rfl) (.inRight (.loadCell (.var rfl) rfl))

example : Evaluates [wrapped, .word (w 9)] before invoke (.inRight .word (.word (w 9))) after :=
  invoke_evaluates view writes

example {value : Value} {finalStore : Store}
    (completed : ∃ fuel, runStateful fuel (.initial invoke [wrapped, .word (w 9)] before) = .done value finalStore) :
    Evaluates (.word (w 9) :: captured) before code value finalStore :=
  invoke_run_done_iff.mp completed

end Tests.SourceCoreCallableViewWrappers
