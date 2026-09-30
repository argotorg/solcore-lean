import Solcore.Core.TaggedFunction
import Solcore.Core.OptionalCell

set_option autoImplicit false

namespace Tests.CoreTaggedFunction

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def callableType : Ty := TaggedFunction.functionType .unit .word

/-- The closure captures a location and observes a write after creation. -/
private def capturedProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (.letE (TaggedFunction.anonymous (.lambda .unit (LanguageResult.resultType .word)
      (LanguageResult.success (.loadCell (.var 1)))))
      (.letE (.storeCell (.var 1) (literal 7))
        (TaggedFunction.call .word (LanguageResult.success (.var 1))
          (LanguageResult.success .unit))))
}

private def calleeFailure : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (TaggedFunction.call .word (LanguageResult.failure callableType (literal 41))
      (.letE (.storeCell (.var 0) (literal 99)) (LanguageResult.success .unit)))
}

/-- The argument updates the store, then fails; the closure body is skipped. -/
private def argumentFailure : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (TaggedFunction.call .word
      (LanguageResult.success (TaggedFunction.anonymous
        (.lambda .unit (LanguageResult.resultType .word)
          (.letE (.storeCell (.var 1) (literal 99)) (LanguageResult.success (literal 99))))))
      (.letE (.storeCell (.var 0) (literal 7)) (LanguageResult.failure .unit (literal 42))))
}

private def identityProgram (left right : Expr) : Program := {
  resultType := LanguageResult.resultType .bool
  body := TaggedFunction.equal (LanguageResult.success left) (LanguageResult.success right)
}

private def functionBody : Expr :=
  .lambda .unit (LanguageResult.resultType .word) (LanguageResult.success (literal 8))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expect (label : String) (program : Program) (value : Value) (store : Store := []) : IO Unit := do
  assertTrue program.check s!"{label}: checker rejected the function representation"
  assertTrue (program.runStateful 1000 == .done value store)
    s!"{label}: function result or shared store differs"

def run : IO Unit := do
  expect "mutable capture" capturedProgram (.inRight .word (scalar 7)) [scalar 7]
  expect "failed callee" calleeFailure (.inLeft .word (scalar 41)) [scalar 1]
  expect "failed argument" argumentFailure (.inLeft .word (scalar 42)) [scalar 7]
  let anonymous := TaggedFunction.anonymous functionBody
  let named := TaggedFunction.identified (word 1) functionBody
  expect "same anonymous closure" (identityProgram anonymous anonymous) (.inRight .word (.bool false))
  expect "same named identity" (identityProgram named named) (.inRight .word (.bool true))
  expect "different named identity"
    (identityProgram named (TaggedFunction.identified (word 2) functionBody)) (.inRight .word (.bool false))
  expect "anonymous left" (identityProgram anonymous named) (.inRight .word (.bool false))
  expect "anonymous right" (identityProgram named anonymous) (.inRight .word (.bool false))

end Tests.CoreTaggedFunction
