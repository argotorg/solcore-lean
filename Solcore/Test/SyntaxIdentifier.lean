import Solcore.Syntax.Identifier

/-! Public canonical identifier validation regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (message : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{message}: expected {reprStr expected}, got {reprStr actual}")

private def validIdentifiers : List String := [
  "value",
  "value_2",
  "λ",
  "fλ2",
  "comptime",
  "derive",
  "enum",
  "from",
  "hiding",
  "impl",
  "mapping",
  "returns",
  "trait",
  "where",
  "while"
]

private def invalidIdentifiers : List String := [
  "",
  "_",
  "_value",
  "$",
  "$value",
  "value$tail",
  "`templateValue`",
  "${templateValue}",
  "0",
  "0x2a",
  "2value",
  "return",
  "true",
  "false",
  "\"text\"",
  "__",
  "value-name",
  "two names",
  "value;",
  "value/*comment*/"
]

private def hardKeywords : List HardKeyword := [
  .contractKw,
  .importKw, .exportKw, .asKw, .letKw, .dataKw, .classKw,
  .forallKw, .instanceKw, .ifKw, .elseKw, .forKw, .switchKw,
  .typeKw, .caseKw, .defaultKw, .matchKw, .publicKw, .payableKw,
  .functionKw, .constructorKw, .fallbackKw, .returnKw, .leaveKw,
  .continueKw, .breakKw, .lamKw, .assemblyKw, .pragmaKw,
  .trueKw, .falseKw
]

private def contextualKeywords : List ContextualKeyword := [
  .comptime,
  .derive, .enum, .from, .hiding, .impl, .mapping, .returns,
  .trait, .where, .while
]

example : validIdentifiers.all isValidIdentifier = true := by
  native_decide

example : invalidIdentifiers.any isValidIdentifier = false := by
  native_decide

example : hardKeywords.any (isValidIdentifier ·.spelling) = false := by
  native_decide

example : contextualKeywords.all (isValidIdentifier ·.spelling) = true := by
  native_decide

/-- Run ordinary-identifier validation regressions pinned to solcore-rs PR #20. -/
def testSyntaxIdentifier : IO Unit := do
  for text in validIdentifiers do
    assertEqual (isValidIdentifier text) true
      s!"identifier {text.quote} should be valid"
  for text in invalidIdentifiers do
    assertEqual (isValidIdentifier text) false
      s!"identifier {text.quote} should be invalid"
  for keyword in hardKeywords do
    assertEqual (isValidIdentifier keyword.spelling) false
      s!"hard keyword {keyword.spelling.quote} should be invalid"
  for keyword in contextualKeywords do
    assertEqual (isValidIdentifier keyword.spelling) true
      s!"contextual word {keyword.spelling.quote} should be valid"

end Tests
