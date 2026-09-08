import Solcore.Syntax.Parser.Term
import Solcore.Frontend.WordLiteral
import Solcore.Frontend.LocalInputsExecution

/-! Full-source literal regressions for numeric interpretation and checked execution.
Parser acceptance, natural-number meaning, and strict Word range are distinct.
The monomorphic local-expression adapter admits exactly the strict Word values. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsedLiteral? (content : String) : IO (Option Syntax.CoreLiteral) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-word-literal.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      match source.value with
      | .literal literal => return some literal
      | _ => return none
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkNumeric (content : String) (expectedPayload : Syntax.CoreLiteralValue)
    (expected : Nat) : IO Unit := do
  let some literal ← parsedLiteral? content
    | throw (IO.userError s!"{content}: expected one complete literal expression")
  assertTrue (decide (literal.value = expectedPayload)) s!"{content}: changed numeric spelling"
  assertTrue (decide (numericLiteralValue? literal.value = some expected))
    s!"{content}: wrong natural-number meaning"
  let actual := interpretWordLiteral? literal
  assertTrue (decide (actual = Core.Word.ofNat? expected))
    s!"{content}: wrong strict Word range or value"
  let source : Syntax.Expr := ⟨literal.span, .literal literal⟩
  let checked := LocalInputs.empty.check? source
  let store : Core.Store := [.word Core.Word.zero, .bool false]
  match actual with
  | some word =>
      assertTrue (decide (word.val = expected)) s!"{content}: Word value was reduced"
      assertTrue (decide (checked = some (.word word, .word)))
        s!"{content}: wrong literal Core or source type"
      let some (actualCore, _) := checked
        | throw (IO.userError s!"{content}: literal did not check")
      assertTrue (decide (LocalInputs.empty.run? 0 source store =
        some (.word, .outOfFuel (Core.State.initial actualCore [] store))))
        s!"{content}: literal completed without its one transition"
      for fuel in [1, 6] do
        assertTrue (decide (LocalInputs.empty.run? fuel source store =
          some (.word, .done (.word word) store)))
          s!"{content}: checked literal changed value or store"
  | none =>
      assertTrue (decide (Core.wordModulus ≤ expected)) s!"{content}: in-range value was rejected"
      assertTrue checked.isNone s!"{content}: overflowing literal checked"
      for fuel in [0, 7] do
        assertTrue (LocalInputs.empty.run? fuel source store).isNone
          s!"{content}: overflowing literal reached execution"
  let shifted : Syntax.CoreLiteral :=
    { literal with span := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩ }
  assertTrue (decide (interpretWordLiteral? shifted = actual))
    s!"{content}: literal interpretation depended on source ranges"
  assertTrue (decide (LocalInputs.empty.check? ⟨shifted.span, .literal shifted⟩ = checked))
    s!"{content}: literal checking depended on either source range"

def frontendParsedWordLiteralTests : IO Unit := do
  checkNumeric "0" (.decimal "0") 0
  checkNumeric "1" (.decimal "1") 1
  checkNumeric "0007" (.decimal "0007") 7
  checkNumeric " /* leading */ 0007 /* trailing */ " (.decimal "0007") 7
  checkNumeric "0x0" (.hexadecimal "0x0") 0
  checkNumeric "0x1" (.hexadecimal "0x1") 1
  checkNumeric "0xaBcD" (.hexadecimal "0xaBcD") 43981
  checkNumeric "0xAbCd" (.hexadecimal "0xAbCd") 43981
  checkNumeric "43981" (.decimal "43981") 43981
  let decimalMaximum := toString (Core.wordModulus - 1)
  let decimalOverflow := toString Core.wordModulus
  checkNumeric decimalMaximum (.decimal decimalMaximum) (Core.wordModulus - 1)
  checkNumeric decimalOverflow (.decimal decimalOverflow) Core.wordModulus
  let hexMaximum := "0x" ++ String.ofList (List.replicate 64 'F')
  let hexOverflow := "0x1" ++ String.ofList (List.replicate 64 '0')
  checkNumeric hexMaximum (.hexadecimal hexMaximum) (Core.wordModulus - 1)
  checkNumeric hexOverflow (.hexadecimal hexOverflow) Core.wordModulus
  let zeroes := String.ofList (List.replicate 100 '0')
  checkNumeric (zeroes ++ "7") (.decimal (zeroes ++ "7")) 7
  checkNumeric ("0x" ++ zeroes ++ "aF") (.hexadecimal ("0x" ++ zeroes ++ "aF")) 175
  for content in ["0x", "0Xff", "1_000", "123abc", "0x1g", "٤", "４", "1.0", "-1", "+1", "7 8"] do
    let parsed ← parsedLiteral? content
    assertTrue parsed.isNone s!"{content}: accepted an incomplete or malformed numeric expression"
  let some quoted ← parsedLiteral? "\"7\""
    | throw (IO.userError "quoted source should parse as a string literal")
  assertTrue (decide (numericLiteralValue? quoted.value = none ∧ interpretWordLiteral? quoted = none))
    "a quoted string received numeric meaning"
  assertTrue (LocalInputs.empty.check? ⟨quoted.span, .literal quoted⟩).isNone
    "a quoted string became a checked numeric expression"

end Tests
