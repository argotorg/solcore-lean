import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.LocalInputsExecution

/-! Complete canonical sources preserve addition's exact tree, modular values,
strict checking, parameter positions, and checked machine fuel boundaries. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedAddition", by decide⟩], by decide⟩⟩, 3⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool true]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-addition.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression (content : String) : IO Syntax.Expr := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (cost : Nat) : IO Unit := do
  let source ← expression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store =
      some (.word, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store))
      s!"{content}: wrong value, store, or completion threshold"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: checking was bypassed"
  let declarationText := "function rejected(l: Word, r: Word, c: Bool) returns (Word) { return "
    ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) declarationText
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone
    s!"{content}: invalid whole body compiled"

private def checkShapes : IO Unit := do
  let leftAssociated ← expression "1 + 2 + 3"
  assertTrue (match leftAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .add⟩ _⟩ ⟨_, .add⟩ _ => true
    | _ => false) "addition parser changed left associativity"
  let rightGrouped ← expression "1 + (2 + 3)"
  assertTrue (match rightGrouped.value with
    | .binary _ ⟨_, .add⟩ ⟨_, .group ⟨_, .binary _ ⟨_, .add⟩ _⟩⟩ => true
    | _ => false) "addition parser lost explicit right grouping"
  let mixed ← expression "1 | 2 ^ 3 & 4 + 5"
  assertTrue (match mixed.value with
    | .binary _ ⟨_, .bitOr⟩ ⟨_, .binary _ ⟨_, .bitXor⟩
        ⟨_, .binary _ ⟨_, .bitAnd⟩ ⟨_, .binary _ ⟨_, .add⟩ _⟩⟩⟩ => true
    | _ => false) "addition/bitwise parser precedence changed"

/-- Every tested pair of source positions is retained in open Core, including
nonadjacent and repeated positions. Same-typed values remain individually visible. -/
private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function sum_{arity}_{left}_{right}({parameters}) returns (Word)"
          ++ " { return " ++ s!"p{left} + p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .add⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source parameter references changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordAdd (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .word))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .word))
          s!"{content}: open Core failed typing in its parameter context"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner declaration arguments
          | throw (IO.userError s!"{content}: matching arguments failed preparation")
        assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
          prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context))
          s!"{content}: runtime preparation changed its compiled projection"
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values)) s!"{content}: argument values were reordered"
        let initial := Core.State.initial compiled.core values store
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            some (.word, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            prepared.inputs.runReturnBody? fuel declaration.value.body store))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 store =
          some (.word, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let beforeAdd : Core.State := ⟨.ret (.word rightValue), [.binaryApply .wordAdd (.word leftValue)], store⟩
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 4 store =
          some (.word, .outOfFuel beforeAdd))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 5 store =
          some (.word, .done (.word (leftValue.add rightValue)) store))) s!"{content}: wrong exact five-fuel result"

def frontendParsedWordAdditionTests : IO Unit := do
  let supplied := inputs true
  checkRun supplied "1 + 2" (.binary .wordAdd (literal 1) (literal 2)) (word 3) 5
  checkRun supplied "/* left */ 0x01 + /* right */ 0002" (.binary .wordAdd (literal 1) (literal 2)) (word 3) 5
  checkRun supplied s!"{Core.Word.maximum.val} + 1"
    (.binary .wordAdd (.word Core.Word.maximum) (literal 1)) Core.Word.zero 5
  checkRun supplied "0 + l" (.binary .wordAdd (literal 0) (.var 2)) (word 7) 5
  checkRun supplied "r + 0" (.binary .wordAdd (.var 1) (literal 0)) (word 9) 5
  checkRun supplied "1 + 2 + 3" (.binary .wordAdd (.binary .wordAdd (literal 1) (literal 2)) (literal 3)) (word 6) 9
  checkRun supplied "((1 + 2)) + 3" (.binary .wordAdd (.binary .wordAdd (literal 1) (literal 2)) (literal 3)) (word 6) 9
  checkRun supplied "1 + (2 + 3)" (.binary .wordAdd (literal 1) (.binary .wordAdd (literal 2) (literal 3))) (word 6) 9
  checkRun supplied "1 | 2 ^ 3 & 4 + 5" (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3) (.binary .wordAdd (literal 4) (literal 5))))) (word 3) 17
  checkRun supplied "1 + 2 & 4 + 5" (.binary .wordAnd
    (.binary .wordAdd (literal 1) (literal 2)) (.binary .wordAdd (literal 4) (literal 5))) (word 1) 13
  checkRun supplied "1 + (2 & 4) + 5" (.binary .wordAdd
    (.binary .wordAdd (literal 1) (.binary .wordAnd (literal 2) (literal 4))) (literal 5)) (word 6) 13
  checkRun supplied "~(l + r)" (.unary .wordNot (.binary .wordAdd (.var 2) (.var 1))) (word 16).bitNot 7
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "c ? l + r : 0"
      (.ifE (.var 0) (.binary .wordAdd (.var 2) (.var 1)) (literal 0))
      (word (if choice then 16 else 0)) (if choice then 8 else 4)
    checkRun selected "c ? 0 : l + r"
      (.ifE (.var 0) (literal 0) (.binary .wordAdd (.var 2) (.var 1)))
      (word (if choice then 0 else 16)) (if choice then 4 else 8)
    for content in ["c + l", "l + c", "c ? l : 0 + c", "c ? c + 0 : r"] do
      checkRejected selected content true
    for content in ["0 + missing", "missing + 0", s!"0 + {Core.wordModulus}",
        s!"{Core.wordModulus} + 0", "c ? l : 0 + missing", "c ? missing + 0 : r",
        s!"c ? l : 0 + {Core.wordModulus}", s!"c ? {Core.wordModulus} + 0 : r",
        "0 + \"1\"", "l - r", "l * r", "l / r", "l % r", "l < r"] do
      checkRejected selected content false
  checkShapes
  checkParameterPositions
  for content in ["+1", "-1", "1 +", "1 + 2 3", "1 + 2 trailing", "l += r"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone
      s!"{content}: malformed, unsupported prefix, or unconsumed source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing() returns (Word) { return 1 + 2; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
