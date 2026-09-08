import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.TerminalReturnBodyRenamingProperties

/-! Canonical unsigned quotient and remainder preserve original operand order.
Zero divisors produce zero only after both children execute; literal boundaries,
actual typed arguments, whole checking, and genuine checkpoints stay explicit. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedDivision", by decide⟩], by decide⟩⟩, 31⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 63 }
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 43 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; simp_all [shift]
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store :=
  [[.word (word 91), .bool true], [.cellRef .word 40, .unit, .word Core.Word.maximum]]
private def result (remainder : Bool) (left right : Nat) : Core.Word :=
  word (if right == 0 then 0 else if remainder then left % right else left / right)
private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-division.sol"⟩, content }
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
private def leafValue? (expression : Core.Expr) (environment : Core.Environment) : Option Core.Value :=
  match expression with | .word value => some (.word value) | .var index => environment[index]? | _ => none

private def checkMachine (run : Nat → Option (Core.Ty × Core.StatefulRunResult)) (core : Core.Expr)
    (environment : Core.Environment) (store : Core.Store) (type : Core.Ty) (value : Core.Value)
    (cost bound : Nat) : IO Unit := do
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "selected cost exceeded its source bound"
  for fuel in List.range (bound + 3) do
    assertTrue (decide (run fuel = some (type, Core.runStateful fuel (Core.State.initial core environment store))))
      "actual compiled Core or full same-fuel result changed"
    assertTrue (match run fuel with
      | some (actualType, .done actualValue finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = store)
      | some (actualType, .outOfFuel checkpoint) => decide (fuel < cost ∧ actualType = type ∧ checkpoint.store = store)
      | _ => false) "wrong exact threshold, value, return type, or own store"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
    for remaining in List.range (cost - spent + 3) do
      let resumed := Core.runStateful remaining checkpoint
      assertTrue (decide (run (spent + remaining) = some (type, resumed))) "same-state resumption changed"
      assertTrue (match resumed with
        | .done actualValue finalStore => decide (cost - spent ≤ remaining ∧ actualValue = value ∧ finalStore = store)
        | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = store)
        | _ => false) "wrong exact residual cost or resumed store"
  match core with
  | .binary operator left right =>
      if let (some leftValue, some rightValue) := (leafValue? left environment, leafValue? right environment) then
        let two : Core.State := ⟨.ret leftValue, [.binaryRight operator right environment], store⟩
        let four : Core.State := ⟨.ret rightValue, [.binaryApply operator leftValue], store⟩
        assertTrue (decide (run 2 = some (type, .outOfFuel two) ∧ run 4 = some (type, .outOfFuel four) ∧
          Core.runStateful 2 two = .outOfFuel four ∧ Core.runStateful 1 four = .done value store ∧
          Core.runStateful 0 four = .outOfFuel four ∧
          Core.runStateful 0 { four with continuation := [] } = .done rightValue store))
          "left/right order, both-child evaluation, multichunk resumption, or pending application changed"
  | _ => pure ()

private def checkExpression (content : String) (core : Core.Expr) (value : Core.Word) (cost : Nat) : IO Unit := do
  let some source ← parsed? Syntax.Parser.expression content | throw (IO.userError "expression did not fully parse")
  assertTrue (decide (LocalInputs.empty.check? source = some (core, .word))) "literal expression's exact Core/type changed"
  assertTrue (localExpressionFuelBound source == cost) "strict expression source bound changed"
  for store in stores do
    checkMachine (fun fuel => LocalInputs.empty.run? fuel source store) core [] store .word (.word value) cost cost

private def checkEntry (content : String) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty)
    (bound : Nat) (cases : List (List TypedRuntimeArgument × Core.Value × Nat)) : IO Unit := do
  let some source ← parsed? (Syntax.Parser.functionDecl .module) content | throw (IO.userError "entry did not fully parse")
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError s!"{content}: value-free compilation failed")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name _ := parameter.value | throw (IO.userError "unsupported parameter compiled")
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        compiled.inputs.context.values = parameterTypes.reverse ∧ Core.infer? parameterTypes.reverse core = some type ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse))
        "exact open Core, original source identities, or declared type changed"
      assertTrue (terminalReturnTreeFuelBound source.value.body == bound) "entry's source bound changed"
      for (arguments, value, cost) in cases do
        if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
          let some prepared := prepareRuntimeFunction? types owner source arguments
            | throw (IO.userError "actual matching arguments did not prepare")
          let mapped := prepared.inputs.mapIds shift shiftInjective
          assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧
            prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context.values = parameterTypes.reverse ∧
            prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧
            prepared.inputs.checkTerminalReturnBody? source.value.body = some (core, type) ∧
            mapped.checkTerminalReturnBody? source.value.body = some (core, type)))
            "preparation or injective relabeling changed actual arguments/Core/body"
          for store in stores do
            have _ := provenance.run_done_of_fuelBound arguments matching store
              (terminalReturnTreeFuelBound source.value.body) (Nat.le_refl _)
            let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
            checkMachine run core (arguments.reverse.map (·.value)) store type value cost bound
            for fuel in List.range (bound + 3) do
              have _ := provenance.run_eq arguments matching fuel store
              assertTrue (decide (run fuel = runRuntimeFunction? types otherOwner source arguments fuel store ∧
                run fuel = mapped.runTerminalReturnBody? fuel source.value.body store)) "owner/ID relabeling changed full states"
              for replacement in stores do
                if replacement != store then
                  assertTrue (decide (run fuel ≠ runRuntimeFunction? types owner source arguments fuel replacement))
                    "store replay erased distinct stores from full results"
        else throw (IO.userError "positive fixture supplied mismatching argument types")
      for arguments in [[], [boolArg true], [wordArg 7, boolArg false], [wordArg 7, wordArg 9, boolArg true]] do
        if arguments.map (·.type) != parameterTypes then
          assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "actual argument guard was bypassed"

private def reject (content : String) (arguments : List TypedRuntimeArgument) : IO Unit := do
  let some source ← parsed? (Syntax.Parser.functionDecl .module) content | throw (IO.userError s!"{content}: negative did not parse")
  assertTrue ((compileRuntimeFunction? types owner source).isNone &&
    (prepareRuntimeFunction? types owner source arguments).isNone) s!"{content}: invalid whole entry checked"
  for store in stores do
    for fuel in [0, terminalReturnTreeFuelBound source.value.body, 50] do
      assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "rejection exposed an actual checkpoint"

private def positions (symbol : String) (sourceOperator : Syntax.BinaryOp) (operator : Core.BinaryOp)
    (remainder : Bool) : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function ordered({parameters}) returns (Word)" ++ "{return " ++ s!"p{left} {symbol} p{right};" ++ "}"
        let some source ← parsed? (Syntax.Parser.functionDecl .module) content | throw (IO.userError "positions did not parse")
        assertTrue (match source.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨span, op⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              op == sourceOperator && l.value == s!"p{left}" && r.value == s!"p{right}" &&
                decide (l.span.endByte ≤ span.startByte ∧ span.endByte ≤ r.span.startByte)
          | _ => false) "canonical ordered source operator/positions changed"
        let cases := [false, true].map fun zeroFirst =>
          let argumentValue := fun index => if zeroFirst && index == 0 then 0 else 10 * index + 7
          (indices.map (fun index => wordArg (argumentValue index)),
            Core.Value.word (result remainder (argumentValue left) (argumentValue right)), 5)
        checkEntry content (.binary operator (.var (arity - 1 - left)) (.var (arity - 1 - right)))
          .word (List.replicate arity .word) 5 cases

def frontendParsedWordDivisionTests : IO Unit := do
  let boundaries := [0, 1, 3, 7, 2 ^ 255, Core.Word.maximum.val]
  for (symbol, sourceOperator, operator, remainder) in
      [("/", Syntax.BinaryOp.divide, Core.BinaryOp.wordDiv, false), ("%", .modulo, .wordMod, true)] do
    let cases := boundaries.flatMap fun left => boundaries.map fun right =>
      ([wordArg left, wordArg right], Core.Value.word (result remainder left right), 5)
    checkEntry ("function divide(l: Word,r: Word) returns (Word){return l " ++ symbol ++ " r;}")
      (.binary operator (.var 1) (.var 0)) .word [.word, .word] 5 cases
    for (left, right) in [(7, 3), (3, 7), (7, 0), (0, 7), (0, 0), (Core.Word.maximum.val, 2 ^ 255)] do
      checkExpression s!" /* numerator */ (({left})) {symbol} /* divisor */ ({right})"
        (.binary operator (literal left) (literal right)) (result remainder left right) 5
    positions symbol sourceOperator operator remainder
    let branchCases := [false, true].flatMap fun choice => boundaries.map fun right =>
      ([boolArg choice, wordArg 7, wordArg right], Core.Value.word
        (if choice then result remainder 7 right else word 7), if choice then 8 else 4)
    for body in ["{return c ? l " ++ symbol ++ " r : l;}", "{if(c){return l " ++ symbol ++ " r;}else{return l;}}"] do
      checkEntry ("function selected(c: Bool,l: Word,r: Word) returns (Word)" ++ body)
        (.ifE (.var 2) (.binary operator (.var 1) (.var 0)) (.var 1)) .word [.bool, .word, .word] 8 branchCases
    let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
    let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
    let closure : TypedRuntimeArgument :=
      ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
    for (name, argument) in [("Bool", boolArg false), ("Unit", unit), ("Cell", cell), ("Fn", closure)] do
      for operand in ["x " ++ symbol ++ " y", "y " ++ symbol ++ " x"] do
        reject (s!"function wrong(x: {name},y: Word) returns (Word)" ++ "{return " ++ operand ++ ";}")
          [argument, wordArg 7]
    for choice in [false, true] do
      let arguments := [boolArg choice, wordArg 7, wordArg 3]
      for invalid in ["missing " ++ symbol ++ " r", "l " ++ symbol ++ " missing", "l(c) " ++ symbol ++ " r",
          "l " ++ symbol ++ " r(c)", s!"{Core.wordModulus} {symbol} r", s!"l {symbol} {Core.wordModulus}",
          "c " ++ symbol ++ " r", "l " ++ symbol ++ " c"] do
        for body in ["{return c ? l : " ++ invalid ++ ";}", "{if(c){return " ++ invalid ++ ";}else{return l;}}"] do
          reject ("function skipped(c: Bool,l: Word,r: Word) returns (Word)" ++ body) arguments
    reject ("function wrong(l: Word,r: Word) returns (Bool){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
    reject ("function wrong(l: Word,r: Word){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
    reject ("function wrong(l: Word,r: Word) returns (Unknown){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
  checkExpression "20 / 3 * 2 % 7" (.binary .wordMod
    (.binary .wordMul (.binary .wordDiv (literal 20) (literal 3)) (literal 2)) (literal 7)) (word 5) 13
  checkExpression "20 / (3 * 2) % 7" (.binary .wordMod
    (.binary .wordDiv (literal 20) (.binary .wordMul (literal 3) (literal 2))) (literal 7)) (word 3) 13
  checkExpression "20 - 7 % 3 + 8 / 2" (.binary .wordAdd
    (.binary .wordSub (literal 20) (.binary .wordMod (literal 7) (literal 3)))
    (.binary .wordDiv (literal 8) (literal 2))) (word 23) 17
  checkExpression "0 / (7 % 0)" (.binary .wordDiv (literal 0) (.binary .wordMod (literal 7) (literal 0))) (word 0) 9
  let shortCases := [false, true].flatMap fun choice => boundaries.map fun right =>
    ([boolArg choice, wordArg 7, wordArg right], Core.Value.bool (choice && (result false 7 right == word 0)),
      if choice then 12 else 4)
  checkEntry "function short(c: Bool,l: Word,r: Word) returns (Bool){return c && l / r == 0;}"
    (.ifE (.var 2) (.binary .wordEq (.binary .wordDiv (.var 1) (.var 0)) (literal 0)) (.bool false))
    .bool [.bool, .word, .word] 12 shortCases
  let guardCases := boundaries.flatMap fun left => boundaries.map fun right =>
    let choice := decide (result false left right > word right)
    ([wordArg left, wordArg right], Core.Value.word (if choice then result true left right else word left),
      if choice then 16 else 12)
  checkEntry "function guard(l: Word,r: Word) returns (Word){if(l / r > r){return l % r;}else{return l;}}"
    (.ifE (.binary .wordGt (.binary .wordDiv (.var 1) (.var 0)) (.var 0))
      (.binary .wordMod (.var 1) (.var 0)) (.var 1)) .word [.word, .word] 16 guardCases
  for content in ["7 /", "7 %", "7 / 3 trailing", "7 % 3 2", "-7 / 3", "7 / -3", "l /= r", "l %= r"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone "malformed, signed-prefix, or unconsumed expression accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function f() returns (Word){return 7 % 0;} trailing").isNone "function parser accepted only a valid prefix"

end Tests
