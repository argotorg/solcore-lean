import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TerminalReturnTree

/-! Compile each complete declaration once without values, then supply actual
ordered arguments. Terminal entries preserve exact costs, genuine checkpoints,
independent provenance, owner changes, and each execution's own store. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalRuntimeEntry", by decide⟩], by decide⟩⟩, 30⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 52 }
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def stores : List Core.Store :=
  [[.word (word 91), .bool true], [.unit, .cellRef .word 40, .bool false],
    [.closure .bool .bool (.var 0) [], .word Core.Word.maximum]]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-entry.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private structure Entry where
  declaration : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types owner declaration compiled

private def compile (content : String) (core : Core.Expr) (type : Core.Ty)
    (parameterTypes : List Core.Ty) (bound : Nat) : IO Entry := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: incomplete declaration")
  match accepted : compileRuntimeFunction? types owner declaration with
  | none => throw (IO.userError s!"{content}: terminal compilation failed")
  | some compiled =>
      let names ← declaration.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name _ := parameter.value | throw (IO.userError "unsupported parameter compiled")
        assertTrue (parameter.span.contains name.span && declaration.span.contains parameter.span)
          "parameter source positions escaped their declaration"
        pure name.value
      let expectedNames := (names.zipIdx.map fun (name, index) =>
        (name, (⟨owner, index⟩ : Resolved.LocalId))).reverse
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        compiled.inputs.context.values = parameterTypes.reverse ∧ compiled.inputs.names = expectedNames ∧
        Core.infer? parameterTypes.reverse core = some type)) "wrong open Core, source IDs, or declared return type"
      assertTrue (terminalReturnTreeFuelBound declaration.value.body == bound &&
        typedLetReturnTreeFuelBound declaration.value.body == bound) "wrong old body or integrated entry bound"
      match declaration.value.body.value with
      | [⟨_, .returnStmt _⟩] =>
          assertTrue (returnBodyFuelBound declaration.value.body == bound) "singleton source bound changed"
      | [⟨span, .ifThen condition thenBody (some elseBody)⟩] =>
          assertTrue (returnBodyFuelBound declaration.value.body == 0 &&
            span.contains condition.span && span.contains thenBody.span && span.contains elseBody.span &&
            decide (condition.span.endByte ≤ thenBody.span.startByte ∧ thenBody.span.endByte ≤ elseBody.span.startByte))
            "original singleton bound or written arm positions changed"
      | _ => throw (IO.userError "compiled a non-terminal body shape")
      return ⟨declaration, compiled, compileRuntimeFunction?_sound accepted⟩

private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) : IO Unit := do
  let source := entry.declaration
  let compiled := entry.compiled
  let bound := typedLetReturnTreeFuelBound source.value.body
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "actual selected cost exceeded source budget"
  if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
    let some prepared := prepareRuntimeFunction? types owner source arguments
      | throw (IO.userError "actual matching arguments did not prepare")
    have _ := entry.provenance.prepare_arguments arguments matching
    assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
      prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context.values = compiled.inputs.context.values ∧
      prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧
      prepared.inputs.checkTerminalReturnTree? source.value.body = some (compiled.core, compiled.returnType)))
      "preparation changed static projection, ordered actual values, or the original checked body"
    let expectedRows := (compiled.inputs.names.reverse.zip arguments).map fun (name, argument) =>
      (name.1, name.2, argument.type, argument.value)
    assertTrue (decide (prepared.inputs.bindings.map (fun row => (row.name, row.id, row.type, row.value)) =
      expectedRows.reverse)) "actual source positions were paired with different values"
    for initialStore in stores do
      have _ := entry.provenance.run_done_of_fuelBound arguments matching initialStore bound (Nat.le_refl _)
      let run := fun fuel => runRuntimeFunction? types owner source arguments fuel initialStore
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
      for fuel in List.range (bound + 3) do
        have _ := entry.provenance.run_eq arguments matching fuel initialStore
        have _ := runRuntimeFunction?_owner_eq types owner otherOwner source arguments fuel initialStore
        assertTrue (decide (run fuel = some (compiled.returnType, Core.runStateful fuel initial) ∧
          run fuel = prepared.inputs.runTerminalReturnTree? fuel source.value.body initialStore ∧
          run fuel = runRuntimeFunction? types otherOwner source arguments fuel initialStore))
          "entry wrapper or owner change altered the full same-fuel machine result"
        assertTrue (match run fuel with
          | some (type, .done result finalStore) =>
              decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
          | some (type, .outOfFuel checkpoint) =>
              decide (fuel < cost ∧ type = compiled.returnType ∧ checkpoint.store = initialStore)
          | _ => false) "wrong exact threshold, typed value, or own store"
        for replacement in stores do
          have _ := runRuntimeFunction?_done_store_iff types owner source arguments fuel initialStore replacement
            compiled.returnType value
          assertTrue ((decide (run fuel = some (compiled.returnType, .done value initialStore))) ==
            decide (runRuntimeFunction? types owner source arguments fuel replacement =
              some (compiled.returnType, .done value replacement))) "store replay changed completion observations"
          if replacement != initialStore then
            assertTrue (decide (run fuel ≠ runRuntimeFunction? types owner source arguments fuel replacement))
              "distinct own stores were erased from complete results/checkpoints"
      for spent in List.range cost do
        match exhausted : run spent with
        | some (type, .outOfFuel checkpoint) =>
            for remaining in List.range (cost - spent + 3) do
              have _ := runRuntimeFunction?_resume exhausted remaining
              let resumed := Core.runStateful remaining checkpoint
              assertTrue (decide (run (spent + remaining) = some (type, resumed))) "genuine checkpoint resumption changed"
              assertTrue (match resumed with
                | .done result finalStore => decide (cost - spent ≤ remaining ∧ result = value ∧ finalStore = initialStore)
                | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = initialStore)
                | _ => false) "resumption changed the exact residual cost or checkpoint's store"
        | _ => throw (IO.userError "genuine pre-completion checkpoint disappeared")
      match compiled.core with
      | .ifE condition thenCore elseCore =>
          let environment := arguments.reverse.map (·.value)
          let expected : Core.State := ⟨.eval condition environment,
            [.ifBranches thenCore elseCore environment], initialStore⟩
          assertTrue (decide (run 1 = some (compiled.returnType, .outOfFuel expected))) "initial conditional frame changed"
      | _ => pure ()
  else throw (IO.userError "positive test supplied mismatching argument types")

private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse))
    "negative actual arguments accidentally matched"
  assertTrue (prepareRuntimeFunction? types owner entry.declaration arguments).isNone "ordered argument guard bypassed"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.declaration.value.body, 60] do
      assertTrue (runRuntimeFunction? types otherOwner entry.declaration arguments fuel store).isNone
        "ample fuel or owner change bypassed actual argument guard"

private def reject (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError s!"{content}: negative fixture did not fully parse")
  assertTrue (compileRuntimeFunction? types owner source).isNone s!"{content}: invalid whole entry compiled"
  for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
      [boolArg false, wordArg 7, wordArg 9], [boolArg true, wordArg 7, wordArg 9]] do
    assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "rejected entry prepared actual arguments"
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone
          "whole header/parameter/arm rejection depended on fuel or selected value"

private def discardedPrefix : IO Unit := do
  let some source ← parsed? "function invalid(c: Bool,t: Word,f: Word) returns (Word){t; if(c){return t;}else{return f;}}"
    | throw (IO.userError "original discarded-prefix declaration did not parse")
  let tail : Core.Expr := .ifE (.var 3) (.var 2) (.var 1)
  let core : Core.Expr := .letE (.var 1) tail
  let some compiled := compileRuntimeFunction? types owner source
    | throw (IO.userError "valid strict expression prefix did not compile")
  let names : LocalNameTable := [("f", ⟨owner, 2⟩), ("t", ⟨owner, 1⟩), ("c", ⟨owner, 0⟩)]
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = .word ∧
    compiled.inputs.names = names ∧ compiled.inputs.context.values = [.word, .word, .bool] ∧
    elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body = none ∧
    terminalReturnTreeFuelBound source.value.body = 0 ∧ typedLetReturnTreeFuelBound source.value.body = 7))
    "discard prefix changed parameter-only records or the old adapter boundary"
  match source.value.body.value with
  | [⟨statementSpan, .expression expression true⟩, conditional] =>
      assertTrue (statementSpan.contains expression.span &&
        decide (statementSpan.endByte ≤ conditional.span.startByte)) "discard source order or semicolon changed"
  | _ => throw (IO.userError "original strict prefix AST changed")
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg 7, wordArg 9]
    let environment := [.word (word 9), .word (word 7), .bool choice]
    let value := Core.Value.word (word (if choice then 7 else 9))
    let some prepared := prepareRuntimeFunction? types owner source arguments
      | throw (IO.userError "original ordered arguments did not prepare")
    assertTrue (decide (prepared.core = core ∧ prepared.returnType = .word ∧
      prepared.inputs.names = names ∧ prepared.inputs.environment.values = environment ∧
      prepared.inputs.bindings.length = 3)) "discard added a source binding or reordered actual arguments"
    for store in stores do
      have paths (k : List Core.Frame) : Core.Steps 7
          ⟨.eval core environment, k, store⟩ ⟨.ret value, k, store⟩ := by
        cases choice <;>
          exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
            (.cons .enterIf (.cons (.var rfl)
              (.cons (by first | exact .chooseFalse | exact .chooseTrue) (.cons (.var rfl) .refl))))))
      have _ := paths []
      let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
      for fuel in List.range 10 do
        assertTrue (decide (run fuel = some (.word, Core.runStateful fuel (Core.State.initial core environment store)) ∧
          run fuel = prepared.inputs.runTypedLetReturnTree? types owner fuel source.value.body store))
          "strict prefix entry disagreed with the original Core/body runner"
        assertTrue (match run fuel with
          | some (.word, .done result finalStore) => decide (7 ≤ fuel ∧ result = value ∧ finalStore = store)
          | some (.word, .outOfFuel checkpoint) => decide (fuel < 7 ∧ checkpoint.store = store)
          | _ => false) "discard prefix did not retain its exact seven-step cost"
      assertTrue (decide (run 2 = some (.word, .outOfFuel
        ⟨.ret (.word (word 7)), [.letBody tail environment], store⟩) ∧
        run 3 = some (.word, .outOfFuel ⟨.eval tail (.word (word 7) :: environment), [], store⟩)))
        "discard's hidden Core value or original saved environment changed"
      for spent in List.range 7 do
        let some (.word, .outOfFuel checkpoint) := run spent
          | throw (IO.userError "discard checkpoint disappeared")
        for remaining in List.range (10 - spent) do
          assertTrue (decide (run (spent + remaining) = some (.word, Core.runStateful remaining checkpoint)))
            "discard checkpoint did not resume exactly"

def frontendParsedTerminalRuntimeEntriesTests : IO Unit := do
  discardedPrefix
  let bare ← compile "function bare(){return;}" .unit .unit [] 1
  checkCase bare [] .unit 1
  let units ← compile "function units(c: Bool){if(c){return;}else{return;}}"
    (.ifE (.var 0) .unit .unit) .unit [.bool] 4
  for choice in [false, true] do checkCase units [boolArg choice] .unit 4
  let nested ← compile "function nested(c: Bool,t: Word,f: Word) returns (Word){if(c){if(c){return t;}else{return f;}}else{return f;}}"
    (.ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0)) .word [.bool, .word, .word] 7
  for choice in [false, true] do
    checkCase nested [boolArg choice, wordArg 7, wordArg 9] (.word (word (if choice then 7 else 9))) (if choice then 7 else 4)
  let short ← compile "function short(c: Bool,t: Word,f: Word) returns (Word){if(c){return ~t;}else{return f;}}"
    (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word [.bool, .word, .word] 6
  let compare ← compile "function compare(c: Bool,t: Word,f: Word) returns (Bool){if(c){return t < f;}else{return t >= f;}}"
    (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0)))) .bool [.bool, .word, .word] 16
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      for choice in [false, true] do
        let arguments := [boolArg choice, wordArg left, wordArg right]
        checkCase short arguments (.word (if choice then (word left).bitNot else word right)) (if choice then 6 else 4)
        let less := decide (word left < word right)
        checkCase compare arguments (.bool (if choice then less else !less)) (if choice then 14 else 16)
  for arguments in [[], [boolArg true], [wordArg 7, boolArg false, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectArguments short arguments
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", wordArg 7, wordArg 9), ("Bool", boolArg true, boolArg false),
      ("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight)] do
    for body in ["{return c ? t : f;}", "{if(c){return t;}else{return f;}}"] do
      let entry ← compile (s!"function values(c: Bool,t: {name},f: {name}) returns ({name})" ++ body)
        (.ifE (.var 2) (.var 1) (.var 0)) left.type [.bool, left.type, right.type] 4
      for choice in [false, true] do
        checkCase entry [boolArg choice, left, right] (if choice then left.value else right.value) 4
  let nominal ← compile "function nominal(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}"
    (.ifE (.var 1) (.var 0) (.var 0)) (.namedData ⟨91⟩) [.bool, .namedData ⟨91⟩] 4
  for argument in [unit, wordArg 7, boolArg false, cellLeft, closureLeft] do
    rejectArguments nominal [boolArg true, argument]
  for body in ["{}", "{if(c){return t;}}", "{if(c){return t;}else{return f;}return t;}",
      "{if(c){return t;return f;}else{return f;}}",
      "{if(t){return t;}else{return f;}}",
      "{if(c){return t;}else{return c;}}", "{if(c){return;}else{return f;}}"] do
    reject ("function invalid(c: Bool,t: Word,f: Word) returns (Word)" ++ body)
  for invalid in ["missing", "c", "t + c", "t(c)", s!"{Core.wordModulus}"] do
    reject ("function skipped(c: Bool,t: Word,f: Word) returns (Word){if(c){return t;}else{return " ++ invalid ++ ";}}")
    reject ("function skipped(c: Bool,t: Word,f: Word) returns (Word){if(c){return " ++ invalid ++ ";}else{return f;}}")
  for header in ["function wrong(c: Bool)", "function wrong(c: Bool) returns (Bool)",
      "function wrong(c: Bool) returns ()", "function wrong(c: Bool) returns (Word,Bool)",
      "function wrong(c: Bool) returns (Unknown)", "function wrong<T>(c: Bool) returns (Word)",
      "function wrong(c: Bool) returns (Word) where Word: Eq", "function wrong(c: Bool,c: Bool) returns (Word)",
      "function wrong(comptime c: Bool) returns (Word)", "function wrong(c: Unknown) returns (Word)"] do
    reject (header ++ "{if(c){return 7;}else{return 9;}}")
  reject "function wrong(c: Bool) public returns (Word){if(c){return 7;}else{return 9;}}" .contract
  for content in ["", "function f(c: Bool)", "function f(c: Bool){if(c){return;}else{return;}",
      "function f(c: Bool){if(c){return}else{return;}}", "function f(c: Bool){if(c){return;}else{return;}} trailing"] do
    assertTrue (← parsed? content).isNone "malformed or partially consumed declaration accepted"

end Tests
