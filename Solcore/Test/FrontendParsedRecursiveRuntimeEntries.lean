import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Resolved.LocalScopeProperties

/-! Compile actual recursive declarations once, then supply independent actual
arguments. Source-selected cost scripts and exact compilation provenance meet
at the unchanged Core runner; nominal compilation never invents inhabitants. -/

set_option autoImplicit false

namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 31⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 58 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-recursive-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next => return if next.atEnd && next.diagnostics.isEmpty then some source else none
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")

private structure Reference (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  costed : LocalExpressionEvaluatesWithCost table environment store source value store 1
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Reference table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "unknown scripted name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "missing actual scripted value")
          | some value => return ⟨value, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected an identifier")
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TerminalReturnTreeEvaluatesWithCost table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match choices, sourceAt : source with
  | [], ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | [], ⟨_, [⟨_, .returnStmt (some ⟨_, .unary ⟨_, .bitNot⟩ operand⟩)⟩]⟩ =>
      let child ← reference table environment store operand
      match actual : child.value with
      | .word value => return ⟨.word value.bitNot, 3, by
          rw [sourceAt]; exact .single (.expression (.bitNot (by simpa only [actual] using child.costed)))⟩
      | _ => throw (IO.userError "scripted complement did not receive a Word")
  | [], ⟨_, [⟨_, .returnStmt (some ⟨_, .binary left ⟨_, .subtract⟩ right⟩)⟩]⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match firstAt : first.value, secondAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), 5, by
          rw [sourceAt]; exact .single (.expression (.subtract
            (by simpa only [firstAt] using first.costed) (by simpa only [secondAt] using second.costed)))⟩
      | _, _ => throw (IO.userError "ordered subtraction received a non-Word")
  | [], ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      let leaf ← reference table environment store expression
      return ⟨leaf.value, 1, by rw [sourceAt]; exact .single (.expression leaf.costed)⟩
  | choice :: rest, ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← certify table environment store thenBody rest
            return ⟨child.value, 1 + child.cost + 2, by
              rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store elseBody rest
            return ⟨child.value, 1 + child.cost + 2, by
              rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagreed with the actual guard")
  | _, _ => throw (IO.userError "script disagreed with the original body")
termination_by choices.length

private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types owner source compiled
private theorem excludeWrong {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (provenance : RuntimeFunctionCompiles types owner source compiled) {wrong : Core.Expr} (different : wrong ≠ compiled.core) :
    ¬ RuntimeFunctionCompiles types owner source { compiled with core := wrong } := by
  intro other
  exact different (congrArg CompiledRuntimeFunction.core (other.result_unique provenance))
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty) (bound : Nat) : IO Entry := do
  let some source ← parsed? content | throw (IO.userError "complete declaration did not parse")
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "valid recursive declaration did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "unexpected parameter policy")
        assertTrue (parameter.span.contains name.span && parameter.span.contains annotation.span && source.span.contains parameter.span)
          "actual parameter source positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameterTypes.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        Core.infer? parameterTypes.reverse core = some type ∧ terminalReturnTreeFuelBound source.value.body = bound ∧
        typedLetReturnTreeFuelBound source.value.body = bound))
        "value-free compilation changed actual Core/type/rows/source budget"
      let wrong : Core.Expr := match compiled.core with
        | .ifE condition left right => .ifE (.unary .boolNot condition) left right
        | actual => .ifE (.bool true) actual actual
      if different : wrong ≠ compiled.core then
        have _ := excludeWrong provenance different
        assertTrue (decide (Core.infer? compiled.inputs.context.values wrong = some compiled.returnType)) "wrong Core was not equally typed"
      else throw (IO.userError "wrong-Core contrast was trivial")
      have _ := provenance.core_hasType
      return ⟨source, compiled, provenance⟩

private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument) (choices : List Bool) (value : Core.Value) (cost : Nat) : IO Unit := do
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types owner entry.source arguments with
    | none => throw (IO.userError "matching actual arguments did not prepare")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := entry.provenance.prepare_arguments arguments matching
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = entry.compiled.returnType ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "preparation changed source positions, Core or actual values"
      for store in stores do
        let certificate ← certify prepared.inputs.names prepared.inputs.environment store entry.source.value.body choices
        let costed := RuntimeFunctionEvaluatesWithCost.intro preparation (certificate.costed.typedLetReturnTree owner)
        have _ := costed.compiled_toSteps entry.provenance
        have _ := costed.cost_le_fuelBound
        have _ := costed.hasType.run_done_of_fuelBound store
        let bound := typedLetReturnTreeFuelBound entry.source.value.body
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store bound (Nat.le_refl _)
        assertTrue (decide (certificate.cost = cost ∧ certificate.value = value)) "independent recursive source cost/value changed"
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types owner entry.source arguments fuel store
        for fuel in List.range (bound + 3) do
          have _ := entry.provenance.run_eq arguments matching fuel store
          have _ := runRuntimeFunction?_factorization types owner entry.source arguments fuel store
          have _ := runRuntimeFunction?_owner_eq types owner otherOwner entry.source arguments fuel store
          assertTrue (decide (run fuel = some (entry.compiled.returnType, Core.runStateful fuel initial) ∧
            run fuel = prepared.inputs.runTerminalReturnTree? fuel entry.source.value.body store ∧
            run fuel = runRuntimeFunction? types otherOwner entry.source arguments fuel store)) "entry/owner changed complete Core execution"
          assertTrue (match run fuel with
            | some (type, .done result finalStore) => decide (type = entry.compiled.returnType ∧ result = value ∧ finalStore = store ∧ cost ≤ fuel)
            | some (type, .outOfFuel state) => decide (type = entry.compiled.returnType ∧ state.store = store ∧ fuel < cost)
            | _ => false) "wrong entry threshold, returned value/type or own store"
          for replacement in stores do
            have _ := runRuntimeFunction?_done_store_iff types owner entry.source arguments fuel store replacement entry.compiled.returnType value
            have _ := runRuntimeFunction?_outOfFuel_store_iff types owner entry.source arguments fuel store replacement entry.compiled.returnType
            if replacement != store then
              assertTrue (decide (run fuel ≠ runRuntimeFunction? types owner entry.source arguments fuel replacement))
                "distinct stores were erased from full entry results"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
            if coreAt : Core.runStateful spent initial = .outOfFuel checkpoint then
              have _ := costed.compiled_residual_of_outOfFuel entry.provenance coreAt
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint))) "genuine entry resumption changed"
              if 0 < spent then
                assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store ∧
                  run (cost - spent) ≠ some (type, .done value store))) "resumption was replaced by restarting the entry"
              for middle in List.range (cost - spent) do
                let .outOfFuel next := Core.runStateful middle checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for remaining in List.range (cost - spent - middle + 3) do
                  assertTrue (decide (run (spent + middle + remaining) = some (type, Core.runStateful remaining next))) "three chunks changed real frames/environment"
            else throw (IO.userError "entry returned a checkpoint not belonging to its compiled Core")
          | _ => throw (IO.userError "below-cost entry checkpoint disappeared")
  else throw (IO.userError "positive arguments violated the exact type guard")

private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse)) "negative arguments actually matched"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.source.value.body, 60] do
      assertTrue ((prepareRuntimeFunction? types owner entry.source arguments).isNone &&
        (runRuntimeFunction? types owner entry.source arguments fuel store).isNone) "argument rejection produced a checkpoint"
private def reject (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError "semantic rejection did not fully parse")
  assertTrue (compileRuntimeFunction? types owner source).isNone "invalid whole recursive entry compiled"
  for arguments in [[], [boolArg true], [boolArg true, boolArg true, wordArg 7, wordArg 9], [boolArg true, boolArg false, wordArg 7, wordArg 9],
      [boolArg false, boolArg true, wordArg 7, wordArg 9]] do
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue ((prepareRuntimeFunction? types owner source arguments).isNone &&
          (runRuntimeFunction? types owner source arguments fuel store).isNone) "whole rejection depended on fuel or selected path"

def frontendParsedRecursiveRuntimeEntryTests : IO Unit := do
  let content := "{if(c){if(d){return x;}else{return y;}}else{return x;}}"
  let core : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.var 1) (.var 0)) (.var 1)
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let closureLeft : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", wordArg 9, wordArg Core.Word.maximum.val), ("Bool", boolArg true, boolArg false),
      ("Unit", unit, unit), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", closureLeft, closureRight)] do
    let entry ← compile (s!"function tree(c: Bool,d: Bool,x: {name},y: {name}) returns ({name})" ++ content)
      core left.type [.bool, .bool, left.type, right.type] 7
    for c in [false, true] do
      for d in [false, true] do
        checkCase entry [boolArg c, boolArg d, left, right] (if c then [true, d] else [false])
          (if c && !d then right.value else left.value) (if c then 7 else 4)
    for arguments in [[], [boolArg true], [left, boolArg true, boolArg false, right],
        [boolArg false, boolArg false, left, boolArg false], [boolArg true, boolArg false, left, right, unit]] do
      if arguments.map (·.type) != entry.compiled.inputs.context.values.reverse then rejectArguments entry arguments
  let arithmetic ← compile "function arithmetic(x: Word,c: Bool,y: Word,d: Bool) returns (Word){if(c){if(d){return ~x;}else{return x - y;}}else{return y;}}"
    (.ifE (.var 2) (.ifE (.var 0) (.unary .wordNot (.var 3)) (.binary .wordSub (.var 3) (.var 1))) (.var 1))
    .word [.word, .bool, .word, .bool] 11
  for (x, y) in [(9, 2), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checkCase arithmetic [wordArg x, boolArg c, wordArg y, boolArg d] (if c then [true, d] else [false])
          (.word (if c then if d then (word x).bitNot else (word x).sub (word y) else word y)) (if c then if d then 9 else 11 else 4)
  let mirror ← compile "function mirror(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){return x;}else{if(d){return y;}else{if(c){return x;}else{return y;}}}}"
    (.ifE (.var 3) (.var 1) (.ifE (.var 2) (.var 0) (.ifE (.var 3) (.var 1) (.var 0)))) .word [.bool, .bool, .word, .word] 10
  for (c, d) in [(true, false), (false, true), (false, false)] do
    checkCase mirror [boolArg c, boolArg d, wordArg 9, wordArg 2]
      (if c then [true] else if d then [false, true] else [false, false, false]) (.word (word (if c then 9 else 2))) (if c then 4 else if d then 7 else 10)
  let bare ← compile "function bare(c: Bool,d: Bool){if(c){if(d){return;}else{return;}}else{return;}}"
    (.ifE (.var 1) (.ifE (.var 0) .unit .unit) .unit) .unit [.bool, .bool] 7
  checkCase bare [boolArg true, boolArg false] [true, false] .unit 7
  let nominal ← compile ("function nominal(c: Bool,d: Bool,x: Opaque,y: Opaque) returns (Opaque)" ++ content)
    core (.namedData ⟨91⟩) [.bool, .bool, .namedData ⟨91⟩, .namedData ⟨91⟩] 7
  for argument in [unit, wordArg 7, boolArg false, closureLeft, (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument)] do
    rejectArguments nominal [boolArg true, boolArg false, argument, argument]
  for invalid in ["{return missing;}", "{return c;}", "{return x();}", "{}", "{if(d){return x;}}",
      "{return x;return y;}", "{if(x){return x;}else{return y;}}", "{return " ++ toString Core.wordModulus ++ ";}"] do
    reject ("function invalid(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){if(d){return x;}else" ++ invalid ++ "}else{return y;}}")
  for header in ["function wrong(c: Bool,d: Bool,x: Word,y: Word)", "function wrong(c: Bool,d: Bool,x: Word,y: Word) returns (Bool)",
      "function wrong(c: Bool,d: Bool,x: Word,y: Word) returns ()", "function wrong(c: Bool,d: Bool,x: Word,y: Word) returns (Word,Bool)",
      "function wrong<T>(c: Bool,d: Bool,x: Word,y: Word) returns (Word)", "function wrong(c: Bool,d: Bool,x: Word,y: Word,c: Bool) returns (Word)",
      "function wrong(c: Bool,d: Bool,comptime x: Word,y: Word) returns (Word)", "function wrong(c: Bool,d: Bool,x: Word,y: Unknown) returns (Word)"] do
    reject (header ++ content)
  reject "function wrapped(){{return;}}"
  reject "function extra(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){if(d){return x;}else{return y;}}else{return x;}return y;}"
  reject "function publicOnly(c: Bool,d: Bool,x: Word,y: Word) public returns (Word){if(c){if(d){return x;}else{return y;}}else{return x;}}" .contract
  for content in ["", "function f(c){return;}", "function f(){if(c){return;}else{return;}",
      "function f(){return}", "function f(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete or diagnosed source entered recursive runtime semantics"

end Tests
