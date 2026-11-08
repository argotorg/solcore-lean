import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Resolved.LocalScope

/-!
# Recursive runtime entry tests

Recursive runtime entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveRuntimeEntries
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

private def wrappedBare : IO Unit := do
  let some source ← parsed? "function wrapped(){{return;}}" | throw (IO.userError "original wrapper did not parse")
  match atBody : source.value.body with
  | ⟨outer, [⟨inner, .block [⟨returned, .returnStmt none⟩]⟩]⟩ =>
    assertTrue (outer.contains inner && inner.contains returned && decide (outer ≠ inner)) "original wrapper ranges changed"
    if shape : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
        source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none ∧
        source.value.signature.returnsClause = none ∧ source.value.signature.parameters.elements = [] then
      have compilation : RuntimeFunctionCompiles types owner source ⟨.empty, .unit, .unit⟩ :=
        ⟨⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, by rw [shape.2.2.2.2.1]; exact .absent⟩,
          by rw [shape.2.2.2.2.2]; exact .nil,
          by rw [atBody]; exact .block (.single .bare)⟩
      have _ := compilation.complete
      let some prepared := prepareRuntimeFunction? types owner source [] | throw (IO.userError "wrapped bare entry rejected")
      assertTrue (decide (prepared.core = .unit ∧ prepared.returnType = .unit ∧ prepared.inputs.bindings = [] ∧
        typedLetReturnTreeFuelBound source.value.body = 1) &&
        (prepared.inputs.runTerminalReturnTree? 1 source.value.body []).isNone) "wrapper changed Core/rows/bound or old adapter"
      for store in stores do
        have path (k : List Core.Frame) : Core.Steps 1 ⟨.eval .unit [], k, store⟩ ⟨.ret .unit, k, store⟩ := .cons .unit .refl
        have _ := path []
        for fuel in List.range 4 do
          assertTrue (decide (runRuntimeFunction? types owner source [] fuel store = some (.unit,
            if fuel = 0 then .outOfFuel (.initial .unit [] store) else .done .unit store))) "wrapper added a transition"
        assertTrue (decide (Core.runStateful 1 (.initial .unit [] store) = .done .unit store)) "checkpoint zero failed to resume"
    else throw (IO.userError "original empty header/parameter fields changed")
  | _ => throw (IO.userError "original singleton wrapper was rewritten")

def frontendParsedRecursiveRuntimeEntryTests : IO Unit := do
  wrappedBare
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
  reject "function extra(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){if(d){return x;}else{return y;}}else{return x;}return y;}"
  reject "function publicOnly(c: Bool,d: Bool,x: Word,y: Word) public returns (Word){if(c){if(d){return x;}else{return y;}}else{return x;}}" .contract
  for content in ["", "function f(c){return;}", "function f(){if(c){return;}else{return;}",
      "function f(){return}", "function f(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete or diagnosed source entered recursive runtime semantics"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveRuntimeEntryProperties
/-! Value-free recursive compilation and actual-argument execution are distinct
contracts. Original parameter order, exact Core and genuine states are retained. -/

set_option autoImplicit false

namespace Tests.FrontendRecursiveRuntimeEntry

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private theorem yc : "y" ≠ "c" := by decide
private theorem xc : "x" ≠ "c" := by decide
private theorem yx : "y" ≠ "x" := by decide
private theorem i20 : id 2 ≠ id 0 := by decide
private theorem i10 : id 1 ≠ id 0 := by decide
private theorem i21 : id 2 ≠ id 1 := by decide
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive-entry.sol"⟩, 101, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def body : Nat → Syntax.Block
  | 0 => returned "x"
  | depth + 1 => branch (body depth) (returned "y")
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def parameters := [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def declaration (depth : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "recursive"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, body depth⟩⟩
private def staticInputs (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type).bindFresh owner "y" type
private def compiled (depth : Nat) (type : Core.Ty) : CompiledRuntimeFunction := ⟨staticInputs type, core depth, type⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (staticInputs type) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates (staticInputs type).names (staticInputs type).context (body depth) (core depth) type := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail yx .head)) (.var (.tail i21 .head)) (.var (.tail i21 .head)))
  | succ depth ih =>
    exact .conditional (.identifier (.tail yc (.tail xc .head)))
      (.var (.tail i20 (.tail i10 .head))) (.var (.tail i20 (.tail i10 .head))) ih
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (depth : Nat) (type : Core.Ty) :
    RuntimeFunctionCompiles (types type) owner (declaration depth) (compiled depth type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, declared type, TypedLetReturnBodyElaborates.returnTree <| .terminal (elaborated depth type)⟩

theorem arbitrary_depth_and_types_compile_from_independent_whole_source_provenance
    (depth : Nat) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    RuntimeFunctionCompiles (types type) owner (declaration depth) (compiled depth type) ∧
    compileRuntimeFunction? (types type) owner (declaration depth) = some (compiled depth type) ∧
    (compiled depth type).inputs.context.values = [type, type, .bool] ∧ Core.HasType [type, type, .bool] (core depth) type definitions := by
  refine ⟨compilation depth type, (compilation depth type).complete, rfl, ?_⟩
  induction depth with
  | zero => exact .var rfl
  | succ depth ih => exact .ifE (.var rfl) ih (.var rfl)

theorem nominal_compilation_does_not_manufacture_an_actual_argument (depth : Nat) (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (declaration depth) = some (compiled depth (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation depth _).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem same_typed_wrong_core_and_arbitrary_records_do_not_supply_provenance
    (depth : Nat) (type : Core.Ty) (candidate : CompiledRuntimeFunction)
    (provenance : RuntimeFunctionCompiles (types type) owner (declaration depth) candidate) :
    candidate = compiled depth type ∧ Core.HasType [type, type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (declaration depth) { compiled depth type with core := .var 0 } := by
  refine ⟨provenance.result_unique (compilation depth type), .var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation depth type))
  cases depth <;> cases wrong

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (choice : Bool) (left right : Actual type) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨type, left.val, left.property⟩, ⟨type, right.val, right.property⟩]
private def inputs {type : Core.Ty} (choice : Bool) (left right : Actual type) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "x" type left.val left.property).bindFresh
    owner "y" type right.val right.property
private def prepared {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) : PreparedRuntimeFunction :=
  ⟨inputs choice left right, core depth, type⟩
private theorem preparation {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) :
    RuntimeFunctionPrepares (types type) owner (declaration depth) (arguments choice left right) (prepared depth choice left right) :=
  ⟨(compilation depth type).header, .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal (elaborated depth type)⟩
private theorem conditionCost {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail yc (.tail xc .head)) (.tail i20 (.tail i10 .head))
private theorem trueBodyCost {type : Core.Ty} (depth : Nat) (left right : Actual type) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost (inputs true left right).names (inputs true left right).environment
      store (body depth) left.val store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail yx .head) (.tail i21 .head)))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, body, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private def required (depth : Nat) (choice : Bool) : Nat := if choice then 3 * (depth + 1) + 1 else 4
private def result {type : Core.Ty} (choice : Bool) (left right : Actual type) : Core.Value := if choice then left.val else right.val
private theorem costed {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration (depth + 1)) (arguments choice left right)
      store type (result choice left right) store (required depth choice) := by
  apply RuntimeFunctionEvaluatesWithCost.intro (preparation (depth + 1) choice left right)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  have y : LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "y") right.val store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse (conditionCost false left right store) (.single (.expression y))
  · exact trueBodyCost (depth + 1) left right store

theorem actual_preparation_and_factorization_keep_source_argument_order_exactly_once
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (fuel : Nat) (store : Core.Store) :
    prepareRuntimeFunction? (types type) owner (declaration depth) (arguments choice left right) = some (prepared depth choice left right) ∧
    (prepared depth choice left right).toCompiled = compiled depth type ∧
    (prepared depth choice left right).inputs.environment.values = [right.val, left.val, .bool choice] ∧
    runRuntimeFunction? (types type) owner (declaration depth) (arguments choice left right) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (core depth) ((arguments choice left right).reverse.map (·.value)) store)) :=
  ⟨(preparation depth choice left right).complete, rfl, rfl, (compilation depth type).run_eq _ rfl fuel store⟩

theorem independent_recursive_cost_gives_all_entry_and_compiled_thresholds_and_safety
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) (fuel : Nat)
    (error : Core.MachineFault) (state : Core.State) :
    Core.Steps (required depth choice) (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store)
      (Core.State.final (result choice left right) store) ∧ Core.ValueHasType (result choice left right) type ∧
    (runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel store =
      some (type, .done (result choice left right) store) ↔ required depth choice ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required depth choice) ∧
    Core.runStateful fuel (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store) ≠ .fault error state :=
  ⟨(costed depth choice left right store).compiled_toSteps (compilation _ type), (costed depth choice left right store).preserves_type,
    (costed depth choice left right store).run_done_iff, (costed depth choice left right store).run_outOfFuel_iff,
    (compilation (depth + 1) type).compiled_never_faults (arguments choice left right) rfl fuel store error state⟩

private theorem treeBound (depth : Nat) : terminalReturnTreeFuelBound (body depth) = 3 * depth + 1 := by
  induction depth with
  | zero => simp [body, returned, ref, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | succ depth ih =>
    simp only [body, branch, terminalReturnTreeFuelBound, ih, returned, returnBodyFuelBound,
      ref, localExpressionFuelBound]
    omega
private theorem recursiveBound (depth : Nat) : typedLetReturnTreeFuelBound (body depth) = 3 * depth + 1 := by
  induction depth with
  | zero => simp [body, returned, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | succ depth ih =>
    simp only [body, branch, typedLetReturnTreeFuelBound, ih, returned, returnBodyFuelBound, ref, localExpressionFuelBound]
    omega
theorem all_three_entry_bound_contracts_use_the_recursive_bound
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    required depth choice ≤ typedLetReturnTreeFuelBound (declaration (depth + 1)).value.body ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration (depth + 1))
      (arguments choice left right) (3 * (depth + 1) + 1) store = some (type, .done value store)) ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration (depth + 1))
      (arguments choice left right) (3 * (depth + 1) + 1) store = some (type, .done value store) ∧
      Core.runStateful (3 * (depth + 1) + 1) (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store) = .done value store) := by
  have enough : typedLetReturnTreeFuelBound (declaration (depth + 1)).value.body ≤ 3 * (depth + 1) + 1 :=
    Nat.le_of_eq (recursiveBound _)
  exact ⟨(costed depth choice left right store).cost_le_fuelBound,
    (preparation _ choice left right).hasType.run_done_of_fuelBound store _ enough,
    (compilation _ type).run_done_of_fuelBound (arguments choice left right) rfl store _ enough⟩

theorem old_nonrecursive_bound_is_insufficient_for_the_new_deep_entry
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) :
    terminalReturnTreeFuelBound (body 2) = 7 ∧ terminalReturnBodyFuelBound (body 2) = 4 ∧
    (∃ checkpoint, runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 4 store = some (type, .outOfFuel checkpoint)) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments false left right) 4 store = some (type, .done right.val store) :=
  ⟨treeBound 2, by simp [body, branch, returned, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound],
    (costed 1 true left right store).run_outOfFuel_iff.mpr (by decide),
    (costed 1 false left right store).run_done_iff.mpr (by decide)⟩

private def checkpoint {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (core depth) (.var 0) [right.val, left.val, .bool choice]], store⟩
private theorem exhausted {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) 2 store =
      some (type, .outOfFuel (checkpoint depth choice left right store)) := by
  rw [(compilation _ type).run_eq (arguments choice left right) rfl 2 store]
  cases choice <;> rfl
theorem recursive_entry_resumes_its_real_checkpoint_and_exact_compiled_residual
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) 2 store =
      some (type, .outOfFuel (checkpoint depth choice left right store)) ∧
    Core.Steps (required depth choice - 2) (checkpoint depth choice left right store) (Core.State.final (result choice left right) store) ∧
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) (2 + additional) store =
      some (type, Core.runStateful additional (checkpoint depth choice left right store)) :=
  ⟨exhausted depth choice left right store, ((costed depth choice left right store).residual_of_outOfFuel
      (exhausted depth choice left right store)).2, runRuntimeFunction?_resume (exhausted depth choice left right store) additional⟩

theorem owner_changes_keep_full_checkpoints_while_store_replay_keeps_its_own_store
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (otherOwner : Resolved.DeclarationId)
    (first replacement : Core.Store) (fuel : Nat) :
    runRuntimeFunction? (types type) otherOwner (declaration (depth + 1)) (arguments choice left right) 2 first =
      some (type, .outOfFuel (checkpoint depth choice left right first)) ∧
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration (depth + 1)) (arguments choice left right)
      replacement type (result choice left right) replacement (required depth choice) ∧
    ((∃ state, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel first = some (type, .outOfFuel state)) ↔
      ∃ state, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel replacement = some (type, .outOfFuel state)) :=
  ⟨(runRuntimeFunction?_owner_eq (types type) otherOwner owner _ _ 2 first).trans (exhausted depth choice left right first),
    (costed depth choice left right first).change_store replacement, runRuntimeFunction?_outOfFuel_store_iff (types type) owner _ _ fuel first replacement type⟩

theorem multiple_chunks_retain_the_actual_compiled_remainder
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (checkpoint 1 true left right store) = .outOfFuel (checkpoint 0 true left right store) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 5 store =
      some (type, .outOfFuel (checkpoint 0 true left right store)) ∧
    Core.Steps 2 (checkpoint 0 true left right store) (Core.State.final left.val store) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) (5 + additional) store =
      some (type, Core.runStateful additional (checkpoint 0 true left right store)) := by
  have machine : Core.runStateful 5 (Core.State.initial (compiled 2 type).core
      ((arguments true left right).reverse.map (·.value)) store) = .outOfFuel (checkpoint 0 true left right store) := rfl
  have actual : runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 5 store =
      some (type, .outOfFuel (checkpoint 0 true left right store)) :=
    ((compilation 2 type).run_eq (arguments true left right) rfl 5 store).trans (congrArg (fun result => some (type, result)) machine)
  exact ⟨rfl, actual, ((costed 1 true left right store).compiled_residual_of_outOfFuel (compilation 2 type) machine).2,
    runRuntimeFunction?_resume actual additional⟩

theorem actual_typed_cells_and_captured_closures_return_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word)) owner (declaration 2)
      (arguments true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩) 7 store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    runRuntimeFunction? (types (.function .bool .word)) owner (declaration 2)
      (arguments true ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩
        ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) 7 store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(costed 1 true _ _ store).run_done_iff.mpr (by decide), (costed 1 true _ _ store).run_done_iff.mpr (by decide)⟩

theorem missing_or_wrong_ordered_actual_types_do_not_follow_from_static_compilation
    (depth : Nat) (type : Core.Ty) (supplied : List TypedRuntimeArgument)
    (mismatch : supplied.map (·.type) ≠ [.bool, type, type]) (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (types type) owner (declaration depth) = some (compiled depth type) ∧
    runRuntimeFunction? (types type) owner (declaration depth) supplied fuel store = none := by
  refine ⟨(compilation depth type).complete, ?_⟩
  rw [runRuntimeFunction?_factorization, (compilation depth type).complete]
  simp only [bind, Option.bind_some, show (compiled depth type).inputs.context.values.reverse = [.bool, type, type] from rfl,
    if_neg mismatch]

private def publicEntry (depth : Nat) : Syntax.FunctionDecl :=
  ⟨span, ⟨{ (declaration depth).value.signature with modifiers := ⟨some span, none⟩ }, body depth⟩⟩
private def duplicateEntry (depth : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨{ (declaration depth).value.signature with parameters := ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "x" "Payload"]⟩ }, body depth⟩⟩
theorem whole_header_and_complete_parameter_policy_still_precede_deep_body_acceptance
    (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates (staticInputs type).names (staticInputs type).context (body depth) (core depth) type ∧
    compileRuntimeFunction? (types type) owner (publicEntry depth) = none ∧
    compileRuntimeFunction? (types type) owner (duplicateEntry depth) = none :=
  by
    refine ⟨elaborated depth type, rfl, ?_⟩
    apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    cases accepted.parameters with
    | cons _ _ tail => cases tail with
      | cons _ _ tail => cases tail with
        | cons _ unused _ => exact unused (by change "x" ∈ ["x", "c"]; decide)

end Tests.FrontendRecursiveRuntimeEntry
end
