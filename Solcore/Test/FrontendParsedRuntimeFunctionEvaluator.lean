import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Original complete declarations and actual arguments retain the full gate.
Independent body certificates, Core, triples and checkpoint expectations never
come from the new entry evaluator's output. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectEntry", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["Opaque"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩)]
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span.source = file.id ∧ source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) &&
        source.span.contains source.value.body.span) "original declaration range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete declaration: {content}")
  return source

private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store body value store cost
private def certify (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [atBody]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body

private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types owner source compiled
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameters : List Core.Ty) : IO Entry := do
  let source ← parsed content
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "positive original declaration did not compile")
  | some compiled =>
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "parameter shape changed")
        assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span) "original parameter positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameters.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameters.length ∧ Core.infer? parameters.reverse core = some type)) "independent Core/type or original parameter-only layout changed"
      let provenance := compileRuntimeFunction?_sound accepted
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ : ¬ RuntimeFunctionCompiles types owner source { compiled with core := wrong } := by
          intro alternative
          exact different (congrArg CompiledRuntimeFunction.core (alternative.result_unique provenance))
        assertTrue (decide (Core.infer? parameters.reverse wrong = some type)) "wrong-Core contrast lost the same type"
      else throw (IO.userError "wrong Core unexpectedly matched")
      return ⟨source, compiled, provenance⟩
private def checked (entry : Entry) (arguments : List TypedRuntimeArgument) (choices : List Bool)
    (value : Core.Value) (cost : Nat) : IO Unit := do
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types owner entry.source arguments with
    | none => throw (IO.userError "matching actual arguments did not prepare")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := prepareRuntimeFunction?_factorization types owner entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = entry.compiled.returnType ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value))) "arguments were rebound/reversed twice or locals leaked into parameters"
      assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner entry.source arguments =
        some (entry.compiled.returnType, value, cost))) "independent direct entry triple changed"
      for store in stores do
        let certificate ← certify prepared.inputs.names prepared.inputs.environment store entry.source.value.body choices
        assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent original-AST certificate changed"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation certificate.costed
        have computed := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        let reflected := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, computed⟩
        have _ := independent.deterministic reflected
        have _ := reflected.compiled_toSteps entry.provenance
        have _ := reflected.cost_le_fuelBound
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store (typedLetReturnTreeFuelBound entry.source.value.body) (Nat.le_refl _)
        for replacement in stores do
          if different : replacement ≠ store then
            have _ : ¬ RuntimeFunctionEvaluatesWithCost types owner entry.source arguments store prepared.returnType certificate.value replacement certificate.cost :=
              fun impossible => different (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp impossible).1
            pure ()
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types owner entry.source arguments fuel store
        for fuel in List.range (typedLetReturnTreeFuelBound entry.source.value.body + 3) do
          have _ := reflected.run_done_iff (fuel := fuel)
          have _ := reflected.run_outOfFuel_iff (fuel := fuel)
          have _ := reflected.compiled_run_done_iff (fuel := fuel) entry.provenance
          have _ := reflected.compiled_run_outOfFuel_iff (fuel := fuel) entry.provenance
          assertTrue (decide (run fuel = some (entry.compiled.returnType, Core.runStateful fuel initial))) "actual compiled Core/full result changed"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = entry.compiled.returnType ∧ v = value ∧ s = store)
            | some (t, .outOfFuel state) => decide (fuel < cost ∧ t = entry.compiled.returnType ∧ state.store = store)
            | _ => false) "independent threshold/value/own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
            if same : t = prepared.returnType then
              have _ := reflected.residual_of_outOfFuel (show run spent = some (prepared.returnType, .outOfFuel checkpoint) by simpa only [same] using exhausted)
              if actualOut : Core.runStateful spent initial = .outOfFuel checkpoint then
                have _ := reflected.compiled_residual_of_outOfFuel entry.provenance actualOut
                pure ()
              else throw (IO.userError "actual compiled path disagreed with entry checkpoint")
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "actual full checkpoint resumption changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "independent remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (t, .done value store))) "restart impersonated checkpoint resumption"
            else throw (IO.userError "checkpoint changed declared return type")
          | _ => throw (IO.userError "actual below-cost checkpoint missing")
  else throw (IO.userError "positive fixture changed ordered argument types")
private def rejected (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  match preparation : prepareRuntimeFunction? types owner source arguments with
  | some _ => throw (IO.userError "invalid whole gate prepared")
  | none =>
      have directNone := evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr preparation
      have _ := evaluateRuntimeFunctionWithCost?_eq_none_iff.mp directNone
      assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "preparation failure was hidden by raw success"
      for store in stores do
        for fuel in [0, 1, 60] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "whole rejection exposed a checkpoint"
private def spine (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := spine count (level + 1) annotation
      ("if(c){" ++ s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: {annotation}=y;return z{level};" ++ "}",
        .ifE (.var (level + 3)) (.letE (.var (if level = 0 then 1 else 0)) core) (.letE (.var level) (.var 0)))

def frontendParsedRuntimeFunctionEvaluatorTests : IO Unit := do
  for depth in [0, 1, 2, 5, 12] do
    let (body, core) := spine depth 0 "Word"
    let entry ← compile ("function deep(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}") core .word [.bool, .bool, .word, .word]
    for c in [false, true] do
      checked entry [boolArg c, boolArg false, wordArg 9, wordArg 2] (if depth = 0 then [] else if c then List.replicate depth true else [false])
        (w (if depth = 0 || c then 9 else 2)) (if depth = 0 then 1 else if c then 6 * depth + 1 else 7)
  let ordered ← compile "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let q: Word=z;return ~q;}else{let q: Word=y - z;return q;}}else{let z: Word=y - x;return y;}}"
    (.ifE (.var 3) (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1))) .word [.bool, .bool, .word, .word]
  for (x, y) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checked ordered [boolArg c, boolArg d, wordArg x, wordArg y] (if c then [true, d] else [false])
          (if c then if d then w (Core.wordModulus - 1 - (x + Core.wordModulus - y) % Core.wordModulus)
            else w (y + Core.wordModulus - (x + Core.wordModulus - y) % Core.wordModulus) else w y) (if c then if d then 19 else 21 else 11)
  let bare ← compile "function bare(){return;}" .unit .unit []
  checked bare [] [] .unit 1
  let strict ← compile "function strict(x: Word,y: Word) returns (Word){let unused: Word=x - y;return y;}"
    (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word [.word, .word]
  checked strict [wordArg 9, wordArg 2] [] (w 2) 8
  for store in stores do
    let env := [w 2, w 9]
    assertTrue (decide (runRuntimeFunction? types owner strict.source [wordArg 9, wordArg 2] 6 store = some (.word, .outOfFuel
      ⟨.ret (w 7), [.letBody (.var 1) env], store⟩) ∧
      runRuntimeFunction? types owner strict.source [wordArg 9, wordArg 2] 7 store = some (.word, .outOfFuel
        ⟨.eval (.var 1) (w 7 :: env), [], store⟩))) "strict unused initializer or actual captured tail scope changed"
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  for (name, x, y) in [("Cell", (⟨.cell .word, .cellRef .word 999, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 40, .cellRef⟩),
      ("Fn", closure, ⟨.function .word .word, .closure .word .word (.var 0) [], .closure .nil (.var rfl)⟩), ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    let entry ← compile (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
      "=x;let q: " ++ name ++ "=y;return z;}else{let z: " ++ name ++ "=y;return z;}}")
      (.ifE (.var 2) (.letE (.var 1) (.letE (.var 1) (.var 1))) (.letE (.var 0) (.var 0))) x.type [.bool, x.type, y.type]
    for c in [false, true] do checked entry [boolArg c, x, y] [c] (if c then x.value else y.value) (if c then 10 else 7)
  let unused ← compile "function unused(x: Word,y: Bool){return;}" .unit .unit [.word, .bool]
  checked unused [wordArg 9, boolArg true] [] .unit 1
  for arguments in [[], [wordArg 9], [boolArg true, wordArg 9], [boolArg true, boolArg true], [wordArg 9, boolArg true, wordArg 2]] do
    assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner [] [] unused.source.value.body = some (.unit, 1))) "unused argument contrast lost raw body success"
    rejected unused.source arguments
  for header in ["function generic<T>()", "function many() returns (Unit,Bool)", "function empty() returns ()", "function unknown() returns (Unknown)",
      "function duplicate(x: Word,x: Bool)", "function staged(comptime x: Word)", "function unknownParameter(x: Unknown)", "function wrong() returns (Word)"] do
    let source ← parsed (header ++ "{return;}")
    assertTrue (compileRuntimeFunction? types owner source).isNone "invalid header/parameter/return contract compiled"
    for store in stores do
      let certificate ← certify [] [] store source.value.body []
      assertTrue (decide (certificate.value = .unit ∧ certificate.cost = 1 ∧
        evaluateTypedLetReturnTreeWithCost? owner [] [] source.value.body = some (.unit, 1))) "whole rejection lost independently successful raw body"
    for arguments in [[], [wordArg 9], [wordArg 9, boolArg true]] do rejected source arguments
  for (result, body) in [("Bool", "{if(c){let z: Word=x;return z;}else{return x;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{let z: Unknown=x;return z;}}"),
      ("Word", "{if(c){let z: Bool=x;return z;}else{return x;}}"),
      ("Word", "{if(c){let x: Word=x;return x;}else{return x;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{return missing;}}"),
      ("Word", "{if(c){let z: Word=x;return z;}else{return c;}}") ] do
    let source ← parsed (s!"function raw(c: Bool,x: Word) returns ({result})" ++ body)
    let arguments := [boolArg true, wordArg 9]
    let some actual := bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments
      | throw (IO.userError "raw/whole contrast lost original actual parameters")
    for store in stores do
      let certificate ← certify actual.names actual.environment store source.value.body [true]
      assertTrue (decide (certificate.value = w 9 ∧ certificate.cost = 7 ∧ actual.environment.values = arguments.reverse.map (·.value) ∧
        evaluateTypedLetReturnTreeWithCost? owner actual.names actual.environment source.value.body = some (w 9, 7))) "raw selected certificate changed"
    rejected source arguments
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨_, typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for depth in [1, 3] do
      let (body, core) := spine depth 0 name
      let entry ← compile (s!"function nominal(c: Bool,d: Bool,x: {name},y: {name}) returns ({name})" ++ "{" ++ body ++ "}") core type [.bool, .bool, type, type]
      for arguments in [[], [boolArg true, boolArg false, wordArg 9, wordArg 2], [boolArg true, boolArg false, closure, closure]] do rejected entry.source arguments
  for content in ["function missing(x){return x;}", "function unfinished(){return;", "function trailing(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired entry meaning"

end Tests
