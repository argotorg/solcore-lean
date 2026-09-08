import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionExecutionFactorization

/-! The common body interface preserves both original runners at every fuel.
Singleton and terminal-conditional profiles retain their own Core, costs and
actual values; current runtime entries still accept only singleton returns. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalReturnBody", by decide⟩], by decide⟩⟩, 28⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def store : Core.Store := [.word (word 91), .bool true]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def arguments (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-return.sol"⟩, content }
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
private def body (content : String) : IO Syntax.Block := do
  let some result ← parsed? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free block")
  return result

private def checkBody (inputs : LocalInputs) (source : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let singleton := match source.value with | [⟨_, .returnStmt _⟩] => true | _ => false
  let originalCheck := if singleton then inputs.checkReturnBody? source else inputs.checkConditionalReturnBody? source
  let excludedCheck := if singleton then inputs.checkConditionalReturnBody? source else inputs.checkReturnBody? source
  let originalRun := if singleton then inputs.runReturnBody? else inputs.runConditionalReturnBody?
  let excludedRun := if singleton then inputs.runConditionalReturnBody? else inputs.runReturnBody?
  let originalBound := if singleton then returnBodyFuelBound source else conditionalReturnBodyFuelBound source
  assertTrue (decide (inputs.checkTerminalReturnBody? source = some (core, type) ∧ originalCheck = some (core, type)))
    s!"wrong exact common/original Core and type: {reprStr (inputs.checkTerminalReturnBody? source)}"
  assertTrue (terminalReturnBodyFuelBound source == bound && originalBound == bound) "dispatch added source fuel"
  assertTrue excludedCheck.isNone "an existing separate checker broadened its shape"
  let initial := Core.State.initial core inputs.environment.values store
  let run := fun fuel => inputs.runTerminalReturnBody? fuel source store
  for fuel in List.range (bound + 3) do
    assertTrue (decide (run fuel = originalRun fuel source store ∧
      run fuel = some (type, Core.runStateful fuel initial))) "common runner changed the original full same-fuel result"
    assertTrue (excludedRun fuel source store).isNone "an existing runner broadened its shape"
    assertTrue (match run fuel with
      | some (actualType, .done actualValue finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = store)
      | some (actualType, .outOfFuel state) => decide (fuel < cost ∧ actualType = type ∧ state.store = store)
      | _ => false) "common runner added cost or changed actual values/stores"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
    for remaining in List.range (cost - spent + 3) do
      assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)))
        "same-state resumption changed a frame/environment or the full result"
  match source.value, core with
  | [⟨statementSpan, .returnStmt expression⟩], _ =>
      assertTrue (source.span.contains statementSpan) "original return span changed"
      match expression with
      | none => assertTrue (decide (core = .unit ∧ type = .unit ∧ cost = 1)) "bare return gained an operation"
      | some child =>
          for fuel in List.range (bound + 3) do
            assertTrue (decide (run fuel = inputs.run? fuel child store)) "expression return gained overhead"
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩], .ifE conditionCore thenCore elseCore =>
      assertTrue (decide (inputs.check? condition = some (conditionCore, .bool) ∧
        inputs.checkReturnBody? thenBody = some (thenCore, type) ∧
        inputs.checkReturnBody? elseBody = some (elseCore, type))) "union recursively changed the original arm adapter"
      assertTrue (source.span.contains statementSpan && statementSpan.contains condition.span &&
        statementSpan.contains thenBody.span && statementSpan.contains elseBody.span &&
        decide (condition.span.endByte ≤ thenBody.span.startByte ∧ thenBody.span.endByte ≤ elseBody.span.startByte))
        "canonical spans or written branch order changed"
      let first : Core.State := ⟨.eval conditionCore inputs.environment.values,
        [.ifBranches thenCore elseCore inputs.environment.values], store⟩
      assertTrue (decide (run 1 = some (type, .outOfFuel first))) "conditional frame changed at the common boundary"
  | _, _ => throw (IO.userError "accepted something outside both terminal profiles")
private def checkText (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  checkBody inputs (← body content) core type value cost bound

private def checkEntry (content : String) (supplied : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "complete declaration did not parse")
  let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements supplied
    | throw (IO.userError "actual declaration arguments did not bind")
  assertTrue (decide (inputs.environment.values = supplied.reverse.map (·.value))) "actual argument order changed"
  checkBody inputs declaration.value.body core type value cost bound
  match declaration.value.body.value with
  | [⟨_, .returnStmt _⟩] =>
      match accepted : compileRuntimeFunction? types owner declaration with
      | none => throw (IO.userError "old singleton entry stopped compiling")
      | some compiled =>
          let provenance := compileRuntimeFunction?_sound accepted
          let some prepared := prepareRuntimeFunction? types owner declaration supplied
            | throw (IO.userError "actual singleton arguments stopped preparing")
          assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ prepared.core = core ∧
            prepared.inputs.environment.values = supplied.reverse.map (·.value))) "entry lost actual compilation projection"
          if matching : supplied.map (·.type) = compiled.inputs.context.values.reverse then
            have _ := provenance.run_eq supplied matching bound store
            for fuel in List.range (bound + 3) do
              assertTrue (decide (runRuntimeFunction? types owner declaration supplied fuel store =
                inputs.runTerminalReturnBody? fuel declaration.value.body store)) "old singleton entry behavior changed"
          else throw (IO.userError "actual singleton argument type order changed")
  | _ =>
      assertTrue (returnBodyFuelBound declaration.value.body == 0) "old entry bound silently broadened"
      assertTrue ((compileRuntimeFunction? types owner declaration).isNone &&
        (prepareRuntimeFunction? types owner declaration supplied).isNone) "union became runtime entry integration"
      for fuel in [0, cost, bound, bound + 20] do
        assertTrue (runRuntimeFunction? types owner declaration supplied fuel store).isNone
          "old entry runner accepted a terminal statement conditional"

private theorem selectedPiecesEvaluate (inputs : LocalInputs) (blockSpan statementSpan : Syntax.SourceSpan)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block) (choice : Bool) (type : Core.Ty) (value : Core.Value)
    (conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store))
    (branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (type, .done value store)) :
    TerminalReturnBodyEvaluates inputs.names inputs.environment store
      ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value store := by
  obtain ⟨_, _, conditionCosted, _⟩ := LocalInputs.run?_done_iff_typed_cost.mp conditionDone
  cases choice with
  | false =>
      change inputs.runReturnBody? 40 elseBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .conditional (.ifFalse conditionCosted.erase branchCosted.erase)
  | true =>
      change inputs.runReturnBody? 40 thenBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .conditional (.ifTrue conditionCosted.erase branchCosted.erase)

private def checkSkipped (inputs : LocalInputs) (choice : Bool) (invalid : String) : IO Unit := do
  let content := if choice then "{ if(c) { return t; } else { return " ++ invalid ++ "; } }"
    else "{ if(c) { return " ++ invalid ++ "; } else { return f; } }"
  let source ← body content
  assertTrue (inputs.checkTerminalReturnBody? source).isNone "invalid unselected arm checked"
  assertTrue (inputs.checkConditionalReturnBody? source).isNone "common rejection differed from original conditional rejection"
  for fuel in [0, 4, terminalReturnBodyFuelBound source, 40] do
    assertTrue (inputs.runTerminalReturnBody? fuel source store).isNone "numeric bound bypassed whole-arm rejection"
  match source.value with
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩] =>
      let expected := Core.Value.word (word (if choice then 7 else 9))
      if conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store) then
        if branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (.word, .done expected store) then
          have _ := selectedPiecesEvaluate inputs source.span statementSpan condition thenBody elseBody
            choice .word expected conditionDone branchDone
          pure ()
        else throw (IO.userError "selected valid arm did not independently execute")
      else throw (IO.userError "actual condition selected the wrong branch")
  | _ => throw (IO.userError "skipped-arm fixture lost its canonical conditional")

private def checkRejected (inputs : LocalInputs) (content : String) (zeroShapeBound : Bool) : IO Unit := do
  let source ← body content
  assertTrue (inputs.checkTerminalReturnBody? source).isNone s!"{content}: unsupported body checked"
  assertTrue ((inputs.checkReturnBody? source).isNone && (inputs.checkConditionalReturnBody? source).isNone)
    "common rejection differed from the two original checker failures"
  if zeroShapeBound then assertTrue (terminalReturnBodyFuelBound source == 0) "unsupported outer shape gained a bound"
  for fuel in [0, 1, 4, 13, terminalReturnBodyFuelBound source, 50] do
    assertTrue ((inputs.runTerminalReturnBody? fuel source store).isNone &&
      (inputs.runReturnBody? fuel source store).isNone && (inputs.runConditionalReturnBody? fuel source store).isNone)
      "structural/type rejection or original runner agreement depended on fuel"

def frontendParsedTerminalReturnBodiesTests : IO Unit := do
  checkText LocalInputs.empty " /* unit */ { return; } " .unit .unit .unit 1 1
  checkText LocalInputs.empty "{ return ((0007)); }" (.word (word 7)) .word (.word (word 7)) 1 1
  checkEntry "function bare() returns (Unit) { return; }" [] .unit .unit .unit 1 1
  for choice in [false, true] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      "function parameters(c: Bool, t: Word, f: Word) returns (Word) { return t; }"
      | throw (IO.userError "actual parameter declaration did not parse")
    let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "typed Word parameters did not bind")
    checkText inputs "{ return; }" .unit .unit .unit 1 1
    checkText inputs "{ return t; }" (.var 1) .word (.word (word 7)) 1 1
    checkText inputs "{ return ~t; }" (.unary .wordNot (.var 1)) .word (.word ((word 7).bitNot)) 3 3
    checkText inputs "{ return t + f; }" (.binary .wordAdd (.var 1) (.var 0)) .word (.word (word 16)) 5 5
    checkText inputs "{ return c ? t * f : f; }" (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      .word (.word (word (if choice then 63 else 9))) (if choice then 8 else 4) 8
    checkText inputs "{ return c && t < f; }" (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false))
      .bool (.bool choice) (if choice then 14 else 4) 14
    let simple := Core.Expr.ifE (.var 2) (.var 1) (.var 0)
    let simpleBody ← body "{ if(c){return t;}else{return f;} }"
    let pending : Core.State := ⟨.ret (.bool choice), [.ifBranches (.var 1) (.var 0) inputs.environment.values], store⟩
    assertTrue (decide (inputs.runTerminalReturnBody? 2 simpleBody store = some (.word, .outOfFuel pending) ∧
      Core.runStateful 0 pending = .outOfFuel pending ∧
      Core.runStateful 1 pending = .outOfFuel ⟨.eval (if choice then .var 1 else .var 0) inputs.environment.values, [], store⟩ ∧
      Core.runStateful 0 { pending with continuation := [] } = .done (.bool choice) store))
      "pending conditional selection or dropped-frame counterexample changed"
    checkText inputs " /* lead */ { if /* guard */ (c) { return ((t)); } else { return f; } }"
      simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkEntry "function choose(c: Bool, t: Word, f: Word) returns (Word) { if(c){return t;}else{return f;} }"
      (arguments choice) simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkText inputs "{ if(c){return t * f + t;}else{return f;} }"
      (.ifE (.var 2) (.binary .wordAdd (.binary .wordMul (.var 1) (.var 0)) (.var 1)) (.var 0))
      .word (.word (word (if choice then 70 else 9))) (if choice then 12 else 4) 12
    checkText inputs "{ if(c){return t < f;}else{return t >= f;} }"
      (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0))))
      .bool (.bool choice) (if choice then 14 else 16) 16
    checkText inputs "{ if(c && t < f){return t + f;}else{return f;} }"
      (.ifE (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false)) (.binary .wordAdd (.var 1) (.var 0)) (.var 0))
      .word (.word (word (if choice then 16 else 9))) (if choice then 21 else 7) 21
    checkText inputs "{ if(c){return c ? t - f : f;}else{return c ? t : f;} }"
      (.ifE (.var 2) (.ifE (.var 2) (.binary .wordSub (.var 1) (.var 0)) (.var 0))
        (.ifE (.var 2) (.var 1) (.var 0))) .word
      (.word (if choice then (word 7).sub (word 9) else word 9)) (if choice then 11 else 7) 11
    for invalid in ["missing", "c", "t / f", "t(c)", s!"{Core.wordModulus}"] do
      checkSkipped inputs choice invalid
    for content in ["{}", "{ return t; return f; }", "{ t; return f; }", "{ return t; missing; }", "{ if(c){return t;} }",
        "{ t; if(c){return t;}else{return f;} }", "{ if(c){return t;}else{return f;} return t; }",
        "{ if(c){return t;}else{return f;} if(c){return f;}else{return t;} }",
        "{ { if(c){return t;}else{return f;} } }"] do checkRejected inputs content true
    for content in ["{ return missing; }", "{ return t / f; }", "{ return c ? t : missing; }",
        "{ return c ? t : c; }", "{ if(t){return t;}else{return f;} }", "{ if(missing){return t;}else{return f;} }",
        "{ if(c){return t;}else{return c;} }", "{ if(c){return;}else{return t;} }",
        "{ if(c){}else{return f;} }", "{ if(c){return t;}else{} }",
        "{ if(c){t; return t;}else{return f;} }", "{ if(c){return t; f;}else{return f;} }",
        "{ if(c){return t; return f;}else{return f;} }", "{ if(c){return t;}else{return f; t;} }",
        "{ if(c){if(c){return t;}else{return f;}}else{return f;} }",
        "{ if(c){return t;}else{if(c){return t;}else{return f;}} }",
        "{ if(c){return t;}else{while(c){return f;}} }"] do checkRejected inputs content false
    checkText inputs "{ if(c){return;}else{return;} }" (.ifE (.var 2) .unit .unit) .unit .unit 4 4
  checkText LocalInputs.empty "{ if(0 < 1){return;}else{return;} }"
    (.ifE (lt (.word (word 0)) (.word (word 1))) .unit .unit) .unit .unit 14 14
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", (⟨.word, .word Core.Word.maximum, .word⟩ : TypedRuntimeArgument),
      ⟨.word, .word (word (2 ^ 255)), .word⟩), ("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight),
      ("Bool", (⟨.bool, .bool true, .bool⟩ : TypedRuntimeArgument), ⟨.bool, .bool false, .bool⟩)] do
    for choice in [false, true] do
      checkEntry (s!"function expression(c: Bool, t: {name}, f: {name}) returns ({name})" ++
        " { return c ? t : f; }") [⟨.bool, .bool choice, .bool⟩, left, right]
        (.ifE (.var 2) (.var 1) (.var 0)) left.type (if choice then left.value else right.value) 4 4
      checkEntry (s!"function values(c: Bool, t: {name}, f: {name}) returns ({name})" ++
        " { if(c){return t;}else{return f;} }") [⟨.bool, .bool choice, .bool⟩, left, right]
        (.ifE (.var 2) (.var 1) (.var 0)) left.type (if choice then left.value else right.value) 4 4
      checkEntry "function units(c: Bool, u: Unit) returns (Unit) { if(c){return;}else{return u;} }"
        [⟨.bool, .bool choice, .bool⟩, unit] (.ifE (.var 1) .unit (.var 0)) .unit .unit 4 4
  for content in ["", "if(c){return t;}else{return f;}", "{ if(c){return t;}else{return f;} ",
      "{ if(c){return t}else{return f;} }", "{ if(c){return t;}else }", "{ if(c){return t;}else{return f;} } trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "malformed or incompletely consumed block accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(c: Bool) returns (Unit) { if(c){return;}else{return;} } trailing").isNone
    "function helper accepted only a valid prefix"

end Tests
