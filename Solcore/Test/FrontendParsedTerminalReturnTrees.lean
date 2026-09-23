import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.TypedLetReturnTree

/-! Recursive bodies are checked statically using actual parsed parameters.
No values, tree execution or costs are assumed by recursive entry compilation.
Source depth, unlike the depth of its lowered Core, controls the old body profile. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StaticReturnTrees", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Unit"], .unit), (["Word"], .word), (["Fn"], .function .word (.namedData ⟨91⟩))]
private def parameterText : String := "c: Bool,d: Bool,x: Opaque,y: Opaque,u: Unit,w: Word,f: Fn"
private def parameterTypes : List Core.Ty :=
  [.bool, .bool, .namedData ⟨91⟩, .namedData ⟨91⟩, .unit, .word, .function .word (.namedData ⟨91⟩)]

private structure TreeFixture where
  content : String
  core : Core.Expr
  depth : Nat
private def leaf (expression : String) (core : Core.Expr) : TreeFixture :=
  ⟨"{return " ++ expression ++ ";}", core, 0⟩
private def node (condition : String) (core : Core.Expr) (left right : TreeFixture) : TreeFixture :=
  ⟨"{if(" ++ condition ++ ")" ++ left.content ++ "else" ++ right.content ++ "}",
    .ifE core left.core right.core, max left.depth right.depth + 1⟩
private def spine : Nat → Bool → TreeFixture → TreeFixture → TreeFixture
  | 0, _, selected, _ => selected
  | depth + 1, right, selected, other =>
      let nested := spine depth (!right) selected other
      if right then node "d" (.var 5) other nested else node "c" (.var 6) nested other
private def bury : Nat → Bool → String → String
  | 0, _, content => content
  | depth + 1, right, content =>
      let nested := bury depth (!right) content
      if right then "{if(d){return y;}else" ++ nested ++ "}"
      else "{if(c)" ++ nested ++ "else{return x;}}"
private def buriedCore : Nat → Bool → Core.Expr → Core.Expr
  | 0, _, core => core
  | depth + 1, right, core =>
      let nested := buriedCore depth (!right) core
      if right then .ifE (.var 5) (.var 3) nested else .ifE (.var 6) nested (.var 4)

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-static-return-trees.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def staticInputs (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  match accepted : declareRuntimeParameters? types owner source.value.signature.parameters.elements with
  | none => throw (IO.userError "complete static parameters failed without needing values")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      assertTrue (decide (inputs.context.values = parameterTypes.reverse ∧
        inputs.names.map Prod.fst = ["f", "w", "u", "y", "x", "d", "c"] ∧
        inputs.ids = (List.range 7).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId))))
        "original parameter spelling, position, type or generated identity changed"
      return inputs

private theorem excludeWrong {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Block} {core wrong : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context source core type) (different : wrong ≠ core) :
    ¬ TerminalReturnTreeElaborates table context source wrong type :=
  fun other => different (other.result_unique elaboration).1

private def compatibility (inputs : LocalTypeInputs) (source : Syntax.Block) : IO Unit := do
  match source with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =>
      have _ := elaborateTerminalReturnTree?_single inputs.names inputs.context returned blockSpan returnSpan
      have _ := elaborateTerminalReturnTree?_single_terminal inputs.names inputs.context returned blockSpan returnSpan
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source =
        elaborateReturnBody? inputs.names inputs.context source ∧
        elaborateTerminalReturnTree? inputs.names inputs.context source =
          elaborateTerminalReturnBody? inputs.names inputs.context source)) "singleton Option equality lost rejection or exact Core"
  | ⟨blockSpan, [⟨ifSpan, .ifThen condition ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
      (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =>
      have _ := elaborateTerminalReturnTree?_conditional_singletons inputs.names inputs.context condition thenReturned elseReturned
        blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan
      have _ := elaborateTerminalReturnTree?_conditional_singletons_terminal inputs.names inputs.context condition thenReturned elseReturned
        blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source =
        elaborateConditionalReturnBody? inputs.names inputs.context source ∧
        elaborateTerminalReturnTree? inputs.names inputs.context source =
          elaborateTerminalReturnBody? inputs.names inputs.context source)) "one-level Option equality lost an invalid arm"
  | _ => pure ()
  match accepted : elaborateReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some _ =>
      let old := elaborateReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
  match accepted : elaborateConditionalReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some _ =>
      let old := elaborateConditionalReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
  match accepted : elaborateTerminalReturnBody? inputs.names inputs.context source with
  | none => pure ()
  | some pair =>
      let old := elaborateTerminalReturnBody?_elaborates accepted
      have _ := old.returnTree
      have _ := old.hasType.returnTree
      have _ := old.returnTree_complete
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context source = some pair))
        "old successful elaboration lost its identical tree embedding"

private def checkTree (inputs : LocalTypeInputs) (source : Syntax.Block) (expected : Core.Expr)
    (type : Core.Ty) : IO Unit := do
  match accepted : elaborateTerminalReturnTree? inputs.names inputs.context source with
  | none => throw (IO.userError "finite recursive tree was rejected")
  | some (core, actualType) =>
      let elaboration := elaborateTerminalReturnTree?_elaborates accepted
      have _ := elaborateTerminalReturnTree?_iff.mp accepted
      let typing := elaborateTerminalReturnTree?_sound accepted
      have _ := elaboration.complete
      have _ := elaboration.hasType
      have _ := typing.elaborates_exact
      have _ := typing.elaborates
      have _ := terminalReturnTreeHasType_iff_elaborates_exact.mp typing
      have _ := terminalReturnTreeHasType_iff_elaborates.mp typing
      have _ := elaborateTerminalReturnTree?_core_hasType accepted
      have _ := elaboration.result_unique elaboration
      have _ := typing.type_unique typing
      assertTrue (decide (core = expected ∧ actualType = type ∧
        Core.infer? inputs.context.values expected = some type)) "recursive source lost exact ordered Core or result type"
      let wrong := match core with
        | .ifE condition left right =>
            if left != right then Core.Expr.ifE condition right left
            else .ifE (.unary .boolNot condition) left right
        | _ => .ifE (.bool true) core core
      if different : wrong ≠ core then
        have _ := excludeWrong elaboration different
        assertTrue (decide (Core.infer? inputs.context.values wrong = some actualType))
          "wrong-tree comparison was not independently equally typed"
      else throw (IO.userError "wrong-Core contrast accidentally equaled the actual tree")
      match sourceAt : source with
      | ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
          have shaped : elaborateTerminalReturnTree? inputs.names inputs.context
              ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, actualType) := by
            simpa only [sourceAt] using accepted
          have _ := elaborateTerminalReturnTree?_children shaped
          let otherSpan : Syntax.SourceSpan := ⟨⟨.main, "outer-ranges-only.sol"⟩, 900, 2⟩
          have _ := elaborateTerminalReturnTree?_spans inputs.names inputs.context condition thenBody elseBody
            blockSpan statementSpan otherSpan otherSpan
          assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context
            ⟨otherSpan, [⟨otherSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, actualType)))
            "outer ranges changed static meaning of original ordered children"
          match core with
          | .ifE conditionCore thenCore elseCore =>
              assertTrue (decide (elaborateLocalExpression? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
                elaborateTerminalReturnTree? inputs.names inputs.context thenBody = some (thenCore, type) ∧
                elaborateTerminalReturnTree? inputs.names inputs.context elseBody = some (elseCore, type)))
                "ordered children did not use the original static inputs"
          | _ => throw (IO.userError "conditional source did not lower to ordered ifE")
          assertTrue (source.span.contains statementSpan && statementSpan.contains condition.span &&
            statementSpan.contains thenBody.span && statementSpan.contains elseBody.span &&
            decide (thenBody.span.endByte ≤ elseBody.span.startByte)) "own recursive child spans or written order changed"
      | ⟨_, [⟨_, .returnStmt _⟩]⟩ => pure ()
      | _ => throw (IO.userError "accepted tree lost its original whole-block shape")
  compatibility inputs source

private def checkFixture (fixture : TreeFixture) (type : Core.Ty) (annotation : String) : IO Unit := do
  let some block ← parsed? (Syntax.Parser.block .allow) fixture.content
    | throw (IO.userError "actual complete block failed to parse")
  let returns := if annotation.isEmpty then "" else s!" returns ({annotation})"
  let some source ← parsed? (Syntax.Parser.functionDecl .module)
      (s!"function tree({parameterText})" ++ returns ++ fixture.content)
    | throw (IO.userError "same text in its own complete declaration failed to parse")
  let inputs ← staticInputs source
  if headerAt : interpretRuntimeFunctionHeader? types source.value.signature = some type then
    have _ := interpretRuntimeFunctionHeader?_iff.mp headerAt
    checkTree inputs block fixture.core type
    checkTree inputs source.value.body fixture.core type
    assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun result => (result.core, result.returnType)) =
      some (fixture.core, type))) "value-free recursive entry compilation lost its exact body"
    if 1 < fixture.depth then
      assertTrue ((elaborateTerminalReturnBody? inputs.names inputs.context block).isNone &&
        (elaborateTerminalReturnBody? inputs.names inputs.context source.value.body).isNone) "recursive entry support expanded the old body adapter"
    else
      assertTrue (decide (elaborateTerminalReturnBody? inputs.names inputs.context block = some (fixture.core, type) ∧
        (compileRuntimeFunction? types owner source).map (fun result => (result.core, result.returnType)) =
          some (fixture.core, type))) "old source shapes lost their exact optional result"
  else throw (IO.userError "entry contrast had a bad header rather than a deeper body")

private def rejected (content : String) (entryCore : Option Core.Expr := none) : IO Unit := do
  let some block ← parsed? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"semantic tree rejection did not fully parse: {content}")
  let some source ← parsed? (Syntax.Parser.functionDecl .module)
      (s!"function invalid({parameterText}) returns (Opaque)" ++ content)
    | throw (IO.userError "invalid tree in whole declaration failed to parse")
  let inputs ← staticInputs source
  for ownBody in [block, source.value.body] do
    match failed : elaborateTerminalReturnTree? inputs.names inputs.context ownBody with
    | some _ => throw (IO.userError "a deeply unselected invalid child bypassed whole-tree checking")
    | none =>
        have _ := elaborateTerminalReturnTree?_eq_none_iff.mp failed
        compatibility inputs ownBody
    if entryCore.isSome then
      assertTrue (elaborateTypedLetReturnBody? types owner inputs ownBody).isNone "recursive entry changed the old prefix adapter"
  match entryCore with
  | none => assertTrue (compileRuntimeFunction? types owner source).isNone "invalid whole source entered runtime compilation"
  | some core => assertTrue (decide (Core.infer? parameterTypes.reverse core = some (.namedData ⟨91⟩) ∧
      (compileRuntimeFunction? types owner source).map (fun compiled =>
        (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
          some (core, .namedData ⟨91⟩, inputs.names, parameterTypes.reverse))) "nominal recursive entry changed exact Core or original parameter-only rows"

def frontendParsedTerminalReturnTreeTests : IO Unit := do
  let left := leaf "x" (.var 4)
  let right := leaf "y" (.var 3)
  checkFixture (node "c" (.var 6) left left) (.namedData ⟨91⟩) "Opaque"
  for depth in [0, 1, 2, 3, 5, 8, 16] do
    for direction in [false, true] do
      checkFixture (spine depth direction left right) (.namedData ⟨91⟩) "Opaque"
  for (leftDepth, rightDepth) in [(0, 7), (6, 1), (3, 5), (9, 2)] do
    checkFixture (node "c" (.var 6) (spine leftDepth false left right) (spine rightDepth true right left))
      (.namedData ⟨91⟩) "Opaque"
  let bare : TreeFixture := ⟨"{return;}", .unit, 0⟩
  for depth in [0, 1, 4, 9] do checkFixture (spine depth false bare (leaf "u" (.var 2))) .unit ""
  checkFixture (spine 5 true (leaf "c" (.var 6)) (leaf "!d" (.unary .boolNot (.var 5)))) .bool "Bool"
  let expressionLeaf := leaf "c ? x : y" (.ifE (.var 6) (.var 4) (.var 3))
  checkFixture expressionLeaf (.namedData ⟨91⟩) "Opaque"
  checkFixture (node "c && !d" (.ifE (.var 6) (.unary .boolNot (.var 5)) (.bool false))
    expressionLeaf (spine 3 true left right)) (.namedData ⟨91⟩) "Opaque"
  let arithmetic := leaf "w / (w + 1)" (.binary .wordDiv (.var 1)
    (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))))
  checkFixture (spine 3 false arithmetic (leaf "w" (.var 1))) .word "Word"
  rejected "{return missing;}"
  rejected "{return f(w);}"
  for depth in [0, 2, 5] do
    for direction in [false, true] do
      let deep := bury depth direction "{let z: Opaque = x;return z;}"
      let core := buriedCore depth direction (.letE (.var 4) (.var 0))
      let equal := Core.Expr.binary .wordEq (.word .zero) (.word .zero)
      let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
        else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
      rejected content (some (if direction then .ifE equal (.var 4) core else .ifE (.unary .boolNot equal) core (.var 3)))
  let some wrapped ← parsed? (Syntax.Parser.block .allow) "{{return x;}}"
    | throw (IO.userError "original terminal block leaf did not parse")
  assertTrue (terminalReturnTreeFuelBound wrapped == 0 && typedLetReturnTreeFuelBound wrapped == 1)
    "terminal wrappers changed the old unsupported bound or added a new transition"
  for depth in [0, 2, 5] do
    for direction in [false, true] do
      let deep := bury depth direction "{{return x;}}"
      let core := buriedCore depth direction (.var 4)
      let equal := Core.Expr.binary .wordEq (.word .zero) (.word .zero)
      let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
        else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
      rejected content (some (if direction then .ifE equal (.var 4) core else .ifE (.unary .boolNot equal) core (.var 3)))
  for invalid in ["{return missing;}", "{return c;}", "{return;}",
      "{if(w){return x;}else{return y;}}", "{if(c){return x;}}", "{return x;return y;}",
      "{}", "{return f(w);}"] do
    for depth in [0, 2, 5] do
      for direction in [false, true] do
        let deep := bury depth direction invalid
        -- Constant comparison guards place the bad subtree on the unselected side.
        let content := if direction then "{if(0 == 0){return x;}else" ++ deep ++ "}"
          else "{if(0 != 0)" ++ deep ++ "else{return y;}}"
        rejected content
  for content in ["", "{return x;", "{return x}", "{if(c){return x;}else{return y;}} trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "incomplete or diagnosed block acquired tree meaning"

end Tests
