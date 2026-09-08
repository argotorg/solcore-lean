import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TerminalReturnTreeExecutionProperties
import Solcore.Frontend.TerminalReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeProperties
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.RuntimeParameters
import Solcore.Resolved.LocalScopeProperties

/-! Fixture-supplied branch scripts certify actual parsed selected paths.
This is not a tree runner: no branch search, execution API or fuel policy is
introduced. Core correspondence always uses the actual whole checker result. -/

set_option autoImplicit false

namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def inputs (c d : Bool) (type : Core.Ty) (x y : Core.Value)
    (xTyped : Core.ValueHasType x type) (yTyped : Core.ValueHasType y type) : LocalInputs :=
  let flags := (LocalInputs.empty.bindFresh owner "c" .bool (.bool c) .bool).bindFresh owner "d" .bool (.bool d) .bool
  (flags.bindFresh owner "x" type x xTyped).bindFresh owner "y" type y yTyped
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def body (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "fixture did not parse as a block")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd)
    s!"block was diagnosed or partially consumed: {content}; {reprStr next.diagnostics}; atEnd={next.atEnd}"
  return source

private structure Reference (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  costed : LocalExpressionEvaluatesWithCost table environment store source value store 1
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Reference table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script referenced an unknown name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script referenced a missing actual value")
          | some value => return ⟨value, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected its actual identifier expression")
private structure ExpressionCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def expressionCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) : IO (ExpressionCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ =>
      let ref ← reference table environment store source
      return ⟨ref.value, 1, ref.costed⟩
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let ref ← reference table environment store operand
      match actual : ref.value with
      | .word value => return ⟨.word value.bitNot, 3, by rw [sourceAt]; exact .bitNot (by simpa only [actual] using ref.costed)⟩
      | _ => throw (IO.userError "word certificate received a non-word value")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match firstAt : first.value, secondAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), 5, by
          rw [sourceAt]
          exact .subtract (by simpa only [firstAt] using first.costed) (by simpa only [secondAt] using second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction certificate received a non-word")
  | _ => throw (IO.userError "expression is outside this fixture certificate vocabulary")
private structure LeafCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : ReturnBodyEvaluatesWithCost table environment store source value store cost
private def leafCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) : IO (LeafCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .bare⟩
  | ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      let leaf ← expressionCertificate table environment store expression
      return ⟨leaf.value, leaf.cost, by rw [sourceAt]; exact .expression leaf.costed⟩
  | _ => throw (IO.userError "script did not end at a singleton return")

private theorem oldEmbeddings {table : LocalNameTable} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment store source value store cost) :
    TerminalReturnTreeEvaluates table environment store source value store ∧
      TerminalReturnTreeEvaluatesWithCost table environment store source value store cost := by
  have oldRaw := evaluation.erase.returnTree
  have oldCost := evaluation.returnTree
  have unionRaw := (TerminalReturnBodyEvaluates.conditional evaluation.erase).returnTree
  have unionCost := (TerminalReturnBodyEvaluatesWithCost.conditional evaluation).returnTree
  have _ := oldRaw.deterministic unionRaw
  have _ := oldCost.deterministic unionCost
  exact ⟨oldRaw, unionCost⟩
private structure TreeCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TerminalReturnTreeEvaluates table environment store source value store
  costed : TerminalReturnTreeEvaluatesWithCost table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) (choices : List Bool) : IO (TreeCertificate table environment store source) := do
  match choices with
  | [] =>
      let leaf ← leafCertificate table environment store source
      have _ := leaf.costed.returnTree
      have _ := leaf.costed.erase.returnTree
      return ⟨leaf.value, leaf.cost, .single leaf.costed.erase, .single leaf.costed⟩
  | choice :: rest =>
      match sourceAt : source with
      | ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
          let guard ← reference table environment store condition
          if agrees : guard.value = .bool choice then
            match choiceAt : choice with
            | true =>
                have conditionCost : LocalExpressionEvaluatesWithCost table environment store condition (.bool true) store 1 := by
                  simpa only [agrees, choiceAt] using guard.costed
                let child ← certify table environment store thenBody rest
                if rest.isEmpty then
                  let leaf ← leafCertificate table environment store thenBody
                  have _ := oldEmbeddings (ConditionalReturnBodyEvaluatesWithCost.ifTrue
                    (blockSpan := blockSpan) (statementSpan := statementSpan) (elseBody := elseBody) conditionCost leaf.costed)
                  pure ()
                return ⟨child.value, 1 + child.cost + 2, by rw [sourceAt]; exact .ifTrue conditionCost.erase child.raw,
                  by rw [sourceAt]; exact .ifTrue conditionCost child.costed⟩
            | false =>
                have conditionCost : LocalExpressionEvaluatesWithCost table environment store condition (.bool false) store 1 := by
                  simpa only [agrees, choiceAt] using guard.costed
                let child ← certify table environment store elseBody rest
                if rest.isEmpty then
                  let leaf ← leafCertificate table environment store elseBody
                  have _ := oldEmbeddings (ConditionalReturnBodyEvaluatesWithCost.ifFalse
                    (blockSpan := blockSpan) (statementSpan := statementSpan) (thenBody := thenBody) conditionCost leaf.costed)
                  pure ()
                return ⟨child.value, 1 + child.cost + 2, by rw [sourceAt]; exact .ifFalse conditionCost.erase child.raw,
                  by rw [sourceAt]; exact .ifFalse conditionCost child.costed⟩
          else throw (IO.userError "supplied branch script disagreed with actual condition value")
      | _ => throw (IO.userError "script expected an explicit if/else node")
termination_by choices.length

private theorem arbitraryContinuation {table : LocalNameTable} {environment : Resolved.Environment}
    {context : Resolved.Context} {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : TreeCertificate table environment store source)
    (accepted : elaborateTerminalReturnTree? table context source = some (core, type))
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation
private def checked (localInputs : LocalInputs) (store : Core.Store) (source : Syntax.Block)
    (choices : List Bool) (expected : Core.Expr) (value : Core.Value) (cost : Nat) : IO Unit := do
  let certificate ← certify localInputs.names localInputs.environment store source choices
  assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent selected source cost/value changed"
  match accepted : elaborateTerminalReturnTree? localInputs.names localInputs.context source with
  | none => throw (IO.userError "whole tree checking failed")
  | some (core, type) =>
      let typing := elaborateTerminalReturnTree?_sound accepted
      have _ := typing.evaluates localInputs.sameIds localInputs.environmentTyped store
      have _ := certificate.raw.preserves_type typing localInputs.sameIds localInputs.environmentTyped
      have _ := certificate.raw.store_eq
      have _ := certificate.raw.exists_cost
      have _ := terminalReturnTreeEvaluates_iff_exists_cost.mp certificate.raw
      have _ := certificate.raw.deterministic certificate.costed.erase
      have _ := certificate.costed.store_eq
      have _ := certificate.costed.cost_pos
      have _ := certificate.costed.deterministic certificate.costed
      let correspondence := elaborateTerminalReturnTree?_evaluates_iff accepted localInputs.sameIds
      have coreEvaluation := correspondence.mp certificate.raw
      have _ := correspondence.mpr coreEvaluation
      have _ := certificate.costed.checked_toSteps accepted localInputs.sameIds
      have _ := arbitraryContinuation certificate accepted localInputs.sameIds
      assertTrue (decide (core = expected ∧ Core.infer? localInputs.context.values core = some type ∧
        Core.runStateful cost (.initial core localInputs.environment.values store) = .done value store))
        "actual checked Core did not have the certified path endpoint"
      -- runStateful inspects the next frame even at zero fuel; this head accepts every returned value.
      let continuation : List Core.Frame := [.letBody (.var 0) [.word (word 17)], .unaryApply .wordNot]
      have _ := arbitraryContinuation certificate accepted localInputs.sameIds continuation
      assertTrue (decide (Core.runStateful cost ⟨.eval core localInputs.environment.values, continuation, store⟩ =
        .outOfFuel ⟨.ret value, continuation, store⟩)) "pending arbitrary continuation was executed, edited or discarded"
      if (Core.UnaryOp.wordNot.apply value).isNone then
        let faulty : List Core.Frame := [.unaryApply .wordNot, .binaryApply .wordSub (.word (word 17))]
        have _ := arbitraryContinuation certificate accepted localInputs.sameIds faulty
        assertTrue (decide (Core.runStateful cost ⟨.eval core localInputs.environment.values, faulty, store⟩ =
          .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, faulty, store⟩))
          "fault observation at zero remaining fuel lost the certified endpoint or original continuation"

def frontendParsedTerminalReturnTreeEvaluationTests : IO Unit := do
  let source ← body "{if(c){if(d){return ~x;}else{return x - y;}}else{return y;}}"
  let core : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.unary .wordNot (.var 1))
    (.binary .wordSub (.var 1) (.var 0))) (.var 0)
  let mirror ← body "{if(c){return x;}else{if(d){return y;}else{if(c){return ~x;}else{return x - y;}}}}"
  let mirrorCore : Core.Expr := .ifE (.var 3) (.var 1) (.ifE (.var 2) (.var 0)
    (.ifE (.var 3) (.unary .wordNot (.var 1)) (.binary .wordSub (.var 1) (.var 0))))
  for c in [false, true] do
    for d in [false, true] do
      for (x, y) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
        let actual := inputs c d .word (.word x) (.word y) .word .word
        for store in stores do
          checked actual store source (if c then [true, d] else [false]) core
            (.word (if c then if d then x.bitNot else x.sub y else y)) (if c then if d then 9 else 11 else 4)
          checked actual store mirror (if c then [true] else if d then [false, true] else [false, false, false]) mirrorCore
            (.word (if c then x else if d then y else x.sub y)) (if c then 4 else if d then 7 else 14)
  let opaqueSource ← body "{if(c){if(d){return x;}else{return y;}}else{return x;}}"
  let opaqueCore : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.var 1) (.var 0)) (.var 1)
  let closureLeft : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (left, right) in [(closureLeft, closureRight),
      (⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩)] do
    if matching : right.type = left.type then
      for c in [false, true] do
        for d in [false, true] do
          for store in stores do
            checked (inputs c d left.type left.value right.value left.valueTyped (matching ▸ right.valueTyped)) store opaqueSource
              (if c then [true, d] else [false]) opaqueCore (if c && !d then right.value else left.value) (if c then 7 else 4)
    else throw (IO.userError "opaque fixture supplied different types")
  let units ← body "{if(c){if(d){return;}else{return;}}else{return;}}"
  for store in stores do
    checked (inputs true false .unit .unit .unit .unit .unit) store units [true, false]
      (.ifE (.var 3) (.ifE (.var 2) .unit .unit) .unit) .unit 7
  let actual := inputs true true .word (.word (word 9)) (.word (word 2)) .word .word
  for invalid in ["{return missing;}", "{return c;}", "{}", "{if(d){return x;}}", "{return x;return y;}", "{return x();}"] do
    let skipped ← body ("{if(c){if(d){return x;}else" ++ invalid ++ "}else{return y;}}")
    for store in stores do
      let certificate ← certify actual.names actual.environment store skipped [true, true]
      have _ := certificate.raw.exists_cost
      have _ := certificate.raw.store_eq
      have _ := certificate.costed.cost_pos
      assertTrue (decide (certificate.value = .word (word 9) ∧ certificate.cost = 7) &&
        (elaborateTerminalReturnTree? actual.names actual.context skipped).isNone) "raw skipped success was mistaken for whole acceptance"
  let untyped : Resolved.Environment := actual.environment.map fun entry => (entry.1, Core.Value.bool true)
  have aligned : untyped.ids = actual.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def] using actual.sameIds
  for store in stores do
    let certificate ← certify actual.names untyped store opaqueSource [true, true]
    match accepted : elaborateTerminalReturnTree? actual.names actual.context opaqueSource with
    | none => throw (IO.userError "aligned raw contrast lost actual whole checking")
    | some (actualCore, type) =>
        let bridge := elaborateTerminalReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mp certificate.raw
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 7 ∧ actualCore = opaqueCore ∧
          Core.runStateful 7 (.initial actualCore untyped.values store) = .done (.bool true) store))
          "raw identity-aligned correspondence incorrectly demanded runtime typing"
  let referenceBody ← body "{return x;}"
  let reordered : Resolved.Environment := actual.environment.reverse
  for store in stores do
    let certificate ← certify actual.names reordered store referenceBody []
    let some (actualCore, type) := elaborateTerminalReturnTree? actual.names actual.context referenceBody
      | throw (IO.userError "misalignment contrast lost actual checker provenance")
    have _ := certificate.raw.store_eq
    assertTrue (decide (reordered.ids ≠ actual.context.ids ∧ certificate.value = .word (word 9) ∧
      type = .word ∧ actualCore = .var 1 ∧ Core.runStateful 1 (.initial actualCore reordered.values store) =
        .done (.bool true) store)) "reordered identities were treated as an aligned positional environment"

end Tests
