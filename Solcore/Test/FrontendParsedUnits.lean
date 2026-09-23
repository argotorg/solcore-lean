import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.TypeName

/-! Completely parsed empty tuples, separate nullary/binary products, and
independent transition certificates. Constant leaves need no runtime alignment. -/
set_option autoImplicit false
namespace Tests
namespace ParsedUnits
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnit", by decide⟩], by decide⟩⟩, 23⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def stores : List Core.Store := [[], [w 42, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "empty-tuples.sol"⟩, content⟩
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "original complete byte range changed"
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete expression: {content}")
  return source
private structure Certificate (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression table source resolved
  lowered : Resolved.Lowers context.ids resolved core
  typing : LocalExpressionHasType table context source type
  raw : LocalExpressionEvaluatesWithCost table environment store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core environment.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (table : LocalNameTable) (context : Resolved.Context) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) : IO (Certificate table context environment store source) := do
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [sourceAt]; exact .unit, .unit,
      by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .group inner⟩ =>
      let child ← certify table context environment store inner
      return { child with resolution := by rw [sourceAt]; exact .group child.resolution
                          typing := by rw [sourceAt]; exact .group child.typing
                          raw := by rw [sourceAt]; exact .group child.raw }
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← certify table context environment store left
      let b ← certify table context environment store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .pair a.typing b.typing,
        by rw [sourceAt]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let a ← certify table context environment store first
      let b ← certify table context environment store ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .many a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .many a.typing b.typing, by rw [sourceAt]; exact .many a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | _ => throw (IO.userError "outside independent constant certificate grammar")
termination_by sizeOf source
private def checked (content : String) (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed content
  for store in stores do
    let evidence ← certify table context environment store source
    assertTrue (decide (evidence.core = core ∧ evidence.type = type ∧ evidence.value = value ∧ evidence.cost = cost)) "independent constant certificate changed"
    have accepted := elaborateLocalExpression?_complete evidence.resolution evidence.lowered
      (evidence.resolution.preserves_type evidence.typing)
    have _ := elaborateLocalExpression?_core_hasType accepted
    have direct := evaluateLocalExpressionWithCost?_complete evidence.raw
    have _ := evaluateLocalExpressionWithCost?_sound direct store
    have _ := (evaluateLocalExpressionWithCost?_iff store).mpr evidence.raw
    have _ := localExpressionEvaluatesWithCost_iff_evaluate.mp evidence.raw
    have _ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mp ⟨evidence.cost, direct⟩
    have _ := (evaluateLocalExpressionWithCost?_value_iff store).mpr evidence.raw.erase
    assertTrue (decide (elaborateLocalExpression? table context source = some (core, type) ∧
      evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧
      Core.infer? context.values core = some type ∧ localExpressionFuelBound source = cost)) "independent Core/type/value/cost/bound changed"
    for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
      have _ := evidence.paths k
      pure () -- No sameIds premise: these independently constructed paths contain no references.
    let start := Core.State.initial evidence.core environment.values store
    for fuel in List.range (cost + 3) do
      have _ := (evidence.paths []).runStateful_done_iff (fuel := fuel)
      assertTrue (match Core.runStateful fuel start with
        | .done result finalStore => decide (cost ≤ fuel ∧ result = value ∧ finalStore = store)
        | .outOfFuel checkpoint => decide (fuel < cost ∧ checkpoint.store = store)
        | _ => false) "constant fuel threshold or own store changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel checkpoint =>
          have _ := (evidence.paths []).residual_of_outOfFuel exhausted
          for additional in List.range (cost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            have _ := (evidence.paths []).resumed_done_iff (additional := additional) exhausted
            assertTrue (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional) start)) "actual continuation replay changed"
            assertTrue (match Core.runStateful additional checkpoint with
              | .done result finalStore => decide (cost - spent ≤ additional ∧ result = value ∧ finalStore = store)
              | .outOfFuel next => decide (additional < cost - spent ∧ next.store = store)
              | _ => false) "independent remaining cost changed"
          if spent > 0 then assertTrue (Core.runStateful (cost - spent) start != .done value store) "restart discarded consumed cost"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second actual chunk absent")
            assertTrue (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk failed"
      | _ => throw (IO.userError "genuine checkpoint absent")
    assertTrue (match Core.runStateful cost ⟨.eval core environment.values, [.unaryApply .wordNot], store⟩ with
      | .fault _ endpoint => decide (endpoint = ⟨.ret value, [.unaryApply .wordNot], store⟩)
      | _ => false) "unit/product endpoint incorrectly guaranteed arbitrary-continuation exhaustion"
    assertTrue (decide (Core.runStateful cost ⟨.eval core environment.values, [.letBody (.var 0) []], store⟩ =
      .outOfFuel ⟨.ret value, [.letBody (.var 0) []], store⟩ ∧
      Core.runStateful (cost + 2) ⟨.eval core environment.values, [.letBody (.var 0) []], store⟩ = .done value store))
      "pending strict binding lost its two transitions"
private def shortCircuit (choice : Bool) (isAnd : Bool) : IO Unit := do
  let inputs := LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
  let source ← parsed (if isAnd then "c && ()" else "c || ()")
  let expected := if (if isAnd then choice else !choice) then Core.Value.unit else .bool choice
  assertTrue (decide (evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (expected, 4)) &&
    (inputs.check? source).isNone) "raw Unit forwarding became whole Bool typing"
  for store in stores do
    for fuel in [0, 4, 8] do assertTrue (inputs.run? fuel source store).isNone "whole rejection exposed execution"
    match sourceAt : source with
    | ⟨_, .binary ⟨guardSpan, .identifier name⟩ ⟨_, op⟩ ⟨_, .tuple ⟨_, []⟩⟩⟩ =>
        if nameAt : name.value = "c" then
          have guard : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store
              ⟨guardSpan, .identifier name⟩ (.bool choice) store 1 := .identifier (by rw [nameAt]; exact .head) .head
          match opAt : op, atChoice : choice with
          | .logicalAnd, true =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.unit, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.andTrue (atChoice ▸ guard) .unit)
              pure ()
          | .logicalOr, false =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.unit, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.orFalse (atChoice ▸ guard) .unit)
              pure ()
          | .logicalAnd, false =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.bool false, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.andFalse (atChoice ▸ guard))
              pure ()
          | .logicalOr, true =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.bool true, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.orTrue (atChoice ▸ guard))
              pure ()
          | _, _ => throw (IO.userError "logical operator changed")
        else throw (IO.userError "guard spelling changed")
    | _ => throw (IO.userError "original Unit child disappeared")
private def conditional (choice : Bool) : IO Unit := do
  let inputs := LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
  let source ← parsed "c ? () : ()"
  for store in stores do
    match sourceAt : source with
    | ⟨_, .conditional ⟨guardSpan, .identifier name⟩ _ ⟨_, .tuple ⟨_, []⟩⟩ _ ⟨_, .tuple ⟨_, []⟩⟩⟩ =>
        if nameAt : name.value = "c" then
          have guard : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store
              ⟨guardSpan, .identifier name⟩ (.bool choice) store 1 := .identifier (by rw [nameAt]; exact .head) .head
          have raw : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source .unit store 4 := by
            rw [sourceAt]
            cases choice
            · exact .ifFalse guard .unit
            · exact .ifTrue guard .unit
          have resolved : ResolvesLocalExpression inputs.names source (.ifE (.var (Resolved.freshLocalId owner [])) .unit .unit) := by
            rw [sourceAt]; exact .conditional (.identifier (by rw [nameAt]; exact .head)) .unit .unit
          have accepted := elaborateLocalExpression?_complete (context := inputs.context) resolved (.ifE (.var .head) .unit .unit)
            (Resolved.HasType.ifE (.var .head) .unit .unit)
          have _ := evaluateLocalExpressionWithCost?_complete raw
          have _ := raw.checked_toSteps accepted inputs.sameIds
          assertTrue (decide (inputs.check? source = some (.ifE (.var 0) .unit .unit, .unit))) "conditional unit Core changed"
          for fuel in List.range 7 do
            assertTrue (match inputs.run? fuel source store with
              | some (type, .done value finalStore) => decide (4 ≤ fuel ∧ type = .unit ∧ value = .unit ∧ finalStore = store)
              | some (type, .outOfFuel checkpoint) => decide (fuel < 4 ∧ type = .unit ∧ checkpoint.store = store)
              | _ => false) "selected unit conditional cost changed"
          assertTrue (decide (inputs.run? 3 source store = some (.unit, .outOfFuel (.initial .unit inputs.environment.values store))))
            "selected arm checkpoint was not the original unit expression"
        else throw (IO.userError "conditional guard spelling changed")
    | _ => throw (IO.userError "original conditional Unit children changed")
  let skipped ← parsed "c ? () : missing"
  assertTrue ((inputs.check? skipped).isNone && decide (evaluateLocalExpressionWithCost? inputs.names inputs.environment skipped =
    if choice then some (.unit, 4) else none)) "raw skipped missing arm bypassed whole checking"
end ParsedUnits
open ParsedUnits Solcore Solcore.Frontend
def frontendParsedUnitTests : IO Unit := do
  let hostileNames : LocalNameTable := [("Unit", id 7), ("Unit", id 99), ("missing", id 2)]
  let hostileContext : Resolved.Context := [(id 2, .namedData ⟨83⟩), (id 99, .word)]
  let hostileEnvironment : Resolved.Environment := [(id 7, .cellRef .word 999), (id 7, .closure .word .bool (.var 999) [w 12])]
  let actual := LocalInputs.empty.bindFresh owner "Unit" .word (w 9) .word
  for (table, context, environment) in [([], [], []), (hostileNames, hostileContext, hostileEnvironment),
      (actual.names, actual.context, actual.environment)] do
    for text in ["()", "(())", "((),)", "((()),)"] do checked text table context environment .unit .unit .unit 1
    checked "((), ())" table context environment (.pair .unit .unit) (.product .unit .unit) (.pair .unit .unit) 5
    checked "((),((),()))" table context environment (.pair .unit (.pair .unit .unit))
      (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
    checked "(((),()),())" table context environment (.pair (.pair .unit .unit) .unit)
      (.product (.product .unit .unit) .unit) (.pair (.pair .unit .unit) .unit) 9
    for depth in [0, 1, 3, 6] do
      let text := (List.range depth).foldl (fun inner _ => "(()," ++ inner ++ ")") "()"
      let core := (List.range depth).foldl (fun inner _ => Core.Expr.pair .unit inner) .unit
      let type := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) .unit
      let value := (List.range depth).foldl (fun inner _ => Core.Value.pair .unit inner) .unit
      checked text table context environment core type value (4 * depth + 1)
  let source ← parsed "()"
  assertTrue (match source.value with | .tuple ⟨span, []⟩ => decide (span = source.span) | _ => false) "empty delimited range changed"
  let named ← parsed "Unit"
  assertTrue (decide (actual.check? named = some (.var 0, .word) ∧ actual.check? source = some (.unit, .unit) ∧
    evaluateLocalExpressionWithCost? hostileNames hostileEnvironment named = some (.cellRef .word 999, 1) ∧
    evaluateLocalExpressionWithCost? hostileNames [] source = some (.unit, 1))) "Unit spelling became reserved or empty constant looked up a name"
  for store in stores do
    assertTrue (decide (actual.run? 0 source store = some (.unit, .outOfFuel (.initial .unit actual.environment.values store)) ∧
      actual.run? 1 source store = some (.unit, .done .unit store))) "genuine zero/one Unit boundary changed"
    match exhausted : actual.run? 0 source store with
    | some (_, .outOfFuel _) => have _ := LocalInputs.run?_resume exhausted 1; pure ()
    | _ => throw (IO.userError "Unit checkpoint absent")
    let initial := Core.State.initial (.pair .unit .unit) hostileEnvironment.values store
    assertTrue (decide (Core.runStateful 2 initial = .outOfFuel
      ⟨.ret .unit, [.pairRight .unit hostileEnvironment.values], store⟩ ∧
      Core.runStateful 4 initial = .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩)) "unit pair frames were collapsed"
    let certificate ← certify actual.names actual.context actual.environment store source
    let accepted := elaborateLocalExpression?_complete certificate.resolution certificate.lowered
      (certificate.resolution.preserves_type certificate.typing)
    have _ := certificate.raw.checked_toSteps accepted actual.sameIds
    have _ := actual.typed_evaluator_execution certificate.typing store
    pure ()
  for choice in [false, true] do
    for isAnd in [false, true] do shortCircuit choice isAnd
    conditional choice
  checked "((),(),())" hostileNames hostileContext hostileEnvironment (.pair .unit (.pair .unit .unit))
    (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
  checked "((),(),(),())" hostileNames hostileContext hostileEnvironment (.pair .unit (.pair .unit (.pair .unit .unit)))
    (.product .unit (.product .unit (.product .unit .unit))) (.pair .unit (.pair .unit (.pair .unit .unit))) 13
  for text in ["().x", "()[0]", "[()]", "() ()", "() && ()", "!()", "~()"] do
    let invalid ← parsed text
    assertTrue ((resolveLocalExpression? [] invalid).isNone || (elaborateLocalExpression? [] [] invalid).isNone) "unsupported syntax became checked"
    assertTrue (evaluateLocalExpressionWithCost? [] [] invalid).isNone "unsupported/ill-shaped raw syntax succeeded"
  let singleton : Syntax.Expr := ⟨source.span, .tuple ⟨source.span, [source]⟩⟩
  assertTrue ((resolveLocalExpression? [] singleton).isNone && (evaluateLocalExpressionWithCost? [] [] singleton).isNone) "manual singleton acquired grouping meaning"
  for text in ["()", "(Word, Word)"] do
    let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "type lexer invariant")
    let .ok type next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) | throw (IO.userError "type parser failed")
    assertTrue (next.atEnd && (interpretTypeName? [(["Word"], .word)] type).isNone) "expression Unit enabled tuple type syntax"
  for (text, expected) in [("Unit", Core.Ty.word), ("Nothing", .unit)] do
    let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "alias lexer invariant")
    let .ok type next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) | throw (IO.userError "alias parser failed")
    assertTrue (next.atEnd && decide (interpretTypeName? [(["Unit"], .word), (["Nothing"], .unit)] type = some expected))
      "Unit spelling acquired a reserved type-name meaning"
  let malformedSpan : Syntax.SourceSpan := ⟨⟨.main, "not-parsed.sol"⟩, 99, 2⟩
  let manual : Syntax.Expr := ⟨malformedSpan, .tuple ⟨⟨(file "").id, 7, 1⟩, []⟩⟩
  for store in stores do
    let evidence ← certify hostileNames hostileContext hostileEnvironment store manual
    have _ := evaluateLocalExpressionWithCost?_complete evidence.raw
    assertTrue (decide (evidence.core = .unit ∧ evidence.type = .unit ∧ evidence.value = .unit ∧ evidence.cost = 1))
      "raw/static Unit unexpectedly required valid occurrence ranges"
  for text in ["(", "())", "(,)", "(),"] do assertTrue (← parsed? text).isNone s!"incomplete source accepted: {text}"
end Tests
