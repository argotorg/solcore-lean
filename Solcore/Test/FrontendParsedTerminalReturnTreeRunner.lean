import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeResumptionProperties
import Solcore.Frontend.TerminalReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.LocalInputsProperties
import Solcore.Resolved.LocalScopeProperties

/-! Actual checked recursive bodies retain their full machine states. Small
fixture-supplied branch scripts independently certify the selected source cost;
the recursive entry retains these exact body runs while old adapters stay separate. -/

set_option autoImplicit false

namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeRunner", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def inputs (c d : Bool) (left right : TypedRuntimeArgument)
    (matching : right.type = left.type) : LocalInputs :=
  let flags := (LocalInputs.empty.bindFresh owner "c" .bool (.bool c) .bool).bindFresh owner "d" .bool (.bool d) .bool
  (flags.bindFresh owner "x" left.type left.value left.valueTyped).bindFresh owner "y" left.type right.value
    (matching ▸ right.valueTyped)
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def parsed {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-runner.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"fixture did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def body := parsed (Syntax.Parser.block .allow)

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
              rw [sourceAt]
              exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store elseBody rest
            return ⟨child.value, 1 + child.cost + 2, by
              rw [sourceAt]
              exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagreed with the actual condition value")
  | _, _ => throw (IO.userError "script disagreed with the parsed body shape")
termination_by choices.length

private def oldShapes (actual : LocalInputs) (source : Syntax.Block) (fuel : Nat) (store : Core.Store) : IO Unit := do
  let run := actual.runTerminalReturnTree? fuel source store
  match source.value with
  | [⟨returnSpan, .returnStmt returned⟩] =>
      have _ := actual.runTerminalReturnTree?_single fuel returned source.span returnSpan store
      have _ := actual.runTerminalReturnTree?_single_terminal fuel returned source.span returnSpan store
      assertTrue (decide (run = actual.runReturnBody? fuel source store ∧
        run = actual.runTerminalReturnBody? fuel source store)) "old singleton full result changed"
  | [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩] =>
      match thenBody.value, elseBody.value with
      | [⟨thenReturn, .returnStmt thenReturned⟩], [⟨elseReturn, .returnStmt elseReturned⟩] =>
          have _ := actual.runTerminalReturnTree?_conditional_singletons fuel condition thenReturned elseReturned
            source.span ifSpan thenBody.span thenReturn elseBody.span elseReturn store
          have _ := actual.runTerminalReturnTree?_conditional_singletons_terminal fuel condition thenReturned elseReturned
            source.span ifSpan thenBody.span thenReturn elseBody.span elseReturn store
          assertTrue (decide (run = actual.runConditionalReturnBody? fuel source store ∧
            run = actual.runTerminalReturnBody? fuel source store)) "old shallow full result changed"
      | _, _ => assertTrue (actual.runTerminalReturnBody? fuel source store).isNone "old runner accepted a deep tree"
  | _ => pure ()

private def checked (actual : LocalInputs) (source : Syntax.Block) (choices : List Bool) (expected : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) (store : Core.Store) : IO Unit := do
  let certificate ← certify actual.names actual.environment store source choices
  assertTrue (decide (certificate.value = value ∧ certificate.cost = cost ∧ terminalReturnTreeFuelBound source = bound))
    "independent source cost/value or recursive bound changed"
  match accepted : actual.checkTerminalReturnTree? source with
  | none => throw (IO.userError "whole recursive checker rejected a valid body")
  | some (core, actualType) =>
      assertTrue (decide (core = expected ∧ actualType = type)) "actual checked Core or return type changed"
      let typing := elaborateTerminalReturnTree?_sound accepted
      have _ := certificate.costed.cost_le_fuelBound
      have _ := certificate.costed.checked_runStateful_done_iff (fuel := cost) accepted actual.sameIds
      have _ := certificate.costed.checked_runStateful_outOfFuel_iff (fuel := 0) accepted actual.sameIds
      have _ := elaborateTerminalReturnTree?_run_done_iff_cost (initialStore := store) (finalStore := store)
        (value := value) (fuel := cost) accepted actual.sameIds
      have _ := LocalInputs.terminalReturnTree_typed_cost_execution (inputs := actual) typing store
      have _ := elaborateTerminalReturnTree?_run_done_of_fuelBound accepted actual.sameIds actual.environmentTyped store
      have _ := LocalInputs.runTerminalReturnTree?_done_of_fuelBound (inputs := actual) typing store
      let initial := Core.State.initial core actual.environment.values store
      let run := fun fuel => actual.runTerminalReturnTree? fuel source store
      for fuel in List.range (bound + 3) do
        oldShapes actual source fuel store
        have _ := LocalInputs.runTerminalReturnTree?_never_faults actual source fuel store type
        assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial))) "runner replaced Core or reordered values"
        match outcome : run fuel with
        | some (resultType, .done result finalStore) =>
            have _ := LocalInputs.runTerminalReturnTree?_done_iff_typed_cost.mp outcome
            assertTrue (decide (cost ≤ fuel ∧ resultType = type ∧ result = value ∧ finalStore = store)) "wrong completion boundary/value/store"
        | some (resultType, .outOfFuel state) =>
            have _ := LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost.mp ⟨state, outcome⟩
            assertTrue (decide (fuel < cost ∧ resultType = type ∧ state.store = store)) "wrong exhaustion boundary/store"
        | _ => throw (IO.userError "typed runner faulted or disappeared")
      for spent in List.range cost do
        match exhausted : run spent with
        | some (checkpointType, .outOfFuel checkpoint) =>
            have _ : spent < certificate.cost ∧ Core.Steps (certificate.cost - spent) checkpoint
                (.final certificate.value store) := by
              obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTerminalReturnTree?_eq_some_iff.mp exhausted
              exact certificate.costed.checked_residual_of_outOfFuel checkedAt actual.sameIds pathAt
            assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "genuine checkpoint was not resumable at zero fuel"
            for remaining in List.range (cost - spent + 3) do
              have _ := LocalInputs.runTerminalReturnTree?_resume exhausted remaining
              let resumed := Core.runStateful remaining checkpoint
              assertTrue (decide (run (spent + remaining) = some (checkpointType, resumed))) "full genuine resumption result changed"
              assertTrue (match resumed with
                | .done result finalStore => decide (cost - spent ≤ remaining ∧ result = value ∧ finalStore = store)
                | .outOfFuel state => decide (remaining < cost - spent ∧ state.store = store)
                | _ => false) "wrong residual threshold or retained store"
            for middle in List.range (cost - spent) do
              let .outOfFuel second := Core.runStateful middle checkpoint | throw (IO.userError "second checkpoint disappeared")
              for last in List.range (cost - spent - middle + 3) do
                assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last second)))
                  "three genuine chunks changed control, frames, environment or store"
        | _ => throw (IO.userError "expected a genuine checkpoint below independent source cost")
      match core with
      | .ifE guard thenCore elseCore =>
          let environment := actual.environment.values
          let pending : Core.State := ⟨.eval guard environment, [.ifBranches thenCore elseCore environment], store⟩
          assertTrue (decide (run 1 = some (type, .outOfFuel pending))) "ordered branches or captured actual environment changed"
          let some (_, .outOfFuel checkpoint) := run 2 | throw (IO.userError "guard checkpoint disappeared")
          assertTrue (decide (Core.runStateful 0 { checkpoint with continuation := [] } ≠ Core.runStateful 0 checkpoint))
            "discarding the genuine conditional frame did not alter zero-fuel observation"
      | _ => pure ()

def frontendParsedTerminalReturnTreeRunnerTests : IO Unit := do
  let content := "{if(c){if(d){return x;}else{return y;}}else{return x;}}"
  let source ← body content
  let core : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.var 1) (.var 0)) (.var 1)
  assertTrue (terminalReturnBodyFuelBound source == 4 && terminalReturnTreeFuelBound source == 7) "old and recursive bounds were conflated"
  let leftClosure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let rightClosure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true],
    .closure (.cons .bool .nil) (.var rfl)⟩
  for (left, right) in [(⟨.word, .word (word 9), .word⟩, ⟨.word, .word Core.Word.maximum, .word⟩),
      (⟨.bool, .bool true, .bool⟩, ⟨.bool, .bool false, .bool⟩), (⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩),
      (⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩), (leftClosure, rightClosure)] do
    if matching : right.type = left.type then
      for c in [false, true] do
        for d in [false, true] do
          let actual := inputs c d left right matching
          assertTrue (decide (actual.environment.values = [right.value, left.value, .bool d, .bool c])) "actual argument order changed"
          for store in stores do
            checked actual source (if c then [true, d] else [false]) core left.type
              (if c && !d then right.value else left.value) (if c then 7 else 4) 7 store
    else throw (IO.userError "opaque argument pair has mismatching types")
  let actual := inputs true false ⟨.word, .word (word 9), .word⟩ ⟨.word, .word (word 2), .word⟩ rfl
  let mirror ← body "{if(c){return x;}else{if(d){return y;}else{if(c){return x;}else{return y;}}}}"
  let mirrorCore : Core.Expr := .ifE (.var 3) (.var 1) (.ifE (.var 2) (.var 0) (.ifE (.var 3) (.var 1) (.var 0)))
  for store in stores do
    checked actual mirror [true] mirrorCore .word (.word (word 9)) 4 10 store
    let mirrored := inputs false false ⟨.word, .word (word 9), .word⟩ ⟨.word, .word (word 2), .word⟩ rfl
    checked mirrored mirror [false, false, false] mirrorCore .word (.word (word 2)) 10 10 store
    checked actual (← body "{return;}") [] .unit .unit .unit 1 1 store
    checked actual (← body "{return x;}") [] (.var 1) .word (.word (word 9)) 1 1 store
    checked actual (← body "{if(c){return;}else{return;}}") [true] (.ifE (.var 3) .unit .unit) .unit .unit 4 4 store
    checked actual (← body "{if(c){if(d){return;}else{return;}}else{return;}}") [true, false]
      (.ifE (.var 3) (.ifE (.var 2) .unit .unit) .unit) .unit .unit 7 7 store
  for invalid in ["{return missing;}", "{return c;}", "{}", "{if(d){return x;}}", "{return x;return y;}", "{return x();}"] do
    let rejected ← body ("{if(c){if(d)" ++ invalid ++ "else{return x;}}else{return y;}}")
    for store in stores do
      let raw ← certify actual.names actual.environment store rejected [true, false]
      have _ := raw.costed.cost_le_fuelBound
      assertTrue (raw.cost == 7 && raw.value == .word (word 9) && (actual.checkTerminalReturnTree? rejected).isNone)
        "raw skipped success incorrectly licensed whole checking"
      for fuel in [0, 4, 7, terminalReturnTreeFuelBound rejected, 40] do
        have _ := (LocalInputs.runTerminalReturnTree?_eq_none_iff (inputs := actual) (body := rejected) (fuel := fuel) (store := store))
        oldShapes actual rejected fuel store
        assertTrue (actual.runTerminalReturnTree? fuel rejected store).isNone "numeric bound bypassed invalid deep syntax"
  for content in ["{}", "{return x;return y;}", "{if(c){return x;}}"] do
    let rejected ← body content
    assertTrue (terminalReturnTreeFuelBound rejected == 0 && (actual.checkTerminalReturnTree? rejected).isNone)
      "unsupported zero bound became an acceptance certificate"
  for content in ["{return missing;}", "{if(c){return x;}else{return c;}}"] do
    let rejected ← body content
    for store in stores do
      for fuel in [0, 1, 4, 20] do oldShapes actual rejected fuel store
  let declaration ← parsed (Syntax.Parser.functionDecl .module)
    ("function f(c: Bool,d: Bool,x: Word,y: Word) returns (Word) " ++ content)
  let types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
  let arguments : List TypedRuntimeArgument := [⟨.bool, .bool true, .bool⟩, ⟨.bool, .bool false, .bool⟩,
    ⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩]
  let some boundInputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "actual declaration parameters failed to bind")
  assertTrue (decide (boundInputs.checkTerminalReturnTree? declaration.value.body = some (core, .word) ∧
    boundInputs.environment.values = arguments.reverse.map (·.value) ∧
    interpretRuntimeFunctionHeader? types declaration.value.signature = some .word) &&
    decide ((compileRuntimeFunction? types owner declaration).map (fun result => (result.core, result.returnType)) = some (core, .word) ∧
      (prepareRuntimeFunction? types owner declaration arguments).map (fun result =>
        (result.core, result.returnType, result.inputs.environment.values)) = some (core, .word, arguments.reverse.map (·.value))))
    "recursive entry compilation/preparation lost its exact body or actual ordered arguments"
  for store in stores do
    checked boundInputs declaration.value.body [true, false] core .word (.word (word 2)) 7 7 store
    for fuel in [0, 4, 7, 20] do
      assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
        boundInputs.runTerminalReturnTree? fuel declaration.value.body store)) "entry added transitions or changed a genuine body state"
    let untyped : Resolved.Environment := actual.environment.map fun entry => (entry.1, .word (word 23))
    assertTrue (decide (untyped.ids = actual.context.ids)) "untyped boundary fixture lost identity alignment"
    let badState : Core.State := ⟨.ret (.word (word 23)), [.ifBranches (.ifE (.var 2) (.var 1) (.var 0)) (.var 1) untyped.values], store⟩
    assertTrue (decide (Core.runStateful 7 (.initial core untyped.values store) = .fault (.expectedBool (.word (word 23))) badState))
      "aligned but untyped values incorrectly gained sufficient-fuel safety"

end Tests
