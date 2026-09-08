import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TerminalReturnTreeRenamingProperties
import Solcore.Frontend.TerminalReturnTreeStoreProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeResumptionProperties
import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Resolved.LocalScopeProperties

/-! Identity changes preserve complete results; store changes preserve their
observations, with distinct actual checkpoints resumed independently. Raw
selected paths replay even when whole checking rejects a deep skipped child. -/

set_option autoImplicit false

namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeInvariance", by decide⟩], by decide⟩⟩, 23⟩
private def ownerShift (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 11 }
private theorem ownerShiftInjective : Function.Injective ownerShift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change left.declarationIndex + 11 = right.declarationIndex + 11 at indices
  have original := Nat.add_right_cancel indices
  cases left; cases right; simp_all [ownerShift]
private def binderShift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 37 }
private theorem binderShiftInjective : Function.Injective binderShift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := congrArg Resolved.LocalId.binderIndex same
  change left.binderIndex + 37 = right.binderIndex + 37 at indices
  have original := Nat.add_right_cancel indices
  cases left; cases right; simp_all [binderShift]
private def mapping := binderShift ∘ ownerLocalIdMap ownerShift
private theorem mappingInjective : Function.Injective mapping :=
  binderShiftInjective.comp (ownerLocalIdMap_injective ownerShift ownerShiftInjective)
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def firstStore : Core.Store := [.word (word 91), .cellRef .word 40]
private def secondStore : Core.Store := [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def parsed {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-invariance.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed) | throw (IO.userError "fixture did not parse")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
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
      else throw (IO.userError "script disagreed with actual condition")
  | _, _ => throw (IO.userError "script disagreed with actual body shape")
termination_by choices.length

private theorem replay {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Block}
    {store : Core.Store} (certificate : Certificate table environment store source) (replacement : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost table environment replacement source certificate.value replacement certificate.cost := by
  have raw := certificate.costed.erase
  have rawReplay := raw.change_store replacement
  have costReplay := certificate.costed.change_store replacement
  have _ := (terminalReturnTreeEvaluates_store_iff (replacement := replacement)).mp raw
  have _ := (terminalReturnTreeEvaluatesWithCost_store_iff (replacement := replacement)).mp certificate.costed
  have _ := (terminalReturnTreeEvaluates_store_iff (initialStore := store) (finalStore := store)).mpr ⟨rfl, rawReplay⟩
  have _ := (terminalReturnTreeEvaluatesWithCost_store_iff (initialStore := store) (finalStore := store)).mpr ⟨rfl, costReplay⟩
  exact costReplay

private def relabeled (actual : LocalInputs) (source : Syntax.Block) : IO LocalInputs := do
  let renamed := actual.mapIds mapping mappingInjective
  let ownerOnly := actual.mapIds (ownerLocalIdMap ownerShift) (ownerLocalIdMap_injective ownerShift ownerShiftInjective)
  have _ := actual.mapIds_comp (ownerLocalIdMap ownerShift) binderShift
    (ownerLocalIdMap_injective ownerShift ownerShiftInjective) binderShiftInjective
  have _ := elaborateTerminalReturnTree?_mapIds mapping mappingInjective actual.names actual.context source
  have _ := actual.checkTerminalReturnTree?_mapIds mapping mappingInjective source
  assertTrue (decide (renamed.ids = actual.ids.map mapping ∧ renamed.context.values = actual.context.values ∧
    renamed.environment.values = actual.environment.values ∧ renamed.names.map Prod.fst = actual.names.map Prod.fst ∧
    renamed.ids = (ownerOnly.mapIds binderShift binderShiftInjective).ids ∧
    renamed.checkTerminalReturnTree? source = actual.checkTerminalReturnTree? source)) "identity change altered source meaning or ordered rows"
  if !actual.bindings.isEmpty then
    assertTrue (decide (renamed.ids ≠ actual.ids ∧ ownerOnly.ids ≠ actual.ids ∧ renamed.ids ≠ ownerOnly.ids))
      "owner/binder maps were not genuine identity changes"
  match accepted : actual.checkTerminalReturnTree? source with
  | none => pure ()
  | some _ =>
      have _ := (elaborateTerminalReturnTree?_elaborates accepted).mapIds mapping mappingInjective
      pure ()
  return renamed
private def observation (result : Option (Core.Ty × Core.StatefulRunResult)) (type : Core.Ty)
    (value : Core.Value) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match result with
  | some (actualType, .done actualValue finalStore) => decide (actualType = type ∧ actualValue = value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (actualType, .outOfFuel checkpoint) => decide (actualType = type ∧ checkpoint.store = store ∧ fuel < cost)
  | _ => false
private def checked (actual : LocalInputs) (source : Syntax.Block) (choices : List Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let renamed ← relabeled actual source
  let certificate ← certify actual.names actual.environment firstStore source choices
  have _ := replay certificate secondStore
  assertTrue (decide (actual.checkTerminalReturnTree? source = some (core, type) ∧ certificate.value = value ∧
    certificate.cost = cost ∧ terminalReturnTreeFuelBound source = bound)) "actual Core or independent value/cost/bound changed"
  let run := fun store fuel => actual.runTerminalReturnTree? fuel source store
  for fuel in List.range (bound + 3) do
    have _ := actual.runTerminalReturnTree?_done_store_iff fuel source firstStore secondStore type value
    have _ := actual.runTerminalReturnTree?_outOfFuel_store_iff fuel source firstStore secondStore type
    assertTrue (decide (run firstStore fuel ≠ run secondStore fuel)) "distinct stores disappeared from complete machine results"
    assertTrue (decide (run firstStore fuel = some (type, .done value firstStore)) ==
      decide (run secondStore fuel = some (type, .done value secondStore))) "own-store completion presence changed"
    for store in [firstStore, secondStore] do
      have _ := actual.runTerminalReturnTree?_mapIds mapping mappingInjective fuel source store
      assertTrue (decide (renamed.runTerminalReturnTree? fuel source store = run store fuel ∧
        run store fuel = some (type, Core.runStateful fuel (.initial core actual.environment.values store))))
        "identity relabeling changed a complete same-fuel actual result"
      assertTrue (observation (run store fuel) type value store cost fuel) "store replay changed value/type/threshold or its own store"
  for spent in List.range cost do
    match leftAt : run firstStore spent, rightAt : run secondStore spent with
    | some (leftType, .outOfFuel left), some (rightType, .outOfFuel right) =>
        assertTrue (decide (left ≠ right ∧ left.control = right.control ∧ left.continuation = right.continuation ∧
          left.store = firstStore ∧ right.store = secondStore)) "actual store checkpoints were erased or conflated"
        assertTrue (decide (renamed.runTerminalReturnTree? spent source firstStore = some (leftType, .outOfFuel left) ∧
          renamed.runTerminalReturnTree? spent source secondStore = some (rightType, .outOfFuel right))) "identity change replaced a genuine checkpoint"
        for remaining in List.range (cost - spent + 3) do
          have _ := LocalInputs.runTerminalReturnTree?_resume leftAt remaining
          have _ := LocalInputs.runTerminalReturnTree?_resume rightAt remaining
          let leftResumed := Core.runStateful remaining left
          let rightResumed := Core.runStateful remaining right
          assertTrue (decide (run firstStore (spent + remaining) = some (leftType, leftResumed) ∧
            run secondStore (spent + remaining) = some (rightType, rightResumed) ∧ leftResumed ≠ rightResumed ∧
            renamed.runTerminalReturnTree? (spent + remaining) source firstStore = some (leftType, leftResumed) ∧
            renamed.runTerminalReturnTree? (spent + remaining) source secondStore = some (rightType, rightResumed)))
            "resumption copied another run's store or rebuilt a checkpoint"
          assertTrue (observation (some (leftType, leftResumed)) type value firstStore (cost - spent) remaining &&
            observation (some (rightType, rightResumed)) type value secondStore (cost - spent) remaining)
            "independent actual resumption changed its residual observation"
    | _, _ => throw (IO.userError "genuine below-cost checkpoint disappeared")

private def fixture (content annotation : String) (left right : TypedRuntimeArgument) (c d : Bool)
    (choices : List Bool) (core : Core.Expr) (value : Core.Value) (cost bound : Nat) (deep : Bool := true) : IO Unit := do
  let source ← parsed (Syntax.Parser.functionDecl .module)
    (s!"function tree(c: Bool,d: Bool,x: {annotation},y: {annotation}) returns ({annotation}) " ++ content)
  let arguments : List TypedRuntimeArgument := [⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩, left, right]
  let some actual := bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments
    | throw (IO.userError "actual parsed arguments did not bind")
  assertTrue (decide (actual.environment.values = arguments.reverse.map (·.value) ∧
    interpretRuntimeFunctionHeader? types source.value.signature = some left.type)) "actual order/header changed"
  checked actual source.value.body choices core left.type value cost bound
  let some owned := bindRuntimeParameters? types (ownerShift owner) source.value.signature.parameters.elements arguments
    | throw (IO.userError "actual arguments did not bind at another owner")
  assertTrue (decide (owned.ids = actual.ids.map (ownerLocalIdMap ownerShift) ∧
    owned.checkTerminalReturnTree? source.value.body = some (core, left.type))) "owner rebinding changed the actual body"
  if deep then
    assertTrue (actual.checkTerminalReturnBody? source.value.body).isNone "recursive entry support changed the old body adapter"
    for selectedOwner in [owner, ownerShift owner] do
      assertTrue (decide ((compileRuntimeFunction? types selectedOwner source).map (fun result => (result.core, result.returnType)) =
        some (core, left.type) ∧ (prepareRuntimeFunction? types selectedOwner source arguments).map (fun result =>
          (result.core, result.returnType, result.inputs.environment.values)) = some (core, left.type, arguments.reverse.map (·.value))))
        "recursive entry changed the exact owner-independent projection or actual values"
      for store in [firstStore, secondStore] do
        for fuel in [0, cost, bound, bound + 2] do
          assertTrue (decide (runRuntimeFunction? types selectedOwner source arguments fuel store =
            actual.runTerminalReturnTree? fuel source.value.body store)) "entry changed its same-fuel recursive body result"

def frontendParsedTerminalReturnTreeInvarianceTests : IO Unit := do
  let content := "{if(c){if(d){return x;}else{return y;}}else{return x;}}"
  let core : Core.Expr := .ifE (.var 3) (.ifE (.var 2) (.var 1) (.var 0)) (.var 1)
  let closureLeft : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true],
    .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Word", (⟨.word, .word (word 9), .word⟩ : TypedRuntimeArgument), ⟨.word, .word Core.Word.maximum, .word⟩),
      ("Bool", ⟨.bool, .bool true, .bool⟩, ⟨.bool, .bool false, .bool⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩),
      ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩), ("Fn", closureLeft, closureRight)] do
    for c in [false, true] do
      for d in [false, true] do
        fixture content name left right c d (if c then [true, d] else [false]) core
          (if c && !d then right.value else left.value) (if c then 7 else 4) 7
  let left : TypedRuntimeArgument := ⟨.word, .word (word 9), .word⟩
  let right : TypedRuntimeArgument := ⟨.word, .word (word 2), .word⟩
  let mirror := "{if(c){return x;}else{if(d){return y;}else{if(c){return x;}else{return y;}}}}"
  let mirrorCore : Core.Expr := .ifE (.var 3) (.var 1) (.ifE (.var 2) (.var 0) (.ifE (.var 3) (.var 1) (.var 0)))
  for (c, d) in [(true, false), (false, true), (false, false)] do
    fixture mirror "Word" left right c d (if c then [true] else if d then [false, true] else [false, false, false])
      mirrorCore (if c then left.value else right.value) (if c then 4 else if d then 7 else 10) 10
  fixture "{return x;}" "Word" left right true false [] (.var 1) left.value 1 1 false
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  fixture "{return;}" "Unit" unit unit true false [] .unit .unit 1 1 false
  fixture "{if(c){if(d){return;}else{return;}}else{return;}}" "Unit" unit unit true false
    [true, false] (.ifE (.var 3) (.ifE (.var 2) .unit .unit) .unit) .unit 7 7
  let flags := (LocalInputs.empty.bindFresh owner "c" .bool (.bool true) .bool).bindFresh owner "d" .bool (.bool true) .bool
  let actual := (flags.bindFresh owner "x" .word left.value left.valueTyped).bindFresh owner "y" .word right.value right.valueTyped
  for invalid in ["{return missing;}", "{return c;}", "{}", "{if(d){return x;}}", "{return x;return y;}", "{return x();}"] do
    let rejected ← parsed (Syntax.Parser.block .allow) ("{if(c){if(d){return x;}else" ++ invalid ++ "}else{return y;}}")
    let renamed ← relabeled actual rejected
    let certificate ← certify actual.names actual.environment firstStore rejected [true, true]
    have _ := replay certificate secondStore
    let independent ← certify actual.names actual.environment secondStore rejected [true, true]
    have _ := (replay certificate secondStore).deterministic independent.costed
    assertTrue (decide (certificate.cost = 7 ∧ certificate.value = left.value ∧
      independent.cost = 7 ∧ independent.value = left.value) && (actual.checkTerminalReturnTree? rejected).isNone)
      "raw skipped replay became a whole acceptance certificate"
    for store in [firstStore, secondStore] do
      for fuel in [0, 4, 7, terminalReturnTreeFuelBound rejected, 40] do
        have _ := actual.runTerminalReturnTree?_mapIds mapping mappingInjective fuel rejected store
        have _ := actual.runTerminalReturnTree?_done_store_iff fuel rejected firstStore secondStore .word left.value
        have _ := actual.runTerminalReturnTree?_outOfFuel_store_iff fuel rejected firstStore secondStore .word
        assertTrue ((actual.runTerminalReturnTree? fuel rejected store).isNone &&
          (renamed.runTerminalReturnTree? fuel rejected store).isNone) "identity/store replay enabled a rejected deep body"

end Tests
