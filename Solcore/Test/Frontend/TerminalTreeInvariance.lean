import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Resolved.LocalScope

/-!
# Terminal tree invariance tests

Invariance of terminal return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTerminalReturnTreeInvariance
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
end

section
-- leanmerge: from Solcore.Test.FrontendTerminalReturnTreeInvarianceProperties
/-! Static relabeling needs no runtime inhabitants. Actual typed runners retain
whole checkpoints under ID maps, but replacement stores remain distinct. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTreeInvariance

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeInvariance", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-invariance.sol"⟩, 91, 6⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def environment (choice : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(id 2, right), (id 1, left), (id 0, .bool choice)]
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (choice : Bool) (left right : Actual type) : LocalInputs :=
  ⟨[⟨"y", id 2, type, right.val, right.property⟩, ⟨"x", id 1, type, left.val, left.property⟩,
    ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 2, id 1, id 0].Nodup; decide⟩
private def x := returned (ref "x")
private def y := returned (ref "y")
private def spine : Nat → Syntax.Block
  | 0 => x
  | depth + 1 => branch (spine depth) y
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates names (context type) (spine depth) (core depth) type := by
  have xE : TerminalReturnTreeElaborates names (context type) x (.var 1) type :=
    .single (.expression (.identifier (.tail (by decide) .head))
      (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head)))
  have yE : TerminalReturnTreeElaborates names (context type) y (.var 0) type :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  induction depth with
  | zero => exact xE
  | succ depth ih =>
    exact .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) .head))) ih yE
private theorem conditionCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem trueCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, spine, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private theorem yCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "y") right store 1 := .identifier .head .head
private theorem falseCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 :=
  .ifFalse (conditionCost false left right store) (.single (.expression (yCost false left right store)))

theorem arbitrary_depth_static_transport_retains_exact_core_without_runtime_values
    (depth : Nat) (type : Core.Ty) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeElaborates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type))
      (spine depth) (core depth) type ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type)) (spine depth) =
      some (core depth, type) :=
  ⟨(elaborated depth type).mapIds mapping injective,
    (elaborateTerminalReturnTree?_mapIds mapping injective names (context type) (spine depth)).trans (elaborated depth type).complete⟩

theorem nominal_static_transport_does_not_provide_a_typed_runtime_inhabitant
    (depth : Nat) (nominal : Core.DataTypeId) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context (.namedData nominal)))
      (spine depth) = some (core depth, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(arbitrary_depth_static_transport_retains_exact_core_without_runtime_values depth _ mapping injective).2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_typed_inputs_keep_all_same_fuel_optional_results_under_injective_maps
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs choice left right).mapIds mapping injective).checkTerminalReturnTree? (spine depth) = some (core depth, type) ∧
    ((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) store =
      (inputs choice left right).runTerminalReturnTree? fuel (spine depth) store :=
  ⟨((inputs choice left right).checkTerminalReturnTree?_mapIds mapping injective (spine depth)).trans (elaborated depth type).complete,
    (inputs choice left right).runTerminalReturnTree?_mapIds mapping injective fuel (spine depth) store⟩

theorem raw_replay_needs_no_checking_alignment_or_value_typing
    (depth : Nat) (left right : Core.Value) (first replacement : Core.Store) :
    TerminalReturnTreeEvaluates names (environment true left right) replacement (spine depth) left replacement ∧
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) replacement (spine depth) left replacement (3 * depth + 1) ∧
    TerminalReturnTreeEvaluates names (environment false left right) replacement (spine (depth + 1)) right replacement ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) replacement (spine (depth + 1)) right replacement 4 :=
  ⟨(trueCost depth left right first).erase.change_store replacement, (trueCost depth left right first).change_store replacement,
    (falseCost depth left right first).erase.change_store replacement, (falseCost depth left right first).change_store replacement⟩

theorem raw_and_cost_replay_equivalences_retain_both_original_stores
    (depth : Nat) (choice : Bool) (left right value : Core.Value) (initialStore finalStore replacement : Core.Store) (cost : Nat) :
    (TerminalReturnTreeEvaluates names (environment choice left right) initialStore (spine depth) value finalStore ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluates names (environment choice left right) replacement (spine depth) value replacement) ∧
    (TerminalReturnTreeEvaluatesWithCost names (environment choice left right) initialStore (spine depth) value finalStore cost ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluatesWithCost names (environment choice left right) replacement (spine depth) value replacement cost) :=
  ⟨terminalReturnTreeEvaluates_store_iff, terminalReturnTreeEvaluatesWithCost_store_iff⟩

theorem identity_transport_and_store_replay_compose_at_each_fuel_without_state_equality
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (value : Core.Value)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (first replacement : Core.Store) :
    (((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) first = some (type, .done value first) ↔
      (inputs choice left right).runTerminalReturnTree? fuel (spine depth) replacement = some (type, .done value replacement)) ∧
    ((∃ checkpoint, ((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) first =
      some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice left right).runTerminalReturnTree? fuel (spine depth) replacement = some (type, .outOfFuel checkpoint)) := by
  rw [(inputs choice left right).runTerminalReturnTree?_mapIds mapping injective fuel (spine depth) first]
  exact ⟨(inputs choice left right).runTerminalReturnTree?_done_store_iff fuel (spine depth) first replacement type value,
    (inputs choice left right).runTerminalReturnTree?_outOfFuel_store_iff fuel (spine depth) first replacement type⟩

private def shifted (localId : Resolved.LocalId) : Resolved.LocalId := ⟨localId.owner, localId.binderIndex + 7⟩
private theorem shiftedInjective : Function.Injective shifted := by
  intro ⟨ownerA, indexA⟩ ⟨ownerB, indexB⟩ same
  simp only [shifted, Resolved.LocalId.mk.injEq] at same
  obtain ⟨rfl, indexes⟩ := same
  cases Nat.add_right_cancel indexes
  rfl
private def checkpoint (depth : Nat) (choice : Bool) (left right : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (core depth) (.var 0) [right, left, .bool choice]], store⟩
private theorem exhausted {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) store =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val store)) := by
  apply LocalInputs.runTerminalReturnTree?_eq_some_iff.mpr
  refine ⟨core (depth + 1), (elaborated (depth + 1) type).complete, ?_⟩
  cases choice <;> rfl
theorem genuine_identity_changes_preserve_the_whole_arbitrary_depth_checkpoint
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    shifted (id 0) ≠ id 0 ∧
    ((inputs choice left right).mapIds shifted shiftedInjective).runTerminalReturnTree? 2 (spine (depth + 1)) store =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val store)) :=
  ⟨by decide, ((inputs choice left right).runTerminalReturnTree?_mapIds shifted shiftedInjective 2 (spine (depth + 1)) store).trans
    (exhausted depth choice left right store)⟩

theorem different_nonempty_stores_produce_different_full_checkpoints
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (tail : Core.Store) :
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.unit :: tail) =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val (.unit :: tail))) ∧
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.bool true :: tail) =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val (.bool true :: tail))) ∧
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.unit :: tail) ≠
      (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.bool true :: tail) := by
  refine ⟨exhausted depth choice left right _, exhausted depth choice left right _, ?_⟩
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private theorem completed {type : Core.Ty} (depth : Nat) (left right : Actual type) (store : Core.Store) :
    (inputs true left right).runTerminalReturnTree? (3 * depth + 1) (spine depth) store = some (type, .done left.val store) :=
  LocalInputs.runTerminalReturnTree?_eq_some_iff.mpr ⟨core depth, (elaborated depth type).complete,
    ((trueCost depth left.val right.val store).checked_runStateful_done_iff (elaborated depth type).complete rfl).mpr (Nat.le_refl _)⟩
theorem existing_typed_cells_and_captured_closures_replay_without_store_access
    (depth : Nat) (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (inputs true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) first =
      some (.cell .word, .done (.cellRef .word location) first) ∧
    (inputs true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (inputs true ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩
      ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) replacement =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) := by
  refine ⟨completed depth _ _ first, ?_, ?_⟩
  · exact (LocalInputs.runTerminalReturnTree?_done_store_iff _ _ _ first replacement _ _).mp (completed depth _ _ first)
  · exact (LocalInputs.runTerminalReturnTree?_done_store_iff _ _ _ first replacement _ _).mp (completed depth _ _ first)

private def bad : Nat → Syntax.Block
  | 0 => returned (ref "missing")
  | depth + 1 => branch y (bad depth)
private theorem badUntyped (depth : Nat) (type : Core.Ty) : ¬ ∃ result, TerminalReturnTreeHasType names (context type) (bad depth) result := by
  induction depth with
  | zero =>
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf =>
      cases leaf with
      | expression typed =>
        obtain ⟨resolved, resolution, _⟩ := typed.resolves
        have accepted := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at accepted
  | succ depth ih =>
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ _ no => exact ih ⟨result, no⟩
theorem skipped_deep_invalid_trees_replay_raw_but_remain_absent_after_both_changes
    {type : Core.Ty} (depth : Nat) (left right : Actual type) (first replacement : Core.Store) (fuel : Nat)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) first (branch (bad depth) y) right.val first 4 ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) replacement (branch (bad depth) y) right.val replacement 4 ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type)) (branch (bad depth) y) = none ∧
    ((inputs false left right).mapIds mapping injective).runTerminalReturnTree? fuel (branch (bad depth) y) replacement = none := by
  have raw : TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) first
      (branch (bad depth) y) right.val first 4 :=
    .ifFalse (conditionCost false left.val right.val first) (.single (.expression (yCost false left.val right.val first)))
  have rejected : elaborateTerminalReturnTree? names (context type) (branch (bad depth) y) = none := by
    apply elaborateTerminalReturnTree?_eq_none_iff.mpr
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ yes _ => exact badUntyped depth type ⟨result, yes⟩
  exact ⟨raw, raw.change_store replacement,
    (elaborateTerminalReturnTree?_mapIds mapping injective names (context type) _).trans rejected,
    ((inputs false left right).runTerminalReturnTree?_mapIds mapping injective fuel _ replacement).trans
      (LocalInputs.runTerminalReturnTree?_eq_none_iff.mpr rejected)⟩

private def collapse (_ : Resolved.LocalId) : Resolved.LocalId := id 0
private def notY := returned ⟨span, .unary ⟨span, .logicalNot⟩ (ref "y")⟩
private def contrast := branch (branch x notY) notY
private def contrastCore : Core.Expr := .ifE (.var 2) (.ifE (.var 2) (.var 1) (.unary .boolNot (.var 0))) (.unary .boolNot (.var 0))
private def collapsedCore : Core.Expr := .ifE (.var 0) (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0))) (.unary .boolNot (.var 0))
theorem merging_ids_changes_first_lookup_value_exact_cost_and_accepted_core (store : Core.Store) :
    ¬ Function.Injective collapse ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false (.bool false) (.bool true)) store contrast (.bool false) store 6 ∧
    TerminalReturnTreeEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store contrast (.bool true) store 7 ∧
    elaborateTerminalReturnTree? names (context .bool) contrast = some (contrastCore, .bool) ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) contrast =
      some (collapsedCore, .bool) ∧ collapsedCore ≠ contrastCore := by
  have selected : LocalExpressionEvaluatesWithCost names (environment false (.bool false) (.bool true)) store (ref "y") (.bool true) store 1 :=
    .identifier .head .head
  have mappedC : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store (ref "c") (.bool true) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) .head
  have mappedX : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store (ref "x") (.bool true) store 1 :=
    .identifier (.tail (by decide) .head) .head
  have cR : ResolvesLocalExpression (LocalNameTable.mapIds collapse names) (ref "c") (.var (id 0)) :=
    .identifier (.tail (by decide) (.tail (by decide) .head))
  have xE : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) x (.var 0) .bool :=
    .single (.expression (.identifier (.tail (by decide) .head)) (.var .head) (.var .head))
  have nE : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) notY (.unary .boolNot (.var 0)) .bool :=
    .single (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  have mapped : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) contrast collapsedCore .bool :=
    .conditional cR (.var .head) (.var .head) (.conditional cR (.var .head) (.var .head) xE nE) nE
  have originalR : ResolvesLocalExpression names (ref "c") (.var (id 0)) :=
    .identifier (.tail (by decide) (.tail (by decide) .head))
  have originalL : Resolved.Lowers (context .bool).ids (.var (id 0)) (.var 2) :=
    .var (.tail (by decide) (.tail (by decide) .head))
  have originalT : Resolved.HasType (context .bool) (.var (id 0)) .bool :=
    .var (.tail (by decide) (.tail (by decide) .head))
  have originalX : TerminalReturnTreeElaborates names (context .bool) x (.var 1) .bool :=
    .single (.expression (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))
  have originalN : TerminalReturnTreeElaborates names (context .bool) notY (.unary .boolNot (.var 0)) .bool :=
    .single (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  have original : TerminalReturnTreeElaborates names (context .bool) contrast contrastCore .bool :=
    .conditional originalR originalL originalT (.conditional originalR originalL originalT originalX originalN) originalN
  refine ⟨?_, .ifFalse (conditionCost false (.bool false) (.bool true) store) (.single (.expression (.logicalNot selected))),
    .ifTrue mappedC (.ifTrue mappedC (.single (.expression mappedX))), original.complete, mapped.complete, by decide⟩
  intro injective
  have distinct : id 2 ≠ id 0 := by decide
  exact distinct (injective (a₁ := id 2) (a₂ := id 0) rfl)

end Tests.FrontendTerminalReturnTreeInvariance
end
