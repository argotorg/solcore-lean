import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TerminalReturnBodyRenamingProperties
import Solcore.Frontend.TerminalReturnBodyStoreProperties
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties

/-! Parsed body identity changes preserve complete same-fuel machine results.
Store replay preserves actual values and thresholds, not the store-bearing
results or suspended states. Existing entry owner/store contracts also apply. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TerminalBodyInvariance", by decide⟩], by decide⟩⟩, 29⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 41 }
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 37 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have sameOwner := congrArg Resolved.LocalId.owner same
  have sameIndex := congrArg Resolved.LocalId.binderIndex same
  change left.binderIndex + 37 = right.binderIndex + 37 at sameIndex
  have originalIndex := Nat.add_right_cancel sameIndex
  cases left
  cases right
  simp_all [shift]
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def stores : List Core.Store :=
  [[.word (word 91), .bool true], [.unit, .cellRef .word 40, .bool false],
    [.closure .bool .bool (.var 0) [], .word Core.Word.maximum]]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def arguments (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-terminal-invariance.sol"⟩, content }
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
  let mapped := inputs.mapIds shift shiftInjective
  have _ := inputs.checkTerminalReturnBody?_mapIds shift shiftInjective source
  assertTrue (decide (mapped.ids = inputs.ids.map shift ∧ mapped.context.values = inputs.context.values ∧
    mapped.environment.values = inputs.environment.values ∧ mapped.names.map (·.1) = inputs.names.map (·.1)))
    "identity relabeling changed ordered values, types, spellings, or chosen IDs"
  if !inputs.bindings.isEmpty then
    assertTrue (decide (mapped.ids ≠ inputs.ids ∧ mapped.names ≠ inputs.names)) "identity map was accidentally trivial"
  assertTrue (decide (inputs.checkTerminalReturnBody? source = some (core, type) ∧
    mapped.checkTerminalReturnBody? source = some (core, type))) "exact body Core/type changed under injective relabeling"
  assertTrue (terminalReturnBodyFuelBound source == bound) "source bound changed"
  for initialStore in stores do
    let run := fun fuel => inputs.runTerminalReturnBody? fuel source initialStore
    let mappedRun := fun fuel => mapped.runTerminalReturnBody? fuel source initialStore
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTerminalReturnBody?_mapIds shift shiftInjective fuel source initialStore
      assertTrue (decide (mappedRun fuel = run fuel ∧ run fuel = some (type, Core.runStateful fuel
        (Core.State.initial core inputs.environment.values initialStore)))) "mapped full same-fuel checkpoint/result changed"
      assertTrue (match run fuel with
        | some (actualType, .done actualValue finalStore) =>
            decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = initialStore)
        | some (actualType, .outOfFuel checkpoint) =>
            decide (fuel < cost ∧ actualType = type ∧ checkpoint.store = initialStore)
        | _ => false) "store replay changed the actual value, exact cost, or its own store"
      for replacement in stores do
        have _ := inputs.runTerminalReturnBody?_done_store_iff fuel source initialStore replacement type value
        have _ := inputs.runTerminalReturnBody?_outOfFuel_store_iff fuel source initialStore replacement type
        if replacement != initialStore then
          assertTrue (decide (run fuel ≠ inputs.runTerminalReturnBody? fuel source replacement))
            "distinct stores were incorrectly erased from full results/states"
    for spent in List.range cost do
      let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
      for remaining in List.range (cost - spent + 3) do
        let resumed := Core.runStateful remaining checkpoint
        assertTrue (decide (run (spent + remaining) = some (type, resumed) ∧
          mappedRun (spent + remaining) = some (type, resumed))) "mapped same-state resumption changed"
        assertTrue (match resumed with
          | .done actualValue finalStore => decide (cost - spent ≤ remaining ∧ actualValue = value ∧ finalStore = initialStore)
          | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = initialStore)
          | _ => false) "resumption replaced the checkpoint's own store"
private def checkText (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  checkBody inputs (← body content) core type value cost bound

private def checkEntry (content : String) (supplied : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "complete declaration did not parse")
  let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements supplied
    | throw (IO.userError "actual ordered parameters did not bind")
  assertTrue (decide (inputs.environment.values = supplied.reverse.map (·.value))) "actual parameter values changed"
  checkBody inputs declaration.value.body core type value cost bound
  let singleton := match declaration.value.body.value with | [⟨_, .returnStmt _⟩] => true | _ => false
  if !singleton then
    assertTrue (returnBodyFuelBound declaration.value.body == 0) "original singleton bound broadened"
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError "invariant terminal entry did not compile")
  let some prepared := prepareRuntimeFunction? types otherOwner declaration supplied
    | throw (IO.userError "relabeled actual terminal arguments did not prepare")
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ prepared.core = core ∧
    prepared.returnType = type ∧ prepared.inputs.environment.values = supplied.reverse.map (·.value)))
    "entry relabeling changed actual Core, return type, or argument values"
  for initialStore in stores do
    for fuel in List.range (bound + 3) do
      have _ := runRuntimeFunction?_owner_eq types owner otherOwner declaration supplied fuel initialStore
      let original := runRuntimeFunction? types owner declaration supplied fuel initialStore
      assertTrue (decide (original = runRuntimeFunction? types otherOwner declaration supplied fuel initialStore))
        "owner API stopped preserving complete same-fuel results"
      assertTrue (decide (original = inputs.runTerminalReturnBody? fuel declaration.value.body initialStore))
        "entry no longer agrees with its terminal body execution"
      for replacement in stores do
        have _ := runRuntimeFunction?_done_store_iff types owner declaration supplied fuel initialStore replacement type value
        have _ := runRuntimeFunction?_outOfFuel_store_iff types owner declaration supplied fuel initialStore replacement type
        let completed := decide (original = some (type, .done value initialStore))
        let replayed := decide (runRuntimeFunction? types owner declaration supplied fuel replacement =
          some (type, .done value replacement))
        assertTrue (completed == replayed) "store API lost its own-store completion observation"

private def checkRejected (inputs : LocalInputs) (content : String) : IO Unit := do
  let source ← body content
  let mapped := inputs.mapIds shift shiftInjective
  assertTrue ((inputs.checkTerminalReturnBody? source).isNone && (mapped.checkTerminalReturnBody? source).isNone)
    "injective IDs changed whole rejection of written syntax"
  for initialStore in stores do
    for fuel in [0, 1, 4, 13, terminalReturnBodyFuelBound source, 50] do
      assertTrue ((inputs.runTerminalReturnBody? fuel source initialStore).isNone &&
        (mapped.runTerminalReturnBody? fuel source initialStore).isNone) "store/identity change enabled a rejected body"

def frontendParsedTerminalBodyInvarianceTests : IO Unit := do
  checkText LocalInputs.empty "{ return; }" .unit .unit .unit 1 1
  for choice in [false, true] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      "function parameters(c: Bool, t: Word, f: Word) returns (Word) { return t; }"
      | throw (IO.userError "parameter declaration did not parse")
    let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "actual typed arguments did not bind")
    checkText inputs " /* source */ { return ((t)); } " (.var 1) .word (.word (word 7)) 1 1
    for content in ["{ return c ? ~t : f; }", "{ if(c){return ~t;}else{return f;} }"] do
      checkText inputs content (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
        (.word (if choice then (word 7).bitNot else word 9)) (if choice then 6 else 4) 6
    checkText inputs "{ if(c){return t < f;}else{return t >= f;} }"
      (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0))))
      .bool (.bool choice) (if choice then 14 else 16) 16
    checkText inputs "{ return c && t < f; }" (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false))
      .bool (.bool choice) (if choice then 14 else 4) 14
    checkText inputs "{ if(c){return;}else{return;} }" (.ifE (.var 2) .unit .unit) .unit .unit 4 4
    for content in ["{}", "{ return missing; }", "{ return c ? t : missing; }", "{ return c ? missing : f; }",
        "{ if(c){return t;}else{return missing;} }", "{ if(c){return missing;}else{return f;} }",
        "{ if(c){return t;}else{return c;} }", "{ if(c){return c;}else{return f;} }",
        "{ if(t){return t;}else{return f;} }", "{ if(c){return t;} }",
        "{ return t; return f; }", "{ if(c){return t;}else{return f;} return t; }",
        "{ if(c){if(c){return t;}else{return f;}}else{return f;} }"] do checkRejected inputs content
    for invalid in [s!"{Core.wordModulus}", "t / f", "t(c)"] do
      checkRejected inputs ("{ if(c){return t;}else{return " ++ invalid ++ ";} }")
      checkRejected inputs ("{ if(c){return " ++ invalid ++ ";}else{return f;} }")
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
      for content in ["{ return c ? t : f; }", "{ if(c){return t;}else{return f;} }"] do
        checkEntry (s!"function values(c: Bool, t: {name}, f: {name}) returns ({name}) " ++ content)
          [⟨.bool, .bool choice, .bool⟩, left, right] (.ifE (.var 2) (.var 1) (.var 0))
          left.type (if choice then left.value else right.value) 4 4
  for content in ["", "{ return t; } trailing", "{ if(c){return t;}else{return f;} } trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "incomplete canonical body consumption accepted"

end Tests
