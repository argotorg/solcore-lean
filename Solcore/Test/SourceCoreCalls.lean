import Solcore.Frontend.SourceCoreCalls
import Solcore.Frontend.SourceCoreFaultSites

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreCalls

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreCalls

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 91
private def internalReason : Core.Word := word 99

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function zero() returns (Word) { return 7; }",
    "function increment(value: Word) returns (Word) { return value + 1; }",
    "function combine(a: Word, b: Word, c: Word) returns (Word) { return a + b + c; }",
    "function nested(value: Word) returns (Word) { return combine(zero(), increment(value), value) * 2; }",
    "function countdown(n: Word) returns (Word) { return n == 0 ? n : countdown(n - 1); }",
    "function even(n: Word) returns (Bool) { return n == 0 ? true : odd(n - 1); }",
    "function odd(n: Word) returns (Bool) { return n == 0 ? false : even(n - 1); }",
    "function conditional(flag: Bool, value: Word) returns (Word, Bool) { return ((flag ? increment(value) : zero()), (flag || increment(value) > 0)); }",
    "function echoProduct(value: (Word, Bool)) returns (Word, Bool) { return value; }",
    "function productCall(value: Word) returns (Word, Bool) { return echoProduct((value, true)); }",
    "function staged(comptime value: Word) returns (Word) { return value; }",
    "function stagedCall() returns (Word) { return staged(1); }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"missing call fixture {name}")

private def prepare (program : CheckedProgram) (name : String) : IO Plan := do
  let plan ← match SourceSpecializationWorklist.run program [← request program name] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"call plan failed: {reprStr result}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"call plan preparation failed: {reprStr error}")

private def seed (plan : Plan) : IO Key :=
  match plan.seedKeys with
  | key :: _ => pure key
  | [] => throw (IO.userError "missing seed")

private def rejected {error value : Type} : Except error value → Bool
  | .error _ => true
  | .ok _ => false

private def signature (specialized : SourceSpecialization.SpecializedFunction) : IO Signature := do
  match specialized.function.type with
  | .function parameter result =>
      match SourceCoreBasic.projectType (.declaration specialized.key.declaration) parameter,
          SourceCoreBasic.projectType (.declaration specialized.key.declaration) result with
      | .ok parameterType, .ok resultType => pure { key := specialized.key, parameterType, resultType }
      | _, _ => throw (IO.userError "call signature projection failed")
  | _ => throw (IO.userError "call fixture does not have function type")

private def returned (source : TypedSource) : IO ExpressionId := do
  match source.nodes.findSome? fun
    | .statement node => match node.form with
      | .returnStmt (some id) => some id
      | _ => none
    | _ => none with
  | some id => pure id
  | none => throw (IO.userError "call fixture must return one expression")

private def inputScope (source : TypedSource) : IO Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"call input rejected: {reprStr error}")) []

private structure Compiled where
  context : SourceCoreCalls.Context
  source : TypedSource
  scope : Scope
  id : ExpressionId
  lowered : LoweredExpr

private def compile (plan : Plan) (owner : Key) (administrativeCount : Nat := 0) : IO Compiled := do
  let specialized ← match SourceCompilationPlan.exactSpecialization plan owner with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"caller not found: {reprStr error}")
  let globals ← plan.specializations.reverse.mapM signature
  let source := specialized.function.typedBody
  let context : SourceCoreCalls.Context := {
    plan, owner, globals, administrativePrefix := administrativeCount
    solvedRequirements := specialized.function.solvedRequirements
    internalReason := internalReason }
  let scope ← inputScope source
  let id ← returned source
  let lowered ← match lowerExpressionWithReasons 100 context source scope id (fun _ => reason) with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError s!"call lowering rejected: {reprStr error}")
  let types := SourceCoreLocalCell.coreContext scope ++ List.replicate administrativeCount .unit ++ globals.map (·.referenceType)
  assertTrue (decide (Core.infer? types lowered.expression = some (Core.LanguageResult.resultType lowered.type)))
    "lowered call failed Core type checking"
  pure { context, source, scope, id, lowered }

/-- Test-only closures use the same public expression compiler, including
recursive calls. Allocate parameter cells in source order from one raw bundle. -/
private def closureBody (plan : Plan) (global : Signature) : IO Core.Expr := do
  let compiled ← compile plan global.key 1
  let inputs := compiled.scope.reverse
  let projection (index count : Nat) : Core.Expr :=
    let rec select (index count : Nat) (bundle : Core.Expr) : Core.Expr :=
      match count with
      | 0 => .unit
      | 1 => bundle
      | count + 2 => if index = 0 then .first bundle else select (index - 1) (count + 1) (.second bundle)
    select index count (.var index)
  let body := (inputs.zipIdx).foldr (fun ((_, type), index) body =>
    .letE (Core.OptionalCell.allocateInitialized type (projection index inputs.length)) body) compiled.lowered.expression
  assertTrue (decide (Core.infer? (global.parameterType :: compiled.context.globals.map (·.referenceType)) body =
    some (Core.LanguageResult.resultType global.resultType))) "compiled global closure body failed Core checker"
  pure body

private def execute (compiled : Compiled) (arguments : List (Option Core.Value)) (fuel : Nat := 5000) :
    IO Core.StatefulRunResult := do
  let globals := compiled.context.globals
  let references := globals.zipIdx.map fun (global, index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType global.functionType) index
  let globalStore ← globals.mapM fun global => do
    pure (present (.closure global.parameterType (Core.LanguageResult.resultType global.resultType)
      (← closureBody compiled.context.plan global) references))
  let inputs := compiled.scope.reverse
  assertTrue (inputs.length == arguments.length) "call fixture input arity mismatch"
  let inputStore := (inputs.zip arguments).map fun ((_, type), value) =>
    match value with
    | some value => present value
    | none => Core.Value.inLeft type .unit
  let inputReferences := (inputs.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) (globals.length + index)).reverse
  let environment := inputReferences ++ List.replicate compiled.context.administrativePrefix .unit ++ references
  pure (Core.runStateful fuel (.initial compiled.lowered.expression environment (globalStore ++ inputStore)))

private def testCompiledCalls (program : CheckedProgram) : IO Unit := do
  let nestedPlan ← prepare program "nested"
  let nested ← compile nestedPlan (← seed nestedPlan) 2
  match Core.LanguageResult.observeResult (← execute nested [some (scalar 4)]) with
  | .succeeded value store =>
      assertTrue (value == scalar 32) "nested/zero/three-argument calls changed their result"
      -- Four initial global cells, caller input, increment input, then combine's three inputs.
      assertTrue ((store.drop nested.context.globals.length) ==
        [present (scalar 4), present (scalar 4), present (scalar 7), present (scalar 5), present (scalar 4)])
        "calls did not allocate argument cells in source order"
  | result => throw (IO.userError s!"nested calls did not complete: {reprStr result}")
  match Core.LanguageResult.observeResult (← execute nested [none]) with
  | .failed token store =>
      assertTrue (token == reason) "nested call lost the failed argument's diagnostic"
      assertTrue (store.drop nested.context.globals.length == [.inLeft .word .unit])
        "failed argument allocated later function parameters"
  | result => throw (IO.userError s!"uninitialized call argument did not fail: {reprStr result}")
  let recursionPlan ← prepare program "countdown"
  let recursion ← compile recursionPlan (← seed recursionPlan) 1
  match Core.LanguageResult.observeResult (← execute recursion [some (scalar 4)]) with
  | .succeeded value store =>
      assertTrue (value == scalar 0) "self recursive call changed its result"
      assertTrue ((store.drop recursion.context.globals.length) ==
        [present (scalar 4), present (scalar 3), present (scalar 2), present (scalar 1), present (scalar 0)])
        "recursive calls did not retain shared store allocations"
  | result => throw (IO.userError s!"recursive call did not complete: {reprStr result}")
  match ← execute recursion [some (scalar 4)] 10 with
  | .outOfFuel checkpoint =>
      match Core.LanguageResult.observeResult (Core.runStateful 5000 checkpoint) with
      | .succeeded value _ => assertTrue (value == scalar 0) "resumed recursive call changed its result"
      | result => throw (IO.userError s!"recursive resume failed: {reprStr result}")
  | _ => throw (IO.userError "recursive call did not suspend with small fuel")
  let mutualPlan ← prepare program "even"
  let mutualCompiled ← compile mutualPlan (← seed mutualPlan)
  for (input, expected) in [(4, true), (3, false)] do
    match Core.LanguageResult.observeResult (← execute mutualCompiled [some (scalar input)]) with
    | .succeeded value store =>
        assertTrue (value == .bool expected) "mutual recursive call changed its result"
        assertTrue (store.length == mutualCompiled.context.globals.length + input + 1)
          "mutual recursion lost shared parameter allocations"
    | result => throw (IO.userError s!"mutual recursion did not complete: {reprStr result}")
  let conditionalPlan ← prepare program "conditional"
  let conditional ← compile conditionalPlan (← seed conditionalPlan)
  match Core.LanguageResult.observeResult (← execute conditional [some (.bool true), some (scalar 4)]) with
  | .succeeded value _ => assertTrue (value == .pair (scalar 5) (.bool true)) "nested conditional/tuple call failed"
  | result => throw (IO.userError s!"conditional call failed: {reprStr result}")

  let productPlan ← prepare program "productCall"
  let productEntry ← compile productPlan (← seed productPlan)
  match Core.LanguageResult.observeResult (← execute productEntry [some (scalar 8)]) with
  | .succeeded value store =>
      assertTrue (value == .pair (scalar 8) (.bool true)) "one product argument was unpacked as two parameters"
      assertTrue (store.drop productEntry.context.globals.length ==
        [present (scalar 8), present (.pair (scalar 8) (.bool true))])
        "product parameter did not retain its one-cell identity"
  | result => throw (IO.userError s!"product call failed: {reprStr result}")

private def testRejectedMetadata (program : CheckedProgram) : IO Unit := do
  let plan ← prepare program "nested"
  let compiled ← compile plan (← seed plan)
  let reject (context : SourceCoreCalls.Context) (source : TypedSource := compiled.source) : IO Unit := do
    assertTrue (rejected (lowerExpressionWithReasons 100 context source compiled.scope compiled.id (fun _ => reason)))
      "forged call metadata was accepted"
  reject { compiled.context with plan := { plan with callEdges := [] } }
  reject { compiled.context with plan := { plan with callEdges := plan.callEdges ++ plan.callEdges } }
  reject { compiled.context with globals := [] }
  reject { compiled.context with globals := compiled.context.globals ++ compiled.context.globals }
  reject { compiled.context with globals := compiled.context.globals.map fun global => { global with parameterType := .bool } }
  reject { compiled.context with globals := compiled.context.globals.map fun global => { global with resultType := .bool } }
  let altered (change : ExpressionNode → ExpressionNode) : TypedSource :=
    { compiled.source with nodes := compiled.source.nodes.map fun
      | .expression node => .expression (change node)
      | node => node }
  reject compiled.context (altered fun node => match node.form with
    | .call callee arguments target => { node with form := .call callee (arguments ++ arguments) target }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .call _ _ _ => { node with requirements := [⟨999⟩] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .reference _ (.declaration _) => { node with requirements := [⟨999⟩] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .call _ _ _ => { node with coercions := [{ requirement := ⟨999⟩, source := .word, target := .word }] }
    | _ => node)
  reject compiled.context (altered fun node => match node.form with
    | .reference _ (.declaration _) =>
        { node with coercions := [{ requirement := ⟨999⟩, source := .word, target := .word }] }
    | _ => node)
  reject { compiled.context with plan := { plan with specializations := plan.specializations.map fun specialized =>
    if specialized.key = compiled.context.owner then
      { specialized with assumptions := [ProgramSignatures.builtinIntPredicate .word] }
    else specialized } }
  let stagedPlan ← prepare program "stagedCall"
  let globals ← stagedPlan.specializations.reverse.mapM signature
  let specialized ← match SourceCompilationPlan.exactSpecialization stagedPlan (← seed stagedPlan) with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"staged caller missing: {reprStr error}")
  assertTrue (rejected (lowerExpressionWithReasons 100
    { plan := stagedPlan, owner := specialized.key, globals, administrativePrefix := 0,
      solvedRequirements := specialized.function.solvedRequirements, internalReason }
    specialized.function.typedBody [] (← returned specialized.function.typedBody) (fun _ => reason)))
    "staged call entered the ordinary monomorphic profile"

private def testCallOrder (key : Key) : IO Unit := do
  let signature : Signature := { key, parameterType := .word, resultType := .word }
  let fn := signature.functionType
  let reference := Core.Value.cellRef (Core.OptionalCell.cellType fn) 0
  let noFunction := Core.Value.inLeft fn .unit
  let body := Core.LanguageResult.success (.var 0)
  let closure := Core.Value.closure .word (Core.LanguageResult.resultType .word) body []
  let expression := call signature 0
    (Core.LanguageResult.failure .word (.word reason)) internalReason
  assertTrue (Core.LanguageResult.observeResult (Core.runStateful 100 (.initial expression [reference] [noFunction])) ==
    .failed reason [noFunction]) "failed argument did not skip the uninitialized global read"
  let install := Core.LanguageResult.success
    (.letE (.storeCell (.var 0) (.inRight .unit (.lambda .word (Core.LanguageResult.resultType .word) body)))
      (.word (word 12)))
  let installedExpression := call signature 0 install internalReason
  assertTrue (decide (Core.infer? [signature.referenceType] installedExpression =
    some (Core.LanguageResult.resultType .word))) "store-order fixture failed Core checker"
  let observed := Core.LanguageResult.observeResult
    (Core.runStateful 200 (.initial installedExpression [reference] [noFunction]))
  -- The installed closure captures the original global reference and sees the latest store.
  let capturedClosure := Core.Value.closure .word (Core.LanguageResult.resultType .word) body [reference]
  assertTrue (observed == .succeeded (scalar 12) [present capturedClosure])
    "global cell was read before the argument installed its closure"
  assertTrue (Core.LanguageResult.observeResult (Core.runStateful 100 (.initial
    (call signature 0 (Core.LanguageResult.success (.word (word 5))) internalReason)
    [reference] [present closure])) == .succeeded (scalar 5) [present closure])
    "direct call did not pass its argument payload"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"call fixtures failed source checking: {reprStr error}")
  testCompiledCalls program
  testRejectedMetadata program
  testCallOrder (← seed (← prepare program "zero"))

end Tests.SourceCoreCalls
