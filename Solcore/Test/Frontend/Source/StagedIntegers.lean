import Solcore

/-!
# Staged integer tests

Closed staged integers: calls, intrinsics and locals, with their tamper checks.
-/

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerCalls
/-! Whole-program regressions for direct staged-integer source calls. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerCalls

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-call module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-call fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private def functionNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction := do
  let signature ← signatureNamed program name
  match program.functions.filter fun function =>
      function.declaration == signature.id with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def directCalls (function : CheckedFunction) :
    List ExpressionNode :=
  function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .call _ _ (.declaration _) => some node
        | _ => none
    | .statement _ => none

private def monoRequest (signature : ProgramFunctionSignature) :
    SourceSpecializationWorklist.Request := {
  declaration := signature.id
  parameterSubstitution := []
}

private def runWorklist (label : String) (program : CheckedProgram)
    (signature : ProgramFunctionSignature) (budget : Nat) :
    IO SourceSpecializationWorklist.Outcome :=
  match SourceSpecializationWorklist.run program [monoRequest signature]
      budget with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError
      s!"{label}: worklist failed: {reprStr error}")

private def specializationKey (signature : ProgramFunctionSignature) :
    SourceSpecialization.SpecializationKey := {
  declaration := signature.id
  arguments := []
}

private def positiveSource : String := String.intercalate "\n" [
  "function dec(comptime x: integer) returns (comptime<integer>) {",
  "  return integerSub(x, 1);",
  "}",
  "function dec2(x: integer) returns (comptime<integer>) {",
  "  return dec(dec(x));",
  "}",
  "function legacyDec(x: integer) returns (integer) {",
  "  return integerSub(x, 1);",
  "}",
  "function baseline() returns (Word) {",
  "  return wordFromInteger(dec(10));",
  "}",
  "function legacyFallback() returns (Word) {",
  "  return wordFromInteger(legacyDec(10));",
  "}",
  "function repeated() returns (Word) {",
  "  return wordFromInteger(integerAdd(dec(10), dec(4)));",
  "}",
  "function nested() returns (Word) {",
  "  return wordFromInteger(dec2(10));",
  "}",
  "function eagerBranches() returns (Word) {",
  "  return wordFromInteger(true ? dec(10) : dec(0));",
  "}"
]

private def limits (budget : Nat) : Limits := {
  checkingFuel := 1024
  specializationBudget := budget
  executionFuel := 2048
}

private def assertPreparedWord (name : String) (expected : Core.Word)
    (store : Core.Store := []) : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: staged-call preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: staged source calls were not erased to one Word constant"
  assertTrue (decide (prepared.run? [] 2048 store =
      some (.done (.word expected) store)))
    s!"{name}: staged source-call execution changed value or store"

private def testTypedCarrierAndStandaloneBoundary : IO Unit := do
  let program ← checkedProgram positiveSource
  let decSignature ← signatureNamed program "dec"
  let dec ← functionNamed program "dec"
  assertTrue (decSignature.parameterTypes == [Ty.integer] &&
      decSignature.parameterComptime == [true] &&
      decSignature.returnTypes == [Ty.integer] &&
      decSignature.returnComptime &&
      dec.returnComptime &&
      dec.type == Ty.function Ty.integer Ty.integer)
    "comptime parameter/result contract disappeared or entered the function type"
  let input ← match dec.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"dec retained {inputs.length} typed inputs")
  assertTrue (input.scheme == .mono Ty.integer && input.comptime &&
      input.id.owner == dec.declaration)
    "integer parameter lost its exact monomorphic comptime binder"

  let dec2Signature ← signatureNamed program "dec2"
  let dec2 ← functionNamed program "dec2"
  assertTrue (dec2Signature.parameterComptime == [false] &&
      dec2Signature.returnComptime && dec2.returnComptime &&
      dec2.typedBody.inputs.map (·.comptime) == [false])
    "comptime result incorrectly forced an explicit parameter marker"

  let baseline ← functionNamed program "baseline"
  let call ← match directCalls baseline with
    | [call] => pure call
    | calls => throw (IO.userError
        s!"baseline retained {calls.length} direct calls")
  match call.form with
  | .call callee [argument] (.declaration instantiation) => do
      assertTrue (instantiation.declaration == decSignature.id &&
          instantiation.parameterSubstitution.isEmpty &&
          instantiation.predicates.isEmpty &&
          instantiation.parameterComptime == [true] &&
          instantiation.returnComptime &&
          instantiation.type == Ty.function Ty.integer Ty.integer &&
          call.type == Ty.integer && call.requirements.isEmpty &&
          call.coercions.isEmpty)
        "direct integer call lost its exact resolution or result metadata"
      match baseline.typedBody.lookupExpression? callee with
      | some calleeNode =>
          match calleeNode.form with
          | .reference spelling (.declaration reference) =>
              assertTrue (spelling == "dec" && reference == instantiation &&
                  calleeNode.type == instantiation.type &&
                  calleeNode.requirements.isEmpty &&
                  calleeNode.coercions.isEmpty)
                "direct integer callee lost identity, spelling, or metadata"
          | _ => throw (IO.userError
              s!"direct integer callee changed form: {reprStr calleeNode}")
      | none => throw (IO.userError "direct integer callee was absent")
      match baseline.typedBody.lookupExpression? argument with
      | some argumentNode =>
          match argumentNode.form with
          | .integerLiteral _ resolution =>
              assertTrue (argumentNode.type == Ty.integer &&
                  resolution.rawValue == 10 &&
                  resolution.targetType == Ty.integer &&
                  argumentNode.requirements == [resolution.requirement] &&
                  argumentNode.coercions.isEmpty)
                "direct-call argument lost exact integer literal evidence"
          | _ => throw (IO.userError
              s!"direct-call argument changed form: {reprStr argumentNode}")
      | none => throw (IO.userError "direct-call argument was absent")
  | _ => throw (IO.userError
      s!"baseline direct call changed shape: {reprStr call}")
  match SourceCoreElaboration.evaluateStagedInteger
      baseline.solvedRequirements baseline.typedBody call.id with
  | .error error =>
      assertTrue (decide (error.site = .occurrence call.id.occurrence) &&
          error.reason == .stagedIntegerExpressionNotClosed)
        s!"standalone evaluator rejected the direct call incorrectly: {reprStr error}"
  | .ok value => throw (IO.userError
      s!"standalone evaluator unexpectedly acquired whole-program authority: {reprStr value}")

private def testPlansAndBudgets : IO Unit := do
  let program ← checkedProgram positiveSource
  let dec ← signatureNamed program "dec"
  let dec2 ← signatureNamed program "dec2"
  let baseline ← signatureNamed program "baseline"
  let repeated ← signatureNamed program "repeated"
  let nested ← signatureNamed program "nested"
  let decKey := specializationKey dec
  let dec2Key := specializationKey dec2
  let baselineKey := specializationKey baseline
  let repeatedKey := specializationKey repeated
  let nestedKey := specializationKey nested

  let baselineFunction ← functionNamed program "baseline"
  let baselineOccurrence ← match directCalls baselineFunction with
    | [call] => pure call.id
    | _ => throw (IO.userError "baseline lost its direct call")
  match ← runWorklist "baseline budget one" program baseline 1 with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.map (·.key) = [baselineKey] ∧
          plan.callEdges = [{
            caller := baselineKey
            occurrence := baselineOccurrence
            callee := decKey
          }] ∧ next = decKey ∧ pending.length = 1))
        "baseline budget exhaustion lost its admitted edge or pending callee"
  | outcome => throw (IO.userError
      s!"baseline budget one unexpectedly completed: {reprStr outcome}")
  match ← runWorklist "baseline budget two" program baseline 2 with
  | .complete plan =>
      assertTrue (decide (plan.seedKeys = [baselineKey] ∧
          plan.specializations.map (·.key) = [baselineKey, decKey] ∧
          plan.callEdges = [{
            caller := baselineKey
            occurrence := baselineOccurrence
            callee := decKey
          }]))
        "baseline plan changed FIFO specialization or exact edge order"
  | outcome => throw (IO.userError
      s!"baseline budget two did not complete: {reprStr outcome}")

  let repeatedFunction ← functionNamed program "repeated"
  let repeatedOccurrences := (directCalls repeatedFunction).map (·.id)
  assertTrue (repeatedOccurrences.length == 2)
    "repeated fixture lost one direct call occurrence"
  match ← runWorklist "repeated calls" program repeated 2 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.key) =
          [repeatedKey, decKey] ∧
          plan.callEdges.map (fun edge =>
            (edge.caller, edge.occurrence, edge.callee)) =
          repeatedOccurrences.map fun occurrence =>
            (repeatedKey, occurrence, decKey)))
        "repeated calls were deduplicated as edges or reordered"
  | outcome => throw (IO.userError
      s!"repeated-call plan did not complete: {reprStr outcome}")

  let nestedFunction ← functionNamed program "nested"
  let dec2Function ← functionNamed program "dec2"
  let nestedOccurrence ← match directCalls nestedFunction with
    | [call] => pure call.id
    | _ => throw (IO.userError "nested root lost its dec2 call")
  let dec2Occurrences := (directCalls dec2Function).map (·.id)
  assertTrue (dec2Occurrences.length == 2)
    "dec2 lost its inner/outer direct-call occurrences"
  match ← runWorklist "nested budget two" program nested 2 with
  | .budgetExhausted plan next pending =>
      let expectedEdges : List SourceSpecializationWorklist.CallEdge :=
        [{ caller := nestedKey, occurrence := nestedOccurrence,
           callee := dec2Key }] ++
        dec2Occurrences.map fun occurrence =>
          { caller := dec2Key, occurrence, callee := decKey }
      assertTrue (decide (plan.specializations.map (·.key) =
          [nestedKey, dec2Key] ∧ plan.callEdges = expectedEdges ∧
          next = decKey ∧ pending.length = 2))
        "nested budget exposure lost FIFO calls or duplicate pending requests"
  | outcome => throw (IO.userError
      s!"nested budget two unexpectedly completed: {reprStr outcome}")
  match ← runWorklist "nested budget three" program nested 3 with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.key) =
          [nestedKey, dec2Key, decKey] ∧ plan.callEdges.length = 3))
        "nested call chain changed its distinct specialization order"
  | outcome => throw (IO.userError
      s!"nested budget three did not complete: {reprStr outcome}")

private def testRequirementLedgerIsolation : IO Unit := do
  let program ← checkedProgram positiveSource
  let dec ← functionNamed program "dec"
  let repeated ← functionNamed program "repeated"
  let decRequirements := dec.solvedRequirements.map (·.id)
  let callerRequirements := repeated.solvedRequirements.map (·.id)
  assertTrue (decRequirements.length == 1 &&
      callerRequirements.length == 2 &&
      decRequirements.head? == callerRequirements.head?)
    "fixture no longer exposes function-local requirement-ID overlap"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 77)]
  assertPreparedWord "repeated" (Core.Word.ofNatModulo 12) store

private def testPublicExecution : IO Unit := do
  assertPreparedWord "baseline" (Core.Word.ofNatModulo 9)
  assertPreparedWord "legacyFallback" (Core.Word.ofNatModulo 9)
  assertPreparedWord "nested" (Core.Word.ofNatModulo 8)
  assertPreparedWord "eagerBranches" (Core.Word.ofNatModulo 9)

private def testIntegerRootBoundary : IO Unit := do
  let program ← checkedProgram positiveSource
  let legacyDec ← functionNamed program "legacyDec"
  let input ← match legacyDec.typedBody.inputs with
    | [input] => pure input
    | _ => throw (IO.userError "integer root fixture lost its input")
  let moduleId ← mainModule
  match prepare (workspace positiveSource) (Seed.named moduleId "legacyDec")
      (limits 1) with
  | .error (.linking (.sourceCore error)) =>
      assertTrue (decide (error.site = .binder input.id) &&
          error.reason == .unsupportedType Ty.integer)
        s!"integer root failed at the wrong boundary: {reprStr error}"
  | result => throw (IO.userError
      s!"integer source function escaped as a runtime root: {reprStr result}")

private def testRuntimeComptimeBoundaries : IO Unit := do
  let moduleId ← mainModule
  let closedParameterSource := String.intercalate "\n" [
    "function identity(comptime value: Word) returns (Word) { return value; }",
    "function main() returns (Word) { return identity(7); }"
  ]
  let prepared ← match prepare (workspace closedParameterSource)
      (Seed.named moduleId "main") (limits 2) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"closed comptime argument was rejected: {reprStr error}")
  let seven := Core.Word.ofNatModulo 7
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.run? [] 64 = some (.done (.word seven) [])))
    "closed literal did not satisfy a comptime parameter"

  let runtimeArgumentSource := String.intercalate "\n" [
    "function identity(comptime value: Word) returns (Word) { return value; }",
    "function main(value: Word) returns (Word) { return identity(value); }"
  ]
  match prepare (workspace runtimeArgumentSource) (Seed.named moduleId "main")
      (limits 2) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"runtime argument crossed a comptime parameter: {reprStr result}")

  let deferredRuntimeArgumentSource := String.intercalate "\n" [
    "function identity(comptime value: Word) returns (Word) { return value; }",
    "function producer(value: Word) returns (Word) { return value; }",
    "function main(value: Word) returns (Word) { return identity(producer(value)); }"
  ]
  match prepare (workspace deferredRuntimeArgumentSource)
      (Seed.named moduleId "main") (limits 3) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred call crossed a comptime parameter: {reprStr result}")

  let runtimeLocalArgumentSource := String.intercalate "\n" [
    "function identity(comptime value: Word) returns (Word) { return value; }",
    "function main(value: Word) returns (Word) {",
    "  let alias: Word = value;",
    "  return identity(alias);",
    "}"
  ]
  match prepare (workspace runtimeLocalArgumentSource)
      (Seed.named moduleId "main") (limits 2) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"runtime-dependent local crossed a comptime parameter: {reprStr result}")

  let deferredLocalArgumentSource := String.intercalate "\n" [
    "function identity(comptime value: Word) returns (Word) { return value; }",
    "function producer(value: Word) returns (Word) { return value; }",
    "function main(value: Word) returns (Word) {",
    "  let alias: Word = producer(value);",
    "  return identity(alias);",
    "}"
  ]
  match prepare (workspace deferredLocalArgumentSource)
      (Seed.named moduleId "main") (limits 3) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred local crossed a comptime parameter: {reprStr result}")

  let markedRootParameter :=
    "function identity(comptime value: Word) returns (Word) { return value; }"
  match prepare (workspace markedRootParameter)
      (Seed.named moduleId "identity") (limits 1) with
  | .error (.linking (.runtimeRootComptimeParameter _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"comptime parameter escaped as a runtime root: {reprStr result}")

  let markedRootResult :=
    "function constant() returns (comptime<Word>) { return 7; }"
  match prepare (workspace markedRootResult)
      (Seed.named moduleId "constant") (limits 1) with
  | .error (.linking (.runtimeRootComptimeResult _)) => pure ()
  | result => throw (IO.userError
      s!"comptime result escaped as a runtime root: {reprStr result}")

  let markedRuntimeResult := String.intercalate "\n" [
    "function constant() returns (comptime<Word>) { return 7; }",
    "function main() returns (Word) { return constant(); }"
  ]
  match prepare (workspace markedRuntimeResult) (Seed.named moduleId "main")
      (limits 2) with
  | .ok prepared =>
      assertTrue (decide (prepared.inputTypes = [] ∧
          prepared.entry.elaborated.resolved = .word seven ∧
          prepared.run? [] 64 = some (.done (.word seven) [])))
        "marked Word result was not materialized as a closed Core constant"
  | .error error => throw (IO.userError
      s!"marked Word result was not materialized: {reprStr error}")

private def expectStagedCycle (label source root expected : String)
    (budget : Nat) : IO Unit := do
  let program ← checkedProgram source
  let expectedSignature ← signatureNamed program expected
  let expectedKey := specializationKey expectedSignature
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId root)
      (limits budget) with
  | .error (.linking (.stagedInvocationCycle key)) =>
      assertTrue (key == expectedKey)
        s!"{label}: recursion error retained the wrong key {reprStr key}"
  | result => throw (IO.userError
      s!"{label}: recursive staged call was not rejected: {reprStr result}")

private def testRecursiveBoundaries : IO Unit := do
  let selfSource := String.intercalate "\n" [
    "function loop(comptime x: integer) returns (comptime<integer>) { return loop(x); }",
    "function main() returns (Word) { return wordFromInteger(loop(1)); }"
  ]
  let selfProgram ← checkedProgram selfSource
  let loop ← signatureNamed selfProgram "loop"
  let main ← signatureNamed selfProgram "main"
  let selfOutcome ← runWorklist "self recursion" selfProgram main 2
  match selfOutcome with
  | .complete plan =>
      assertTrue (decide (plan.specializations.map (·.key) =
          [specializationKey main, specializationKey loop] ∧
          plan.callEdges.length = 2))
        "self-recursive plan did not remain finite and explicit"
  | outcome => throw (IO.userError
      s!"self-recursive plan did not close: {reprStr outcome}")
  expectStagedCycle "self recursion" selfSource "main" "loop" 2

  let mutualSource := String.intercalate "\n" [
    "function left(comptime x: integer) returns (comptime<integer>) { return right(x); }",
    "function right(comptime x: integer) returns (comptime<integer>) { return left(x); }",
    "function main() returns (Word) { return wordFromInteger(left(1)); }"
  ]
  let mutualProgram ← checkedProgram mutualSource
  let mutualMain ← signatureNamed mutualProgram "main"
  match ← runWorklist "mutual recursion" mutualProgram mutualMain 3 with
  | .complete plan =>
      assertTrue (plan.specializations.length == 3 &&
          plan.callEdges.length == 3)
        "mutual-recursive plan lost a specialization or edge"
  | outcome => throw (IO.userError
      s!"mutual-recursive plan did not close: {reprStr outcome}")
  expectStagedCycle "mutual recursion" mutualSource "main" "left" 3

  let deadSource := String.intercalate "\n" [
    "function dec(comptime x: integer) returns (comptime<integer>) { return integerSub(x, 1); }",
    "function loop(comptime x: integer) returns (comptime<integer>) { return loop(x); }",
    "function main() returns (Word) {",
    "  return wordFromInteger(true ? dec(10) : loop(0));",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace deadSource)
      (Seed.named moduleId "main") (limits 3) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"unselected recursive branch was executed: {reprStr error}")
  assertTrue (decide (prepared.run? [] 64 =
      some (.done (.word (Core.Word.ofNatModulo 9)) [])))
    "unselected recursive branch changed the selected staged value"

/-- Exercise direct integer source calls through planning, linking, and execution. -/
def testSourceStagedIntegerCalls : IO Unit := do
  testTypedCarrierAndStandaloneBoundary
  testPlansAndBudgets
  testRequirementLedgerIsolation
  testPublicExecution
  testIntegerRootBoundary
  testRuntimeComptimeBoundaries
  testRecursiveBoundaries
  IO.println "staged integer source-call checks GREEN"

end Tests.SourceStagedIntegerCalls
end

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerCallsTamper
/-! Adversarial regressions for direct staged-integer source calls. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerCallsTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def source : String := String.intercalate "\n" [
  "function combine(comptime left: integer, comptime right: integer) returns (comptime<integer>) {",
  "  let sum: integer = integerAdd(left, right);",
  "  return sum;",
  "}",
  "function entry() returns (Word) {",
  "  return wordFromInteger(combine(7, 5));",
  "}"
]

private def checkedProgram : IO CheckedProgram := do
  match checkProgram (workspace source) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-call tamper fixture failed checking: {reprStr errors}")

private def checkedProgramOf (label content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"{label}: fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature := do
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private def functionFor (program : CheckedProgram)
    (signature : ProgramFunctionSignature) : IO CheckedFunction := do
  match program.functions.filter fun function =>
      function.declaration == signature.id with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"expected one body named `{signature.name}`, found {functions.length}")

private def monoRequest (signature : ProgramFunctionSignature) :
    SourceSpecializationWorklist.Request := {
  declaration := signature.id
  parameterSubstitution := []
}

private def keyOf (signature : ProgramFunctionSignature) :
    SourceSpecialization.SpecializationKey := {
  declaration := signature.id
  arguments := []
}

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def withExpression (function : CheckedFunction) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  function with
  typedBody := changeExpression function.typedBody id change
}

private def withInputs (function : CheckedFunction)
    (inputs : List TypedBinder) : CheckedFunction := {
  function with typedBody := { function.typedBody with inputs }
}

private structure Fixture where
  program : CheckedProgram
  entrySignature : ProgramFunctionSignature
  combineSignature : ProgramFunctionSignature
  entry : CheckedFunction
  combine : CheckedFunction
  plan : SourceSpecializationWorklist.Plan
  entryKey : SourceSpecialization.SpecializationKey
  combineKey : SourceSpecialization.SpecializationKey
  call : ExpressionNode
  callee : ExpressionId
  leftArgument : ExpressionId
  rightArgument : ExpressionId
  leftRequirement : RequirementId
  rightRequirement : RequirementId
  leftInput : TypedBinder
  rightInput : TypedBinder
  leftReference : ExpressionId
  rightReference : ExpressionId

private def directCall (function : CheckedFunction) : IO ExpressionNode := do
  let calls := function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .call _ _ (.declaration _) => some node
        | _ => none
    | .statement _ => none
  match calls with
  | [call] => pure call
  | _ => throw (IO.userError
      s!"expected one direct staged call, found {calls.length}")

private def literalRequirement (function : CheckedFunction)
    (id : ExpressionId) : IO RequirementId := do
  match function.typedBody.lookupExpression? id with
  | some { form := .integerLiteral _ resolution, .. } =>
      pure resolution.requirement
  | node => throw (IO.userError
      s!"staged-call argument lost its integer literal: {reprStr node}")

private def localReference (function : CheckedFunction)
    (binder : Resolved.LocalId) : IO ExpressionId := do
  let references := function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .reference _ (.local actual) =>
            if actual == binder then some node.id else none
        | _ => none
    | .statement _ => none
  match references with
  | [reference] => pure reference
  | _ => throw (IO.userError
      s!"expected one reference to {reprStr binder}, found {references.length}")

private def fixture : IO Fixture := do
  let program ← checkedProgram
  let entrySignature ← signatureNamed program "entry"
  let combineSignature ← signatureNamed program "combine"
  let entry ← functionFor program entrySignature
  let combine ← functionFor program combineSignature
  let call ← directCall entry
  let (callee, leftArgument, rightArgument) ← match call.form with
    | .call callee [left, right] (.declaration _) =>
        pure (callee, left, right)
    | form => throw (IO.userError
        s!"direct staged call changed shape: {reprStr form}")
  let leftRequirement ← literalRequirement entry leftArgument
  let rightRequirement ← literalRequirement entry rightArgument
  let (leftInput, rightInput) ← match combine.typedBody.inputs with
    | [left, right] => pure (left, right)
    | inputs => throw (IO.userError
        s!"combine retained {inputs.length} inputs")
  let leftReference ← localReference combine leftInput.id
  let rightReference ← localReference combine rightInput.id
  let plan ← match SourceSpecializationWorklist.run program
      [monoRequest entrySignature] 2 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError
        s!"staged-call tamper plan did not complete: {reprStr result}")
  pure {
    program
    entrySignature
    combineSignature
    entry
    combine
    plan
    entryKey := keyOf entrySignature
    combineKey := keyOf combineSignature
    call
    callee
    leftArgument
    rightArgument
    leftRequirement
    rightRequirement
    leftInput
    rightInput
    leftReference
    rightReference
  }

private def planPolicy
    (argumentTypes : List Ty)
    (requirements : ExpressionNode → List RequirementId) :
    SourceCoreElaboration.StagedIntegerCallElaborator
      SourceCoreElaboration.Error :=
  fun node _ _ _ => pure {
    argumentTypes
    consumedRequirements := requirements node
    invoke := fun values => pure (values.foldl (fun sum value => sum + value) 0)
  }

private def exactPolicy :
    SourceCoreElaboration.StagedIntegerCallElaborator
      SourceCoreElaboration.Error :=
  planPolicy [Ty.integer, Ty.integer] (fun node => node.requirements)

private def expectExpressionErrorAt (label : String)
    (function : CheckedFunction) (id : ExpressionId)
    (policy : SourceCoreElaboration.StagedIntegerCallElaborator
      SourceCoreElaboration.Error)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedIntegerWith (fun error => error) policy
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed staged call evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-call error {reprStr error}"

private def expectFunctionErrorAt (label : String)
    (function : CheckedFunction) (arguments : List Int)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedIntegerFunction function arguments with
  | .ok value => throw (IO.userError
      s!"{label}: malformed staged function evaluated to {value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-function error {reprStr error}"

private def testCallExpressionContract (fixture : Fixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedIntegerWith id exactPolicy
      fixture.entry.solvedRequirements fixture.entry.typedBody fixture.call.id with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (12 : Int) ∧
          evaluated.consumedRequirements =
            [fixture.leftRequirement, fixture.rightRequirement]))
        "staged-call callback baseline lost value or argument requirement order"
  | .error error => throw (IO.userError
      s!"staged-call callback baseline failed: {reprStr error}")

  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.call.id.occurrence
  let wrongNodeType := withExpression fixture.entry fixture.call.id fun node =>
    { node with type := Ty.word }
  expectExpressionErrorAt "staged call result type" wrongNodeType
    fixture.call.id exactPolicy callSite fun reason =>
      reason == .stagedIntegerTypeMismatch Ty.integer Ty.word

  let coercion : CoercionStep := {
    requirement := fixture.leftRequirement
    source := Ty.integer
    target := Ty.integer
  }
  let coerced := withExpression fixture.entry fixture.call.id fun node =>
    { node with coercions := [coercion] }
  expectExpressionErrorAt "staged call coercion" coerced fixture.call.id
    exactPolicy callSite fun reason => reason == .coercionsPresent [coercion]

  let required := withExpression fixture.entry fixture.call.id fun node =>
    { node with requirements := [fixture.leftRequirement] }
  let noRequirements := planPolicy [Ty.integer, Ty.integer] (fun _ => [])
  expectExpressionErrorAt "staged call requirements" required fixture.call.id
    noRequirements callSite fun reason =>
      reason == .stagedIntegerCallRequirementsMismatch
        [fixture.leftRequirement] []

  let shortPlan := planPolicy [Ty.integer] (fun node => node.requirements)
  expectExpressionErrorAt "staged call policy arity" fixture.entry
    fixture.call.id shortPlan callSite fun reason =>
      reason == .stagedIntegerCallArgumentArityMismatch 1 2

  let wrongArgument := withExpression fixture.entry fixture.leftArgument
    fun node => { node with type := Ty.word }
  expectExpressionErrorAt "staged call argument type" wrongArgument
    fixture.call.id exactPolicy
    (.occurrence fixture.leftArgument.occurrence) fun reason =>
      reason == .stagedIntegerTypeMismatch Ty.integer Ty.word

private def testFunctionAndInputContract (fixture : Fixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedIntegerFunction fixture.combine
      [(7 : Int), (5 : Int)] with
  | .ok value =>
      assertTrue (value == (12 : Int))
        "staged function baseline changed its exact integer result"
  | .error error => throw (IO.userError
      s!"staged function baseline failed: {reprStr error}")

  expectFunctionErrorAt "staged function argument arity" fixture.combine
    [(7 : Int)] (.declaration fixture.combine.declaration) fun reason =>
      reason == .stagedIntegerArgumentArityMismatch 2 1

  let wrongFunctionType : CheckedFunction := {
    fixture.combine with type := Ty.function Ty.integer Ty.word
  }
  let expectedType := Ty.function
    (Ty.productMany [Ty.integer, Ty.integer]) Ty.integer
  expectFunctionErrorAt "staged function type" wrongFunctionType
    [(7 : Int), (5 : Int)] (.declaration fixture.combine.declaration)
    fun reason => reason == .stagedIntegerFunctionTypeMismatch expectedType
      (Ty.function Ty.integer Ty.word)

  let foreignOwner : Resolved.DeclarationId := {
    fixture.combine.declaration with
    declarationIndex := fixture.combine.declaration.declarationIndex + 100
  }
  let foreignInput : TypedBinder := {
    fixture.leftInput with
    id := { fixture.leftInput.id with owner := foreignOwner }
  }
  let foreignInputs := withInputs fixture.combine
    [foreignInput, fixture.rightInput]
  expectFunctionErrorAt "foreign staged input" foreignInputs
    [(7 : Int), (5 : Int)] (.binder foreignInput.id) fun reason =>
      reason == .ownerMismatch fixture.combine.declaration foreignOwner

  let wrongTypeInput : TypedBinder := {
    fixture.leftInput with scheme := .mono Ty.word
  }
  let wrongTypeInputs := withInputs fixture.combine
    [wrongTypeInput, fixture.rightInput]
  expectFunctionErrorAt "staged input type" wrongTypeInputs
    [(7 : Int), (5 : Int)] (.binder wrongTypeInput.id) fun reason =>
      reason == .stagedIntegerTypeMismatch Ty.integer Ty.word

  let typeVariable : TypeVarId := ⟨93⟩
  let quantifiedInput : TypedBinder := {
    fixture.leftInput with
    scheme := { quantified := [typeVariable], body := Ty.integer }
  }
  let quantifiedInputs := withInputs fixture.combine
    [quantifiedInput, fixture.rightInput]
  expectFunctionErrorAt "quantified staged input" quantifiedInputs
    [(7 : Int), (5 : Int)] (.binder quantifiedInput.id) fun reason =>
      reason == .polymorphicInput [typeVariable]

  let duplicateInput : TypedBinder := {
    fixture.rightInput with id := fixture.leftInput.id
  }
  let duplicateInputs := withInputs fixture.combine
    [fixture.leftInput, duplicateInput]
  expectFunctionErrorAt "duplicate staged input" duplicateInputs
    [(7 : Int), (5 : Int)] (.binder duplicateInput.id) fun reason =>
      reason == .duplicateInput duplicateInput.id

private def testCalleeReferenceContract (fixture : Fixture) : IO Unit := do
  let leftSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.leftReference.occurrence
  let misspelled := withExpression fixture.combine fixture.leftReference
    fun node => { node with
      form := .reference "forged_left" (.local fixture.leftInput.id) }
  expectFunctionErrorAt "staged input reference spelling" misspelled
    [(7 : Int), (5 : Int)] leftSite fun reason =>
      reason == .stagedIntegerLocalSpellingMismatch fixture.leftInput.id
        fixture.leftInput.name "forged_left"

  let foreignOwner : Resolved.DeclarationId := {
    fixture.combine.declaration with
    declarationIndex := fixture.combine.declaration.declarationIndex + 101
  }
  let foreign : Resolved.LocalId := {
    owner := foreignOwner
    binderIndex := fixture.leftInput.id.binderIndex
  }
  let foreignReference := withExpression fixture.combine fixture.leftReference
    fun node => { node with
      form := .reference fixture.leftInput.name (.local foreign) }
  expectFunctionErrorAt "foreign staged input reference" foreignReference
    [(7 : Int), (5 : Int)] leftSite fun reason =>
      reason == .ownerMismatch fixture.combine.declaration foreignOwner

  let unknown : Resolved.LocalId := {
    owner := fixture.combine.declaration
    binderIndex := fixture.combine.typedBody.nodes.length + 100
  }
  let unknownReference := withExpression fixture.combine fixture.leftReference
    fun node => { node with
      form := .reference fixture.leftInput.name (.local unknown) }
  expectFunctionErrorAt "unknown staged input reference" unknownReference
    [(7 : Int), (5 : Int)] leftSite fun reason =>
      reason == .unknownLocal unknown

private def expectCallEdgesMismatch (label : String) (fixture : Fixture)
    (actual : List SourceSpecializationWorklist.CallEdge) : IO Unit := do
  let tampered : SourceSpecializationWorklist.Plan := {
    fixture.plan with callEdges := actual
  }
  match SourceCoreDirectLinking.validatePlan fixture.program tampered with
  | .error (.callEdgesMismatch expected found) =>
      assertTrue (decide (expected = fixture.plan.callEdges ∧ found = actual))
        s!"{label}: plan error lost exact edge lists"
  | result => throw (IO.userError
      s!"{label}: malformed edge plan produced {reprStr result}")

private def testPlanEdgeValidation (fixture : Fixture) : IO Unit := do
  let edge ← match fixture.plan.callEdges with
    | [edge] => pure edge
    | edges => throw (IO.userError
        s!"staged-call plan retained {edges.length} edges")
  expectCallEdgesMismatch "missing staged-call edge" fixture []
  expectCallEdgesMismatch "wrong staged-call edge" fixture
    [{ edge with callee := fixture.entryKey }]
  expectCallEdgesMismatch "duplicate staged-call edge" fixture [edge, edge]

private def testPredicateEvidenceForwarded : IO Unit := do
  let predicateSource := String.intercalate "\n" [
    "trait Marker<T> {}",
    "impl Marker<integer> {}",
    "function marked(comptime value: integer) returns (comptime<integer>) where integer: Marker {",
    "  return integerAdd(value, 1);",
    "}",
    "function relay(comptime value: integer) returns (comptime<integer>) where integer: Marker {",
    "  return marked(value);",
    "}",
    "function entry() returns (Word) {",
    "  return wordFromInteger(relay(3));",
    "}"
  ]
  let program ← checkedProgramOf "predicate-bearing staged call"
    predicateSource
  let entrySignature ← signatureNamed program "entry"
  let entry ← functionFor program entrySignature
  let call ← directCall entry
  let predicates ← match call.form with
    | .call _ [_] (.declaration instantiation) =>
        if instantiation.predicates.isEmpty then
          throw (IO.userError
            "predicate-bearing staged call lost its declaration predicate")
        else
          pure instantiation.predicates
    | form => throw (IO.userError
        s!"predicate-bearing staged call changed shape: {reprStr form}")
  let outcome ← match SourceSpecializationWorklist.run program
      [monoRequest entrySignature] 3 with
    | .ok outcome@(.complete _) => pure outcome
    | result => throw (IO.userError
        s!"predicate-bearing staged call did not plan: {reprStr result}")
  assertTrue (!predicates.isEmpty)
    "predicate-bearing staged call lost its declaration predicate"
  let linked ← match SourceCoreDirectLinking.link program outcome with
    | .ok linked => pure linked
    | .error error => throw (IO.userError
        s!"predicate-bearing staged call did not link: {reprStr error}")
  let linkedEntry ← match linked.findEntry? (keyOf entrySignature) with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "predicate-bearing staged call lost its linked entry")
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 19)]
  assertTrue (decide (linkedEntry.run? [] 4096 store = some
      (.done (.word (Core.Word.ofNatModulo 4)) store)))
    "proof-only integer call evidence changed the result or store"

/-- Reject forged staged-call metadata, binders, local edges, and call plans,
while retaining exact proof-only predicate evidence across nested calls. -/
def testSourceStagedIntegerCallsTamper : IO Unit := do
  let value ← fixture
  testCallExpressionContract value
  testFunctionAndInputContract value
  testCalleeReferenceContract value
  testPlanEdgeValidation value
  testPredicateEvidenceForwarded
  IO.println "staged integer source-call tamper checks GREEN"

end Tests.SourceStagedIntegerCallsTamper
end

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerIntrinsics
/-! End-to-end regressions for the first closed staged-integer intrinsic slice. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerIntrinsics

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-integer test module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-integer fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry =>
        entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.find? fun signature =>
      signature.name == name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "staged-integer fixture root is not a valued return")
  | roots => throw (IO.userError
      s!"staged-integer fixture retained {roots.length} roots")

private def positiveSource : String :=
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  String.intercalate "\n" [
    "function basic() returns (Word) {",
    "  return wordFromInteger(integerSub(10, 3));",
    "}",
    "function negative() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}",
    "function deepNegative() returns (Word) {",
    "  return wordFromInteger(integerSub(0, " ++ successor ++ "));",
    "}",
    "function exactNegativeModulus() returns (Word) {",
    "  return wordFromInteger(integerSub(0, " ++ modulus ++ "));",
    "}",
    "function positiveWrap() returns (Word) {",
    "  return wordFromInteger(integerSub(" ++ successor ++ ", 1));",
    "}",
    "function hexadecimal() returns (Word) {",
    "  return wordFromInteger(integerSub(0x20, 0x01));",
    "}",
    "function directHexadecimal() returns (Word) {",
    "  return wordFromInteger(0x100);",
    "}",
    "function nested() returns (Word) {",
    "  return wordFromInteger(integerSub(integerSub(20, 3), integerSub(9, 4)));",
    "}",
    "function grouped() returns (Word) {",
    "  return wordFromInteger((integerSub((5), (8))));",
    "}",
    "function direct() returns (Word) {",
    "  return wordFromInteger(" ++ successor ++ ");",
    "}"
  ]

private def expandedSource : String :=
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  let plusFive := toString (Core.wordModulus + 5)
  let plusSeven := toString (Core.wordModulus + 7)
  let halfModulus : Nat := 2 ^ 128
  let half := toString halfModulus
  String.intercalate "\n" [
    "function addHugeNegative() returns (Word) {",
    "  return wordFromInteger(integerAdd(" ++ plusFive ++
      ", integerSub(0, " ++ plusSeven ++ ")));",
    "}",
    "function addNegatives() returns (Word) {",
    "  return wordFromInteger(integerAdd(integerSub(0, 5), integerSub(0, 8)));",
    "}",
    "function arithmeticNested() returns (Word) {",
    "  return wordFromInteger(integerSub(integerAdd(20, integerSub(0, 3)), integerAdd(4, 5)));",
    "}",
    "function mulPower() returns (Word) {",
    "  return wordFromInteger(integerMul(" ++ half ++ ", " ++ half ++ "));",
    "}",
    "function mulNegative() returns (Word) {",
    "  return wordFromInteger(integerMul(integerSub(0, 3), 5));",
    "}",
    "function mulNegativeBoth() returns (Word) {",
    "  return wordFromInteger(integerMul(integerSub(0, 3), integerSub(0, 5)));",
    "}",
    "function mulZero() returns (Word) {",
    "  return wordFromInteger(integerMul(0, integerSub(0, " ++ plusSeven ++ ")));",
    "}",
    "function mulNested() returns (Word) {",
    "  return wordFromInteger(integerMul(integerAdd(7, integerSub(0, 2)), integerSub(6, 3)));",
    "}",
    "function mulEqBeforeModulo() returns (Bool) {",
    "  return integerEq(integerMul(" ++ modulus ++ ", " ++ modulus ++ "), 0);",
    "}",
    "function wordToModulo() returns (Word) {",
    "  return wordFromInteger(wordToInteger(" ++ successor ++ "));",
    "}",
    "function wordToGrouped() returns (Word) {",
    "  return wordFromInteger(wordToInteger((" ++ successor ++ ")));",
    "}",
    "function wordRoundtripNegative() returns (Word) {",
    "  return wordFromInteger(wordToInteger(wordFromInteger(integerSub(0, 1))));",
    "}",
    "function wordBridgeNested() returns (Word) {",
    "  return wordFromInteger(integerAdd(wordToInteger(wordFromInteger(integerSub(0, 3))), 5));",
    "}",
    "function wordLiteralArithmetic() returns (Word) {",
    "  return wordFromInteger(integerAdd(wordToInteger(" ++ successor ++ "), 2));",
    "}",
    "function wordBridgeComparison() returns (Bool) {",
    "  return integerEq(wordToInteger(wordFromInteger(integerSub(0, 1))), integerSub(0, 1));",
    "}",
    "function eqBeforeModulo() returns (Bool) {",
    "  return integerEq(0, " ++ modulus ++ ");",
    "}",
    "function eqSignedExact() returns (Bool) {",
    "  return integerEq(integerAdd(" ++ plusFive ++
      ", integerSub(0, " ++ plusSeven ++ ")), integerSub(0, 2));",
    "}",
    "function ltBeforeModulo() returns (Bool) {",
    "  return integerLt(" ++ successor ++ ", 2);",
    "}",
    "function ltNegative() returns (Bool) {",
    "  return integerLt(integerSub(0, 2), integerSub(0, 1));",
    "}",
    "function ltNegativeReverse() returns (Bool) {",
    "  return integerLt(integerSub(0, 1), integerSub(0, 2));",
    "}",
    "function eqConditional() returns (Word) {",
    "  return integerEq(0, " ++ modulus ++ ") ? 11 : 22;",
    "}",
    "function ltConditional() returns (Word) {",
    "  return integerLt(integerSub(0, 2), integerSub(0, 1)) ? 33 : 44;",
    "}",
    "function typedSpine() returns (Bool) {",
    "  return integerLt(integerAdd(1, 2), integerSub(4, 5));",
    "}"
  ]

private def limits : Limits := {
  checkingFuel := 1024
  specializationBudget := 1
  executionFuel := 4096
}

private def assertPreparedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: staged intrinsic tree was not erased to one Word constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 9)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: public execution changed its Word value or store"

private def assertPreparedExpandedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: expanded public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: expanded arithmetic was not erased to one Word constant"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 17), .bool false]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: expanded arithmetic changed its result or store"

private def assertPreparedExpandedBool (moduleId : Workspace.ModuleId)
    (name : String) (expected : Bool) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: comparison preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .bool expected ∧
      prepared.entry.elaborated.core = .bool expected))
    s!"{name}: staged comparison was not erased to one Bool constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 23)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.bool expected) store)))
    s!"{name}: staged comparison changed its result or store"

private def assertPreparedExpandedConditional
    (moduleId : Workspace.ModuleId) (name : String) (condition : Bool)
    (thenValue elseValue expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: comparison conditional preparation failed: {reprStr error}")
  let expectedResolved : Resolved.Expr :=
    .ifE (.bool condition) (.word thenValue) (.word elseValue)
  let expectedCore : Core.Expr :=
    .ifE (.bool condition) (.word thenValue) (.word elseValue)
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    s!"{name}: conditional did not retain its erased Bool condition"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 29)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: erased comparison did not drive the expected branch"

private def builtinIntegerEvidence (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate Ty.integer &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intInteger) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def builtinWordEvidence (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate Ty.word &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intWord) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def expectBuiltinCallee (source : TypedSource)
    (callee : ExpressionId) (expected : BuiltinFunctionId) : IO Unit :=
  match source.lookupExpression? callee with
  | some node =>
      match node.form with
      | .reference spelling (.builtinFunction actual) =>
          assertTrue (decide (actual = expected ∧
              node.type = expected.type ∧ spelling = expected.spelling ∧
              node.requirements = [] ∧ node.coercions = []))
            s!"builtin callee `{expected.spelling}` lost its exact identity or type"
      | _ => throw (IO.userError
          s!"builtin callee `{expected.spelling}` changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"builtin callee `{expected.spelling}` changed shape: {reprStr node}")

private def expectBuiltinCall (function : CheckedFunction)
    (id : ExpressionId) (expected : BuiltinFunctionId) :
    IO (List ExpressionId) := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee arguments (.builtinFunction actual) =>
          assertTrue (decide (actual = expected ∧
              arguments.length = expected.parameterTypes.length ∧
              node.type = expected.returnType ∧ node.requirements = [] ∧
              node.coercions = []))
            s!"builtin call `{expected.spelling}` lost its exact signature"
          expectBuiltinCallee function.typedBody callee expected
          pure arguments
      | _ => throw (IO.userError
          s!"builtin call `{expected.spelling}` changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"builtin call `{expected.spelling}` changed shape: {reprStr node}")

private def expectIntegerLiteral (function : CheckedFunction)
    (id : ExpressionId) (source : Syntax.CoreLiteralValue)
    (rawValue : Nat) : IO RequirementId := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral actual resolution =>
          assertTrue (decide (node.type = Ty.integer ∧ actual = source ∧
              resolution.rawValue = rawValue ∧
              resolution.targetType = Ty.integer ∧
              node.requirements = [resolution.requirement] ∧
              node.coercions = []))
            "staged integer literal lost its exact source, target, or requirement"
          let solved := function.solvedRequirements.filter fun row =>
            row.id == resolution.requirement
          match solved with
          | [evidence] =>
              assertTrue (builtinIntegerEvidence evidence)
                "staged integer literal retained the wrong Int evidence"
          | _ => throw (IO.userError
              "staged integer literal did not retain unique Int<integer> evidence")
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"staged integer literal changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"staged integer literal changed shape: {reprStr node}")

private def expectWordLiteral (function : CheckedFunction)
    (id : ExpressionId) (source : Syntax.CoreLiteralValue)
    (rawValue : Nat) : IO RequirementId := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral actual resolution =>
          assertTrue (decide (node.type = Ty.word ∧ actual = source ∧
              resolution.rawValue = rawValue ∧
              resolution.targetType = Ty.word ∧
              node.requirements = [resolution.requirement] ∧
              node.coercions = []))
            "staged Word literal lost its exact source, target, or requirement"
          let solved := function.solvedRequirements.filter fun row =>
            row.id == resolution.requirement
          match solved with
          | [evidence] =>
              assertTrue (builtinWordEvidence evidence)
                "staged Word literal retained the wrong Int<Word> evidence"
          | _ => throw (IO.userError
              "staged Word literal did not retain unique Int<Word> evidence")
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"staged Word literal changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"staged Word literal changed shape: {reprStr node}")

private def testTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "negative"
  let root ← returnedExpression function
  let (inner, left, right) ←
    match function.typedBody.lookupExpression? root with
    | some outer =>
        match outer.form with
        | .call callee [inner] (.builtinFunction .wordFromInteger) =>
            assertTrue (decide (outer.type = Ty.word ∧
                outer.requirements = [] ∧ outer.coercions = []))
              "wordFromInteger call lost its exact result metadata"
            expectBuiltinCallee function.typedBody callee .wordFromInteger
            match function.typedBody.lookupExpression? inner with
            | some innerNode =>
                match innerNode.form with
                | .call innerCallee [left, right]
                    (.builtinFunction .integerSub) =>
                    assertTrue (decide (innerNode.type = Ty.integer ∧
                        innerNode.requirements = [] ∧
                        innerNode.coercions = []))
                      "integerSub call lost its exact result metadata"
                    expectBuiltinCallee function.typedBody innerCallee
                      .integerSub
                    pure (inner, left, right)
                | _ => throw (IO.userError
                    s!"integerSub typed call changed form: {reprStr innerNode}")
            | node => throw (IO.userError
                s!"integerSub typed call changed shape: {reprStr node}")
        | _ => throw (IO.userError
            s!"wordFromInteger typed call changed form: {reprStr outer}")
    | node => throw (IO.userError
        s!"wordFromInteger typed call changed shape: {reprStr node}")
  let leftRequirement ← expectIntegerLiteral function left (.decimal "1") 1
  let rightRequirement ← expectIntegerLiteral function right (.decimal "2") 2
  assertTrue (decide (inner ≠ root ∧ left ≠ right ∧
      function.solvedRequirements.map (·.id) =
        [leftRequirement, rightRequirement]) &&
      function.solvedRequirements.all builtinIntegerEvidence)
    "staged intrinsic inference changed literal identity or evidence order"
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody inner with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-1 : Int) ∧
          evaluated.consumedRequirements =
            [leftRequirement, rightRequirement]))
        "direct staged evaluation lost signed subtraction or evidence order"
  | .error error => throw (IO.userError
      s!"direct staged evaluation rejected checked input: {reprStr error}")

  let signature ← signatureNamed program "negative"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "builtin functions became source specialization edges"
  | result => throw (IO.userError
      s!"builtin-only worklist did not close in one slot: {reprStr result}")

private def testBuiltinCatalog : IO Unit := do
  let expected : List BuiltinFunctionId := [
    .integerSub,
    .wordFromInteger,
    .integerAdd,
    .integerEq,
    .integerLt,
    .integerMul,
    .wordToInteger
  ]
  assertTrue (decide (BuiltinFunctionId.all = expected) &&
      decide expected.Nodup &&
      decide (expected.map BuiltinFunctionId.spelling).Nodup)
    "builtin function catalog changed order or retained duplicates"
  assertTrue (expected.all fun function =>
      builtinFunctionNamed? function.spelling == some function)
    "builtin function lookup is not total on the supported catalog"
  assertTrue (builtinFunctionNamed? "IntegerAdd" == none &&
      builtinFunctionNamed? "integerUnknown" == none)
    "builtin function lookup stopped being exact and case-sensitive"
  let integerBinary := [Ty.integer, Ty.integer]
  assertTrue (decide (
      BuiltinFunctionId.integerAdd.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerAdd.returnType = Ty.integer ∧
      BuiltinFunctionId.integerAdd.scheme =
        .mono BuiltinFunctionId.integerAdd.type ∧
      BuiltinFunctionId.integerEq.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerEq.returnType = Ty.bool ∧
      BuiltinFunctionId.integerEq.scheme =
        .mono BuiltinFunctionId.integerEq.type ∧
      BuiltinFunctionId.integerLt.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerLt.returnType = Ty.bool ∧
      BuiltinFunctionId.integerLt.scheme =
        .mono BuiltinFunctionId.integerLt.type ∧
      BuiltinFunctionId.integerMul.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerMul.returnType = Ty.integer ∧
      BuiltinFunctionId.integerMul.scheme =
        .mono BuiltinFunctionId.integerMul.type ∧
      BuiltinFunctionId.wordToInteger.parameterTypes = [Ty.word] ∧
      BuiltinFunctionId.wordToInteger.returnType = Ty.integer ∧
      BuiltinFunctionId.wordToInteger.scheme =
        .mono BuiltinFunctionId.wordToInteger.type))
    "expanded integer builtin signatures changed"

private def testExpandedTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram expandedSource
  let exactAdd ← checkedNamed program "addHugeNegative"
  let exactRoot ← returnedExpression exactAdd
  let outerArguments ← expectBuiltinCall exactAdd exactRoot .wordFromInteger
  let addId ← match outerArguments with
    | [addId] => pure addId
    | arguments => throw (IO.userError
        s!"wordFromInteger retained {arguments.length} arguments")
  let addArguments ← expectBuiltinCall exactAdd addId .integerAdd
  let (large, negative) ← match addArguments with
    | [large, negative] => pure (large, negative)
    | arguments => throw (IO.userError
        s!"integerAdd retained {arguments.length} arguments")
  let subArguments ← expectBuiltinCall exactAdd negative .integerSub
  let (zero, larger) ← match subArguments with
    | [zero, larger] => pure (zero, larger)
    | arguments => throw (IO.userError
        s!"nested integerSub retained {arguments.length} arguments")
  let largeRequirement ← expectIntegerLiteral exactAdd large
    (.decimal (toString (Core.wordModulus + 5))) (Core.wordModulus + 5)
  let zeroRequirement ← expectIntegerLiteral exactAdd zero (.decimal "0") 0
  let largerRequirement ← expectIntegerLiteral exactAdd larger
    (.decimal (toString (Core.wordModulus + 7))) (Core.wordModulus + 7)
  let exactRequirements :=
    [largeRequirement, zeroRequirement, largerRequirement]
  assertTrue (decide (exactAdd.solvedRequirements.map (·.id) =
      exactRequirements))
    "integerAdd changed source-order literal evidence"
  match SourceCoreElaboration.evaluateStagedInteger
      exactAdd.solvedRequirements exactAdd.typedBody addId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-2 : Int) ∧
          evaluated.consumedRequirements = exactRequirements))
        "integerAdd did not preserve an exact huge signed result"
  | .error error => throw (IO.userError
      s!"checked integerAdd did not stage exactly: {reprStr error}")

  let multiplication ← checkedNamed program "mulPower"
  let multiplicationRoot ← returnedExpression multiplication
  let multiplicationOuter ← expectBuiltinCall multiplication
    multiplicationRoot .wordFromInteger
  let multiplicationId ← match multiplicationOuter with
    | [multiplicationId] => pure multiplicationId
    | arguments => throw (IO.userError
        s!"multiplication conversion retained {arguments.length} arguments")
  let multiplicationArguments ← expectBuiltinCall multiplication
    multiplicationId .integerMul
  let (leftPower, rightPower) ← match multiplicationArguments with
    | [leftPower, rightPower] => pure (leftPower, rightPower)
    | arguments => throw (IO.userError
        s!"integerMul retained {arguments.length} arguments")
  let halfModulus : Nat := 2 ^ 128
  let halfSource := Syntax.CoreLiteralValue.decimal (toString halfModulus)
  let leftPowerRequirement ← expectIntegerLiteral multiplication leftPower
    halfSource halfModulus
  let rightPowerRequirement ← expectIntegerLiteral multiplication rightPower
    halfSource halfModulus
  let multiplicationRequirements :=
    [leftPowerRequirement, rightPowerRequirement]
  assertTrue (decide (multiplication.solvedRequirements.map (·.id) =
      multiplicationRequirements))
    "integerMul changed source-order literal evidence"
  match SourceCoreElaboration.evaluateStagedInteger
      multiplication.solvedRequirements multiplication.typedBody
      multiplicationId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Int.ofNat Core.wordModulus ∧
          evaluated.consumedRequirements = multiplicationRequirements))
        "2^128 * 2^128 was not evaluated as exact mathematical 2^256"
  | .error error => throw (IO.userError
      s!"checked integerMul did not stage exactly: {reprStr error}")

  let multiplicationSignature ← signatureNamed program "mulPower"
  let multiplicationRequest : SourceSpecializationWorklist.Request := {
    declaration := multiplicationSignature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [multiplicationRequest] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "integerMul became a source specialization edge"
  | result => throw (IO.userError
      s!"integerMul worklist did not close in one slot: {reprStr result}")

  let negativeMultiplication ← checkedNamed program "mulNegative"
  let negativeRoot ← returnedExpression negativeMultiplication
  let negativeOuter ← expectBuiltinCall negativeMultiplication negativeRoot
    .wordFromInteger
  let negativeMultiplicationId ← match negativeOuter with
    | [id] => pure id
    | arguments => throw (IO.userError
        s!"negative multiplication retained {arguments.length} outer arguments")
  let _ ← expectBuiltinCall negativeMultiplication negativeMultiplicationId
    .integerMul
  match SourceCoreElaboration.evaluateStagedInteger
      negativeMultiplication.solvedRequirements
      negativeMultiplication.typedBody negativeMultiplicationId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-15 : Int) ∧
          evaluated.consumedRequirements =
            negativeMultiplication.solvedRequirements.map (·.id)))
        "negative multiplication lost its exact sign or requirement order"
  | .error error => throw (IO.userError
      s!"negative integerMul did not stage exactly: {reprStr error}")

  let equality ← checkedNamed program "eqBeforeModulo"
  let equalityRoot ← returnedExpression equality
  let equalityArguments ← expectBuiltinCall equality equalityRoot .integerEq
  assertTrue (equalityArguments.length == 2)
    "integerEq lost its binary typed-IR shape"

  let spine ← checkedNamed program "typedSpine"
  let spineRoot ← returnedExpression spine
  let comparisonArguments ← expectBuiltinCall spine spineRoot .integerLt
  let (sum, difference) ← match comparisonArguments with
    | [sum, difference] => pure (sum, difference)
    | arguments => throw (IO.userError
        s!"integerLt retained {arguments.length} arguments")
  let sumArguments ← expectBuiltinCall spine sum .integerAdd
  let differenceArguments ← expectBuiltinCall spine difference .integerSub
  let literals ← match sumArguments, differenceArguments with
    | [one, two], [four, five] => pure [
        (one, .decimal "1", 1),
        (two, .decimal "2", 2),
        (four, .decimal "4", 4),
        (five, .decimal "5", 5)
      ]
    | _, _ => throw (IO.userError
        "typed comparison arithmetic lost its binary arguments")
  let mut requirements : List RequirementId := []
  for (id, source, rawValue) in literals do
    requirements := requirements ++
      [← expectIntegerLiteral spine id source rawValue]
  assertTrue (decide (spine.solvedRequirements.map (·.id) = requirements) &&
      spine.solvedRequirements.all builtinIntegerEvidence)
    "expanded comparison changed literal requirement order or evidence"

  let signature ← signatureNamed program "typedSpine"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "expanded builtins became source specialization edges"
  | result => throw (IO.userError
      s!"expanded builtin worklist did not close in one slot: {reprStr result}")

private def testWordToIntegerTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram expandedSource
  let modulo ← checkedNamed program "wordToModulo"
  let moduloRoot ← returnedExpression modulo
  let outerArguments ← expectBuiltinCall modulo moduloRoot .wordFromInteger
  let conversion ← match outerArguments with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"wordToModulo retained {arguments.length} outer arguments")
  let conversionArguments ← expectBuiltinCall modulo conversion .wordToInteger
  let literal ← match conversionArguments with
    | [literal] => pure literal
    | arguments => throw (IO.userError
        s!"wordToInteger retained {arguments.length} arguments")
  let literalRequirement ← expectWordLiteral modulo literal
    (.decimal (toString (Core.wordModulus + 1))) (Core.wordModulus + 1)
  assertTrue (decide (modulo.solvedRequirements.map (·.id) =
      [literalRequirement]) && modulo.solvedRequirements.all builtinWordEvidence)
    "wordToInteger did not retain exact Int<Word> literal evidence"
  match SourceCoreElaboration.evaluateStagedWord modulo.solvedRequirements
      modulo.typedBody literal with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo
          (Core.wordModulus + 1) ∧
          evaluated.consumedRequirements = [literalRequirement]))
        "public staged Word evaluator did not reduce before conversion"
  | .error error => throw (IO.userError
      s!"checked staged Word literal did not evaluate: {reprStr error}")
  match SourceCoreElaboration.evaluateStagedInteger modulo.solvedRequirements
      modulo.typedBody conversion with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (1 : Int) ∧
          evaluated.consumedRequirements = [literalRequirement]))
        "wordToInteger did not expose the modulo-reduced Word as nonnegative Int"
  | .error error => throw (IO.userError
      s!"checked wordToInteger did not evaluate: {reprStr error}")

  let roundtrip ← checkedNamed program "wordRoundtripNegative"
  let roundtripRoot ← returnedExpression roundtrip
  let roundtripOuter ← expectBuiltinCall roundtrip roundtripRoot
    .wordFromInteger
  let roundtripConversion ← match roundtripOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"roundtrip retained {arguments.length} outer arguments")
  let roundtripWord ← expectBuiltinCall roundtrip roundtripConversion
    .wordToInteger
  let nestedWordFrom ← match roundtripWord with
    | [word] => pure word
    | arguments => throw (IO.userError
        s!"roundtrip wordToInteger retained {arguments.length} arguments")
  let _ ← expectBuiltinCall roundtrip nestedWordFrom .wordFromInteger
  match SourceCoreElaboration.evaluateStagedInteger
      roundtrip.solvedRequirements roundtrip.typedBody roundtripConversion with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Int.ofNat Core.Word.maximum.val ∧
          evaluated.value ≠ (-1 : Int) ∧
          evaluated.consumedRequirements =
            roundtrip.solvedRequirements.map (·.id)))
        "Word roundtrip incorrectly recovered the pre-modulo negative integer"
  | .error error => throw (IO.userError
      s!"checked signed Word roundtrip did not evaluate: {reprStr error}")

  let mixed ← checkedNamed program "wordLiteralArithmetic"
  let mixedRoot ← returnedExpression mixed
  let mixedOuter ← expectBuiltinCall mixed mixedRoot .wordFromInteger
  let mixedAdd ← match mixedOuter with
    | [add] => pure add
    | arguments => throw (IO.userError
        s!"mixed Word arithmetic retained {arguments.length} outer arguments")
  let mixedArguments ← expectBuiltinCall mixed mixedAdd .integerAdd
  let (mixedConversion, mixedIntegerLiteral) ← match mixedArguments with
    | [conversion, literal] => pure (conversion, literal)
    | arguments => throw (IO.userError
        s!"mixed integerAdd retained {arguments.length} arguments")
  let mixedWordArguments ← expectBuiltinCall mixed mixedConversion
    .wordToInteger
  let mixedWordLiteral ← match mixedWordArguments with
    | [literal] => pure literal
    | arguments => throw (IO.userError
        s!"mixed wordToInteger retained {arguments.length} arguments")
  let mixedWordRequirement ← expectWordLiteral mixed mixedWordLiteral
    (.decimal (toString (Core.wordModulus + 1))) (Core.wordModulus + 1)
  let mixedIntegerRequirement ← expectIntegerLiteral mixed
    mixedIntegerLiteral (.decimal "2") 2
  let mixedRequirements := [mixedWordRequirement, mixedIntegerRequirement]
  assertTrue (decide (mixed.solvedRequirements.map (·.id) =
      mixedRequirements))
    "mixed Int<Word>/Int<integer> evidence lost source order"
  match SourceCoreElaboration.evaluateStagedInteger mixed.solvedRequirements
      mixed.typedBody mixedAdd with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (3 : Int) ∧
          evaluated.consumedRequirements = mixedRequirements))
        "mixed Word-to-integer arithmetic changed evidence consumption order"
  | .error error => throw (IO.userError
      s!"mixed Word-to-integer arithmetic did not evaluate: {reprStr error}")

  let signature ← signatureNamed program "wordToModulo"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "wordToInteger became a source specialization edge"
  | result => throw (IO.userError
      s!"wordToInteger worklist did not close in one slot: {reprStr result}")

private def testPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let maximum := Core.Word.maximum
  let zero := Core.Word.zero
  let cases : List (String × Core.Word) := [
    ("basic", Core.Word.ofNatModulo 7),
    ("negative", maximum),
    ("deepNegative", maximum),
    ("exactNegativeModulus", zero),
    ("positiveWrap", zero),
    ("hexadecimal", Core.Word.ofNatModulo 31),
    ("directHexadecimal", Core.Word.ofNatModulo 256),
    ("nested", Core.Word.ofNatModulo 12),
    ("grouped", Core.Word.ofIntModulo (-3)),
    ("direct", Core.Word.ofNatModulo 1)
  ]
  for (name, expected) in cases do
    assertPreparedWord moduleId name expected

private def testExpandedPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let wordCases : List (String × Core.Word) := [
    ("addHugeNegative", Core.Word.ofIntModulo (-2)),
    ("addNegatives", Core.Word.ofIntModulo (-13)),
    ("arithmeticNested", Core.Word.ofNatModulo 8),
    ("mulPower", Core.Word.zero),
    ("mulNegative", Core.Word.ofIntModulo (-15)),
    ("mulNegativeBoth", Core.Word.ofNatModulo 15),
    ("mulZero", Core.Word.zero),
    ("mulNested", Core.Word.ofNatModulo 15),
    ("wordToModulo", Core.Word.ofNatModulo 1),
    ("wordToGrouped", Core.Word.ofNatModulo 1),
    ("wordRoundtripNegative", Core.Word.maximum),
    ("wordBridgeNested", Core.Word.ofNatModulo 2),
    ("wordLiteralArithmetic", Core.Word.ofNatModulo 3)
  ]
  for (name, expected) in wordCases do
    assertPreparedExpandedWord moduleId name expected
  let boolCases : List (String × Bool) := [
    ("eqBeforeModulo", false),
    ("eqSignedExact", true),
    ("ltBeforeModulo", false),
    ("ltNegative", true),
    ("ltNegativeReverse", false),
    ("mulEqBeforeModulo", false),
    ("wordBridgeComparison", false)
  ]
  for (name, expected) in boolCases do
    assertPreparedExpandedBool moduleId name expected
  assertPreparedExpandedConditional moduleId "eqConditional" false
    (Core.Word.ofNatModulo 11) (Core.Word.ofNatModulo 22)
    (Core.Word.ofNatModulo 22)
  assertPreparedExpandedConditional moduleId "ltConditional" true
    (Core.Word.ofNatModulo 33) (Core.Word.ofNatModulo 44)
    (Core.Word.ofNatModulo 33)

private def testSourceDeclarationsShadowBuiltins : IO Unit := do
  let content := String.intercalate "\n" [
    "function integerSub(left: Word, right: Word) returns (Word) {",
    "  return 41;",
    "}",
    "function wordFromInteger(value: Word) returns (Word) { return value; }",
    "function shadowed() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}"
  ]
  let program ← checkedProgram content
  let function ← checkedNamed program "shadowed"
  let builtinCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.builtinFunction function), .. } =>
        some function
    | _ => none
  let declarationCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.declaration selected), .. } =>
        some selected.declaration
    | _ => none
  assertTrue (builtinCalls.isEmpty && declarationCalls.length == 2)
    "source declarations did not shadow the lowest-priority builtins"
  let moduleId ← mainModule
  let shadowLimits : Limits := { limits with specializationBudget := 3 }
  match run (workspace content) (Seed.named moduleId "shadowed") []
      shadowLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == Core.Word.ofNatModulo 41)
        "source-declaration shadowing returned the wrong Word"
  | result => throw (IO.userError
      s!"source-declaration shadowing did not execute: {reprStr result}")

private def testExpandedSourceDeclarationsShadowBuiltins : IO Unit := do
  let content := String.intercalate "\n" [
    "function integerAdd(left: Word, right: Word) returns (Word) {",
    "  return 40;",
    "}",
    "function integerEq(left: Word, right: Word) returns (Bool) {",
    "  return false;",
    "}",
    "function integerLt(left: Word, right: Word) returns (Bool) {",
    "  return true;",
    "}",
    "function integerMul(left: Word, right: Word) returns (Word) {",
    "  return 41;",
    "}",
    "function wordToInteger(value: Word) returns (Word) {",
    "  return value;",
    "}",
    "function shadowed() returns (Word) {",
    "  return integerEq(integerAdd(1, 2), 40) ? 9 :",
    "    (integerLt(1, 2) ? integerMul(wordToInteger(1), 2) : 42);",
    "}"
  ]
  let program ← checkedProgram content
  let function ← checkedNamed program "shadowed"
  let builtinCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.builtinFunction function), .. } =>
        some function
    | _ => none
  let declarationCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.declaration selected), .. } =>
        some selected.declaration
    | _ => none
  assertTrue (builtinCalls.isEmpty && declarationCalls.length == 5)
    "expanded source declarations did not shadow compiler builtins"
  let moduleId ← mainModule
  let shadowLimits : Limits := { limits with specializationBudget := 6 }
  match run (workspace content) (Seed.named moduleId "shadowed") []
      shadowLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == Core.Word.ofNatModulo 41)
        "expanded source-declaration shadowing returned the wrong Word"
  | result => throw (IO.userError
      s!"expanded source-declaration shadowing did not execute: {reprStr result}")

private def expectBodyError (label content : String)
    (accept : SourceInference.Error → Bool) : IO Unit := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label}: wrong source-inference error"
  | .ok _ => throw (IO.userError s!"{label}: invalid source was accepted")

private def testInferenceRejections : IO Unit := do
  expectBodyError "integerSub arity"
    "function bad() returns (integer) { return integerSub(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerSub 2 1
  expectBodyError "wordFromInteger arity"
    "function bad() returns (Word) { return wordFromInteger(); }"
    fun error => error == .builtinFunctionArityMismatch .wordFromInteger 1 0
  expectBodyError "integerSub operand type"
    "function bad() returns (Word) { return wordFromInteger(integerSub(true, 1)); }"
    fun error => error matches .unification _
  expectBodyError "wordFromInteger operand type"
    "function bad() returns (Word) { return wordFromInteger(true); }"
    fun error => error matches .unification _
  expectBodyError "integerAdd arity"
    "function bad() returns (integer) { return integerAdd(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerAdd 2 1
  expectBodyError "integerEq arity"
    "function bad() returns (Bool) { return integerEq(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerEq 2 1
  expectBodyError "integerLt arity"
    "function bad() returns (Bool) { return integerLt(); }"
    fun error => error == .builtinFunctionArityMismatch .integerLt 2 0
  expectBodyError "integerMul arity"
    "function bad() returns (integer) { return integerMul(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerMul 2 1
  expectBodyError "wordToInteger arity"
    "function bad() returns (integer) { return wordToInteger(); }"
    fun error => error == .builtinFunctionArityMismatch .wordToInteger 1 0
  expectBodyError "integerAdd operand type"
    "function bad() returns (integer) { return integerAdd(true, 1); }"
    fun error => error matches .unification _
  expectBodyError "integerEq operand type"
    "function bad() returns (Bool) { return integerEq(true, 1); }"
    fun error => error matches .unification _
  expectBodyError "integerLt operand type"
    "function bad() returns (Bool) { return integerLt(1, false); }"
    fun error => error matches .unification _
  expectBodyError "integerMul operand type"
    "function bad() returns (integer) { return integerMul(false, 1); }"
    fun error => error matches .unification _
  expectBodyError "wordToInteger operand type"
    "function bad() returns (integer) { return wordToInteger(false); }"
    fun error => error matches .unification _

  let blocked := String.intercalate "\n" [
    "function integerSub(left: Bool, right: Bool) returns (Bool) {",
    "  return left;",
    "}",
    "function bad() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace blocked) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate == ProgramSignatures.builtinIntPredicate Ty.bool
        | .body { error := .unification _, .. } => true
        | _ => false)
        "an incompatible source declaration produced the wrong failure"
  | .ok _ => throw (IO.userError
      "an incompatible source declaration fell through to the builtin")

  let expectExpandedNoFallback (name declaration body : String) : IO Unit := do
    let content := String.intercalate "\n" [declaration, body]
    match SourceInference.loadAndCheckProgram (workspace content) with
    | .error errors =>
        assertTrue (errors.any fun error => match error with
          | .body { error := .noTraitImplementation predicate, .. } =>
              predicate == ProgramSignatures.builtinIntPredicate Ty.bool
          | .body { error := .unification _, .. } => true
          | _ => false)
          s!"{name}: incompatible source declaration produced the wrong failure"
    | .ok _ => throw (IO.userError
        s!"{name}: incompatible source declaration fell through to builtin")
  expectExpandedNoFallback "integerAdd"
    "function integerAdd(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Word) { return wordFromInteger(integerAdd(1, 2)); }"
  expectExpandedNoFallback "integerEq"
    "function integerEq(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Bool) { return integerEq(1, 2); }"
  expectExpandedNoFallback "integerLt"
    "function integerLt(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Bool) { return integerLt(1, 2); }"
  expectExpandedNoFallback "integerMul"
    "function integerMul(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Word) { return wordFromInteger(integerMul(1, 2)); }"
  expectExpandedNoFallback "wordToInteger"
    "function wordToInteger(value: Bool) returns (Bool) { return value; }"
    "function bad() returns (Word) { return wordFromInteger(wordToInteger(1)); }"

private def testRuntimeBoundaryRejections : IO Unit := do
  let dependentProgram ← checkedProgram
    "function dependent(flag: Bool) returns (Word) { return wordFromInteger(flag ? 1 : 2); }"
  let dependent ← checkedNamed dependentProgram "dependent"
  let root ← returnedExpression dependent
  let argument ← match dependent.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call _ [argument] (.builtinFunction .wordFromInteger) =>
            pure argument
        | _ => throw (IO.userError
            "runtime-dependent fixture lost wordFromInteger call")
    | none => throw (IO.userError
        "runtime-dependent fixture lost its return expression")
  let guard ← match dependent.typedBody.lookupExpression? argument with
    | some { form := .conditional guard _ _, .. } => pure guard
    | node => throw (IO.userError
        s!"runtime-dependent fixture lost its conditional guard: {reprStr node}")
  match SourceCoreElaboration.elaborateFunction dependent with
  | .ok _ => throw (IO.userError
      "runtime-dependent staged conditional reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = .occurrence guard.occurrence ∧
          error.reason = .stagedBoolExpressionNotClosed))
        s!"runtime-dependent staged conditional produced the wrong error: {reprStr error}"

  let leakingProgram ← checkedProgram
    "function leaking() returns (integer) { return integerSub(1, 2); }"
  let leaking ← checkedNamed leakingProgram "leaking"
  match SourceCoreElaboration.elaborateFunction leaking with
  | .ok _ => throw (IO.userError
      "a staged integer escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site = .declaration leaking.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"integer leakage produced the wrong boundary error: {reprStr error}"

  let multiplicationLeakProgram ← checkedProgram
    "function leakingMul() returns (integer) { return integerMul(2, 3); }"
  let multiplicationLeak ← checkedNamed multiplicationLeakProgram "leakingMul"
  match SourceCoreElaboration.elaborateFunction multiplicationLeak with
  | .ok _ => throw (IO.userError
      "integerMul escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site =
          .declaration multiplicationLeak.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"integerMul leakage produced the wrong error: {reprStr error}"

  let wordLeakProgram ← checkedProgram
    "function leakingWord() returns (integer) { return wordToInteger(1); }"
  let wordLeak ← checkedNamed wordLeakProgram "leakingWord"
  match SourceCoreElaboration.elaborateFunction wordLeak with
  | .ok _ => throw (IO.userError
      "wordToInteger escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site = .declaration wordLeak.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"wordToInteger leakage produced the wrong error: {reprStr error}"

  let localWordProgram ← checkedProgram
    "function localWord(value: Word) returns (Word) { return wordFromInteger(wordToInteger(value)); }"
  let localWord ← checkedNamed localWordProgram "localWord"
  let localRoot ← returnedExpression localWord
  let localOuter ← expectBuiltinCall localWord localRoot .wordFromInteger
  let localConversion ← match localOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"local Word fixture retained {arguments.length} outer arguments")
  let localArguments ← expectBuiltinCall localWord localConversion
    .wordToInteger
  let localReference ← match localArguments with
    | [reference] => pure reference
    | arguments => throw (IO.userError
        s!"local wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction localWord with
  | .ok _ => throw (IO.userError
      "runtime Word local was accepted by closed staged conversion")
  | .error error =>
      assertTrue (decide (error.site = .occurrence localReference.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"runtime Word local produced the wrong staged error: {reprStr error}"

  let wordOperatorProgram ← checkedProgram
    "function wordOperator() returns (Word) { return wordFromInteger(wordToInteger(1 + 2)); }"
  let wordOperator ← checkedNamed wordOperatorProgram "wordOperator"
  let operatorRoot ← returnedExpression wordOperator
  let operatorOuter ← expectBuiltinCall wordOperator operatorRoot
    .wordFromInteger
  let operatorConversion ← match operatorOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"Word operator fixture retained {arguments.length} outer arguments")
  let operatorArguments ← expectBuiltinCall wordOperator operatorConversion
    .wordToInteger
  let operatorExpression ← match operatorArguments with
    | [expression] => pure expression
    | arguments => throw (IO.userError
        s!"operator wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction wordOperator with
  | .ok _ => throw (IO.userError
      "general runtime Word operator was accepted by staged conversion")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence operatorExpression.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"runtime Word operator produced the wrong staged error: {reprStr error}"

  let sourceCallProgram ← checkedProgram (String.intercalate "\n" [
    "function sourceWord() returns (Word) { return 7; }",
    "function stagedCall() returns (Word) {",
    "  return wordFromInteger(wordToInteger(sourceWord()));",
    "}"
  ])
  let sourceCall ← checkedNamed sourceCallProgram "stagedCall"
  let sourceCallRoot ← returnedExpression sourceCall
  let sourceCallOuter ← expectBuiltinCall sourceCall sourceCallRoot
    .wordFromInteger
  let sourceCallConversion ← match sourceCallOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"source-call fixture retained {arguments.length} outer arguments")
  let sourceCallArguments ← expectBuiltinCall sourceCall sourceCallConversion
    .wordToInteger
  let sourceCallExpression ← match sourceCallArguments with
    | [expression] => pure expression
    | arguments => throw (IO.userError
        s!"source-call wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction sourceCall with
  | .ok _ => throw (IO.userError
      "ordinary Word-returning source call entered staged conversion")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence sourceCallExpression.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"Word-returning source call produced the wrong staged error: {reprStr error}"

  let comparisonProgram ← checkedProgram
    "function dependentEq(flag: Bool) returns (Bool) { return integerEq(flag ? 1 : 2, 1); }"
  let comparison ← checkedNamed comparisonProgram "dependentEq"
  let comparisonRoot ← returnedExpression comparison
  let comparisonArguments ← expectBuiltinCall comparison comparisonRoot .integerEq
  let dependentArgument ← match comparisonArguments with
    | dependentArgument :: _ => pure dependentArgument
    | [] => throw (IO.userError
        "runtime-dependent comparison lost its first argument")
  let comparisonGuard ←
    match comparison.typedBody.lookupExpression? dependentArgument with
    | some { form := .conditional guard _ _, .. } => pure guard
    | node => throw (IO.userError
        s!"runtime-dependent comparison lost its guard: {reprStr node}")
  match SourceCoreElaboration.elaborateFunction comparison with
  | .ok _ => throw (IO.userError
      "runtime-dependent staged comparison reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence comparisonGuard.occurrence ∧
          error.reason = .stagedBoolExpressionNotClosed))
        s!"runtime-dependent comparison produced the wrong error: {reprStr error}"

/-- Exercise exact signed staging, modulo projection, builtin identity,
worklist erasure, source shadowing, and inference rejection. -/
def testSourceStagedIntegerIntrinsics : IO Unit := do
  testBuiltinCatalog
  testTypedCarrierAndWorklist
  testExpandedTypedCarrierAndWorklist
  testWordToIntegerTypedCarrierAndWorklist
  testPublicExecution
  testExpandedPublicExecution
  testSourceDeclarationsShadowBuiltins
  testExpandedSourceDeclarationsShadowBuiltins
  testInferenceRejections
  testRuntimeBoundaryRejections
  IO.println "closed staged integer intrinsics GREEN"

end Tests.SourceStagedIntegerIntrinsics
end

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerIntrinsicsTamper
/-! Adversarial regressions for closed staged-integer intrinsic metadata. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerIntrinsicsTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedFunction : IO CheckedFunction := do
  let content :=
    "function negative() returns (Word) { return wordFromInteger(integerSub(1, 2)); }"
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"staged-integer tamper fixture failed checking: {reprStr errors}")
  match program.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"staged-integer tamper fixture produced {functions.length} functions")

private structure Fixture where
  function : CheckedFunction
  root : ExpressionId
  outerCallee : ExpressionId
  inner : ExpressionId
  innerCallee : ExpressionId
  left : ExpressionId
  right : ExpressionId
  leftSource : Syntax.CoreLiteralValue
  leftResolution : IntegerLiteralResolution
  rightResolution : IntegerLiteralResolution

private def fixture : IO Fixture := do
  let function ← checkedFunction
  let root ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some root), .. } => pure root
        | _ => throw (IO.userError
            "staged-integer tamper fixture lost its valued return")
    | roots => throw (IO.userError
        s!"staged-integer tamper fixture retained {roots.length} roots")
  let (outerCallee, inner) ←
    match function.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call callee [inner] (.builtinFunction .wordFromInteger) =>
            pure (callee, inner)
        | _ => throw (IO.userError
            "staged-integer tamper fixture lost its outer builtin call")
    | none => throw (IO.userError
        "staged-integer tamper fixture lost its root expression")
  let (innerCallee, left, right) ←
    match function.typedBody.lookupExpression? inner with
    | some node =>
        match node.form with
        | .call callee [left, right] (.builtinFunction .integerSub) =>
            pure (callee, left, right)
        | _ => throw (IO.userError
            "staged-integer tamper fixture lost its inner builtin call")
    | none => throw (IO.userError
        "staged-integer tamper fixture lost its inner expression")
  let (leftSource, leftResolution) ←
    match function.typedBody.lookupExpression? left with
    | some node =>
        match node.form with
        | .integerLiteral source resolution => pure (source, resolution)
        | _ => throw (IO.userError
            "staged-integer tamper fixture lost its left literal")
    | none => throw (IO.userError
        "staged-integer tamper fixture lost its left expression")
  let rightResolution ←
    match function.typedBody.lookupExpression? right with
    | some node =>
        match node.form with
        | .integerLiteral _ resolution => pure resolution
        | _ => throw (IO.userError
            "staged-integer tamper fixture lost its right literal")
    | none => throw (IO.userError
        "staged-integer tamper fixture lost its right expression")
  pure {
    function
    root
    outerCallee
    inner
    innerCallee
    left
    right
    leftSource
    leftResolution
    rightResolution
  }

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def withExpression (fixture : Fixture) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  fixture.function with
  typedBody := changeExpression fixture.function.typedBody id change
}

private def changeSolved (fixture : Fixture) (requirement : RequirementId)
    (change : SolvedRequirement → SolvedRequirement) : CheckedFunction := {
  fixture.function with
  solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
    if solved.id = requirement then change solved else solved
}

private def expectElaborationErrorAt (label : String)
    (function : CheckedFunction) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError
      s!"{label}: malformed staged metadata reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def expectEvaluationErrorAt (label : String) (function : CheckedFunction)
    (id : ExpressionId)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody id with
  | .ok evaluated => throw (IO.userError
      s!"{label}: malformed staged metadata evaluated to {reprStr evaluated}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-evaluation error {reprStr error}"

private def expectWordEvaluationErrorAt (label : String)
    (function : CheckedFunction) (id : ExpressionId)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedWord
      function.solvedRequirements function.typedBody id with
  | .ok evaluated => throw (IO.userError
      s!"{label}: malformed staged Word metadata evaluated to {reprStr evaluated}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Word error {reprStr error}"

private def testCheckedBaseline (fixture : Fixture) : IO Unit := do
  let lowered ← match
      SourceCoreElaboration.elaborateFunction fixture.function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked staged-integer fixture did not lower: {reprStr error}")
  assertTrue (decide (lowered.resolved = .word Core.Word.maximum ∧
      lowered.core = .word Core.Word.maximum))
    "checked staged-integer fixture was not erased to maximum Word"
  match SourceCoreElaboration.evaluateStagedInteger
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.inner with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-1 : Int) ∧
          evaluated.consumedRequirements =
            [fixture.leftResolution.requirement,
              fixture.rightResolution.requirement]))
        "direct staged evaluator lost signed value or requirement order"
  | .error error => throw (IO.userError
      s!"checked staged-integer fixture did not evaluate: {reprStr error}")

private def forgedCoercion (fixture : Fixture) : CoercionStep := {
  requirement := fixture.leftResolution.requirement
  source := Ty.integer
  target := Ty.word
}

private def testOuterCallContract (fixture : Fixture) : IO Unit := do
  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.root.occurrence
  let calleeSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.outerCallee.occurrence
  let argumentSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.inner.occurrence
  let requirement := fixture.leftResolution.requirement
  let coercion := forgedCoercion fixture

  let wrongResolution := withExpression fixture fixture.root fun node => {
    node with form := match node.form with
      | .call callee arguments _ =>
          .call callee arguments (.builtinFunction .integerSub)
      | form => form
  }
  expectElaborationErrorAt "outer call resolution identity" wrongResolution
    callSite fun reason => reason == .builtinFunctionCallTypeMismatch
      .integerSub Ty.integer Ty.word

  let nonReference := withExpression fixture fixture.outerCallee fun node => {
    node with form := .group fixture.inner
  }
  expectElaborationErrorAt "outer callee reference shape" nonReference
    calleeSite fun reason =>
      reason == .builtinFunctionCalleeNotReference .wordFromInteger

  let wrongIdentity := withExpression fixture fixture.outerCallee fun node => {
    node with form := (.reference BuiltinFunctionId.wordFromInteger.spelling
      (.builtinFunction .integerSub))
  }
  expectElaborationErrorAt "outer callee builtin identity" wrongIdentity
    calleeSite fun reason => reason ==
      .builtinFunctionCalleeIdentityMismatch .wordFromInteger .integerSub

  let wrongSpelling := withExpression fixture fixture.outerCallee fun node => {
    node with form := (.reference "forgedWordFromInteger"
      (.builtinFunction .wordFromInteger))
  }
  expectElaborationErrorAt "outer callee spelling" wrongSpelling calleeSite
    fun reason => reason == .builtinFunctionCalleeSpellingMismatch
      .wordFromInteger BuiltinFunctionId.wordFromInteger.spelling
      "forgedWordFromInteger"

  let wrongCalleeType := withExpression fixture fixture.outerCallee fun node => {
    node with type := Ty.bool
  }
  expectElaborationErrorAt "outer callee type" wrongCalleeType calleeSite
    fun reason => reason == .builtinFunctionCalleeTypeMismatch
      .wordFromInteger BuiltinFunctionId.wordFromInteger.type Ty.bool

  let wrongCallType := withExpression fixture fixture.root fun node => {
    node with type := Ty.integer
  }
  expectElaborationErrorAt "outer call result type" wrongCallType callSite
    fun reason => reason == .builtinFunctionCallTypeMismatch
      .wordFromInteger Ty.word Ty.integer

  let wrongArity := withExpression fixture fixture.root fun node => {
    node with form := match node.form with
      | .call callee _ resolution => .call callee [] resolution
      | form => form
  }
  expectElaborationErrorAt "outer call arity" wrongArity callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch .wordFromInteger 1 0

  let wrongArgumentType := withExpression fixture fixture.inner fun node => {
    node with type := Ty.word
  }
  expectElaborationErrorAt "outer argument type" wrongArgumentType
    argumentSite fun reason => reason == .builtinFunctionArgumentTypeMismatch
      .wordFromInteger 0 Ty.integer Ty.word

  let callRequirements := withExpression fixture fixture.root fun node => {
    node with requirements := [requirement]
  }
  expectElaborationErrorAt "outer call requirements" callRequirements
    callSite fun reason => reason == .builtinFunctionRequirementsPresent
      .wordFromInteger [requirement]

  let callCoercions := withExpression fixture fixture.root fun node => {
    node with coercions := [coercion]
  }
  expectElaborationErrorAt "outer call coercions" callCoercions callSite
    fun reason => reason == .builtinFunctionCoercionsPresent
      .wordFromInteger [coercion]

  let calleeRequirements :=
    withExpression fixture fixture.outerCallee fun node => {
      node with requirements := [requirement]
    }
  expectElaborationErrorAt "outer callee requirements" calleeRequirements
    calleeSite fun reason => reason == .requirementsPresent [requirement]

  let calleeCoercions :=
    withExpression fixture fixture.outerCallee fun node => {
      node with coercions := [coercion]
    }
  expectElaborationErrorAt "outer callee coercions" calleeCoercions
    calleeSite fun reason => reason == .coercionsPresent [coercion]

private def testInnerCallContract (fixture : Fixture) : IO Unit := do
  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.inner.occurrence
  let calleeSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.innerCallee.occurrence
  let leftSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.left.occurrence
  let requirement := fixture.leftResolution.requirement
  let coercion := forgedCoercion fixture
  let expect label function site accept :=
    expectEvaluationErrorAt label function fixture.inner site accept

  let wrongResolution := withExpression fixture fixture.inner fun node => {
    node with form := match node.form with
      | .call callee arguments _ =>
          .call callee arguments (.builtinFunction .wordFromInteger)
      | form => form
  }
  expect "inner call resolution identity" wrongResolution callSite fun reason =>
    reason == .stagedIntegerExpressionNotClosed

  let nonReference := withExpression fixture fixture.innerCallee fun node => {
    node with form := .group fixture.left
  }
  expect "inner callee reference shape" nonReference calleeSite fun reason =>
    reason == .builtinFunctionCalleeNotReference .integerSub

  let wrongIdentity := withExpression fixture fixture.innerCallee fun node => {
    node with form := (.reference BuiltinFunctionId.integerSub.spelling
      (.builtinFunction .wordFromInteger))
  }
  expect "inner callee builtin identity" wrongIdentity calleeSite fun reason =>
    reason == .builtinFunctionCalleeIdentityMismatch
      .integerSub .wordFromInteger

  let wrongSpelling := withExpression fixture fixture.innerCallee fun node => {
    node with form := (.reference "forgedIntegerSub"
      (.builtinFunction .integerSub))
  }
  expect "inner callee spelling" wrongSpelling calleeSite fun reason =>
    reason == .builtinFunctionCalleeSpellingMismatch .integerSub
      BuiltinFunctionId.integerSub.spelling "forgedIntegerSub"

  let wrongCalleeType :=
    withExpression fixture fixture.innerCallee fun node => {
      node with type := Ty.bool
    }
  expect "inner callee type" wrongCalleeType calleeSite fun reason =>
    reason == .builtinFunctionCalleeTypeMismatch .integerSub
      BuiltinFunctionId.integerSub.type Ty.bool

  let wrongCallType := withExpression fixture fixture.inner fun node => {
    node with type := Ty.word
  }
  expect "inner call result type" wrongCallType callSite fun reason =>
    reason == .builtinFunctionCallTypeMismatch .integerSub
      Ty.integer Ty.word

  let wrongArity := withExpression fixture fixture.inner fun node => {
    node with form := match node.form with
      | .call callee _ resolution =>
          .call callee [fixture.left] resolution
      | form => form
  }
  expect "inner call arity" wrongArity callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch .integerSub 2 1

  let wrongArgumentType := withExpression fixture fixture.left fun node => {
    node with type := Ty.word
  }
  expect "inner argument type" wrongArgumentType leftSite fun reason =>
    reason == .builtinFunctionArgumentTypeMismatch .integerSub 0
      Ty.integer Ty.word

  let callRequirements := withExpression fixture fixture.inner fun node => {
    node with requirements := [requirement]
  }
  expect "inner call requirements" callRequirements callSite fun reason =>
    reason == .builtinFunctionRequirementsPresent .integerSub [requirement]

  let callCoercions := withExpression fixture fixture.inner fun node => {
    node with coercions := [coercion]
  }
  expect "inner call coercions" callCoercions callSite fun reason =>
    reason == .builtinFunctionCoercionsPresent .integerSub [coercion]

  let calleeRequirements :=
    withExpression fixture fixture.innerCallee fun node => {
      node with requirements := [requirement]
    }
  expect "inner callee requirements" calleeRequirements calleeSite fun reason =>
    reason == .requirementsPresent [requirement]

  let calleeCoercions :=
    withExpression fixture fixture.innerCallee fun node => {
      node with coercions := [coercion]
    }
  expect "inner callee coercions" calleeCoercions calleeSite fun reason =>
    reason == .coercionsPresent [coercion]

private def testLiteralCarrier (fixture : Fixture) : IO Unit := do
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.left.occurrence
  let requirement := fixture.leftResolution.requirement
  let coercion := forgedCoercion fixture
  let expect label function :=
    expectEvaluationErrorAt label function fixture.left site

  let wrongNodeType := withExpression fixture fixture.left fun node => {
    node with type := Ty.word
  }
  expect "staged literal node type" wrongNodeType fun reason =>
    reason == .stagedIntegerTypeMismatch Ty.integer Ty.word

  let wrongTarget := withExpression fixture fixture.left fun node => {
    node with form := (.integerLiteral fixture.leftSource {
      fixture.leftResolution with targetType := Ty.word
    })
  }
  expect "staged literal target" wrongTarget fun reason =>
    reason == .integerLiteralTargetTypeMismatch Ty.word Ty.integer

  let detached := withExpression fixture fixture.left fun node => {
    node with requirements := []
  }
  expect "staged literal requirement attachment" detached fun reason =>
    reason == .integerLiteralRequirementsMismatch [requirement] []

  let invalidSource := withExpression fixture fixture.left fun node => {
    node with form := (.integerLiteral (.decimal "1x")
      fixture.leftResolution)
  }
  expect "staged literal source decoding" invalidSource fun reason =>
    reason == .invalidIntegerLiteralSource (.decimal "1x")

  let sourceRawMismatch := withExpression fixture fixture.left fun node => {
    node with form := (.integerLiteral (.decimal "9")
      fixture.leftResolution)
  }
  expect "staged literal source/raw agreement" sourceRawMismatch fun reason =>
    reason == .integerLiteralRawValueMismatch 9
      fixture.leftResolution.rawValue

  let recordedRawMismatch := withExpression fixture fixture.left fun node => {
    node with form := (.integerLiteral fixture.leftSource {
      fixture.leftResolution with
      rawValue := fixture.leftResolution.rawValue + 1
    })
  }
  expect "staged literal recorded raw value" recordedRawMismatch fun reason =>
    reason == .integerLiteralRawValueMismatch fixture.leftResolution.rawValue
      (fixture.leftResolution.rawValue + 1)

  let coerced := withExpression fixture fixture.left fun node => {
    node with coercions := [coercion]
  }
  expect "staged literal coercions" coerced fun reason =>
    reason == .coercionsPresent [coercion]

private def testLiteralEvidence (fixture : Fixture) : IO Unit := do
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.left.occurrence
  let requirement := fixture.leftResolution.requirement
  let expected := fixture.leftResolution.predicate
  let wrong := ProgramSignatures.builtinIntPredicate Ty.bool
  let expect label function :=
    expectEvaluationErrorAt label function fixture.left site
  let solved ← match fixture.function.solvedRequirements.filter fun row =>
      row.id == requirement with
    | [solved] => pure solved
    | rows => throw (IO.userError
        s!"staged literal fixture retained {rows.length} matching evidence rows")

  let missing : CheckedFunction := {
    fixture.function with
    solvedRequirements := fixture.function.solvedRequirements.filter fun row =>
      row.id != requirement
  }
  expect "staged literal missing evidence" missing fun reason =>
    reason == .missingIntegerLiteralRequirement requirement

  let duplicate : CheckedFunction := {
    fixture.function with
    solvedRequirements := solved :: fixture.function.solvedRequirements
  }
  expect "staged literal duplicate evidence" duplicate fun reason =>
    reason == .duplicateIntegerLiteralRequirements requirement 2

  let predicateMismatch := changeSolved fixture requirement fun row => {
    row with predicate := wrong
  }
  expect "staged literal evidence predicate" predicateMismatch fun reason =>
    reason == .integerLiteralPredicateMismatch requirement expected wrong

  let goalMismatch := changeSolved fixture requirement fun row => {
    row with evidence := (.implementation
      (.byImpl wrong (.builtin .intInteger) []))
  }
  expect "staged literal evidence goal" goalMismatch fun reason =>
    reason == .integerLiteralEvidenceGoalMismatch requirement expected wrong

  let assumption := changeSolved fixture requirement fun row => {
    row with evidence := .assumption expected
  }
  expect "staged literal unresolved assumption" assumption fun reason =>
    reason == .unresolvedIntegerLiteralEvidence requirement

  let implementationMismatch :=
    changeSolved fixture requirement fun row => {
      row with evidence := (.implementation
        (.byImpl expected (.builtin .intWord) []))
    }
  expect "staged literal implementation identity" implementationMismatch
    fun reason => reason == .integerLiteralImplementationMismatch requirement
      (.builtin .intInteger) (.builtin .intWord)

  let premise : TypedTraitResolution.Evidence :=
    .byImpl expected (.builtin .intInteger) []
  let premisesPresent := changeSolved fixture requirement fun row => {
    row with evidence := (.implementation
      (.byImpl expected (.builtin .intInteger) [premise]))
  }
  expect "staged literal evidence premises" premisesPresent fun reason =>
    reason == .integerLiteralPremiseCountMismatch requirement 0 1

private def testCyclesAndRequirementAccounting (fixture : Fixture) : IO Unit := do
  let innerCycle := withExpression fixture fixture.inner fun node => {
    node with form := match node.form with
      | .call callee _ resolution =>
          .call callee [fixture.inner, fixture.right] resolution
      | form => form
  }
  expectEvaluationErrorAt "integerSub self-cycle" innerCycle fixture.inner
    (.occurrence fixture.inner.occurrence) fun reason =>
      reason == .stagedIntegerDepthLimit

  let groupCycle := withExpression fixture fixture.left fun node => {
    node with form := .group fixture.left, requirements := []
  }
  expectEvaluationErrorAt "staged group self-cycle" groupCycle fixture.left
    (.occurrence fixture.left.occurrence) fun reason =>
      reason == .stagedIntegerDepthLimit

  let duplicatedLiteral := withExpression fixture fixture.inner fun node => {
    node with form := match node.form with
      | .call callee _ resolution =>
          .call callee [fixture.left, fixture.left] resolution
      | form => form
  }
  expectElaborationErrorAt "duplicated staged literal edge"
    duplicatedLiteral (.declaration fixture.function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement
        fixture.leftResolution.requirement

private structure BinaryFixture where
  function : CheckedFunction
  functionId : BuiltinFunctionId
  root : ExpressionId
  call : ExpressionId
  callee : ExpressionId
  left : ExpressionId
  right : ExpressionId
  leftResolution : IntegerLiteralResolution
  rightResolution : IntegerLiteralResolution

private def binaryFixture (content : String)
    (expected : BuiltinFunctionId) : IO BinaryFixture := do
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"{expected.spelling} tamper fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"{expected.spelling} fixture produced {functions.length} functions")
  let root ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some root), .. } => pure root
        | _ => throw (IO.userError
            s!"{expected.spelling} fixture lost its valued return")
    | roots => throw (IO.userError
        s!"{expected.spelling} fixture retained {roots.length} roots")
  let call ← if (expected == .integerAdd) || (expected == .integerMul) then
      match function.typedBody.lookupExpression? root with
      | some node =>
          match node.form with
          | .call _ [argument] (.builtinFunction .wordFromInteger) =>
              pure argument
          | _ => throw (IO.userError
              s!"{expected.spelling} fixture lost its wordFromInteger boundary")
      | none => throw (IO.userError
          s!"{expected.spelling} fixture lost its root")
    else
      pure root
  let (callee, left, right) ←
    match function.typedBody.lookupExpression? call with
    | some node =>
        match node.form with
        | .call callee [left, right] (.builtinFunction actual) =>
            unless actual = expected do
              throw (IO.userError
                s!"expected {expected.spelling}, found {actual.spelling}")
            pure (callee, left, right)
        | _ => throw (IO.userError
            s!"{expected.spelling} fixture lost its binary call")
    | none => throw (IO.userError
        s!"{expected.spelling} fixture lost its call expression")
  let literalResolution (id : ExpressionId) : IO IntegerLiteralResolution :=
    match function.typedBody.lookupExpression? id with
    | some node =>
        match node.form with
        | .integerLiteral _ resolution => pure resolution
        | _ => throw (IO.userError
            s!"{expected.spelling} fixture argument is not a literal")
    | none => throw (IO.userError
        s!"{expected.spelling} fixture lost a literal expression")
  pure {
    function
    functionId := expected
    root
    call
    callee
    left
    right
    leftResolution := ← literalResolution left
    rightResolution := ← literalResolution right
  }

private def withBinaryExpression (fixture : BinaryFixture)
    (id : ExpressionId) (change : ExpressionNode → ExpressionNode) :
    CheckedFunction := {
  fixture.function with
  typedBody := changeExpression fixture.function.typedBody id change
}

private def expectBinaryErrorAt (fixture : BinaryFixture) (label : String)
    (function : CheckedFunction) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  if (fixture.functionId == .integerAdd) ||
      (fixture.functionId == .integerMul) then
    expectEvaluationErrorAt label function fixture.call site accept
  else
    expectElaborationErrorAt label function site accept

private def mismatchedBuiltin : BuiltinFunctionId → BuiltinFunctionId
  | .integerAdd => .integerSub
  | .integerEq => .integerLt
  | .integerLt => .integerEq
  | .integerMul => .integerAdd
  | .wordToInteger => .wordFromInteger
  | .integerSub => .integerAdd
  | .wordFromInteger => .integerAdd

private def testExpandedBinaryBaseline (fixture : BinaryFixture) : IO Unit := do
  let leftRequirement := fixture.leftResolution.requirement
  let rightRequirement := fixture.rightResolution.requirement
  assertTrue (decide (fixture.function.solvedRequirements.map (·.id) =
      [leftRequirement, rightRequirement]))
    s!"{fixture.functionId.spelling}: literal requirement order changed"
  let lowered ← match SourceCoreElaboration.elaborateFunction fixture.function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"{fixture.functionId.spelling}: checked fixture did not lower: {reprStr error}")
  match fixture.functionId with
  | .integerAdd =>
      assertTrue (decide (lowered.resolved =
          .word (Core.Word.ofNatModulo 3) ∧ lowered.core =
          .word (Core.Word.ofNatModulo 3)))
        "integerAdd baseline did not erase to Word 3"
      match SourceCoreElaboration.evaluateStagedInteger
          fixture.function.solvedRequirements fixture.function.typedBody
          fixture.call with
      | .ok evaluated =>
          assertTrue (decide (evaluated.value = (3 : Int) ∧
              evaluated.consumedRequirements =
                [leftRequirement, rightRequirement]))
            "integerAdd baseline changed exact value or evidence order"
      | .error error => throw (IO.userError
          s!"integerAdd baseline did not evaluate: {reprStr error}")
  | .integerMul =>
      assertTrue (decide (lowered.resolved =
          .word (Core.Word.ofNatModulo 2) ∧ lowered.core =
          .word (Core.Word.ofNatModulo 2)))
        "integerMul baseline did not erase to Word 2"
      match SourceCoreElaboration.evaluateStagedInteger
          fixture.function.solvedRequirements fixture.function.typedBody
          fixture.call with
      | .ok evaluated =>
          assertTrue (decide (evaluated.value = (2 : Int) ∧
              evaluated.consumedRequirements =
                [leftRequirement, rightRequirement]))
            "integerMul baseline changed exact value or evidence order"
      | .error error => throw (IO.userError
          s!"integerMul baseline did not evaluate: {reprStr error}")
  | .integerEq =>
      assertTrue (decide (lowered.resolved = .bool false ∧
          lowered.core = .bool false))
        "integerEq baseline did not erase to Bool false"
  | .integerLt =>
      assertTrue (decide (lowered.resolved = .bool true ∧
          lowered.core = .bool true))
        "integerLt baseline did not erase to Bool true"
  | function => throw (IO.userError
      s!"unexpected expanded tamper fixture {function.spelling}")

private def testExpandedBinaryContract (fixture : BinaryFixture) : IO Unit := do
  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.call.occurrence
  let calleeSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.callee.occurrence
  let leftSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.left.occurrence
  let requirement := fixture.leftResolution.requirement
  let coercion : CoercionStep := {
    requirement
    source := Ty.integer
    target := Ty.word
  }
  let replacement := mismatchedBuiltin fixture.functionId
  let expect label function site accept :=
    expectBinaryErrorAt fixture
      s!"{fixture.functionId.spelling} {label}" function site accept

  let wrongResolution := withBinaryExpression fixture fixture.call fun node => {
    node with form := match node.form with
      | .call callee arguments _ =>
          .call callee arguments (.builtinFunction replacement)
      | form => form
  }
  expect "call resolution identity" wrongResolution calleeSite fun reason =>
    reason == .builtinFunctionCalleeIdentityMismatch replacement
      fixture.functionId

  let nonReference := withBinaryExpression fixture fixture.callee fun node => {
    node with form := .group fixture.left
  }
  expect "callee reference shape" nonReference calleeSite fun reason =>
    reason == .builtinFunctionCalleeNotReference fixture.functionId

  let wrongIdentity := withBinaryExpression fixture fixture.callee fun node => {
    node with form := (.reference fixture.functionId.spelling
      (.builtinFunction replacement))
  }
  expect "callee builtin identity" wrongIdentity calleeSite fun reason =>
    reason == .builtinFunctionCalleeIdentityMismatch fixture.functionId
      replacement

  let forgedSpelling := "forged" ++ fixture.functionId.spelling
  let wrongSpelling := withBinaryExpression fixture fixture.callee fun node => {
    node with form := (.reference forgedSpelling
      (.builtinFunction fixture.functionId))
  }
  expect "callee spelling" wrongSpelling calleeSite fun reason =>
    reason == .builtinFunctionCalleeSpellingMismatch fixture.functionId
      fixture.functionId.spelling forgedSpelling

  let wrongCalleeType := withBinaryExpression fixture fixture.callee fun node => {
    node with type := Ty.bool
  }
  expect "callee type" wrongCalleeType calleeSite fun reason =>
    reason == .builtinFunctionCalleeTypeMismatch fixture.functionId
      fixture.functionId.type Ty.bool

  let wrongCallType := withBinaryExpression fixture fixture.call fun node => {
    node with type := Ty.word
  }
  expect "call result type" wrongCallType callSite fun reason =>
    reason == .builtinFunctionCallTypeMismatch fixture.functionId
      fixture.functionId.returnType Ty.word

  let wrongArity := withBinaryExpression fixture fixture.call fun node => {
    node with form := match node.form with
      | .call callee _ resolution =>
          .call callee [fixture.left] resolution
      | form => form
  }
  expect "call arity" wrongArity callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch fixture.functionId 2 1

  let wrongArgumentType := withBinaryExpression fixture fixture.left fun node => {
    node with type := Ty.bool
  }
  expect "argument type" wrongArgumentType leftSite fun reason =>
    reason == .builtinFunctionArgumentTypeMismatch fixture.functionId 0
      Ty.integer Ty.bool

  let callRequirements := withBinaryExpression fixture fixture.call fun node => {
    node with requirements := [requirement]
  }
  expect "call requirements" callRequirements callSite fun reason =>
    reason == .builtinFunctionRequirementsPresent fixture.functionId
      [requirement]

  let callCoercions := withBinaryExpression fixture fixture.call fun node => {
    node with coercions := [coercion]
  }
  expect "call coercions" callCoercions callSite fun reason =>
    reason == .builtinFunctionCoercionsPresent fixture.functionId [coercion]

  let calleeRequirements :=
    withBinaryExpression fixture fixture.callee fun node => {
      node with requirements := [requirement]
    }
  expect "callee requirements" calleeRequirements calleeSite fun reason =>
    reason == .requirementsPresent [requirement]

  let calleeCoercions :=
    withBinaryExpression fixture fixture.callee fun node => {
      node with coercions := [coercion]
    }
  expect "callee coercions" calleeCoercions calleeSite fun reason =>
    reason == .coercionsPresent [coercion]

  let isArithmetic := (fixture.functionId == .integerAdd) ||
    (fixture.functionId == .integerMul)
  let cyclic := if isArithmetic then
      withBinaryExpression fixture fixture.call fun node => {
        node with form := match node.form with
          | .call callee _ resolution =>
              .call callee [fixture.call, fixture.right] resolution
          | form => form
      }
    else
      withBinaryExpression fixture fixture.left fun node => {
        node with form := .group fixture.left, requirements := []
      }
  let cycleSite := if isArithmetic then callSite else leftSite
  expect "staged argument cycle" cyclic cycleSite fun reason =>
    reason == .stagedIntegerDepthLimit

  let duplicated := withBinaryExpression fixture fixture.call fun node => {
    node with form := match node.form with
      | .call callee _ resolution =>
          .call callee [fixture.left, fixture.left] resolution
      | form => form
  }
  expectElaborationErrorAt
    s!"{fixture.functionId.spelling} duplicated literal edge" duplicated
    (.declaration fixture.function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement requirement

private def testExpandedBuiltinTampering : IO Unit := do
  let add ← binaryFixture
    "function add() returns (Word) { return wordFromInteger(integerAdd(1, 2)); }"
    .integerAdd
  let multiply ← binaryFixture
    "function multiply() returns (Word) { return wordFromInteger(integerMul(1, 2)); }"
    .integerMul
  let equality ← binaryFixture
    "function equality() returns (Bool) { return integerEq(1, 2); }"
    .integerEq
  let less ← binaryFixture
    "function less() returns (Bool) { return integerLt(1, 2); }"
    .integerLt
  for fixture in [add, multiply, equality, less] do
    testExpandedBinaryBaseline fixture
    testExpandedBinaryContract fixture

private structure WordToFixture where
  function : CheckedFunction
  root : ExpressionId
  conversion : ExpressionId
  callee : ExpressionId
  word : ExpressionId
  resolution : IntegerLiteralResolution

private def wordToFixture : IO WordToFixture := do
  let successor := toString (Core.wordModulus + 1)
  let content := "function convert() returns (Word) { return wordFromInteger(wordToInteger(" ++
    successor ++ ")); }"
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"wordToInteger tamper fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"wordToInteger fixture produced {functions.length} functions")
  let root ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some root), .. } => pure root
        | _ => throw (IO.userError
            "wordToInteger fixture lost its valued return")
    | _ => throw (IO.userError "wordToInteger fixture lost its root")
  let conversion ← match function.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call _ [conversion] (.builtinFunction .wordFromInteger) =>
            pure conversion
        | _ => throw (IO.userError
            "wordToInteger fixture lost outer wordFromInteger")
    | none => throw (IO.userError "wordToInteger fixture lost root node")
  let (callee, word) ←
    match function.typedBody.lookupExpression? conversion with
    | some node =>
        match node.form with
        | .call callee [word] (.builtinFunction .wordToInteger) =>
            pure (callee, word)
        | _ => throw (IO.userError
            "wordToInteger fixture lost conversion call")
    | none => throw (IO.userError
        "wordToInteger fixture lost conversion node")
  let resolution ← match function.typedBody.lookupExpression? word with
    | some node =>
        match node.form with
        | .integerLiteral _ resolution => pure resolution
        | _ => throw (IO.userError
            "wordToInteger fixture lost Word literal")
    | none => throw (IO.userError
        "wordToInteger fixture lost Word literal node")
  pure { function, root, conversion, callee, word, resolution }

private def withWordToExpression (fixture : WordToFixture)
    (id : ExpressionId) (change : ExpressionNode → ExpressionNode) :
    CheckedFunction := {
  fixture.function with
  typedBody := changeExpression fixture.function.typedBody id change
}

private def testWordToBaseline (fixture : WordToFixture) : IO Unit := do
  let requirement := fixture.resolution.requirement
  assertTrue (decide (fixture.resolution.targetType = Ty.word ∧
      fixture.function.solvedRequirements.map (·.id) = [requirement] ∧
      fixture.function.solvedRequirements.all fun solved =>
        solved.predicate == ProgramSignatures.builtinIntPredicate Ty.word &&
          match solved.evidence with
          | .implementation (.byImpl goal (.builtin .intWord) []) =>
              goal == solved.predicate
          | _ => false))
    "wordToInteger fixture lost exact Int<Word> evidence"
  match SourceCoreElaboration.evaluateStagedWord
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.word with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo 1 ∧
          evaluated.consumedRequirements = [requirement]))
        "staged Word baseline did not reduce modulo 2^256"
  | .error error => throw (IO.userError
      s!"staged Word baseline did not evaluate: {reprStr error}")
  match SourceCoreElaboration.evaluateStagedInteger
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conversion with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (1 : Int) ∧
          evaluated.consumedRequirements = [requirement]))
        "wordToInteger baseline did not preserve unsigned Word value"
  | .error error => throw (IO.userError
      s!"wordToInteger baseline did not evaluate: {reprStr error}")

private def testWordToCallContract (fixture : WordToFixture) : IO Unit := do
  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.conversion.occurrence
  let calleeSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.callee.occurrence
  let wordSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.word.occurrence
  let requirement := fixture.resolution.requirement
  let coercion : CoercionStep := {
    requirement
    source := Ty.word
    target := Ty.integer
  }
  let expect label function site accept :=
    expectEvaluationErrorAt ("wordToInteger " ++ label) function
      fixture.conversion site accept

  let wrongResolution :=
    withWordToExpression fixture fixture.conversion fun node => {
      node with form := match node.form with
        | .call callee arguments _ =>
            .call callee arguments (.builtinFunction .integerAdd)
        | form => form
    }
  expect "call resolution" wrongResolution callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch .integerAdd 2 1

  let nonReference := withWordToExpression fixture fixture.callee fun node => {
    node with form := .group fixture.word
  }
  expect "callee reference shape" nonReference calleeSite fun reason =>
    reason == .builtinFunctionCalleeNotReference .wordToInteger

  let wrongIdentity := withWordToExpression fixture fixture.callee fun node => {
    node with form := (.reference BuiltinFunctionId.wordToInteger.spelling
      (.builtinFunction .wordFromInteger))
  }
  expect "callee identity" wrongIdentity calleeSite fun reason =>
    reason == .builtinFunctionCalleeIdentityMismatch .wordToInteger
      .wordFromInteger

  let wrongSpelling := withWordToExpression fixture fixture.callee fun node => {
    node with form := (.reference "forgedWordToInteger"
      (.builtinFunction .wordToInteger))
  }
  expect "callee spelling" wrongSpelling calleeSite fun reason =>
    reason == .builtinFunctionCalleeSpellingMismatch .wordToInteger
      BuiltinFunctionId.wordToInteger.spelling "forgedWordToInteger"

  let wrongCalleeType :=
    withWordToExpression fixture fixture.callee fun node => {
      node with type := Ty.bool
    }
  expect "callee type" wrongCalleeType calleeSite fun reason =>
    reason == .builtinFunctionCalleeTypeMismatch .wordToInteger
      BuiltinFunctionId.wordToInteger.type Ty.bool

  let wrongCallType :=
    withWordToExpression fixture fixture.conversion fun node => {
      node with type := Ty.word
    }
  expect "call result type" wrongCallType callSite fun reason =>
    reason == .builtinFunctionCallTypeMismatch .wordToInteger
      Ty.integer Ty.word

  let wrongArity := withWordToExpression fixture fixture.conversion fun node => {
    node with form := match node.form with
      | .call callee _ resolution => .call callee [] resolution
      | form => form
  }
  expect "call arity" wrongArity callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch .wordToInteger 1 0

  let wrongArgumentType := withWordToExpression fixture fixture.word fun node => {
    node with type := Ty.integer
  }
  expect "argument type" wrongArgumentType wordSite fun reason =>
    reason == .builtinFunctionArgumentTypeMismatch .wordToInteger 0
      Ty.word Ty.integer

  let callRequirements :=
    withWordToExpression fixture fixture.conversion fun node => {
      node with requirements := [requirement]
    }
  expect "call requirements" callRequirements callSite fun reason =>
    reason == .builtinFunctionRequirementsPresent .wordToInteger [requirement]

  let callCoercions :=
    withWordToExpression fixture fixture.conversion fun node => {
      node with coercions := [coercion]
    }
  expect "call coercions" callCoercions callSite fun reason =>
    reason == .builtinFunctionCoercionsPresent .wordToInteger [coercion]

  let calleeRequirements :=
    withWordToExpression fixture fixture.callee fun node => {
      node with requirements := [requirement]
    }
  expect "callee requirements" calleeRequirements calleeSite fun reason =>
    reason == .requirementsPresent [requirement]

  let calleeCoercions :=
    withWordToExpression fixture fixture.callee fun node => {
      node with coercions := [coercion]
    }
  expect "callee coercions" calleeCoercions calleeSite fun reason =>
    reason == .coercionsPresent [coercion]

private def testWordLiteralTampering (fixture : WordToFixture) : IO Unit := do
  let site := SourceCoreElaboration.ErrorSite.occurrence fixture.word.occurrence
  let requirement := fixture.resolution.requirement
  let expect label function accept :=
    expectWordEvaluationErrorAt ("staged Word literal " ++ label) function
      fixture.word site accept

  let wrongType := withWordToExpression fixture fixture.word fun node => {
    node with type := Ty.integer
  }
  expect "node type" wrongType fun reason =>
    reason == .stagedWordTypeMismatch Ty.word Ty.integer

  let wrongTarget := withWordToExpression fixture fixture.word fun node => {
    node with form := match node.form with
      | .integerLiteral source resolution =>
          .integerLiteral source { resolution with targetType := Ty.integer }
      | form => form
  }
  expect "target type" wrongTarget fun reason =>
    reason == .integerLiteralTargetTypeMismatch Ty.integer Ty.word

  let detached := withWordToExpression fixture fixture.word fun node => {
    node with requirements := []
  }
  expect "requirement attachment" detached fun reason =>
    reason == .integerLiteralRequirementsMismatch [requirement] []

  let rawMismatch := withWordToExpression fixture fixture.word fun node => {
    node with form := match node.form with
      | .integerLiteral source resolution =>
          .integerLiteral source { resolution with
            rawValue := resolution.rawValue + 1 }
      | form => form
  }
  expect "raw value" rawMismatch fun reason =>
    reason == .integerLiteralRawValueMismatch
      fixture.resolution.rawValue (fixture.resolution.rawValue + 1)

  let expected := fixture.resolution.predicate
  let forgedEvidence : CheckedFunction := {
    fixture.function with
    solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
      if solved.id = requirement then {
        solved with evidence := (.implementation
          (.byImpl expected (.builtin .intInteger) []))
      } else solved
  }
  expect "intInteger evidence" forgedEvidence fun reason =>
    reason == .integerLiteralImplementationMismatch requirement
      (.builtin .intWord) (.builtin .intInteger)

  let groupCycle := withWordToExpression fixture fixture.word fun node => {
    node with form := .group fixture.word, requirements := []
  }
  expect "group cycle" groupCycle fun reason =>
    reason == .stagedWordDepthLimit

private def testCrossDomainCycle (fixture : WordToFixture) : IO Unit := do
  let cyclic := withWordToExpression fixture fixture.conversion fun node => {
    node with form := match node.form with
      | .call callee _ resolution => .call callee [fixture.root] resolution
      | form => form
  }
  match SourceCoreElaboration.evaluateStagedInteger cyclic.solvedRequirements
      cyclic.typedBody fixture.conversion with
  | .ok evaluated => throw (IO.userError
      s!"cross-domain cycle evaluated to {reprStr evaluated}")
  | .error error =>
      let expectedSite := decide (error.site =
          .occurrence fixture.conversion.occurrence) ||
        decide (error.site = .occurrence fixture.root.occurrence)
      let expectedReason := error.reason == .stagedIntegerDepthLimit ||
        error.reason == .stagedWordDepthLimit
      assertTrue (expectedSite && expectedReason)
        s!"cross-domain cycle produced the wrong error {reprStr error}"

private structure NestedWordFromFixture where
  function : CheckedFunction
  conversion : ExpressionId
  wordCall : ExpressionId
  callee : ExpressionId
  integerArgument : ExpressionId

private def nestedWordFromFixture : IO NestedWordFromFixture := do
  let content :=
    "function roundtrip() returns (Word) { return wordFromInteger(wordToInteger(wordFromInteger(integerSub(0, 1)))); }"
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"nested wordFromInteger fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"nested wordFromInteger fixture produced {functions.length} functions")
  let root ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some root), .. } => pure root
        | _ => throw (IO.userError "nested wordFromInteger lost return")
    | _ => throw (IO.userError "nested wordFromInteger lost root")
  let conversion ← match function.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call _ [conversion] (.builtinFunction .wordFromInteger) =>
            pure conversion
        | _ => throw (IO.userError "nested fixture lost outer wordFromInteger")
    | none => throw (IO.userError "nested fixture lost outer node")
  let wordCall ← match function.typedBody.lookupExpression? conversion with
    | some node =>
        match node.form with
        | .call _ [word] (.builtinFunction .wordToInteger) => pure word
        | _ => throw (IO.userError "nested fixture lost wordToInteger")
    | none => throw (IO.userError "nested fixture lost conversion node")
  let (callee, integerArgument) ←
    match function.typedBody.lookupExpression? wordCall with
    | some node =>
        match node.form with
        | .call callee [argument] (.builtinFunction .wordFromInteger) =>
            pure (callee, argument)
        | _ => throw (IO.userError "nested fixture lost inner wordFromInteger")
    | none => throw (IO.userError "nested fixture lost inner Word node")
  pure { function, conversion, wordCall, callee, integerArgument }

private def withNestedWordFromExpression (fixture : NestedWordFromFixture)
    (id : ExpressionId) (change : ExpressionNode → ExpressionNode) :
    CheckedFunction := {
  fixture.function with
  typedBody := changeExpression fixture.function.typedBody id change
}

private def testNestedWordFromMetadata
    (fixture : NestedWordFromFixture) : IO Unit := do
  let callSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.wordCall.occurrence
  let calleeSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.callee.occurrence
  let argumentSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.integerArgument.occurrence
  let requirement ← match fixture.function.solvedRequirements with
    | requirement :: _ => pure requirement.id
    | [] => throw (IO.userError
        "nested wordFromInteger fixture lost literal requirements")
  let coercion : CoercionStep := {
    requirement
    source := Ty.integer
    target := Ty.word
  }
  let expect label function site accept :=
    expectWordEvaluationErrorAt ("nested wordFromInteger " ++ label)
      function fixture.wordCall site accept
  match SourceCoreElaboration.evaluateStagedWord
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.wordCall with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.maximum ∧
          evaluated.consumedRequirements =
            fixture.function.solvedRequirements.map (·.id)))
        "nested wordFromInteger baseline changed modulo or evidence order"
  | .error error => throw (IO.userError
      s!"nested wordFromInteger baseline did not evaluate: {reprStr error}")

  let wrongResolution :=
    withNestedWordFromExpression fixture fixture.wordCall fun node => {
      node with form := match node.form with
        | .call callee arguments _ =>
            .call callee arguments (.builtinFunction .wordToInteger)
        | form => form
    }
  expect "call resolution" wrongResolution callSite fun reason =>
    reason == .stagedWordExpressionNotClosed

  let nonReference :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with form := .group fixture.integerArgument
    }
  expect "callee reference shape" nonReference calleeSite fun reason =>
    reason == .builtinFunctionCalleeNotReference .wordFromInteger

  let wrongIdentity :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with form := (.reference BuiltinFunctionId.wordFromInteger.spelling
        (.builtinFunction .wordToInteger))
    }
  expect "callee identity" wrongIdentity calleeSite fun reason =>
    reason == .builtinFunctionCalleeIdentityMismatch .wordFromInteger
      .wordToInteger

  let wrongSpelling :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with form := (.reference "forgedNestedWordFrom"
        (.builtinFunction .wordFromInteger))
    }
  expect "callee spelling" wrongSpelling calleeSite fun reason =>
    reason == .builtinFunctionCalleeSpellingMismatch .wordFromInteger
      BuiltinFunctionId.wordFromInteger.spelling "forgedNestedWordFrom"

  let wrongCalleeType :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with type := Ty.bool
    }
  expect "callee type" wrongCalleeType calleeSite fun reason =>
    reason == .builtinFunctionCalleeTypeMismatch .wordFromInteger
      BuiltinFunctionId.wordFromInteger.type Ty.bool

  let wrongCallType :=
    withNestedWordFromExpression fixture fixture.wordCall fun node => {
      node with type := Ty.integer
    }
  expect "call result type" wrongCallType callSite fun reason =>
    reason == .builtinFunctionCallTypeMismatch .wordFromInteger
      Ty.word Ty.integer

  let wrongArity :=
    withNestedWordFromExpression fixture fixture.wordCall fun node => {
      node with form := match node.form with
        | .call callee _ resolution => .call callee [] resolution
        | form => form
    }
  expect "call arity" wrongArity callSite fun reason =>
    reason == .builtinFunctionArgumentArityMismatch .wordFromInteger 1 0

  let wrongArgumentType :=
    withNestedWordFromExpression fixture fixture.integerArgument fun node => {
      node with type := Ty.word
    }
  expect "argument type" wrongArgumentType argumentSite fun reason =>
    reason == .builtinFunctionArgumentTypeMismatch .wordFromInteger 0
      Ty.integer Ty.word

  let callRequirements :=
    withNestedWordFromExpression fixture fixture.wordCall fun node => {
      node with requirements := [requirement]
    }
  expect "call requirements" callRequirements callSite fun reason =>
    reason == .builtinFunctionRequirementsPresent .wordFromInteger [requirement]

  let callCoercions :=
    withNestedWordFromExpression fixture fixture.wordCall fun node => {
      node with coercions := [coercion]
    }
  expect "call coercions" callCoercions callSite fun reason =>
    reason == .builtinFunctionCoercionsPresent .wordFromInteger [coercion]

  let calleeRequirements :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with requirements := [requirement]
    }
  expect "callee requirements" calleeRequirements calleeSite fun reason =>
    reason == .requirementsPresent [requirement]

  let calleeCoercions :=
    withNestedWordFromExpression fixture fixture.callee fun node => {
      node with coercions := [coercion]
    }
  expect "callee coercions" calleeCoercions calleeSite fun reason =>
    reason == .coercionsPresent [coercion]

private def testWordRequirementAccounting : IO Unit := do
  let content :=
    "function duplicateWord() returns (Word) { return wordFromInteger(integerAdd(wordToInteger(1), wordToInteger(2))); }"
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"Word requirement fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"Word requirement fixture produced {functions.length} functions")
  let root ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some root), .. } => pure root
        | _ => throw (IO.userError "Word requirement fixture lost return")
    | _ => throw (IO.userError "Word requirement fixture lost root")
  let add ← match function.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call _ [add] (.builtinFunction .wordFromInteger) => pure add
        | _ => throw (IO.userError "Word requirement fixture lost outer call")
    | none => throw (IO.userError "Word requirement fixture lost root node")
  let (leftConversion, rightConversion, addCallee) ←
    match function.typedBody.lookupExpression? add with
    | some node =>
        match node.form with
        | .call callee [left, right] (.builtinFunction .integerAdd) =>
            pure (left, right, callee)
        | _ => throw (IO.userError "Word requirement fixture lost integerAdd")
    | none => throw (IO.userError "Word requirement fixture lost add node")
  let wordArgument (conversion : ExpressionId) : IO ExpressionId :=
    match function.typedBody.lookupExpression? conversion with
    | some node =>
        match node.form with
        | .call _ [word] (.builtinFunction .wordToInteger) => pure word
        | _ => throw (IO.userError "Word requirement fixture lost conversion")
    | none => throw (IO.userError "Word requirement fixture lost conversion node")
  let leftWord ← wordArgument leftConversion
  let rightWord ← wordArgument rightConversion
  let wordRequirement (word : ExpressionId) : IO RequirementId :=
    match function.typedBody.lookupExpression? word with
    | some node =>
        match node.form with
        | .integerLiteral _ resolution => pure resolution.requirement
        | _ => throw (IO.userError "Word requirement fixture lost literal")
    | none => throw (IO.userError "Word requirement fixture lost literal node")
  let leftRequirement ← wordRequirement leftWord
  let rightRequirement ← wordRequirement rightWord
  let expectedRequirements := [leftRequirement, rightRequirement]
  assertTrue (decide (leftConversion ≠ rightConversion ∧
      leftWord ≠ rightWord ∧
      function.solvedRequirements.map (·.id) = expectedRequirements))
    "Word requirement fixture lost distinct source-order evidence"
  match SourceCoreElaboration.evaluateStagedInteger function.solvedRequirements
      function.typedBody add with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (3 : Int) ∧
          evaluated.consumedRequirements = expectedRequirements))
        "Word requirement baseline changed consumption order"
  | .error error => throw (IO.userError
      s!"Word requirement baseline did not evaluate: {reprStr error}")
  let duplicated : CheckedFunction := {
    function with
    typedBody := changeExpression function.typedBody add fun node => {
      node with form := (.call addCallee [leftConversion, leftConversion]
        (.builtinFunction .integerAdd))
    }
  }
  expectElaborationErrorAt "duplicated staged Word literal edge" duplicated
    (.declaration function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement leftRequirement

/-- Reject forged builtin identities and staged literal evidence before Core. -/
def testSourceStagedIntegerIntrinsicsTamper : IO Unit := do
  let checked ← fixture
  testCheckedBaseline checked
  testOuterCallContract checked
  testInnerCallContract checked
  testLiteralCarrier checked
  testLiteralEvidence checked
  testCyclesAndRequirementAccounting checked
  testExpandedBuiltinTampering
  let wordTo ← wordToFixture
  testWordToBaseline wordTo
  testWordToCallContract wordTo
  testWordLiteralTampering wordTo
  testCrossDomainCycle wordTo
  let nestedWordFrom ← nestedWordFromFixture
  testNestedWordFromMetadata nestedWordFrom
  testWordRequirementAccounting
  IO.println "staged integer intrinsic tamper checks GREEN"

end Tests.SourceStagedIntegerIntrinsicsTamper
end

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerLocals
/-! End-to-end regressions for eager, let-bound staged integers. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerLocals

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid staged-local module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-local fixture failed checking: {reprStr errors}")

private def checkedNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry =>
        entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.find? fun signature =>
      signature.name == name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def statementRoots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression expression => throw (IO.userError
        s!"staged-local fixture retained expression root {reprStr expression}")

private def letBinding (function : CheckedFunction) (id : StatementId) :
    IO (TypedBinder × ExpressionId) :=
  match function.typedBody.lookupStatement? id with
  | some node =>
      match node.form with
      | .letDecl binder (some initializer) => do
          assertTrue (node.type == Ty.unit)
            "staged let statement lost Unit type"
          pure (binder, initializer)
      | _ => throw (IO.userError
          s!"expected initialized let statement, found {reprStr node}")
  | none => throw (IO.userError "staged let statement was absent")

private def returnedExpression (function : CheckedFunction)
    (id : StatementId) : IO ExpressionId :=
  match function.typedBody.lookupStatement? id with
  | some { form := .returnStmt (some expression), .. } => pure expression
  | node => throw (IO.userError
      s!"staged-local final statement is not a valued return: {reprStr node}")

private def builtinArguments (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) : IO (List ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee arguments (.builtinFunction actual) => do
          let calleeValid := match function.typedBody.lookupExpression? callee with
            | some calleeNode =>
                match calleeNode.form with
                | .reference spelling (.builtinFunction identity) =>
                    identity == expected && spelling == expected.spelling &&
                      calleeNode.type == expected.type &&
                      calleeNode.requirements.isEmpty &&
                      calleeNode.coercions.isEmpty
                | _ => false
            | none => false
          assertTrue (actual == expected &&
              node.type == expected.returnType &&
              arguments.length == expected.parameterTypes.length &&
              node.requirements.isEmpty && node.coercions.isEmpty &&
              calleeValid)
            s!"builtin `{expected.spelling}` lost exact typed metadata"
          pure arguments
      | _ => throw (IO.userError
          s!"expected builtin `{expected.spelling}`, found {reprStr node}")
  | none => throw (IO.userError
      s!"builtin `{expected.spelling}` was absent")

private def localReference (function : CheckedFunction) (id : ExpressionId)
    (expected : TypedBinder) : IO Unit :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .reference name (.local binder) =>
          assertTrue (binder == expected.id && name == expected.name &&
              node.type == Ty.integer && node.requirements.isEmpty &&
              node.coercions.isEmpty)
            "staged local reference lost binder identity or empty metadata"
      | _ => throw (IO.userError
          s!"expected staged local reference, found {reprStr node}")
  | none => throw (IO.userError "staged local reference was absent")

private def integerLiteralRequirement (function : CheckedFunction)
    (id : ExpressionId) (expected : Nat) : IO RequirementId :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral _ resolution => do
          assertTrue (node.type == Ty.integer &&
              resolution.targetType == Ty.integer &&
              resolution.rawValue == expected &&
              node.requirements == [resolution.requirement] &&
              node.coercions.isEmpty)
            "staged-local literal lost integer target or exact requirement"
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"expected staged integer literal, found {reprStr node}")
  | none => throw (IO.userError "staged integer literal was absent")

private def positiveSource : String := String.intercalate "\n" [
  "function basic() returns (Word) {",
  "  let x = 42;",
  "  let y = integerAdd(x, 8);",
  "  return wordFromInteger(integerMul(y, 2));",
  "}",
  "function negative() returns (Word) {",
  "  let x: integer = integerSub(0, 3);",
  "  let y: integer = integerMul(x, 5);",
  "  return wordFromInteger(y);",
  "}",
  "function reuse() returns (Word) {",
  "  let x: integer = integerSub(1, 2);",
  "  return wordFromInteger(integerAdd(x, x));",
  "}",
  "function shadow() returns (Word) {",
  "  let x: integer = 3;",
  "  let x: integer = integerAdd(x, 1);",
  "  return wordFromInteger(x);",
  "}",
  "function chain() returns (Word) {",
  "  let a: integer = 2;",
  "  let b: integer = integerMul(a, 3);",
  "  let c: integer = integerSub(b, 1);",
  "  return wordFromInteger(c);",
  "}",
  "function unused() returns (Word) {",
  "  let ignored: integer = integerAdd(20, 22);",
  "  return 7;",
  "}",
  "function composed() returns (Word) {",
  "  let base = integerSub(10, 3);",
  "  {",
  "    let chosen = integerLt(base, 8) ? integerAdd(base, 5) : wordToInteger(99);",
  "    return wordFromInteger(chosen);",
  "  }",
  "}",
  "function roundtripEq() returns (Word) {",
  "  let x = 5;",
  "  return integerEq(wordToInteger(wordFromInteger(x)), x) ? 1 : 0;",
  "}",
  "function runtimeWord(value: Word) returns (Word) {",
  "  let next: Word = value + 1;",
  "  return next * 2;",
  "}"
]

private def limits : Limits := {
  checkingFuel := 1024
  specializationBudget := 1
  executionFuel := 1024
}

private def testReferenceCarrier : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "basic"
  let roots ← statementRoots function
  let (xStatement, yStatement, returnStatement) ← match roots with
    | [x, y, result] => pure (x, y, result)
    | _ => throw (IO.userError
        s!"basic staged-local fixture retained {roots.length} roots")
  let (x, xInitializer) ← letBinding function xStatement
  let (y, yInitializer) ← letBinding function yStatement
  assertTrue (x.scheme == .mono Ty.integer &&
      y.scheme == .mono Ty.integer && x.id != y.id &&
      x.id.owner == function.declaration &&
      y.id.owner == function.declaration)
    "staged let binders lost monomorphic integer identity"
  let xRequirement ← integerLiteralRequirement function xInitializer 42
  let yArguments ← builtinArguments function yInitializer .integerAdd
  let (xReference, eight) ← match yArguments with
    | [reference, literal] => pure (reference, literal)
    | _ => throw (IO.userError "integerAdd lost its two operands")
  localReference function xReference x
  let eightRequirement ← integerLiteralRequirement function eight 8
  let returned ← returnedExpression function returnStatement
  let outer ← builtinArguments function returned .wordFromInteger
  let multiplication ← match outer with
    | [inner] => pure inner
    | _ => throw (IO.userError "wordFromInteger lost its argument")
  let multiplicationArguments ←
    builtinArguments function multiplication .integerMul
  let (yReference, two) ← match multiplicationArguments with
    | [reference, literal] => pure (reference, literal)
    | _ => throw (IO.userError "integerMul lost its two operands")
  localReference function yReference y
  let twoRequirement ← integerLiteralRequirement function two 2
  let expectedRequirements := [xRequirement, eightRequirement, twoRequirement]
  assertTrue (function.solvedRequirements.map (·.id) == expectedRequirements)
    "staged let initializer requirements changed source order or duplicated reads"
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody yInitializer with
  | .error error =>
      assertTrue (decide (error.site = .occurrence xReference.occurrence) &&
          error.reason == .unknownLocal x.id)
        s!"public staged evaluator did not preserve its empty-local boundary: {reprStr error}"
  | .ok evaluated => throw (IO.userError
      s!"public staged evaluator unexpectedly captured statement locals: {reprStr evaluated}")
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"reference staged lets did not lower: {reprStr error}")
  let expected := Core.Word.ofNatModulo 100
  assertTrue (decide (lowered.inputs.values = [] ∧
      lowered.resolved = .word expected ∧ lowered.core = .word expected))
    "staged integer lets or local references survived Core lowering"
  let signature ← signatureNamed program "basic"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "staged local intrinsics created source-call edges"
  | result => throw (IO.userError
      s!"staged-local worklist did not close in one slot: {reprStr result}")

private def testShadowingIdentity : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "shadow"
  let roots ← statementRoots function
  let (firstStatement, secondStatement, returnStatement) ← match roots with
    | [first, second, result] => pure (first, second, result)
    | _ => throw (IO.userError "shadow fixture lost its three statements")
  let (first, _) ← letBinding function firstStatement
  let (second, secondInitializer) ← letBinding function secondStatement
  let secondArguments ← builtinArguments function secondInitializer .integerAdd
  let priorReference ← match secondArguments with
    | reference :: _ => pure reference
    | _ => throw (IO.userError "shadowing initializer lost prior reference")
  localReference function priorReference first
  let returned ← returnedExpression function returnStatement
  let outer ← builtinArguments function returned .wordFromInteger
  let finalReference ← match outer with
    | [reference] => pure reference
    | _ => throw (IO.userError "shadowing return lost final reference")
  localReference function finalReference second
  assertTrue (first.name == second.name && first.id != second.id)
    "shadowed staged binders did not retain distinct lexical identities"

private def assertPreparedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: staged-local public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: staged lets were not erased to one Word constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 37)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: staged-local execution changed result or store"

private def assertPreparedRoundtripEq (moduleId : Workspace.ModuleId) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId "roundtripEq") limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"roundtripEq: public preparation failed: {reprStr error}")
  let one := Core.Word.ofNatModulo 1
  let zero := Core.Word.ofNatModulo 0
  let expectedResolved : Resolved.Expr :=
    .ifE (.bool true) (.word one) (.word zero)
  let expectedCore : Core.Expr :=
    .ifE (.bool true) (.word one) (.word zero)
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    "roundtripEq: local cross-domain equality did not become a closed Bool guard"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 41)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word one) store)))
    "roundtripEq: staged equality selected the wrong Word branch or changed store"

private def testPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let cases : List (String × Core.Word) := [
    ("basic", Core.Word.ofNatModulo 100),
    ("negative", Core.Word.ofIntModulo (-15)),
    ("reuse", Core.Word.ofIntModulo (-2)),
    ("shadow", Core.Word.ofNatModulo 4),
    ("chain", Core.Word.ofNatModulo 5),
    ("unused", Core.Word.ofNatModulo 7),
    ("composed", Core.Word.ofNatModulo 12)
  ]
  for (name, expected) in cases do
    assertPreparedWord moduleId name expected
  assertPreparedRoundtripEq moduleId
  let program ← checkedProgram positiveSource
  let unused ← checkedNamed program "unused"
  assertTrue (unused.solvedRequirements.length == 3)
    "unused eager initializer or returned Word lost literal obligations"

private def testRuntimeLetBoundary : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "runtimeWord"
  let roots ← statementRoots function
  let binder ← match roots with
    | letStatement :: _ =>
        match function.typedBody.lookupStatement? letStatement with
        | some { form := .letDecl binder (some _), .. } => pure binder
        | node => throw (IO.userError
            s!"runtime Word fixture lost its let: {reprStr node}")
    | [] => throw (IO.userError "runtime Word fixture lost its statements")
  let lowered ← match SourceCoreElaboration.elaborateFunction function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"ordinary Word let stopped lowering: {reprStr error}")
  match lowered.resolved, lowered.core with
  | .letE actual _ _, .letE _ _ =>
      assertTrue (actual == binder.id)
        "ordinary Word let changed its resolved binder identity"
  | resolved, core => throw (IO.userError
      s!"ordinary Word let was incorrectly staged away: {reprStr resolved}, {reprStr core}")
  let store : Core.Store := [.bool false]
  assertTrue (decide (Core.runStateful 64
      (.initial lowered.core [.word (Core.Word.ofNatModulo 3)] store) =
        .done (.word (Core.Word.ofNatModulo 8)) store))
    "ordinary Word let lost runtime semantics or store preservation"

private def expectSourceCoreError (label content name : String)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) limits with
  | .error (.linking (.sourceCore error)) =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong source-Core error {reprStr error}"
  | result => throw (IO.userError
      s!"{label}: invalid staged local was not rejected: {reprStr result}")

private def testBoundaryRejections : IO Unit := do
  let parameterSource := String.intercalate "\n" [
    "function parameter(value: integer) returns (Word) {",
    "  let local: integer = value;",
    "  return wordFromInteger(local);",
    "}"
  ]
  let parameterProgram ← checkedProgram parameterSource
  let parameter ← checkedNamed parameterProgram "parameter"
  let input ← match parameter.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"integer parameter fixture retained {inputs.length} inputs")
  expectSourceCoreError "integer parameter is not a staged local"
    parameterSource "parameter" (.binder input.id) fun reason =>
      reason == .unsupportedType Ty.integer

  let uninitializedSource := String.intercalate "\n" [
    "function uninitialized() returns (Word) {",
    "  let value: integer;",
    "  return wordFromInteger(value);",
    "}"
  ]
  let uninitializedProgram ← checkedProgram uninitializedSource
  let uninitialized ← checkedNamed uninitializedProgram "uninitialized"
  let roots ← statementRoots uninitialized
  let first ← match roots with
    | first :: _ => pure first
    | [] => throw (IO.userError "uninitialized fixture lost its let")
  expectSourceCoreError "uninitialized staged local" uninitializedSource
    "uninitialized" (.occurrence first.occurrence) fun reason =>
      reason == .uninitializedLet

  let strictSource := String.intercalate "\n" [
    "function strict(value: Word) returns (Word) {",
    "  let ignored: integer = wordToInteger(value);",
    "  return 7;",
    "}"
  ]
  let strictProgram ← checkedProgram strictSource
  let strict ← checkedNamed strictProgram "strict"
  let strictRoots ← statementRoots strict
  let strictLet ← match strictRoots with
    | first :: _ => pure first
    | [] => throw (IO.userError "strict fixture lost its let")
  let (_, strictInitializer) ← letBinding strict strictLet
  let wordArguments ← builtinArguments strict strictInitializer .wordToInteger
  let runtimeWord ← match wordArguments with
    | [argument] => pure argument
    | _ => throw (IO.userError "strict wordToInteger lost its argument")
  expectSourceCoreError "unused initializer remains strict" strictSource
    "strict" (.occurrence runtimeWord.occurrence) fun reason =>
      reason == .stagedWordExpressionNotClosed

/-- Exercise eager let-bound staged integers through checking, linking, and execution. -/
def testSourceStagedIntegerLocals : IO Unit := do
  testReferenceCarrier
  testShadowingIdentity
  testPublicExecution
  testRuntimeLetBoundary
  testBoundaryRejections
  IO.println "let-bound staged integer checks GREEN"

end Tests.SourceStagedIntegerLocals
end

section
-- leanmerge: from Solcore.Test.SourceStagedIntegerLocalsTamper
/-! Adversarial regressions for let-bound staged-integer environments. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerLocalsTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedFunction : IO CheckedFunction := do
  let content := String.intercalate "\n" [
    "function tamper() returns (Word) {",
    "  let x: integer = 5;",
    "  let y: integer = integerAdd(x, 7);",
    "  return wordFromInteger(integerMul(y, 2));",
    "}"
  ]
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"staged-local tamper fixture failed checking: {reprStr errors}")
  match program.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"staged-local tamper fixture produced {functions.length} functions")

private def statementRoots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression expression => throw (IO.userError
        s!"tamper fixture retained expression root {reprStr expression}")

private def letBinding (function : CheckedFunction) (id : StatementId) :
    IO (TypedBinder × ExpressionId) :=
  match function.typedBody.lookupStatement? id with
  | some { form := .letDecl binder (some initializer), .. } =>
      pure (binder, initializer)
  | node => throw (IO.userError
      s!"tamper fixture lost initialized let: {reprStr node}")

private def returnedExpression (function : CheckedFunction)
    (id : StatementId) : IO ExpressionId :=
  match function.typedBody.lookupStatement? id with
  | some { form := .returnStmt (some expression), .. } => pure expression
  | node => throw (IO.userError
      s!"tamper fixture lost valued return: {reprStr node}")

private def unaryArgument (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) : IO ExpressionId :=
  match function.typedBody.lookupExpression? id with
  | some { form := .call _ [argument] (.builtinFunction actual), .. } =>
      if actual == expected then pure argument
      else throw (IO.userError
        s!"expected `{expected.spelling}`, found `{actual.spelling}`")
  | node => throw (IO.userError
      s!"tamper fixture lost unary builtin call: {reprStr node}")

private def binaryArguments (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) : IO (ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some { form := .call _ [left, right] (.builtinFunction actual), .. } =>
      if actual == expected then pure (left, right)
      else throw (IO.userError
        s!"expected `{expected.spelling}`, found `{actual.spelling}`")
  | node => throw (IO.userError
      s!"tamper fixture lost binary builtin call: {reprStr node}")

private def literalRequirement (function : CheckedFunction)
    (id : ExpressionId) : IO RequirementId :=
  match function.typedBody.lookupExpression? id with
  | some { form := .integerLiteral _ resolution, .. } =>
      pure resolution.requirement
  | node => throw (IO.userError
      s!"tamper fixture lost integer literal: {reprStr node}")

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def changeStatement (source : TypedSource) (id : StatementId)
    (change : StatementNode → StatementNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node => .expression node
    | .statement node =>
        if node.id = id then .statement { change node with id }
        else .statement node
}

private def withExpression (function : CheckedFunction) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : CheckedFunction := {
  function with typedBody := changeExpression function.typedBody id change
}

private def withStatement (function : CheckedFunction) (id : StatementId)
    (change : StatementNode → StatementNode) : CheckedFunction := {
  function with typedBody := changeStatement function.typedBody id change
}

private def expectErrorAt (label : String) (function : CheckedFunction)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok lowered => throw (IO.userError
      s!"{label}: malformed staged local lowered to {reprStr lowered.resolved}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private structure Fixture where
  function : CheckedFunction
  xStatement : StatementId
  x : TypedBinder
  xInitializer : ExpressionId
  xRequirement : RequirementId
  yStatement : StatementId
  y : TypedBinder
  yInitializer : ExpressionId
  xReference : ExpressionId
  seven : ExpressionId
  returnStatement : StatementId
  root : ExpressionId
  multiplication : ExpressionId
  yReference : ExpressionId
  two : ExpressionId

private def fixture : IO Fixture := do
  let function ← checkedFunction
  let roots ← statementRoots function
  let (xStatement, yStatement, returnStatement) ← match roots with
    | [x, y, result] => pure (x, y, result)
    | _ => throw (IO.userError
        s!"tamper fixture retained {roots.length} statement roots")
  let (x, xInitializer) ← letBinding function xStatement
  let xRequirement ← literalRequirement function xInitializer
  let (y, yInitializer) ← letBinding function yStatement
  let (xReference, seven) ←
    binaryArguments function yInitializer .integerAdd
  let root ← returnedExpression function returnStatement
  let multiplication ← unaryArgument function root .wordFromInteger
  let (yReference, two) ←
    binaryArguments function multiplication .integerMul
  pure {
    function
    xStatement
    x
    xInitializer
    xRequirement
    yStatement
    y
    yInitializer
    xReference
    seven
    returnStatement
    root
    multiplication
    yReference
    two
  }

private def replaceLetBinder (function : CheckedFunction) (statement : StatementId)
    (binder : TypedBinder) : CheckedFunction :=
  withStatement function statement fun node =>
    match node.form with
    | .letDecl _ initializer => { node with form := .letDecl binder initializer }
    | _ => node

private def testBaseline (fixture : Fixture) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction fixture.function with
  | .ok lowered =>
      let expected := Core.Word.ofNatModulo 24
      assertTrue (decide (lowered.inputs.values = [] ∧
          lowered.resolved = .word expected ∧ lowered.core = .word expected))
        "tamper baseline retained staged lets in Core"
  | .error error => throw (IO.userError
      s!"staged-local tamper baseline failed: {reprStr error}")

private def testStatementAndBinderTampering (fixture : Fixture) : IO Unit := do
  let wrongStatementType := withStatement fixture.function fixture.xStatement
    fun node => { node with type := Ty.word }
  expectErrorAt "staged let statement type" wrongStatementType
    (.occurrence fixture.xStatement.occurrence) fun reason =>
      reason == .typedNodeTypeMismatch Core.Ty.unit Core.Ty.word

  let uninitialized := withStatement fixture.function fixture.xStatement
    fun node =>
      match node.form with
      | .letDecl binder _ => { node with form := .letDecl binder none }
      | _ => node
  expectErrorAt "staged let missing initializer" uninitialized
    (.occurrence fixture.xStatement.occurrence) fun reason =>
      reason == .uninitializedLet

  let typeVariable : TypeVarId := ⟨91⟩
  let quantifiedBinder : TypedBinder := {
    fixture.x with
    scheme := { quantified := [typeVariable], body := Ty.integer }
  }
  let quantified := replaceLetBinder fixture.function fixture.xStatement
    quantifiedBinder
  expectErrorAt "quantified staged binder" quantified
    (.binder quantifiedBinder.id) fun reason =>
      reason == .polymorphicLocal [typeVariable]

  let wrongTypeBinder : TypedBinder := {
    fixture.x with scheme := .mono Ty.word
  }
  let wrongType := replaceLetBinder fixture.function fixture.xStatement
    wrongTypeBinder
  expectErrorAt "wrong staged binder type" wrongType
    (.occurrence fixture.xInitializer.occurrence) fun reason =>
      reason == .unsupportedType Ty.integer

  let foreignOwner : Resolved.DeclarationId := {
    fixture.function.declaration with
    declarationIndex := fixture.function.declaration.declarationIndex + 100
  }
  let foreignBinder : TypedBinder := {
    fixture.x with id := { fixture.x.id with owner := foreignOwner }
  }
  let foreign := replaceLetBinder fixture.function fixture.xStatement foreignBinder
  expectErrorAt "foreign staged binder" foreign (.binder foreignBinder.id)
    fun reason => reason == .ownerMismatch fixture.function.declaration foreignOwner

  let duplicateBinder : TypedBinder := { fixture.y with id := fixture.x.id }
  let duplicate := replaceLetBinder fixture.function fixture.yStatement
    duplicateBinder
  expectErrorAt "duplicate staged binder" duplicate (.binder duplicateBinder.id)
    fun reason => reason == .duplicateLocal duplicateBinder.id

private def testLocalReferenceTampering (fixture : Fixture) : IO Unit := do
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.xReference.occurrence
  let wrongType := withExpression fixture.function fixture.xReference fun node =>
    { node with type := Ty.word }
  expectErrorAt "staged local reference type" wrongType site fun reason =>
    reason == .builtinFunctionArgumentTypeMismatch .integerAdd 0
      Ty.integer Ty.word

  let required := withExpression fixture.function fixture.xReference fun node =>
    { node with requirements := [fixture.xRequirement] }
  expectErrorAt "staged local reference requirements" required site fun reason =>
    reason == .requirementsPresent [fixture.xRequirement]

  let step : CoercionStep := {
    requirement := fixture.xRequirement
    source := Ty.integer
    target := Ty.integer
  }
  let coerced := withExpression fixture.function fixture.xReference fun node =>
    { node with coercions := [step] }
  expectErrorAt "staged local reference coercions" coerced site fun reason =>
    reason == .coercionsPresent [step]

  let misspelled := withExpression fixture.function fixture.xReference fun node =>
    { node with form := .reference "not_x" (.local fixture.x.id) }
  expectErrorAt "staged local reference spelling" misspelled site fun reason =>
    reason == .stagedIntegerLocalSpellingMismatch fixture.x.id
      fixture.x.name "not_x"

  let unknown : Resolved.LocalId := {
    owner := fixture.function.declaration
    binderIndex := fixture.function.typedBody.nodes.length + 100
  }
  let unknownReference := withExpression fixture.function fixture.xReference
    fun node => { node with form := .reference fixture.x.name (.local unknown) }
  expectErrorAt "unknown staged local" unknownReference site fun reason =>
    reason == .unknownLocal unknown

  let foreignOwner : Resolved.DeclarationId := {
    fixture.function.declaration with
    declarationIndex := fixture.function.declaration.declarationIndex + 101
  }
  let foreign : Resolved.LocalId := {
    owner := foreignOwner
    binderIndex := fixture.x.id.binderIndex
  }
  let foreignReference := withExpression fixture.function fixture.xReference
    fun node => { node with form := .reference fixture.x.name (.local foreign) }
  expectErrorAt "foreign staged local reference" foreignReference site fun reason =>
    reason == .ownerMismatch fixture.function.declaration foreignOwner

private def testInitializerIntegrity (fixture : Fixture) : IO Unit := do
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.xInitializer.occurrence
  let wrongType := withExpression fixture.function fixture.xInitializer fun node =>
    { node with type := Ty.word }
  expectErrorAt "staged initializer type" wrongType site fun reason =>
    reason == .stagedIntegerTypeMismatch Ty.integer Ty.word

  let selfReference := withExpression fixture.function fixture.xInitializer
    fun node => {
      node with
      form := .reference fixture.x.name (.local fixture.x.id)
      requirements := []
      coercions := []
    }
  expectErrorAt "self-referential staged initializer" selfReference site
    fun reason => reason == .unknownLocal fixture.x.id

  let forwardReference := withExpression fixture.function fixture.xReference
    fun node => {
      node with form := .reference fixture.y.name (.local fixture.y.id)
    }
  expectErrorAt "forward staged local reference" forwardReference
    (.occurrence fixture.xReference.occurrence) fun reason =>
      reason == .unknownLocal fixture.y.id

  let cycle := withExpression fixture.function fixture.xInitializer fun node => {
    node with
    form := .group fixture.xInitializer
    requirements := []
    coercions := []
  }
  expectErrorAt "staged initializer cycle" cycle site fun reason =>
    reason == .stagedIntegerDepthLimit

private def testDuplicateRequirementAccounting (fixture : Fixture) : IO Unit := do
  let shared := withExpression fixture.function fixture.yInitializer fun node =>
    match node.form with
    | .call callee _ resolution =>
        { node with
          form := .call callee [fixture.xReference, fixture.xInitializer]
            resolution
        }
    | _ => node
  expectErrorAt "shared staged initializer requirement" shared
    (.declaration fixture.function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement fixture.xRequirement

/-- Reject malformed binders, local edges, cycles, and duplicated consumption. -/
def testSourceStagedIntegerLocalsTamper : IO Unit := do
  let value ← fixture
  testBaseline value
  testStatementAndBinderTampering value
  testLocalReferenceTampering value
  testInitializerIntegrity value
  testDuplicateRequirementAccounting value
  IO.println "let-bound staged integer tamper checks GREEN"

end Tests.SourceStagedIntegerLocalsTamper
end
