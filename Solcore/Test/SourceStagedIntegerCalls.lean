import Solcore

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
  "function dec(x: integer) returns (integer) {",
  "  return integerSub(x, 1);",
  "}",
  "function dec2(x: integer) returns (integer) {",
  "  return dec(dec(x));",
  "}",
  "function baseline() returns (Word) {",
  "  return wordFromInteger(dec(10));",
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
      decSignature.returnTypes == [Ty.integer] &&
      dec.type == Ty.function Ty.integer Ty.integer)
    "integer parameter/result disappeared from the function signature"
  let input ← match dec.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"dec retained {inputs.length} typed inputs")
  assertTrue (input.scheme == .mono Ty.integer &&
      input.id.owner == dec.declaration)
    "integer parameter lost its exact monomorphic binder"

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
  assertPreparedWord "nested" (Core.Word.ofNatModulo 8)
  assertPreparedWord "eagerBranches" (Core.Word.ofNatModulo 9)

private def testIntegerRootBoundary : IO Unit := do
  let program ← checkedProgram positiveSource
  let dec ← functionNamed program "dec"
  let input ← match dec.typedBody.inputs with
    | [input] => pure input
    | _ => throw (IO.userError "integer root fixture lost its input")
  let moduleId ← mainModule
  match prepare (workspace positiveSource) (Seed.named moduleId "dec")
      (limits 1) with
  | .error (.linking (.sourceCore error)) =>
      assertTrue (decide (error.site = .binder input.id) &&
          error.reason == .unsupportedType Ty.integer)
        s!"integer root failed at the wrong boundary: {reprStr error}"
  | result => throw (IO.userError
      s!"integer source function escaped as a runtime root: {reprStr result}")

private def expectRecursiveCall (label source root expected : String)
    (budget : Nat) : IO Unit := do
  let program ← checkedProgram source
  let expectedSignature ← signatureNamed program expected
  let expectedKey := specializationKey expectedSignature
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId root)
      (limits budget) with
  | .error (.linking (.recursiveCallCycle key)) =>
      assertTrue (key == expectedKey)
        s!"{label}: recursion error retained the wrong key {reprStr key}"
  | result => throw (IO.userError
      s!"{label}: recursive staged call was not rejected: {reprStr result}")

private def testRecursiveRejections : IO Unit := do
  let selfSource := String.intercalate "\n" [
    "function loop(x: integer) returns (integer) { return loop(x); }",
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
  expectRecursiveCall "self recursion" selfSource "main" "loop" 2

  let mutualSource := String.intercalate "\n" [
    "function left(x: integer) returns (integer) { return right(x); }",
    "function right(x: integer) returns (integer) { return left(x); }",
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
  expectRecursiveCall "mutual recursion" mutualSource "main" "left" 3

  let deadSource := String.intercalate "\n" [
    "function dec(x: integer) returns (integer) { return integerSub(x, 1); }",
    "function loop(x: integer) returns (integer) { return loop(x); }",
    "function main() returns (Word) {",
    "  return wordFromInteger(true ? dec(10) : loop(0));",
    "}"
  ]
  expectRecursiveCall "unselected recursive branch" deadSource "main"
    "loop" 3

/-- Exercise direct integer source calls through planning, linking, and execution. -/
def testSourceStagedIntegerCalls : IO Unit := do
  testTypedCarrierAndStandaloneBoundary
  testPlansAndBudgets
  testRequirementLedgerIsolation
  testPublicExecution
  testIntegerRootBoundary
  testRecursiveRejections
  IO.println "staged integer source-call checks GREEN"

end Tests.SourceStagedIntegerCalls
