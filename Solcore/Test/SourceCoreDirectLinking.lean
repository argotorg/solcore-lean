import Solcore.Frontend.SourceCoreDirectLinking

/-! End-to-end regressions for validated direct-call specialization linking. -/

set_option autoImplicit false

namespace Tests.SourceCoreDirectLinking

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Eq<T> {}",
      "impl Eq<Word> {}",
      "function identity<T>(value: T) returns (T) { return value; }",
      "function wrap<U>(value: U) returns (U) { return identity(value); }",
      "function select<A, B>(left: A, right: B) returns (A) { return left; }",
      "function entry(value: Word, flag: Bool) returns (Word) {",
      "  return flag ? wrap(value) : select(value, flag);",
      "}",
      "function loop<T>(value: T) returns (T) { return loop(value); }",
      "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
      "function constrained(value: Word) returns (Word) { return keep(value); }"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"direct-linking fixture failed checking: {reprStr errors}")

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

private def replaceFunction (program : CheckedProgram)
    (replacement : CheckedFunction) : CheckedProgram := {
  program with
  functions := program.functions.map fun function =>
    if function.declaration == replacement.declaration then replacement
    else function
}

private def renameLocalReference (oldId newId : Resolved.LocalId) :
    ExpressionForm → ExpressionForm
  | .reference name (.local id) =>
      .reference name (.local (if id == oldId then newId else id))
  | form => form

private def renameInput (source : TypedSource) (oldId newId : Resolved.LocalId) :
    TypedSource := {
  source with
  inputs := source.inputs.map fun binder =>
    if binder.id == oldId then { binder with id := newId } else binder
  nodes := source.nodes.map fun
    | .expression node => .expression {
        node with form := renameLocalReference oldId newId node.form
      }
    | .statement node => .statement node
}

private def monomorphicRequest (signature : ProgramFunctionSignature) :
    SourceSpecializationWorklist.Request := {
  declaration := signature.id
  parameterSubstitution := []
}

private def unaryRequest (signature : ProgramFunctionSignature) (type : Ty) :
    IO SourceSpecializationWorklist.Request := do
  match signature.scheme.parameters with
  | [parameter] => pure {
      declaration := signature.id
      parameterSubstitution := [(parameter, type)]
    }
  | parameters => throw (IO.userError
      s!"expected one generic parameter for `{signature.name}`, found {parameters.length}")

private def runOrThrow (label : String) (program : CheckedProgram)
    (requests : List SourceSpecializationWorklist.Request) (budget : Nat) :
    IO SourceSpecializationWorklist.Outcome := do
  match SourceSpecializationWorklist.run program requests budget with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError
      s!"{label}: worklist failed: {reprStr error}")

private def linkOrThrow (label : String) (program : CheckedProgram)
    (outcome : SourceSpecializationWorklist.Outcome) :
    IO SourceCoreDirectLinking.LinkedProgram := do
  match SourceCoreDirectLinking.link program outcome with
  | .ok linked => pure linked
  | .error error => throw (IO.userError
      s!"{label}: linking failed: {reprStr error}")

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def testExecutionAndPlan (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let wrap ← signatureNamed program "wrap"
  let select ← signatureNamed program "select"
  let entry ← signatureNamed program "entry"
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let wrapKey : SourceSpecialization.SpecializationKey := {
    declaration := wrap.id
    arguments := [.word]
  }
  let selectKey : SourceSpecialization.SpecializationKey := {
    declaration := select.id
    arguments := [.word, .bool]
  }
  let identityKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let outcome ← runOrThrow "entry" program [monomorphicRequest entry] 4
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"entry: expected a complete plan, found {reprStr other}")
  assertTrue (decide (plan.seedKeys = [entryKey] ∧
      plan.specializations.map (·.key) =
        [entryKey, wrapKey, selectKey, identityKey]))
    "entry specialization roots or FIFO order changed"
  assertTrue (decide (plan.callEdges.map (fun edge =>
      (edge.caller.declaration, edge.callee.declaration)) = [
        (entry.id, wrap.id),
        (entry.id, select.id),
        (wrap.id, identity.id)
      ]))
    "entry direct-call edges changed their typed-node order"
  let linked ← linkOrThrow "entry" program outcome
  let linkedEntry ← match linked.findEntry? entryKey with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError "entry: linked root was absent")
  assertTrue (decide (linked.entries.map (·.key) = [entryKey] ∧
      Core.infer? linkedEntry.elaborated.inputs.values
        linkedEntry.elaborated.core = some .word))
    "entry lost its seed identity or independently checked Core type"
  let fortyOne := Core.Value.word (word 41)
  assertTrue (decide (
      linkedEntry.run? [fortyOne, .bool true] 512 =
        some (.done fortyOne []) ∧
      linkedEntry.run? [fortyOne, .bool false] 512 =
        some (.done fortyOne [])))
    "linked calls did not execute through both conditional branches"
  assertTrue ((linkedEntry.run? [.bool true, fortyOne] 512).isNone &&
      (linkedEntry.run? [fortyOne] 512).isNone)
    "linked entry accepted wrong runtime argument types or arity"
  let sourceEntry ← functionFor program entry
  match SourceCoreElaboration.elaborateFunction sourceEntry with
  | .error error =>
      assertTrue (error.reason matches .unsupportedExpression .call)
        s!"legacy elaboration rejected the real call for the wrong reason: {reprStr error}"
  | .ok _ => throw (IO.userError
      "legacy call-rejecting elaboration unexpectedly accepted entry")
  let duplicateOutcome ← runOrThrow "duplicate entry roots" program
    [monomorphicRequest entry, monomorphicRequest entry] 4
  let duplicateLinked ← linkOrThrow "duplicate entry roots" program
    duplicateOutcome
  assertTrue (decide (duplicateLinked.entries.map (·.key) =
      [entryKey, entryKey]))
    "linked roots did not preserve duplicate seed order"
  let malformed : SourceSpecializationWorklist.Plan := {
    plan with callEdges := plan.callEdges.tail
  }
  match SourceCoreDirectLinking.link program (.complete malformed) with
  | .error (.callEdgesMismatch expected actual) =>
      assertTrue (decide (expected = plan.callEdges ∧
          actual = plan.callEdges.tail))
        "malformed-plan rejection lost the exact call-edge lists"
  | result => throw (IO.userError
      s!"missing call edge was not rejected defensively: {reprStr result}")

private def testBudgetExhaustion (program : CheckedProgram) : IO Unit := do
  let identity ← signatureNamed program "identity"
  let entry ← signatureNamed program "entry"
  let identityKey : SourceSpecialization.SpecializationKey := {
    declaration := identity.id
    arguments := [.word]
  }
  let outcome ← runOrThrow "entry budget" program
    [monomorphicRequest entry] 3
  match outcome with
  | .budgetExhausted plan next pending =>
      assertTrue (decide (plan.specializations.length = 3 ∧
          plan.callEdges.length = 3 ∧ next = identityKey ∧
          pending.length = 1))
        "finite worklist exposed the wrong pending specialization"
  | other => throw (IO.userError
      s!"entry budget: expected exhaustion, found {reprStr other}")
  match SourceCoreDirectLinking.link program outcome with
  | .error (.budgetExhausted next 1) =>
      assertTrue (decide (next = identityKey))
        "linker budget error lost the next canonical key"
  | result => throw (IO.userError
      s!"budget-exhausted worklist was not rejected: {reprStr result}")

private def testCaptureAvoidance (program : CheckedProgram) : IO Unit := do
  let entry ← signatureNamed program "entry"
  let select ← signatureNamed program "select"
  let entryFunction ← functionFor program entry
  let selectFunction ← functionFor program select
  let callerFlag ← match entryFunction.typedBody.inputs with
    | _ :: flag :: _ => pure flag.id
    | _ => throw (IO.userError "entry lost its two input binders")
  let calleeLeft ← match selectFunction.typedBody.inputs with
    | left :: _ => pure left.id
    | _ => throw (IO.userError "select lost its first input binder")
  let collidingSelect : CheckedFunction := {
    selectFunction with
    typedBody := renameInput selectFunction.typedBody calleeLeft callerFlag
  }
  let collidingProgram := replaceFunction program collidingSelect
  let outcome ← runOrThrow "capture avoidance" collidingProgram
    [monomorphicRequest entry] 4
  let linked ← linkOrThrow "capture avoidance" collidingProgram outcome
  let entryKey : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? entryKey with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError "capture avoidance lost the linked root")
  let fortyOne := Core.Value.word (word 41)
  assertTrue (decide (linkedEntry.run? [fortyOne, .bool false] 512 =
      some (.done fortyOne [])))
    "callee input alias captured a later caller argument"

private def testCycle (program : CheckedProgram) : IO Unit := do
  let loop ← signatureNamed program "loop"
  let request ← unaryRequest loop .word
  let loopKey : SourceSpecialization.SpecializationKey := {
    declaration := loop.id
    arguments := [.word]
  }
  let outcome ← runOrThrow "loop" program [request] 1
  match outcome with
  | .complete _ => pure ()
  | other => throw (IO.userError
      s!"loop: expected a closed worklist plan, found {reprStr other}")
  match SourceCoreDirectLinking.link program outcome with
  | .error (.recursiveCallCycle key) =>
      assertTrue (decide (key = loopKey))
        "cycle rejection lost the recursive specialization key"
  | result => throw (IO.userError
      s!"self-recursive Core link was not rejected: {reprStr result}")

private def testEvidenceBoundary (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let constrained ← signatureNamed program "constrained"
  let outcome ← runOrThrow "constrained" program
    [monomorphicRequest constrained] 2
  match SourceCoreDirectLinking.link program outcome with
  | .error (.unresolvedAssumptions key assumptions) =>
      assertTrue (decide (key.declaration = keep.id ∧ assumptions.length = 1))
        "constraint rejection lost the specialized callee assumption"
  | .error (.sourceCore error) =>
      let explicitEvidenceBoundary := match error.reason with
        | .requirementsPresent requirements => !requirements.isEmpty
        | .unconsumedRequirements requirements => !requirements.isEmpty
        | _ => false
      assertTrue explicitEvidenceBoundary
        s!"constrained call failed outside the evidence boundary: {reprStr error}"
  | result => throw (IO.userError
      s!"constrained direct call was not rejected explicitly: {reprStr result}")

/-- Exercise complete acyclic generic linking, capture-free argument staging,
runtime input validation, finite-budget and recursion boundaries, retained
trait evidence, the legacy call-free entry point, and defensive plan
reconstruction. -/
def testSourceCoreDirectLinking : IO Unit := do
  let program ← checkedProgram
  testExecutionAndPlan program
  testBudgetExhaustion program
  testCaptureAvoidance program
  testCycle program
  testEvidenceBoundary program

end Tests.SourceCoreDirectLinking
