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
      "trait Eq<T> {",
      "  function eq(left: T, right: T) returns (Bool);",
      "}",
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "trait Marker<T> {}",
      "trait Coerce<From, To> {",
      "  function coerce(value: From) returns (To);",
      "}",
      "impl Eq<Word> {",
      "  function eq(left: Word, right: Word) returns (Bool) {",
      "    return !(left == right);",
      "  }",
      "}",
      "impl Add<Word> {",
      "  function add(left: Word, right: Word) returns (Word) {",
      "    return left - right;",
      "  }",
      "}",
      "impl Marker<Bool> {}",
      "impl Coerce<Bool, Word> {",
      "  function coerce(value: Bool) returns (Word) {",
      "    return value ? 41 : 7;",
      "  }",
      "}",
      "function ne<T>(left: T, right: T) returns (Bool) where T: Eq {",
      "  return !(left == right);",
      "}",
      "function identity<T>(value: T) returns (T) { return value; }",
      "function wrap<U>(value: U) returns (U) { return identity(value); }",
      "function select<A, B>(left: A, right: B) returns (A) { return left; }",
      "function entry(value: Word, flag: Bool) returns (Word) {",
      "  return flag ? wrap(value) : select(value, flag);",
      "}",
      "function loop<T>(value: T) returns (T) { return loop(value); }",
      "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
      "function constrained(value: Word) returns (Word) { return keep(value); }",
      "function relay<T>(value: T) returns (T) where T: Eq { return keep(value); }",
      "function nestedConstrained(value: Word) returns (Word) { return relay(value); }",
      "function keepBoth<T>(value: T) returns (T) where T: Eq, T: Add { return value; }",
      "function bothConstrained(value: Word) returns (Word) { return keepBoth(value); }",
      "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
      "  return left + right;",
      "}",
      "function operatorConstrained(left: Word, right: Word) returns (Word) {",
      "  return addWithEvidence(left, right);",
      "}",
      "function equalWithEvidence<T>(left: T, right: T) returns (Bool) where T: Eq {",
      "  return left == right;",
      "}",
      "function equalityConstrained(left: Word, right: Word) returns (Bool) {",
      "  return equalWithEvidence(left, right);",
      "}",
      "function notEqualWithEvidence<T>(left: T, right: T) returns (Bool) where T: Eq {",
      "  return left != right;",
      "}",
      "function inequalityConstrained(left: Word, right: Word) returns (Bool) {",
      "  return notEqualWithEvidence(left, right);",
      "}",
      "function acceptWord(value: Word) returns (Word) { return value; }",
      "function coercionCall(value: Bool) returns (Word) { return acceptWord(value); }",
      "function coerceWithEvidence<T>(value: T) returns (Word) where T: Coerce<Word> {",
      "  return acceptWord(value);",
      "}",
      "function genericCoercion(value: Bool) returns (Word) {",
      "  return coerceWithEvidence(value);",
      "}",
      "function keepMarker<T>(value: T) returns (T) where T: Marker { return value; }",
      "function resultCoercion(value: Bool) returns (Word) {",
      "  return keepMarker(value);",
      "}"
    ]
  }]
  externalLibraries := []
}

private def checkedProgram : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"direct-linking fixture failed checking: {reprStr errors}")

private def checkedProgramOf (content : String) : IO CheckedProgram := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [{ path := "main.solc", content }]
    externalLibraries := []
  }
  match checkProgram workspace with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"direct-linking boundary fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature := do
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private def signatureNamedWithGenericArity (program : CheckedProgram)
    (name : String) (genericArity : Nat) : IO ProgramFunctionSignature := do
  match program.signatures.functions.filter fun signature =>
      signature.name == name &&
        signature.scheme.parameters.length == genericArity with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one `{name}` signature with {genericArity} generic parameters, found {signatures.length}")

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

private def firstDirectCallNode? : List Node → Option ExpressionNode
  | [] => none
  | .expression node :: rest =>
      match node.form with
      | .call _ _ (.declaration _) => some node
      | _ => firstDirectCallNode? rest
  | .statement _ :: rest => firstDirectCallNode? rest

private def firstBinaryNode? : List Node → Option ExpressionNode
  | [] => none
  | .expression node :: rest =>
      match node.form with
      | .binary _ _ _ => some node
      | _ => firstBinaryNode? rest
  | .statement _ :: rest => firstBinaryNode? rest

private def firstUnaryNode? : List Node → Option ExpressionNode
  | [] => none
  | .expression node :: rest =>
      match node.form with
      | .unary _ _ => some node
      | _ => firstUnaryNode? rest
  | .statement _ :: rest => firstUnaryNode? rest

private def firstCoercedNode? : List Node → Option ExpressionNode
  | [] => none
  | .expression node :: rest =>
      if node.coercions.isEmpty then firstCoercedNode? rest else some node
  | .statement _ :: rest => firstCoercedNode? rest

private def replaceExpressionRequirements (nodes : List Node)
    (target : ExpressionId) (requirements : List RequirementId) : List Node :=
  nodes.map fun node => match node with
  | .expression expression =>
      if expression.id == target then
        .expression { expression with requirements }
      else
        node
  | .statement _ => node

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

private def testProofOnlyEvidence (program : CheckedProgram) : IO Unit := do
  let keep ← signatureNamed program "keep"
  let constrained ← signatureNamed program "constrained"
  let outcome ← runOrThrow "constrained" program
    [monomorphicRequest constrained] 2
  let linked ← linkOrThrow "constrained" program outcome
  let constrainedKey : SourceSpecialization.SpecializationKey := {
    declaration := constrained.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? constrainedKey with
    | some entry => pure entry
    | none => throw (IO.userError "constrained: linked root was absent")
  let fortyOne := Core.Value.word (word 41)
  assertTrue (decide (linkedEntry.run? [fortyOne] 256 =
      some (.done fortyOne [])))
    "runtime-unused direct-call evidence did not erase before execution"

  let relay ← signatureNamed program "relay"
  let nested ← signatureNamed program "nestedConstrained"
  let nestedOutcome ← runOrThrow "nested constrained" program
    [monomorphicRequest nested] 3
  let nestedPlan ← match nestedOutcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"nested constrained: expected a complete plan, found {reprStr other}")
  let nestedSpecialized := nestedPlan.specializations.find? fun specialized =>
    specialized.declaration == nested.id
  let relaySpecialized := nestedPlan.specializations.find? fun specialized =>
    specialized.declaration == relay.id
  let keepSpecialized := nestedPlan.specializations.find? fun specialized =>
    specialized.declaration == keep.id
  let implementationAtRoot := nestedSpecialized.any fun specialized =>
    specialized.function.solvedRequirements.any fun requirement =>
      requirement.evidence matches .implementation _
  let assumptionInRelay := relaySpecialized.any fun specialized =>
    specialized.function.solvedRequirements.any fun requirement =>
      requirement.evidence matches .assumption _
  let retainedKeepAssumption := keepSpecialized.any fun specialized =>
    specialized.assumptions.length == 1
  assertTrue (implementationAtRoot && assumptionInRelay &&
      retainedKeepAssumption)
    "nested constrained fixture did not retain its implementation/assumption chain"
  let nestedLinked ← linkOrThrow "nested constrained" program nestedOutcome
  let nestedKey : SourceSpecialization.SpecializationKey := {
    declaration := nested.id
    arguments := []
  }
  let nestedEntry ← match nestedLinked.findEntry? nestedKey with
    | some entry => pure entry
    | none => throw (IO.userError "nested constrained: linked root was absent")
  assertTrue (decide (nestedEntry.run? [fortyOne] 512 =
      some (.done fortyOne [])))
    "assumption evidence was not forwarded through the nested generic call"

  let keepRequest ← unaryRequest keep .word
  let keepOutcome ← runOrThrow "unresolved keep seed" program [keepRequest] 1
  match SourceCoreDirectLinking.link program keepOutcome with
  | .error (.unresolvedAssumptions key assumptions) =>
      assertTrue (decide (key.declaration = keep.id ∧ assumptions.length = 1))
        "unresolved seed rejection lost the specialized root assumption"
  | result => throw (IO.userError
      s!"an unresolved constrained seed was not rejected: {reprStr result}")

private def testRuntimeEvidenceBoundaries (program : CheckedProgram) : IO Unit := do
  let operatorConstrained ← signatureNamed program "operatorConstrained"
  let operatorOutcome ← runOrThrow "operator evidence" program
    [monomorphicRequest operatorConstrained] 2
  let operatorLinked ← linkOrThrow "operator evidence" program operatorOutcome
  let operatorKey : SourceSpecialization.SpecializationKey := {
    declaration := operatorConstrained.id
    arguments := []
  }
  let operatorEntry ← match operatorLinked.findEntry? operatorKey with
    | some entry => pure entry
    | none => throw (IO.userError "operator evidence: linked root was absent")
  assertTrue (decide (operatorEntry.run?
      [.word (word 50), .word (word 8)] 1024 =
        some (.done (.word (word 42)) [])))
    "Add evidence did not execute the selected subtracting impl method body"

  let equalityConstrained ← signatureNamed program "equalityConstrained"
  let equalityOutcome ← runOrThrow "equality evidence" program
    [monomorphicRequest equalityConstrained] 2
  let equalityLinked ← linkOrThrow "equality evidence" program equalityOutcome
  let equalityKey : SourceSpecialization.SpecializationKey := {
    declaration := equalityConstrained.id
    arguments := []
  }
  let equalityEntry ← match equalityLinked.findEntry? equalityKey with
    | some entry => pure entry
    | none => throw (IO.userError "equality evidence: linked root was absent")
  assertTrue (decide (equalityEntry.run?
        [.word (word 50), .word (word 50)] 1024 =
          some (.done (.bool false) []) ∧
      equalityEntry.run? [.word (word 50), .word (word 8)] 1024 =
          some (.done (.bool true) [])))
    "Eq evidence did not execute the selected nonstandard impl method body"

  let inequalityConstrained ← signatureNamed program "inequalityConstrained"
  let inequalityOutcome ← runOrThrow "inequality evidence" program
    [monomorphicRequest inequalityConstrained] 3
  let inequalityLinked ←
    linkOrThrow "inequality evidence" program inequalityOutcome
  let inequalityKey : SourceSpecialization.SpecializationKey := {
    declaration := inequalityConstrained.id
    arguments := []
  }
  let inequalityEntry ← match inequalityLinked.findEntry? inequalityKey with
    | some entry => pure entry
    | none => throw (IO.userError "inequality evidence: linked root was absent")
  assertTrue (decide (inequalityEntry.run?
        [.word (word 50), .word (word 50)] 1024 =
          some (.done (.bool true) []) ∧
      inequalityEntry.run? [.word (word 50), .word (word 8)] 1024 =
          some (.done (.bool false) [])))
    "source != did not negate the selected Eq.eq method result"

  let coercionCall ← signatureNamed program "coercionCall"
  let coercionOutcome ← runOrThrow "coercion call" program
    [monomorphicRequest coercionCall] 2
  let coercionLinked ← linkOrThrow "coercion call" program coercionOutcome
  let coercionKey : SourceSpecialization.SpecializationKey := {
    declaration := coercionCall.id
    arguments := []
  }
  let coercionEntry ← match coercionLinked.findEntry? coercionKey with
    | some entry => pure entry
    | none => throw (IO.userError "coercion call: linked root was absent")
  assertTrue (decide (coercionEntry.run? [.bool true] 1024 =
        some (.done (.word (word 41)) []) ∧
      coercionEntry.run? [.bool false] 1024 =
        some (.done (.word (word 7)) [])))
    "Coerce evidence did not execute its selected conditional method body"

  let genericCoercion ← signatureNamed program "genericCoercion"
  let genericOutcome ← runOrThrow "generic coercion" program
    [monomorphicRequest genericCoercion] 3
  let genericLinked ← linkOrThrow "generic coercion" program genericOutcome
  let genericKey : SourceSpecialization.SpecializationKey := {
    declaration := genericCoercion.id
    arguments := []
  }
  let genericEntry ← match genericLinked.findEntry? genericKey with
    | some entry => pure entry
    | none => throw (IO.userError "generic coercion: linked root was absent")
  assertTrue (decide (genericEntry.run? [.bool true] 2048 =
      some (.done (.word (word 41)) [])))
    "closed Coerce evidence was not forwarded to a generic callee conversion"

  let resultCoercion ← signatureNamed program "resultCoercion"
  let resultOutcome ← runOrThrow "call-result coercion" program
    [monomorphicRequest resultCoercion] 2
  let resultLinked ← linkOrThrow "call-result coercion" program resultOutcome
  let resultKey : SourceSpecialization.SpecializationKey := {
    declaration := resultCoercion.id
    arguments := []
  }
  let resultEntry ← match resultLinked.findEntry? resultKey with
    | some entry => pure entry
    | none => throw (IO.userError "call-result coercion: linked root was absent")
  assertTrue (decide (resultEntry.run? [.bool false] 2048 =
      some (.done (.word (word 7)) [])))
    "call-result coercion did not coexist with its proof-only signature evidence"

private def testImplementationMethodDirectCall : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) {",
    "    return helper(left);",
    "  }",
    "}",
    "function helper(value: Word) returns (Word) { return value; }",
    "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return addWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let helper ← signatureNamed program "helper"
  let outcome ← runOrThrow "implementation method direct call" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"implementation method call: incomplete plan {reprStr other}")
  assertTrue (!(plan.specializations.any fun specialized =>
      specialized.declaration == helper.id))
    "method-only helper unexpectedly appeared in the top-level worklist"
  let linked ← linkOrThrow "implementation method direct call" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "implementation method direct call: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 50), .word (word 8)] 2048 =
        some (.done (.word (word 50)) [])))
    "implementation method did not execute its detached direct-call helper"

private def testMultiMethodImplementationSelection : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "  function tag(value: T) returns (Bool);",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return 91; }",
    "  function tag(value: Word) returns (Bool) { return true; }",
    "}",
    "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return addWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let outcome ← runOrThrow "multi-method implementation selection" program
    [monomorphicRequest entry] 2
  let linked ← linkOrThrow "multi-method implementation selection" program
    outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "multi-method implementation selection: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 50), .word (word 8)] 2048 =
        some (.done (.word (word 91)) [])))
    "multi-method Add implementation did not execute its named add method"

private def testImplementationMethodCallCycle : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) {",
    "    return helper(left);",
    "  }",
    "}",
    "function helper(value: Word) returns (Word) { return helper(value); }",
    "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return addWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let helper ← signatureNamed program "helper"
  let outcome ← runOrThrow "implementation method call cycle" program
    [monomorphicRequest entry] 2
  match SourceCoreDirectLinking.link program outcome with
  | .error (.recursiveCallCycle key) =>
      assertTrue (decide (key.declaration = helper.id ∧ key.arguments = []))
        "detached method-call cycle lost its canonical helper key"
  | result => throw (IO.userError
      s!"a recursive implementation-method helper was executable: {reprStr result}")

private def testStrictRuntimeBinaryEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Sub<T> {",
    "  function sub(left: T, right: T) returns (T);",
    "}",
    "trait Mul<T> {",
    "  function mul(left: T, right: T) returns (T);",
    "}",
    "trait Div<T> {",
    "  function div(left: T, right: T) returns (T);",
    "}",
    "trait Mod<T> {",
    "  function mod(left: T, right: T) returns (T);",
    "}",
    "trait BitAnd<T> {",
    "  function band(left: T, right: T) returns (T);",
    "}",
    "trait BitXor<T> {",
    "  function bxor(left: T, right: T) returns (T);",
    "}",
    "trait BitOr<T> {",
    "  function bor(left: T, right: T) returns (T);",
    "}",
    "impl Sub<Word> {",
    "  function sub(left: Word, right: Word) returns (Word) {",
    "    return left;",
    "  }",
    "}",
    "impl Mul<Word> {",
    "  function mul(left: Word, right: Word) returns (Word) {",
    "    return 91;",
    "  }",
    "}",
    "impl Div<Word> {",
    "  function div(left: Word, right: Word) returns (Word) {",
    "    return 92;",
    "  }",
    "}",
    "impl Mod<Word> {",
    "  function mod(left: Word, right: Word) returns (Word) {",
    "    return 93;",
    "  }",
    "}",
    "impl BitAnd<Word> {",
    "  function band(left: Word, right: Word) returns (Word) {",
    "    return 94;",
    "  }",
    "}",
    "impl BitXor<Word> {",
    "  function bxor(left: Word, right: Word) returns (Word) {",
    "    return 95;",
    "  }",
    "}",
    "impl BitOr<Word> {",
    "  function bor(left: Word, right: Word) returns (Word) {",
    "    return 96;",
    "  }",
    "}",
    "function subtractWithEvidence<T>(left: T, right: T) returns (T) where T: Sub {",
    "  return left - right;",
    "}",
    "function multiplyWithEvidence<T>(left: T, right: T) returns (T) where T: Mul {",
    "  return left * right;",
    "}",
    "function divideWithEvidence<T>(left: T, right: T) returns (T) where T: Div {",
    "  return left / right;",
    "}",
    "function moduloWithEvidence<T>(left: T, right: T) returns (T) where T: Mod {",
    "  return left % right;",
    "}",
    "function bitAndWithEvidence<T>(left: T, right: T) returns (T) where T: BitAnd {",
    "  return left & right;",
    "}",
    "function bitXorWithEvidence<T>(left: T, right: T) returns (T) where T: BitXor {",
    "  return left ^ right;",
    "}",
    "function bitOrWithEvidence<T>(left: T, right: T) returns (T) where T: BitOr {",
    "  return left | right;",
    "}",
    "function subtractEntry(left: Word, right: Word) returns (Word) {",
    "  return subtractWithEvidence(left, right);",
    "}",
    "function multiplyEntry(left: Word, right: Word) returns (Word) {",
    "  return multiplyWithEvidence(left, right);",
    "}",
    "function divideEntry(left: Word, right: Word) returns (Word) {",
    "  return divideWithEvidence(left, right);",
    "}",
    "function moduloEntry(left: Word, right: Word) returns (Word) {",
    "  return moduloWithEvidence(left, right);",
    "}",
    "function bitAndEntry(left: Word, right: Word) returns (Word) {",
    "  return bitAndWithEvidence(left, right);",
    "}",
    "function bitXorEntry(left: Word, right: Word) returns (Word) {",
    "  return bitXorWithEvidence(left, right);",
    "}",
    "function bitOrEntry(left: Word, right: Word) returns (Word) {",
    "  return bitOrWithEvidence(left, right);",
    "}"
  ])
  let cases : List (String × List Core.Value × Core.Value) := [
    ("subtractEntry", [.word (word 50), .word (word 8)], .word (word 50)),
    ("multiplyEntry", [.word (word 6), .word (word 7)], .word (word 91)),
    ("divideEntry", [.word (word 50), .word (word 8)], .word (word 92)),
    ("moduloEntry", [.word (word 50), .word (word 8)], .word (word 93)),
    ("bitAndEntry", [.word (word 6), .word (word 9)], .word (word 94)),
    ("bitXorEntry", [.word (word 6), .word (word 3)], .word (word 95)),
    ("bitOrEntry", [.word (word 6), .word (word 3)], .word (word 96))
  ]
  for (name, inputs, expected) in cases do
    let entry ← signatureNamed program name
    let outcome ← runOrThrow s!"{name} evidence" program
      [monomorphicRequest entry] 2
    let linked ← linkOrThrow s!"{name} evidence" program outcome
    let key : SourceSpecialization.SpecializationKey := {
      declaration := entry.id
      arguments := []
    }
    let linkedEntry ← match linked.findEntry? key with
      | some linkedEntry => pure linkedEntry
      | none => throw (IO.userError s!"{name}: linked root was absent")
    assertTrue (decide (linkedEntry.run? inputs 2048 =
        some (.done expected [])))
      s!"{name} did not execute its selected strict binary method body"

private def testRuntimeBitNotEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T);",
    "}",
    "impl BitNot<Word> {",
    "  function bnot(value: Word) returns (Word) { return 91; }",
    "}",
    "function bitNotWithEvidence<T>(value: T) returns (T) where T: BitNot {",
    "  return ~value;",
    "}",
    "function evidenceEntry(value: Word) returns (Word) {",
    "  return bitNotWithEvidence(value);",
    "}",
    "function builtinEntry(value: Word) returns (Word) { return ~value; }"
  ])
  let bitNotWithEvidence ← signatureNamed program "bitNotWithEvidence"
  let genericFunction ← functionFor program bitNotWithEvidence
  let unary ← match firstUnaryNode? genericFunction.typedBody.nodes with
    | some unary => pure unary
    | none => throw (IO.userError
        "BitNot evidence fixture lost its unary occurrence")
  let solved ← match unary.requirements.filterMap fun requirement =>
      genericFunction.solvedRequirements.find? fun row =>
        row.id == requirement with
    | [solved] => pure solved
    | requirements => throw (IO.userError
        s!"BitNot unary expected one solved requirement, found {requirements.length}")
  let assumptionMatches := match solved.evidence with
    | .assumption predicate => predicate == solved.predicate
    | _ => false
  assertTrue ((match unary.form with
      | .unary .bitNot _ => true
      | _ => false) && unary.requirements.length == 1 && assumptionMatches)
    "generic ~ did not retain its BitNot assumption and occurrence metadata"

  let evidenceEntry ← signatureNamed program "evidenceEntry"
  let evidenceOutcome ← runOrThrow "BitNot evidence" program
    [monomorphicRequest evidenceEntry] 2
  let evidencePlan ← match evidenceOutcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"BitNot evidence: expected a complete plan, found {reprStr other}")
  let specializedGeneric := evidencePlan.specializations.find? fun specialized =>
    specialized.declaration == bitNotWithEvidence.id
  let implementation ← match program.signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"BitNot evidence expected one implementation, found {implementations.length}")
  assertTrue (specializedGeneric.any fun specialized => decide (
      specialized.key.arguments = [.word] ∧
      specialized.assumptions = [implementation.head]))
    "BitNot specialization lost its closed implementation assumption"
  let evidenceLinked ← linkOrThrow "BitNot evidence" program evidenceOutcome
  let evidenceKey : SourceSpecialization.SpecializationKey := {
    declaration := evidenceEntry.id
    arguments := []
  }
  let linkedEvidence ← match evidenceLinked.findEntry? evidenceKey with
    | some entry => pure entry
    | none => throw (IO.userError "BitNot evidence: linked root was absent")
  assertTrue (decide (linkedEvidence.run? [.word (word 7)] 2048 =
      some (.done (.word (word 91)) [])))
    "BitNot evidence did not execute the selected nonstandard bnot method body"

  let builtinEntry ← signatureNamed program "builtinEntry"
  let builtinFunction ← functionFor program builtinEntry
  let builtinUnary ← match firstUnaryNode? builtinFunction.typedBody.nodes with
    | some unary => pure unary
    | none => throw (IO.userError "builtin ~ occurrence was absent")
  assertTrue (builtinUnary.requirements.isEmpty)
    "concrete Word ~ unexpectedly acquired BitNot evidence"
  let builtinOutcome ← runOrThrow "builtin bit-not" program
    [monomorphicRequest builtinEntry] 1
  let builtinLinked ← linkOrThrow "builtin bit-not" program builtinOutcome
  let builtinKey : SourceSpecialization.SpecializationKey := {
    declaration := builtinEntry.id
    arguments := []
  }
  let linkedBuiltin ← match builtinLinked.findEntry? builtinKey with
    | some entry => pure entry
    | none => throw (IO.userError "builtin bit-not: linked root was absent")
  assertTrue (decide (linkedBuiltin.run? [.word (word 7)] 2048 =
      some (.done (.word (word 7).bitNot) [])))
    "concrete Word ~ stopped using the builtin compatibility operation"

private structure NamedOperatorCase where
  entryName : String
  callee : ProgramFunctionSignature
  operandType : Ty
  inputs : List Core.Value
  expected : Bool
  requirementCount : Nat

private def testNamedOperatorCase (program : CheckedProgram)
    (case : NamedOperatorCase) : IO Unit := do
  let entry ← signatureNamed program case.entryName
  let function ← functionFor program entry
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        s!"{case.entryName}: named operator did not become a direct call")
  let (calleeId, arguments, instantiation) ← match call.form with
    | .call callee arguments (.declaration instantiation) =>
        pure (callee, arguments, instantiation)
    | form => throw (IO.userError
        s!"{case.entryName}: selected call changed form: {reprStr form}")
  let calleeNode ← match function.typedBody.lookupExpression? calleeId with
    | some callee => pure callee
    | none => throw (IO.userError
        s!"{case.entryName}: synthetic callee node was absent")
  let calleeMatches := match calleeNode.form with
    | .reference name (.declaration reference) =>
        decide (name = case.callee.name ∧ reference = instantiation)
    | _ => false
  let argumentBinders := arguments.filterMap fun argument =>
    match function.typedBody.lookupExpression? argument with
    | some { form := .reference _ (.local binder), .. } => some binder
    | _ => none
  let solved := call.requirements.filterMap fun requirement =>
    function.solvedRequirements.find? fun row => row.id == requirement
  let expectedType := Ty.function
    (Ty.product case.operandType case.operandType) .bool
  let expectedTypeArguments :=
    if case.callee.scheme.parameters.isEmpty then [] else [case.operandType]
  assertTrue (calleeMatches && decide (
      call.type = .bool ∧ calleeNode.type = instantiation.type ∧
      instantiation.declaration = case.callee.id ∧
      instantiation.type = expectedType ∧
      instantiation.parameterSubstitution.map (fun entry => entry.2) =
        expectedTypeArguments ∧
      arguments.length = 2 ∧
      argumentBinders = function.typedBody.inputs.map (fun binder => binder.id) ∧
      call.requirements.length = case.requirementCount ∧
      solved.length = case.requirementCount ∧
      solved.map (fun row => row.predicate) = instantiation.predicates) &&
      solved.all fun row => row.evidence matches .implementation _)
    s!"{case.entryName}: named operator lost its selected-call typed metadata"

  let outcome ← runOrThrow s!"{case.entryName} named operator" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"{case.entryName}: expected a complete plan, found {reprStr other}")
  let specializedCallee := plan.specializations.find? fun specialized =>
    specialized.declaration == case.callee.id
  assertTrue (decide (
      plan.specializations.map (fun specialized => specialized.declaration) =
        [entry.id, case.callee.id] ∧
      plan.callEdges.map (fun edge =>
        (edge.caller.declaration, edge.occurrence, edge.callee.declaration)) =
        [(entry.id, call.id, case.callee.id)]) &&
      specializedCallee.any fun specialized =>
        decide (specialized.key.arguments = expectedTypeArguments ∧
          specialized.assumptions = instantiation.predicates))
    s!"{case.entryName}: named operator did not specialize through its selected edge"
  let linked ← linkOrThrow s!"{case.entryName} named operator" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        s!"{case.entryName}: linked root was absent")
  assertTrue (decide (linkedEntry.run? case.inputs 2048 =
      some (.done (.bool case.expected) [])))
    s!"{case.entryName}: selected named function body was not authoritative"

private def testNamedOperatorFunctionsAndOrd : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return true; }",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}",
    "function ne<T>(left: T, right: T) returns (Bool) where T: Eq {",
    "  return true;",
    "}",
    "function lt<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return false;",
    "}",
    "function lt(left: Word, right: Word) returns (Word) { return 77; }",
    "function le<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return true;",
    "}",
    "function ge<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return true;",
    "}",
    "function and(left: Bool, right: Bool) returns (Bool) { return false; }",
    "function or(left: Bool, right: Bool) returns (Bool) { return false; }",
    "function gt(left: Word, right: Word) returns (Bool) { return false; }",
    "function notEqualEntry(left: Word, right: Word) returns (Bool) {",
    "  return left != right;",
    "}",
    "function lessEntry(left: Word, right: Word) returns (Bool) {",
    "  let selected = left < right;",
    "  return selected;",
    "}",
    "function lessEqualEntry(left: Word, right: Word) returns (Bool) {",
    "  return left <= right;",
    "}",
    "function greaterEqualEntry(left: Word, right: Word) returns (Bool) {",
    "  return left >= right;",
    "}",
    "function logicalAndEntry(left: Bool, right: Bool) returns (Bool) {",
    "  return left && right;",
    "}",
    "function logicalOrEntry(left: Bool, right: Bool) returns (Bool) {",
    "  return left || right;",
    "}",
    "function greaterWithEvidence<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return left > right;",
    "}",
    "function greaterEntry(left: Word, right: Word) returns (Bool) {",
    "  return greaterWithEvidence(left, right);",
    "}"
  ])
  let ne ← signatureNamedWithGenericArity program "ne" 1
  let lt ← signatureNamedWithGenericArity program "lt" 1
  let le ← signatureNamedWithGenericArity program "le" 1
  let ge ← signatureNamedWithGenericArity program "ge" 1
  let and ← signatureNamedWithGenericArity program "and" 0
  let or ← signatureNamedWithGenericArity program "or" 0
  let cases : List NamedOperatorCase := [
    {
      entryName := "notEqualEntry"
      callee := ne
      operandType := .word
      inputs := [.word (word 7), .word (word 7)]
      expected := true
      requirementCount := 1
    },
    {
      entryName := "lessEntry"
      callee := lt
      operandType := .word
      inputs := [.word (word 1), .word (word 2)]
      expected := false
      requirementCount := 1
    },
    {
      entryName := "lessEqualEntry"
      callee := le
      operandType := .word
      inputs := [.word (word 2), .word (word 1)]
      expected := true
      requirementCount := 1
    },
    {
      entryName := "greaterEqualEntry"
      callee := ge
      operandType := .word
      inputs := [.word (word 1), .word (word 2)]
      expected := true
      requirementCount := 1
    },
    {
      entryName := "logicalAndEntry"
      callee := and
      operandType := .bool
      inputs := [.bool true, .bool true]
      expected := false
      requirementCount := 0
    },
    {
      entryName := "logicalOrEntry"
      callee := or
      operandType := .bool
      inputs := [.bool false, .bool true]
      expected := false
      requirementCount := 0
    }
  ]
  for case in cases do
    testNamedOperatorCase program case

  let ord ← match program.signatures.traits.filter fun trait =>
      trait.name == "Ord" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"Ord dispatch: expected one trait, found {traits.length}")
  let greater ← signatureNamed program "greaterWithEvidence"
  let greaterEntry ← signatureNamed program "greaterEntry"
  let namedGt ← signatureNamedWithGenericArity program "gt" 0
  let greaterFunction ← functionFor program greater
  let greaterBinary ← match firstBinaryNode? greaterFunction.typedBody.nodes with
    | some node => pure node
    | none => throw (IO.userError
        "Ord dispatch: generic greater body lost its binary occurrence")
  let requirement ← match greaterBinary.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"Ord dispatch: expected one binary requirement, found {requirements.length}")
  let solved ← match greaterFunction.solvedRequirements.filter fun row =>
      row.id == requirement with
    | [solved] => pure solved
    | rows => throw (IO.userError
        s!"Ord dispatch: expected one solved row, found {rows.length}")
  assertTrue ((match greaterBinary.form with
      | .binary _ .greater _ => true
      | _ => false) && decide (
      greaterBinary.type = .bool ∧ solved.predicate.trait = ord.id ∧
      solved.predicate.arguments = []) &&
      (solved.evidence matches .assumption _))
    "source > did not retain its Ord.gt requirement and generic assumption"

  let greaterOutcome ← runOrThrow "Ord.gt dispatch" program
    [monomorphicRequest greaterEntry] 2
  let greaterPlan ← match greaterOutcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"Ord dispatch: expected a complete plan, found {reprStr other}")
  let specializedGreater := greaterPlan.specializations.find? fun specialized =>
    specialized.declaration == greater.id
  assertTrue (decide (
      greaterPlan.specializations.map (fun specialized => specialized.declaration) =
        [greaterEntry.id, greater.id] ∧
      greaterPlan.callEdges.map (fun edge => edge.callee.declaration) =
        [greater.id]) &&
      !greaterPlan.specializations.any (fun specialized =>
        specialized.declaration == namedGt.id) &&
      specializedGreater.any fun specialized =>
        decide (specialized.key.arguments = [.word] ∧
          specialized.assumptions.length = 1 ∧
          specialized.assumptions.all fun predicate =>
            predicate.trait = ord.id ∧ predicate.subject = .word))
    "source > selected the named gt decoy or lost its Ord specialization"
  let greaterLinked ← linkOrThrow "Ord.gt dispatch" program greaterOutcome
  let greaterKey : SourceSpecialization.SpecializationKey := {
    declaration := greaterEntry.id
    arguments := []
  }
  let linkedGreater ← match greaterLinked.findEntry? greaterKey with
    | some entry => pure entry
    | none => throw (IO.userError "Ord dispatch: linked root was absent")
  assertTrue (decide (linkedGreater.run?
      [.word (word 1), .word (word 2)] 2048 =
        some (.done (.bool true) [])))
    "source > did not execute the selected nonstandard Ord.gt method body"

private def testTraitPredicateIsStaticMethodAssumption : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}",
    "function greaterWithEvidence<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return left > right;",
    "}",
    "function entry(left: Word, right: Word) returns (Bool) {",
    "  return greaterWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let greater ← signatureNamed program "greaterWithEvidence"
  let function ← functionFor program greater
  let binary ← match firstBinaryNode? function.typedBody.nodes with
    | some binary => pure binary
    | none => throw (IO.userError
        "trait-predicate fixture lost its Ord binary occurrence")
  let solved ← match binary.requirements.filterMap fun requirement =>
      function.solvedRequirements.find? fun row => row.id == requirement with
    | [solved] => pure solved
    | requirements => throw (IO.userError
        s!"trait-predicate fixture expected one Ord requirement, found {requirements.length}")
  let implementation ← match program.signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"trait-predicate fixture expected one Ord impl, found {implementations.length}")
  let evidenceMatches := match solved.evidence with
    | .assumption predicate => decide (predicate = solved.predicate)
    | _ => false
  assertTrue (evidenceMatches && decide (implementation.wherePredicates = []))
    "generic > did not retain its premise-free Ord assumption"
  let outcome ← runOrThrow "static trait predicate assumption" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"static trait predicate: expected a complete plan, found {reprStr other}")
  let specializedGreater := plan.specializations.find? fun specialized =>
    specialized.declaration == greater.id
  assertTrue (specializedGreater.any fun specialized =>
      decide (specialized.assumptions = [implementation.head]))
    "Ord specialization lost its sole explicit Ord<Word> assumption"
  let linked ← linkOrThrow "static trait predicate assumption" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "static trait predicate: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 9), .word (word 1)] 2048 =
        some (.done (.bool true) [])))
    "Ord.gt required an Eq implementation even though its body did not consume Eq"

private def testMissingConsumedTraitPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "function consumeEq<T>(value: T) returns (Bool) where T: Eq { return true; }",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return consumeEq(left); }",
    "}",
    "function greaterWithEvidence<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return left > right;",
    "}",
    "function entry(left: Word, right: Word) returns (Bool) {",
    "  return greaterWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let eq ← match program.signatures.traits.filter fun trait =>
      trait.name == "Eq" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"consumed trait predicate: expected one Eq trait, found {traits.length}")
  let implementation ← match program.signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"consumed trait predicate: expected one Ord impl, found {implementations.length}")
  let outcome ← runOrThrow "consumed trait predicate boundary" program
    [monomorphicRequest entry] 2
  match SourceCoreDirectLinking.link program outcome with
  | .error (.missingAssumptionEvidence key _ _ predicate) =>
      assertTrue (decide (key.declaration = implementation.id ∧
          predicate.trait = eq.id ∧ predicate.subject = .word ∧
          predicate.arguments = []))
        "missing superclass evidence lost its implementation-method predicate"
  | result => throw (IO.userError
      s!"a consumed trait predicate without evidence was accepted: {reprStr result}")

private def testConsumedTraitPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
    "}",
    "function equalWithEvidence<T>(left: T, right: T) returns (Bool) where T: Eq {",
    "  return left == right;",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) {",
    "    return equalWithEvidence(left, right);",
    "  }",
    "}",
    "function greaterWithEvidence<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return left > right;",
    "}",
    "function entry(left: Word, right: Word) returns (Bool) {",
    "  return greaterWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let equal ← signatureNamed program "equalWithEvidence"
  let outcome ← runOrThrow "consumed trait predicate evidence" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"consumed trait predicate: incomplete plan {reprStr other}")
  assertTrue (!(plan.specializations.any fun specialized =>
      specialized.declaration == equal.id))
    "superclass helper unexpectedly appeared in the top-level worklist"
  let linked ← linkOrThrow "consumed trait predicate evidence" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "consumed trait predicate: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 9), .word (word 9)] 4096 =
        some (.done (.bool false) [])))
    "Ord.gt did not forward Eq superclass evidence through its method helper"

private def testGenericTraitPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Ord<T> where T: Eq {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
    "}",
    "impl<T> Ord<T> {",
    "  function gt(left: T, right: T) returns (Bool) {",
    "    return left == right;",
    "  }",
    "}",
    "function greaterWithEvidence<T>(left: T, right: T) returns (Bool) where T: Ord {",
    "  return left > right;",
    "}",
    "function entry(left: Word, right: Word) returns (Bool) {",
    "  return greaterWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let outcome ← runOrThrow "generic trait predicate evidence" program
    [monomorphicRequest entry] 2
  let linked ← linkOrThrow "generic trait predicate evidence" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "generic trait predicate: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 9), .word (word 9)] 4096 =
        some (.done (.bool false) [])))
    "generic Ord<T> body did not specialize its trait-header Eq<T> assumption"

private def testImplementationPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
    "}",
    "function equalWithEvidence<T>(left: T, right: T) returns (Bool) where T: Eq {",
    "  return left == right;",
    "}",
    "impl Add<Word> where Word: Eq {",
    "  function add(left: Word, right: Word) returns (Word) {",
    "    return equalWithEvidence(left, right) ? 91 : 92;",
    "  }",
    "}",
    "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return addWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let equal ← signatureNamed program "equalWithEvidence"
  let outcome ← runOrThrow "implementation predicate evidence" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"implementation predicate: incomplete plan {reprStr other}")
  assertTrue (!(plan.specializations.any fun specialized =>
      specialized.declaration == equal.id))
    "implementation-predicate helper unexpectedly appeared in the top-level worklist"
  let linked ← linkOrThrow "implementation predicate evidence" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "implementation predicate: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 9), .word (word 9)] 4096 =
        some (.done (.word (word 92)) [])))
    "Add method did not consume its selected Eq implementation premise"

private def testGenericImplementationPredicateEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait Add<T> where T: Eq {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "impl Eq<Word> {",
    "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
    "}",
    "function equalWithEvidence<T>(left: T, right: T) returns (Bool) where T: Eq {",
    "  return left == right;",
    "}",
    "impl<T> Add<T> where T: Eq {",
    "  function add(left: T, right: T) returns (T) {",
    "    return equalWithEvidence(left, right) ? left : right;",
    "  }",
    "}",
    "function addWithEvidence<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return addWithEvidence(left, right);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let add ← signatureNamed program "addWithEvidence"
  let equal ← signatureNamed program "equalWithEvidence"
  let outcome ← runOrThrow "generic implementation predicate evidence" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"generic implementation predicate: incomplete plan {reprStr other}")
  assertTrue (plan.specializations.any fun specialized =>
      specialized.declaration == add.id)
    "generic Add caller was absent from the top-level specialization plan"
  assertTrue (!(plan.specializations.any fun specialized =>
      specialized.declaration == equal.id))
    "generic implementation helper unexpectedly appeared in the top-level plan"
  let linked ← linkOrThrow "generic implementation predicate evidence" program
    outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "generic implementation predicate: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 91), .word (word 92)] 4096 =
        some (.done (.word (word 92)) [])))
    "generic Add<T> method did not specialize or deduplicate its Eq<T> evidence"

private def testNamedLogicalNotWithEvidence : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Marker<T> {}",
    "impl Marker<Bool> {}",
    "function not<T>(value: T) returns (Bool) where T: Marker {",
    "  return true;",
    "}",
    "function negateWithEvidence<T>(value: T) returns (Bool) where T: Marker {",
    "  return !value;",
    "}",
    "function logicalNotEntry(value: Bool) returns (Bool) {",
    "  return negateWithEvidence(value);",
    "}"
  ])
  let marker ← match program.signatures.traits.filter fun trait =>
      trait.name == "Marker" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"logical !: expected one Marker trait, found {traits.length}")
  let not ← signatureNamed program "not"
  let negate ← signatureNamed program "negateWithEvidence"
  let entry ← signatureNamed program "logicalNotEntry"
  let function ← functionFor program negate
  let input ← match function.typedBody.inputs with
    | [input] => pure input
    | inputs => throw (IO.userError
        s!"logical !: expected one generic input, found {inputs.length}")
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "logical ! did not become a direct call to not")
  let (calleeId, arguments, instantiation) ← match call.form with
    | .call callee arguments (.declaration instantiation) =>
        pure (callee, arguments, instantiation)
    | form => throw (IO.userError
        s!"logical !: selected call changed form: {reprStr form}")
  let calleeNode ← match function.typedBody.lookupExpression? calleeId with
    | some callee => pure callee
    | none => throw (IO.userError
        "logical !: synthetic not callee node was absent")
  let argumentIsInput := match arguments with
    | [argument] =>
        match function.typedBody.lookupExpression? argument with
        | some { form := .reference _ (.local binder), .. } => binder == input.id
        | _ => false
    | _ => false
  let calleeMatches := match calleeNode.form with
    | .reference "not" (.declaration reference) => reference == instantiation
    | _ => false
  let requirement ← match call.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"logical !: expected one call requirement, found {requirements.length}")
  let solved ← match function.solvedRequirements.filter fun row =>
      row.id == requirement with
    | [solved] => pure solved
    | rows => throw (IO.userError
        s!"logical !: expected one solved row, found {rows.length}")
  let operandType := input.scheme.body
  assertTrue (argumentIsInput && calleeMatches && decide (
      call.type = .bool ∧ calleeNode.type = instantiation.type ∧
      instantiation.declaration = not.id ∧
      instantiation.type = .function operandType .bool ∧
      instantiation.parameterSubstitution.map (fun entry => entry.2) =
        [operandType] ∧
      instantiation.predicates = [solved.predicate] ∧
      solved.predicate.trait = marker.id ∧
      solved.predicate.subject = operandType ∧
      solved.predicate.arguments = [] ∧ call.coercions = []) &&
      (solved.evidence matches .assumption _))
    "logical ! lost its selected not call or forwarded generic evidence"

  let outcome ← runOrThrow "logical ! named function" program
    [monomorphicRequest entry] 3
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"logical !: expected a complete plan, found {reprStr other}")
  let expectedPredicate : ProgramPredicate := {
    trait := marker.id
    subject := .bool
    arguments := []
  }
  let specializedNegate := plan.specializations.find? fun specialized =>
    specialized.declaration == negate.id
  let specializedNot := plan.specializations.find? fun specialized =>
    specialized.declaration == not.id
  assertTrue (decide (
      plan.specializations.map (fun specialized => specialized.declaration) =
        [entry.id, negate.id, not.id] ∧
      plan.callEdges.map (fun edge =>
        (edge.caller.declaration, edge.callee.declaration)) =
        [(entry.id, negate.id), (negate.id, not.id)]) &&
      specializedNegate.any fun specialized => decide (
        specialized.key.arguments = [.bool] ∧
        specialized.assumptions = [expectedPredicate]) &&
      specializedNot.any fun specialized => decide (
        specialized.key.arguments = [.bool] ∧
        specialized.assumptions = [expectedPredicate]))
    "logical ! did not retain its ordinary-call worklist edge and evidence"
  let linked ← linkOrThrow "logical ! named function" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError "logical !: linked root was absent")
  assertTrue (decide (linkedEntry.run? [.bool true] 2048 =
      some (.done (.bool true) [])))
    "logical ! did not execute the nonstandard generic not body"

private def testNamedLogicalNotExpectedType : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "function not(value: Word) returns (Word) { return 91; }",
    "function entry(value: Word) returns (Word) { return !value; }"
  ])
  let not ← signatureNamed program "not"
  let entry ← signatureNamed program "entry"
  let function ← functionFor program entry
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "logical ! Word result did not become a direct call")
  let (calleeId, arguments, instantiation) ← match call.form with
    | .call callee arguments (.declaration instantiation) =>
        pure (callee, arguments, instantiation)
    | form => throw (IO.userError
        s!"logical ! Word result: unexpected form {reprStr form}")
  let calleeMatches := match function.typedBody.lookupExpression? calleeId with
    | some { form := .reference "not" (.declaration reference), type, .. } =>
        decide (reference = instantiation ∧ type = .function .word .word)
    | _ => false
  assertTrue (calleeMatches && decide (
      call.type = .word ∧ instantiation.declaration = not.id ∧
      instantiation.type = .function .word .word ∧ arguments.length = 1 ∧
      call.requirements = [] ∧ call.coercions = []))
    "logical ! ignored the selected not function's non-Bool expected type"
  let outcome ← runOrThrow "logical ! expected type" program
    [monomorphicRequest entry] 2
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"logical ! expected type: incomplete plan {reprStr other}")
  assertTrue (decide (
      plan.specializations.map (fun specialized => specialized.declaration) =
        [entry.id, not.id] ∧
      plan.callEdges.map (fun edge => edge.callee.declaration) = [not.id]))
    "logical ! expected type did not produce the selected not edge"
  let linked ← linkOrThrow "logical ! expected type" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "logical ! expected type: linked root was absent")
  assertTrue (decide (linkedEntry.run? [.word (word 7)] 1024 =
      some (.done (.word (word 91)) [])))
    "logical ! did not execute the expected-type-selected not body"

private def testNamedLogicalNotMismatchDoesNotFallback : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [{
      path := "main.solc"
      content := String.intercalate "\n" [
        "function not(value: Word) returns (Bool) { return false; }",
        "function entry(value: Bool) returns (Bool) { return !value; }"
      ]
    }]
    externalLibraries := []
  }
  match checkProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .inference { error := .noMatchingOverload "not" candidates, .. } =>
            candidates.length == 1
        | _ => false)
        "an inapplicable visible not overload lost its selection diagnostic"
  | .ok _ => throw (IO.userError
      "an inapplicable visible not overload silently used builtin fallback")

private def testBuiltinLogicalNotFallback : IO Unit := do
  let program ← checkedProgramOf
    "function entry(value: Bool) returns (Bool) { return !value; }"
  let entry ← signatureNamed program "entry"
  let function ← functionFor program entry
  let unary ← match firstUnaryNode? function.typedBody.nodes with
    | some unary => pure unary
    | none => throw (IO.userError
        "logical ! builtin fallback did not retain a unary node")
  assertTrue ((match unary.form with
      | .unary .logicalNot _ => true
      | _ => false) && unary.type == .bool && unary.requirements.isEmpty &&
      (firstDirectCallNode? function.typedBody.nodes).isNone)
    "logical ! builtin fallback acquired call or evidence metadata"
  let outcome ← runOrThrow "logical ! builtin fallback" program
    [monomorphicRequest entry] 1
  let plan ← match outcome with
    | .complete plan => pure plan
    | other => throw (IO.userError
        s!"logical ! builtin fallback: incomplete plan {reprStr other}")
  assertTrue (decide (
      plan.specializations.map (fun specialized => specialized.declaration) =
        [entry.id] ∧ plan.callEdges = []))
    "logical ! builtin fallback created a named call edge"
  let linked ← linkOrThrow "logical ! builtin fallback" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "logical ! builtin fallback: linked root was absent")
  assertTrue (decide (
      linkedEntry.run? [.bool true] 1024 = some (.done (.bool false) []) ∧
      linkedEntry.run? [.bool false] 1024 = some (.done (.bool true) [])))
    "logical ! builtin fallback changed primitive Bool negation"

private def testNamedOperatorMismatchDoesNotFallback : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [{
      path := "main.solc"
      content := String.intercalate "\n" [
        "function and(left: Word, right: Word) returns (Bool) { return false; }",
        "function entry(left: Bool, right: Bool) returns (Bool) {",
        "  return left && right;",
        "}"
      ]
    }]
    externalLibraries := []
  }
  match checkProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .inference { error := .noMatchingOverload "and" candidates, .. } =>
            candidates.length == 1
        | _ => false)
        "an inapplicable visible and overload lost its selection diagnostic"
  | .ok _ => throw (IO.userError
      "an inapplicable visible and overload silently used builtin fallback")

private def testHeterogeneousNamedOperator : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "function lt(left: Word, right: Bool) returns (Bool) { return right; }",
    "function entry(left: Word, right: Bool) returns (Bool) {",
    "  return left < right;",
    "}"
  ])
  let lt ← signatureNamed program "lt"
  let entry ← signatureNamed program "entry"
  let function ← functionFor program entry
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "heterogeneous <: named operator did not become a direct call")
  let selected := match call.form with
    | .call _ arguments (.declaration instantiation) =>
        decide (arguments.length = 2 ∧ instantiation.declaration = lt.id ∧
          instantiation.type = .function (.product .word .bool) .bool)
    | _ => false
  assertTrue (selected && call.requirements.isEmpty && call.coercions.isEmpty)
    "heterogeneous <: operands were unified before ordinary overload selection"
  let outcome ← runOrThrow "heterogeneous named operator" program
    [monomorphicRequest entry] 2
  let linked ← linkOrThrow "heterogeneous named operator" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "heterogeneous named operator: linked root was absent")
  assertTrue (decide (
      linkedEntry.run? [.word (word 7), .bool true] 1024 =
        some (.done (.bool true) []) ∧
      linkedEntry.run? [.word (word 7), .bool false] 1024 =
        some (.done (.bool false) [])))
    "heterogeneous named operator did not execute the selected function"

private def testNamedOperatorResultCoercionChain : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Ord<T> {",
    "  function gt(left: T, right: T) returns (Bool);",
    "}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To);",
    "}",
    "impl Ord<Word> {",
    "  function gt(left: Word, right: Word) returns (Bool) { return true; }",
    "}",
    "impl Coerce<Word, Bool> {",
    "  function coerce(value: Word) returns (Bool) { return false; }",
    "}",
    "impl Coerce<Bool, Word> {",
    "  function coerce(value: Bool) returns (Word) {",
    "    return value ? 91 : 92;",
    "  }",
    "}",
    "function lt<T>(left: T, right: T) returns (Word) where T: Ord {",
    "  return 5;",
    "}",
    "function entry(left: Word, right: Word) returns (Word) {",
    "  return left < right;",
    "}"
  ])
  let lt ← signatureNamed program "lt"
  let entry ← signatureNamed program "entry"
  let function ← functionFor program entry
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "named operator coercion chain: direct call was absent")
  let instantiation ← match call.form with
    | .call _ _ (.declaration instantiation) => pure instantiation
    | form => throw (IO.userError
        s!"named operator coercion chain: unexpected form {reprStr form}")
  let solved := call.requirements.filterMap fun requirement =>
    function.solvedRequirements.find? fun row => row.id == requirement
  let coercionRequirements := call.coercions.map (fun step => step.requirement)
  let endpoints := call.coercions.map fun step => (step.source, step.target)
  let signatureIsMiddle := match solved, instantiation.predicates with
    | [_, middle, _], [expected] => middle.predicate == expected
    | _, _ => false
  assertTrue (signatureIsMiddle && decide (
      call.type = .word ∧ instantiation.declaration = lt.id ∧
      instantiation.type = .function (.product .word .word) .word ∧
      call.requirements.map (fun requirement => requirement.index) = [0, 1, 2] ∧
      coercionRequirements.map (fun requirement => requirement.index) = [0, 2] ∧
      endpoints = [(.word, .bool), (.bool, .word)]) &&
      solved.all fun row => row.evidence matches .implementation _)
    "named operator lost result/signature/outer coercion requirement order"
  let outcome ← runOrThrow "named operator coercion chain" program
    [monomorphicRequest entry] 2
  let linked ← linkOrThrow "named operator coercion chain" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError
        "named operator coercion chain: linked root was absent")
  assertTrue (decide (linkedEntry.run?
      [.word (word 1), .word (word 2)] 4096 =
        some (.done (.word (word 92)) [])))
    "named operator did not execute both result coercion method bodies"

private structure BuiltinOperatorCase where
  entryName : String
  operator : Syntax.BinaryOp
  inputs : List Core.Value
  expected : Bool

private def testBuiltinOperatorFallback : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "function builtinNotEqual(left: Word, right: Word) returns (Bool) {",
    "  return left != right;",
    "}",
    "function builtinLess(left: Word, right: Word) returns (Bool) {",
    "  return left < right;",
    "}",
    "function builtinLessEqual(left: Word, right: Word) returns (Bool) {",
    "  return left <= right;",
    "}",
    "function builtinGreaterEqual(left: Word, right: Word) returns (Bool) {",
    "  return left >= right;",
    "}",
    "function builtinAnd(left: Bool, right: Bool) returns (Bool) {",
    "  return left && right;",
    "}",
    "function builtinOr(left: Bool, right: Bool) returns (Bool) {",
    "  return left || right;",
    "}",
    "function builtinGreater(left: Word, right: Word) returns (Bool) {",
    "  return left > right;",
    "}"
  ])
  let cases : List BuiltinOperatorCase := [
    {
      entryName := "builtinNotEqual"
      operator := .notEqual
      inputs := [.word (word 7), .word (word 7)]
      expected := false
    },
    {
      entryName := "builtinLess"
      operator := .less
      inputs := [.word (word 1), .word (word 2)]
      expected := true
    },
    {
      entryName := "builtinLessEqual"
      operator := .lessEqual
      inputs := [.word (word 1), .word (word 2)]
      expected := true
    },
    {
      entryName := "builtinGreaterEqual"
      operator := .greaterEqual
      inputs := [.word (word 1), .word (word 2)]
      expected := false
    },
    {
      entryName := "builtinAnd"
      operator := .logicalAnd
      inputs := [.bool true, .bool true]
      expected := true
    },
    {
      entryName := "builtinOr"
      operator := .logicalOr
      inputs := [.bool false, .bool true]
      expected := true
    },
    {
      entryName := "builtinGreater"
      operator := .greater
      inputs := [.word (word 1), .word (word 2)]
      expected := false
    }
  ]
  for case in cases do
    let entry ← signatureNamed program case.entryName
    let function ← functionFor program entry
    let binary ← match firstBinaryNode? function.typedBody.nodes with
      | some binary => pure binary
      | none => throw (IO.userError
          s!"{case.entryName}: builtin fallback did not retain a binary node")
    assertTrue ((match binary.form with
        | .binary _ operator _ => operator == case.operator
        | _ => false) && binary.requirements.isEmpty &&
        (firstDirectCallNode? function.typedBody.nodes).isNone)
      s!"{case.entryName}: builtin fallback acquired call/evidence metadata"
    let outcome ← runOrThrow s!"{case.entryName} builtin fallback" program
      [monomorphicRequest entry] 1
    let plan ← match outcome with
      | .complete plan => pure plan
      | other => throw (IO.userError
          s!"{case.entryName}: expected a complete plan, found {reprStr other}")
    assertTrue (decide (plan.specializations.map
        (fun specialized => specialized.declaration) = [entry.id] ∧
        plan.callEdges = []))
      s!"{case.entryName}: builtin fallback created a named call edge"
    let linked ← linkOrThrow s!"{case.entryName} builtin fallback"
      program outcome
    let key : SourceSpecialization.SpecializationKey := {
      declaration := entry.id
      arguments := []
    }
    let linkedEntry ← match linked.findEntry? key with
      | some linkedEntry => pure linkedEntry
      | none => throw (IO.userError
          s!"{case.entryName}: linked builtin root was absent")
    assertTrue (decide (linkedEntry.run? case.inputs 1024 =
        some (.done (.bool case.expected) [])))
      s!"{case.entryName}: builtin compatibility behavior changed"

private def testMultiStepRuntimeCoercion : IO Unit := do
  let program ← checkedProgramOf (String.intercalate "\n" [
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To);",
    "}",
    "impl Coerce<Bool, Word> {",
    "  function coerce(value: Bool) returns (Word) {",
    "    return value ? 41 : 7;",
    "  }",
    "}",
    "impl Coerce<Word, (Bool, Bool)> {",
    "  function coerce(value: Word) returns ((Bool, Bool)) {",
    "    return (value == 41, value == 7);",
    "  }",
    "}",
    "function acceptPair(value: (Bool, Bool)) returns ((Bool, Bool)) {",
    "  return value;",
    "}",
    "function entry(value: Bool) returns ((Bool, Bool)) {",
    "  return acceptPair(value);",
    "}"
  ])
  let entry ← signatureNamed program "entry"
  let outcome ← runOrThrow "multi-step coercion" program
    [monomorphicRequest entry] 2
  let linked ← linkOrThrow "multi-step coercion" program outcome
  let key : SourceSpecialization.SpecializationKey := {
    declaration := entry.id
    arguments := []
  }
  let linkedEntry ← match linked.findEntry? key with
    | some linkedEntry => pure linkedEntry
    | none => throw (IO.userError "multi-step coercion: linked root was absent")
  assertTrue (decide (linkedEntry.run? [.bool true] 4096 =
        some (.done (.pair (.bool true) (.bool false)) []) ∧
      linkedEntry.run? [.bool false] 4096 =
        some (.done (.pair (.bool false) (.bool true)) [])))
    "multi-step Coerce evidence did not compose both selected method bodies"

private def testMalformedRequirementMetadata
    (program : CheckedProgram) : IO Unit := do
  let constrained ← signatureNamed program "constrained"
  let function ← functionFor program constrained
  let call ← match firstDirectCallNode? function.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "constrained: direct call requirement owner was absent")
  let solved ← match function.solvedRequirements with
    | [solved] => pure solved
    | requirements => throw (IO.userError
        s!"constrained: expected one solved requirement, found {requirements.length}")

  let wrongId : RequirementId := ⟨solved.id.index + 100⟩
  let wrongIdFunction : CheckedFunction := {
    function with
    solvedRequirements := [{ solved with id := wrongId }]
  }
  let wrongIdProgram := replaceFunction program wrongIdFunction
  let wrongIdOutcome ← runOrThrow "malformed requirement id" wrongIdProgram
    [monomorphicRequest constrained] 2
  match SourceCoreDirectLinking.link wrongIdProgram wrongIdOutcome with
  | .error (.missingSolvedRequirement key occurrence requirement) =>
      assertTrue (decide (key.declaration = constrained.id ∧
          occurrence = call.id ∧ requirement = solved.id))
        "malformed requirement-ID rejection lost its caller or occurrence"
  | result => throw (IO.userError
      s!"a call requirement with no solved row was accepted: {reprStr result}")

  let wrongPredicate : ProgramPredicate := {
    solved.predicate with subject := .bool
  }
  let wrongEvidence : PredicateEvidence := match solved.evidence with
    | .assumption _ => .assumption wrongPredicate
    | .implementation (.byImpl _ implementation premises) =>
        .implementation (.byImpl wrongPredicate implementation premises)
  let wrongPredicateFunction : CheckedFunction := {
    function with
    solvedRequirements := [{
      solved with predicate := wrongPredicate, evidence := wrongEvidence
    }]
  }
  let wrongPredicateProgram := replaceFunction program wrongPredicateFunction
  let wrongPredicateOutcome ← runOrThrow "malformed requirement predicate"
    wrongPredicateProgram [monomorphicRequest constrained] 2
  match SourceCoreDirectLinking.link wrongPredicateProgram
      wrongPredicateOutcome with
  | .error (.callRequirementPredicateMismatch key occurrence requirement
      expected actual) =>
      assertTrue (decide (key.declaration = constrained.id ∧
          occurrence = call.id ∧ requirement = solved.id ∧
          expected = solved.predicate ∧ actual = wrongPredicate))
        "malformed requirement-predicate rejection lost exact metadata"
  | result => throw (IO.userError
      s!"a mismatched solved predicate was accepted: {reprStr result}")

  let both ← signatureNamed program "bothConstrained"
  let bothFunction ← functionFor program both
  let bothCall ← match firstDirectCallNode? bothFunction.typedBody.nodes with
    | some call => pure call
    | none => throw (IO.userError
        "bothConstrained: direct call requirement owner was absent")
  let (first, second) ← match bothFunction.solvedRequirements with
    | [first, second] => pure (first, second)
    | requirements => throw (IO.userError
        s!"bothConstrained: expected two solved requirements, found {requirements.length}")
  let reversedRequirements ← match bothCall.requirements with
    | [first, second] => pure [second, first]
    | requirements => throw (IO.userError
        s!"bothConstrained: expected two call requirements, found {requirements.length}")
  let wrongOrderFunction : CheckedFunction := {
    bothFunction with
    typedBody := {
      bothFunction.typedBody with
      nodes := replaceExpressionRequirements bothFunction.typedBody.nodes
        bothCall.id reversedRequirements
    }
  }
  let wrongOrderProgram := replaceFunction program wrongOrderFunction
  let wrongOrderOutcome ← runOrThrow "malformed requirement order"
    wrongOrderProgram [monomorphicRequest both] 2
  match SourceCoreDirectLinking.link wrongOrderProgram wrongOrderOutcome with
  | .error (.callRequirementPredicateMismatch key occurrence requirement
      expected actual) =>
      assertTrue (decide (key.declaration = both.id ∧
          occurrence = bothCall.id ∧ requirement = second.id ∧
          expected = first.predicate ∧ actual = second.predicate))
        "malformed requirement-order rejection lost positional evidence"
  | result => throw (IO.userError
      s!"reordered call requirements were accepted: {reprStr result}")

private def testMalformedCoercionEvidence
    (program : CheckedProgram) : IO Unit := do
  let coercionCall ← signatureNamed program "coercionCall"
  let function ← functionFor program coercionCall
  let node ← match firstCoercedNode? function.typedBody.nodes with
    | some node => pure node
    | none => throw (IO.userError
        "coercionCall: coercion-bearing argument node was absent")
  let step ← match node.coercions with
    | [step] => pure step
    | coercions => throw (IO.userError
        s!"coercionCall: expected one coercion step, found {coercions.length}")
  let solved ← match function.solvedRequirements.filter fun solved =>
      solved.id == step.requirement with
    | [solved] => pure solved
    | requirements => throw (IO.userError
        s!"coercionCall: expected one coercion solved row, found {requirements.length}")
  let evidenceWithGoal := fun goal => match solved.evidence with
    | .assumption _ => PredicateEvidence.assumption goal
    | .implementation (.byImpl _ implementation premises) =>
        .implementation (.byImpl goal implementation premises)
  let wrongPredicate : ProgramPredicate := {
    solved.predicate with subject := .word
  }
  let wrongGoalFunction : CheckedFunction := {
    function with
    solvedRequirements := function.solvedRequirements.map fun requirement =>
      if requirement.id == solved.id then
        { requirement with evidence := evidenceWithGoal wrongPredicate }
      else
        requirement
  }
  let wrongGoalProgram := replaceFunction program wrongGoalFunction
  match SourceSpecializationWorklist.run wrongGoalProgram
      [monomorphicRequest coercionCall] 2 with
  | .error (.specialization declaration
      (.evidenceGoalMismatch requirement expected actual)) =>
      assertTrue (decide (declaration = coercionCall.id ∧
          requirement = solved.id ∧ expected = solved.predicate ∧
          actual = wrongPredicate))
        "malformed coercion evidence goal lost its exact specialization metadata"
  | result => throw (IO.userError
      s!"a coercion evidence-goal mismatch reached linking: {reprStr result}")

  let wrongPredicateFunction : CheckedFunction := {
    function with
    solvedRequirements := function.solvedRequirements.map fun requirement =>
      if requirement.id == solved.id then
        { requirement with
          predicate := wrongPredicate
          evidence := evidenceWithGoal wrongPredicate
        }
      else
        requirement
  }
  let wrongPredicateProgram := replaceFunction program wrongPredicateFunction
  let wrongPredicateOutcome ← runOrThrow "malformed coercion predicate"
    wrongPredicateProgram [monomorphicRequest coercionCall] 2
  match SourceCoreDirectLinking.link wrongPredicateProgram
      wrongPredicateOutcome with
  | .error (.runtimeCoercionPredicateMismatch key occurrence requirement
      expectedSource expectedTarget actual) =>
      assertTrue (decide (key.declaration = coercionCall.id ∧
          occurrence = node.id ∧ requirement = solved.id ∧
          expectedSource = step.source ∧ expectedTarget = step.target ∧
          actual = wrongPredicate))
        "malformed coercion predicate lost its path or solved metadata"
  | result => throw (IO.userError
      s!"a coercion predicate/path mismatch was accepted: {reprStr result}")

/-- Exercise complete acyclic generic linking, capture-free argument staging,
runtime input validation, finite-budget and recursion boundaries, proof-only
trait-evidence forwarding, strict and named operator authority, Ord dispatch,
builtin operator compatibility, runtime evidence/coercion gates, malformed
requirement metadata, the legacy call-free entry point, and defensive plan
reconstruction. -/
def testSourceCoreDirectLinking : IO Unit := do
  let program ← checkedProgram
  testExecutionAndPlan program
  testBudgetExhaustion program
  testCaptureAvoidance program
  testCycle program
  testProofOnlyEvidence program
  testRuntimeEvidenceBoundaries program
  testImplementationMethodDirectCall
  testMultiMethodImplementationSelection
  testImplementationMethodCallCycle
  testStrictRuntimeBinaryEvidence
  testRuntimeBitNotEvidence
  testNamedOperatorFunctionsAndOrd
  testTraitPredicateIsStaticMethodAssumption
  testMissingConsumedTraitPredicateEvidence
  testConsumedTraitPredicateEvidence
  testGenericTraitPredicateEvidence
  testImplementationPredicateEvidence
  testGenericImplementationPredicateEvidence
  testNamedLogicalNotWithEvidence
  testNamedLogicalNotExpectedType
  testNamedLogicalNotMismatchDoesNotFallback
  testBuiltinLogicalNotFallback
  testNamedOperatorMismatchDoesNotFallback
  testHeterogeneousNamedOperator
  testNamedOperatorResultCoercionChain
  testBuiltinOperatorFallback
  testMultiStepRuntimeCoercion
  testMalformedRequirementMetadata program
  testMalformedCoercionEvidence program

end Tests.SourceCoreDirectLinking
