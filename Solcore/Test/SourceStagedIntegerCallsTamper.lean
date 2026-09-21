import Solcore

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
