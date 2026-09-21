import Solcore

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
