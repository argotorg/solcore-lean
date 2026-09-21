import Solcore

/-! Adversarial regressions for closed staged-conditional metadata. -/

set_option autoImplicit false

namespace Tests.SourceStagedConditionalsTamper

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

private def checkedFunction (content : String) : IO CheckedFunction := do
  let program ← match checkProgram (workspace content) with
    | .ok program => pure program
    | .error errors => throw (IO.userError
        s!"staged-conditional tamper fixture failed checking: {reprStr errors}")
  match program.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"staged-conditional fixture produced {functions.length} functions")

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError "tamper fixture lost its valued return")
  | _ => throw (IO.userError "tamper fixture lost its unique root")

private def unaryBuiltinArgument (function : CheckedFunction)
    (id : ExpressionId) (expected : BuiltinFunctionId) : IO ExpressionId :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call _ [argument] (.builtinFunction actual) =>
          if actual == expected then pure argument
          else throw (IO.userError
            s!"expected `{expected.spelling}`, found `{actual.spelling}`")
      | _ => throw (IO.userError
          s!"expected unary builtin `{expected.spelling}`: {reprStr node}")
  | none => throw (IO.userError "unary builtin node was absent")

private def binaryBuiltin (function : CheckedFunction) (id : ExpressionId)
    (expected : BuiltinFunctionId) :
    IO (ExpressionId × ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee [left, right] (.builtinFunction actual) =>
          if actual == expected then pure (callee, left, right)
          else throw (IO.userError
            s!"expected `{expected.spelling}`, found `{actual.spelling}`")
      | _ => throw (IO.userError
          s!"expected binary builtin `{expected.spelling}`: {reprStr node}")
  | none => throw (IO.userError "binary builtin node was absent")

private def conditional (function : CheckedFunction) (id : ExpressionId) :
    IO (ExpressionId × ExpressionId × ExpressionId) :=
  match function.typedBody.lookupExpression? id with
  | some { form := .conditional condition thenBranch elseBranch, .. } =>
      pure (condition, thenBranch, elseBranch)
  | node => throw (IO.userError
      s!"conditional node changed shape: {reprStr node}")

private def literalResolution (function : CheckedFunction)
    (id : ExpressionId) : IO IntegerLiteralResolution :=
  match function.typedBody.lookupExpression? id with
  | some { form := .integerLiteral _ resolution, .. } => pure resolution
  | node => throw (IO.userError
      s!"literal node changed shape: {reprStr node}")

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
  function with typedBody := changeExpression function.typedBody id change
}

private def expectElaborationErrorAt (label : String)
    (function : CheckedFunction) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError
      s!"{label}: malformed conditional reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def expectIntegerErrorAt (label : String)
    (function : CheckedFunction) (id : ExpressionId)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Integer error {reprStr error}"

private def expectWordErrorAt (label : String) (function : CheckedFunction)
    (id : ExpressionId) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedWord
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed Word conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Word error {reprStr error}"

private def expectBoolErrorAt (label : String) (function : CheckedFunction)
    (id : ExpressionId) (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedBool
      function.solvedRequirements function.typedBody id with
  | .ok value => throw (IO.userError
      s!"{label}: malformed Bool conditional evaluated to {reprStr value}")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong staged-Bool error {reprStr error}"

private structure IntegerFixture where
  function : CheckedFunction
  root : ExpressionId
  conditional : ExpressionId
  guard : ExpressionId
  guardCallee : ExpressionId
  guardLeft : ExpressionId
  guardRight : ExpressionId
  thenBranch : ExpressionId
  thenLeft : ExpressionId
  thenRight : ExpressionId
  elseBranch : ExpressionId
  elseCallee : ExpressionId
  elseLeft : ExpressionId
  elseRight : ExpressionId
  elseLeftResolution : IntegerLiteralResolution

private def integerFixture : IO IntegerFixture := do
  let function ← checkedFunction
    "function tamper() returns (Word) { return wordFromInteger(integerLt(1, 2) ? integerSub(10, 3) : integerAdd(20, 4)); }"
  let root ← returnedExpression function
  let conditionalId ← unaryBuiltinArgument function root .wordFromInteger
  let (guard, thenBranch, elseBranch) ← conditional function conditionalId
  let (guardCallee, guardLeft, guardRight) ←
    binaryBuiltin function guard .integerLt
  let (_, thenLeft, thenRight) ←
    binaryBuiltin function thenBranch .integerSub
  let (elseCallee, elseLeft, elseRight) ←
    binaryBuiltin function elseBranch .integerAdd
  let elseLeftResolution ← literalResolution function elseLeft
  pure {
    function
    root
    conditional := conditionalId
    guard
    guardCallee
    guardLeft
    guardRight
    thenBranch
    thenLeft
    thenRight
    elseBranch
    elseCallee
    elseLeft
    elseRight
    elseLeftResolution
  }

private def intCoercion (fixture : IntegerFixture) : CoercionStep := {
  requirement := fixture.elseLeftResolution.requirement
  source := Ty.integer
  target := Ty.word
}

private def testIntegerBaselineAndParentMetadata
    (fixture : IntegerFixture) : IO Unit := do
  let expected := fixture.function.solvedRequirements.map (·.id)
  match SourceCoreElaboration.evaluateStagedInteger
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (7 : Int) ∧
          evaluated.consumedRequirements = expected ∧
          expected.length = 6))
        "integer conditional baseline lost all-branch requirement order"
  | .error error => throw (IO.userError
      s!"integer conditional baseline failed: {reprStr error}")
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.conditional.occurrence
  let requirement := fixture.elseLeftResolution.requirement
  let wrongType := withExpression fixture.function fixture.conditional fun node =>
    { node with type := Ty.word }
  expectIntegerErrorAt "conditional result type" wrongType fixture.conditional
    site fun reason => reason == .stagedIntegerTypeMismatch Ty.integer Ty.word
  let requirements := withExpression fixture.function fixture.conditional
    fun node => { node with requirements := [requirement] }
  expectIntegerErrorAt "conditional own requirements" requirements
    fixture.conditional site fun reason =>
      reason == .requirementsPresent [requirement]
  let coercions := withExpression fixture.function fixture.conditional
    fun node => { node with coercions := [intCoercion fixture] }
  expectIntegerErrorAt "conditional own coercions" coercions
    fixture.conditional site fun reason =>
      reason == .coercionsPresent [intCoercion fixture]

private def testIntegerChildrenAndUnselectedValidation
    (fixture : IntegerFixture) : IO Unit := do
  let guardSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.guard.occurrence
  let thenLiteralSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.thenLeft.occurrence
  let wrongGuardEdge := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional _ thenBranch elseBranch =>
          .conditional fixture.thenLeft thenBranch elseBranch
      | form => form }
  expectIntegerErrorAt "conditional guard type" wrongGuardEdge
    fixture.conditional thenLiteralSite fun reason =>
      reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let wrongBranchEdge := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.guard elseBranch
      | form => form }
  expectIntegerErrorAt "conditional branch type" wrongBranchEdge
    fixture.conditional guardSite fun reason =>
      reason == .stagedIntegerTypeMismatch Ty.integer Ty.bool

  let requirement := fixture.elseLeftResolution.requirement
  let expectedPredicate := fixture.elseLeftResolution.predicate
  let forgedEvidence : CheckedFunction := {
    fixture.function with
    solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
      if solved.id = requirement then {
        solved with evidence := (.implementation
          (.byImpl expectedPredicate (.builtin .intWord) []))
      } else solved
  }
  expectIntegerErrorAt "unselected branch evidence" forgedEvidence
    fixture.conditional (.occurrence fixture.elseLeft.occurrence) fun reason =>
      reason == .integerLiteralImplementationMismatch requirement
        (.builtin .intInteger) (.builtin .intWord)

  let forgedSpelling := withExpression fixture.function fixture.elseCallee
    fun node => { node with form := match node.form with
      | .reference _ resolution => .reference "forgedIntegerAdd" resolution
      | form => form }
  expectIntegerErrorAt "unselected branch builtin spelling" forgedSpelling
    fixture.conditional (.occurrence fixture.elseCallee.occurrence) fun reason =>
      reason == .builtinFunctionCalleeSpellingMismatch .integerAdd
        BuiltinFunctionId.integerAdd.spelling "forgedIntegerAdd"

  let sharedBranch := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition thenBranch _ =>
          .conditional condition thenBranch thenBranch
      | form => form }
  let thenResolution ← literalResolution fixture.function fixture.thenLeft
  expectElaborationErrorAt "shared conditional branch" sharedBranch
    (.declaration fixture.function.declaration) fun reason =>
      reason == .duplicateConsumedRequirement thenResolution.requirement

private def testIntegerAndConditionCycles (fixture : IntegerFixture) : IO Unit := do
  let conditionCycle := withExpression fixture.function fixture.guard fun node =>
    { node with form := .group fixture.guard, requirements := [] }
  expectIntegerErrorAt "conditional guard cycle" conditionCycle
    fixture.conditional (.occurrence fixture.guard.occurrence) fun reason =>
      reason == .stagedBoolDepthLimit
  let branchCycle := withExpression fixture.function fixture.conditional
    fun node => { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedInteger
      branchCycle.solvedRequirements branchCycle.typedBody
      fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedIntegerDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "conditional branch cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"conditional branch cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"conditional branch cycle produced the wrong result: {reprStr result}")

private structure BoolFixture where
  function : CheckedFunction
  conditional : ExpressionId
  condition : ExpressionId
  thenBranch : ExpressionId
  elseBranch : ExpressionId
  requirement : RequirementId

private def boolFixture : IO BoolFixture := do
  let function ← checkedFunction
    "function bools() returns (Word) { return wordFromInteger((true ? false : true) ? 1 : 2); }"
  let root ← returnedExpression function
  let integerConditional ← unaryBuiltinArgument function root .wordFromInteger
  let (boolConditionalGroup, integerThen, _) ←
    conditional function integerConditional
  let boolConditional ←
    match function.typedBody.lookupExpression? boolConditionalGroup with
    | some { form := .group inner, .. } => pure inner
    | _ => pure boolConditionalGroup
  let (condition, thenBranch, elseBranch) ←
    conditional function boolConditional
  let resolution ← literalResolution function integerThen
  pure {
    function
    conditional := boolConditional
    condition
    thenBranch
    elseBranch
    requirement := resolution.requirement
  }

private def testBoolMetadataSpellingAndCycle (fixture : BoolFixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedBool
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = false ∧
          evaluated.consumedRequirements = []))
        "Bool conditional baseline changed"
  | .error error => throw (IO.userError
      s!"Bool conditional baseline failed: {reprStr error}")
  let site := SourceCoreElaboration.ErrorSite.occurrence
    fixture.conditional.occurrence
  let coercion : CoercionStep := {
    requirement := fixture.requirement
    source := Ty.bool
    target := Ty.integer
  }
  let wrongType := withExpression fixture.function fixture.conditional fun node =>
    { node with type := Ty.integer }
  expectBoolErrorAt "Bool conditional type" wrongType fixture.conditional site
    fun reason => reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let requirements := withExpression fixture.function fixture.conditional
    fun node => { node with requirements := [fixture.requirement] }
  expectBoolErrorAt "Bool conditional requirements" requirements
    fixture.conditional site fun reason =>
      reason == .requirementsPresent [fixture.requirement]
  let coercions := withExpression fixture.function fixture.conditional
    fun node => { node with coercions := [coercion] }
  expectBoolErrorAt "Bool conditional coercions" coercions fixture.conditional
    site fun reason => reason == .coercionsPresent [coercion]
  let referenceSite := SourceCoreElaboration.ErrorSite.occurrence
    fixture.elseBranch.occurrence
  let referenceType := withExpression fixture.function fixture.elseBranch
    fun node => { node with type := Ty.integer }
  expectBoolErrorAt "builtin Bool reference type" referenceType
    fixture.conditional referenceSite fun reason =>
      reason == .stagedBoolTypeMismatch Ty.bool Ty.integer
  let referenceRequirements :=
    withExpression fixture.function fixture.elseBranch fun node =>
      { node with requirements := [fixture.requirement] }
  expectBoolErrorAt "builtin Bool reference requirements"
    referenceRequirements fixture.conditional referenceSite fun reason =>
      reason == .requirementsPresent [fixture.requirement]
  let referenceCoercions :=
    withExpression fixture.function fixture.elseBranch fun node =>
      { node with coercions := [coercion] }
  expectBoolErrorAt "builtin Bool reference coercions" referenceCoercions
    fixture.conditional referenceSite fun reason =>
      reason == .coercionsPresent [coercion]
  let spelling := withExpression fixture.function fixture.thenBranch fun node =>
    { node with form := match node.form with
      | .reference _ resolution => .reference "forgedFalse" resolution
      | form => form }
  expectBoolErrorAt "builtin Bool spelling" spelling fixture.conditional
    (.occurrence fixture.thenBranch.occurrence) fun reason =>
      reason == .builtinBooleanSpellingMismatch false "false" "forgedFalse"
  let cycle := withExpression fixture.function fixture.conditional fun node =>
    { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedBool cycle.solvedRequirements
      cycle.typedBody fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedBoolDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "Bool conditional cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"Bool conditional cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"Bool conditional cycle produced the wrong result: {reprStr result}")

private structure WordFixture where
  function : CheckedFunction
  conditional : ExpressionId
  condition : ExpressionId
  thenBranch : ExpressionId

private def wordFixture : IO WordFixture := do
  let function ← checkedFunction
    "function words() returns (Word) { return wordFromInteger(wordToInteger(true ? 1 : 2)); }"
  let root ← returnedExpression function
  let conversion ← unaryBuiltinArgument function root .wordFromInteger
  let wordConditional ← unaryBuiltinArgument function conversion .wordToInteger
  let (condition, thenBranch, _) ← conditional function wordConditional
  pure { function, conditional := wordConditional, condition, thenBranch }

private def testWordCycle (fixture : WordFixture) : IO Unit := do
  match SourceCoreElaboration.evaluateStagedWord
      fixture.function.solvedRequirements fixture.function.typedBody
      fixture.conditional with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo 1 ∧
          evaluated.consumedRequirements =
            fixture.function.solvedRequirements.map (·.id)))
        "Word conditional baseline changed"
  | .error error => throw (IO.userError
      s!"Word conditional baseline failed: {reprStr error}")
  let cycle := withExpression fixture.function fixture.conditional fun node =>
    { node with form := match node.form with
      | .conditional condition _ elseBranch =>
          .conditional condition fixture.conditional elseBranch
      | form => form }
  match SourceCoreElaboration.evaluateStagedWord cycle.solvedRequirements
      cycle.typedBody fixture.conditional with
  | .error error =>
      match error.site, error.reason with
      | .occurrence occurrence, .stagedBoolDepthLimit =>
          assertTrue (occurrence.owner == fixture.conditional.occurrence.owner)
            "Word conditional cycle escaped its declaration"
      | _, _ => throw (IO.userError
          s!"Word conditional cycle produced the wrong error: {reprStr error}")
  | result => throw (IO.userError
      s!"Word conditional cycle produced the wrong result: {reprStr result}")

/-- Reject malformed selected and unselected conditional metadata before Core. -/
def testSourceStagedConditionalsTamper : IO Unit := do
  let integer ← integerFixture
  testIntegerBaselineAndParentMetadata integer
  testIntegerChildrenAndUnselectedValidation integer
  testIntegerAndConditionCycles integer
  let bool ← boolFixture
  testBoolMetadataSpellingAndCycle bool
  let word ← wordFixture
  testWordCycle word
  IO.println "staged conditional tamper checks GREEN"

end Tests.SourceStagedConditionalsTamper
