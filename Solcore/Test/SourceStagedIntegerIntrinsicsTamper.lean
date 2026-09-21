import Solcore

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

/-- Reject forged builtin identities and staged literal evidence before Core. -/
def testSourceStagedIntegerIntrinsicsTamper : IO Unit := do
  let checked ← fixture
  testCheckedBaseline checked
  testOuterCallContract checked
  testInnerCallContract checked
  testLiteralCarrier checked
  testLiteralEvidence checked
  testCyclesAndRequirementAccounting checked
  IO.println "staged integer intrinsic tamper checks GREEN"

end Tests.SourceStagedIntegerIntrinsicsTamper
