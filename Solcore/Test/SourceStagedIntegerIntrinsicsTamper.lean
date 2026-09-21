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
