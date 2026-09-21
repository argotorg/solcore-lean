import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Machine

/-! Adversarial regressions for the occurrence-addressed typed match carrier.
Every malformed value below is obtained by changing one checked match fixture,
so Source Core must reject stale or forged metadata rather than trusting it. -/

set_option autoImplicit false

namespace Tests.SourcePatternMatchingTamper

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedFunction : IO CheckedFunction := do
  let checked ← match checkProgram (workspace (String.intercalate "\n" [
      "function choose(tag: Word, zero: Word, other: Word) returns (Word) {",
      "  match (tag) {",
      "    case 0 { return zero; }",
      "    case _ { return other; }",
      "  }",
      "}"
    ])) with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"typed-match fixture failed checking: {reprStr errors}")
  match checked.functions with
  | [function] => pure function
  | functions => throw (IO.userError
      s!"typed-match fixture produced {functions.length} functions")

private structure Fixture where
  function : CheckedFunction
  statement : StatementId
  resolution : MatchResolution
  literalCase : TypedMatchCase
  wildcardCase : TypedMatchCase
  literalSource : Syntax.CoreLiteralValue
  literalResolution : IntegerLiteralResolution

private def fixture : IO Fixture := do
  let function ← checkedFunction
  let (statement, resolution) ← match function.typedBody.roots with
    | [.statement statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .matchWith resolution, .. } =>
            pure (statement, resolution)
        | _ => throw (IO.userError
            "typed-match fixture lost its match statement")
    | _ => throw (IO.userError
        "typed-match fixture does not have one statement root")
  let (literalCase, wildcardCase) ← match resolution.cases with
    | [literalCase, wildcardCase] => pure (literalCase, wildcardCase)
    | cases => throw (IO.userError
        s!"typed-match fixture retained {cases.length} explicit cases")
  let (literalSource, literalResolution) ←
      match literalCase.pattern.resolution with
    | .integerLiteral source resolution => pure (source, resolution)
    | _ => throw (IO.userError
        "typed-match fixture lost its integer pattern resolution")
  unless wildcardCase.pattern.resolution == .wildcard do
    throw (IO.userError "typed-match fixture lost its wildcard resolution")
  unless literalCase.pattern.requirements ==
      [literalResolution.requirement] &&
      wildcardCase.pattern.requirements.isEmpty &&
      resolution.requirements == [literalResolution.requirement] do
    throw (IO.userError
      "typed-match fixture lost exact pattern requirement ownership")
  pure {
    function
    statement
    resolution
    literalCase
    wildcardCase
    literalSource
    literalResolution
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

private def changeExpression (source : TypedSource) (id : ExpressionId)
    (change : ExpressionNode → ExpressionNode) : TypedSource := {
  source with
  nodes := source.nodes.map fun
    | .expression node =>
        if node.id = id then .expression { change node with id }
        else .expression node
    | .statement node => .statement node
}

private def withResolution (fixture : Fixture)
    (resolution : MatchResolution) : CheckedFunction := {
  fixture.function with
  typedBody := changeStatement fixture.function.typedBody fixture.statement
    fun node => { node with form := .matchWith resolution }
}

private def withCases (fixture : Fixture)
    (literalCase : TypedMatchCase := fixture.literalCase)
    (wildcardCase : TypedMatchCase := fixture.wildcardCase)
    (requirements : List RequirementId := fixture.resolution.requirements) :
    CheckedFunction :=
  withResolution fixture {
    fixture.resolution with
    cases := [literalCase, wildcardCase]
    requirements
  }

private def changeSolved (fixture : Fixture)
    (change : SolvedRequirement → SolvedRequirement) : CheckedFunction := {
  fixture.function with
  solvedRequirements := fixture.function.solvedRequirements.map fun solved =>
    if solved.id = fixture.literalResolution.requirement then change solved
    else solved
}

private def expectErrorAt (label : String) (function : CheckedFunction)
    (site : SourceCoreElaboration.ErrorSite)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit := do
  match SourceCoreElaboration.elaborateFunction function with
  | .ok _ => throw (IO.userError
      s!"{label}: malformed typed match reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site = site) && accept error.reason)
        s!"{label}: wrong elaboration error {reprStr error}"

private def expectError (fixture : Fixture) (label : String)
    (function : CheckedFunction)
    (accept : SourceCoreElaboration.ErrorReason → Bool) : IO Unit :=
  expectErrorAt label function (.occurrence fixture.statement.occurrence) accept

private def intPredicate (target : TypeSystem.Ty) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate target

private def testCheckedBaseline (fixture : Fixture) : IO Unit := do
  let lowered ← match
      SourceCoreElaboration.elaborateFunction fixture.function with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError
        s!"checked typed match did not lower: {reprStr error}")
  let run (tag : Nat) := Core.runStateful 40
    (.initial lowered.core [
      .word (Core.Word.ofNatModulo tag),
      .word (Core.Word.ofNatModulo 11),
      .word (Core.Word.ofNatModulo 22)
    ])
  assertTrue (decide (run 0 =
      .done (.word (Core.Word.ofNatModulo 11)) [] &&
      run 7 = .done (.word (Core.Word.ofNatModulo 22)) []))
    "checked typed match did not preserve literal/wildcard branch selection"

private def testRequirementAttachments (fixture : Fixture) : IO Unit := do
  let requirement := fixture.literalResolution.requirement
  let matchMismatch := withResolution fixture {
    fixture.resolution with requirements := []
  }
  expectError fixture "match requirement list" matchMismatch fun reason =>
    reason == .matchRequirementsMismatch [requirement] []

  let detachedLiteral : TypedMatchCase := {
    fixture.literalCase with
    pattern := { fixture.literalCase.pattern with requirements := [] }
  }
  let literalMismatch := withCases fixture detachedLiteral
    fixture.wildcardCase []
  expectError fixture "integer pattern requirement attachment"
    literalMismatch fun reason =>
      reason == .integerLiteralRequirementsMismatch [requirement] []

  let forged : RequirementId := ⟨requirement.index + 1000⟩
  let attachedWildcard : TypedMatchCase := {
    fixture.wildcardCase with
    pattern := { fixture.wildcardCase.pattern with requirements := [forged] }
  }
  let wildcardMismatch := withCases fixture fixture.literalCase
    attachedWildcard [requirement, forged]
  expectError fixture "wildcard pattern requirement attachment"
    wildcardMismatch fun reason =>
      reason == .matchPatternRequirementsMismatch [] [forged]

private def testPatternPayloads (fixture : Fixture) : IO Unit := do
  let sourceMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral (.decimal "1")
        fixture.literalResolution
    }
  }
  expectError fixture "pattern source payload"
    (withCases fixture sourceMismatch) fun reason =>
      reason == .matchPatternSourceMismatch

  let rawMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral fixture.literalSource {
        fixture.literalResolution with
        rawValue := fixture.literalResolution.rawValue + 1
      }
    }
  }
  expectError fixture "pattern decoded value"
    (withCases fixture rawMismatch) fun reason =>
      reason == .integerLiteralRawValueMismatch
        fixture.literalResolution.rawValue
        (fixture.literalResolution.rawValue + 1)

  let patternTypeMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := { fixture.literalCase.pattern with type := .bool }
  }
  expectError fixture "pattern/scrutinee type"
    (withCases fixture patternTypeMismatch) fun reason =>
      reason == .matchPatternTypeMismatch .word .bool

  let targetMismatch : TypedMatchCase := {
    fixture.literalCase with
    pattern := {
      fixture.literalCase.pattern with
      resolution := .integerLiteral fixture.literalSource {
        fixture.literalResolution with targetType := .bool
      }
    }
  }
  expectError fixture "pattern target type"
    (withCases fixture targetMismatch) fun reason =>
      reason == .integerLiteralTargetTypeMismatch .bool .word

private def testPatternEvidence (fixture : Fixture) : IO Unit := do
  let requirement := fixture.literalResolution.requirement
  let expected := fixture.literalResolution.predicate
  let wrong := intPredicate .bool
  let predicateMismatch := changeSolved fixture fun solved => {
    solved with predicate := wrong
  }
  expectError fixture "pattern predicate" predicateMismatch fun reason =>
    reason == .integerLiteralPredicateMismatch requirement expected wrong

  let evidenceGoalMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl wrong (.builtin .intWord) [])
  }
  expectError fixture "pattern evidence goal" evidenceGoalMismatch fun reason =>
    reason == .integerLiteralEvidenceGoalMismatch requirement expected wrong

  let implementationMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl expected (.builtin .intInteger) [])
  }
  expectError fixture "pattern implementation" implementationMismatch
    fun reason => reason == .integerLiteralImplementationMismatch requirement
      (.builtin .intWord) (.builtin .intInteger)

  let premise : TypedTraitResolution.Evidence :=
    .byImpl expected (.builtin .intWord) []
  let premiseMismatch := changeSolved fixture fun solved => {
    solved with
    evidence := .implementation
      (.byImpl expected (.builtin .intWord) [premise])
  }
  expectError fixture "pattern evidence premises" premiseMismatch fun reason =>
    reason == .integerLiteralPremiseCountMismatch requirement 0 1

private def testHiddenScrutineeIdentity (fixture : Fixture) : IO Unit := do
  let foreignOwner := {
    fixture.function.declaration with
    declarationIndex := fixture.function.declaration.declarationIndex + 1
  }
  let foreignHidden := {
    fixture.resolution.hiddenScrutinee with owner := foreignOwner
  }
  let ownerMismatch := withResolution fixture {
    fixture.resolution with hiddenScrutinee := foreignHidden
  }
  expectError fixture "hidden scrutinee owner" ownerMismatch fun reason =>
    reason == .matchHiddenOwnerMismatch fixture.function.declaration foreignOwner

  let input ← match fixture.function.typedBody.inputs with
    | input :: _ => pure input
    | [] => throw (IO.userError "typed-match fixture lost its input scope")
  let collision := withResolution fixture {
    fixture.resolution with hiddenScrutinee := input.id
  }
  expectError fixture "hidden scrutinee scope collision" collision fun reason =>
    reason == .duplicateMatchHidden input.id

  let branchExpression ← match fixture.literalCase.body with
    | [statement] =>
        match fixture.function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some expression), .. } => pure expression
        | _ => throw (IO.userError
            "typed-match fixture lost its literal branch return")
    | body => throw (IO.userError
        s!"typed-match literal branch retained {body.length} statements")
  let hiddenReference : CheckedFunction := {
    fixture.function with
    typedBody := changeExpression fixture.function.typedBody branchExpression
      fun node => {
        node with
        form := .reference "forged-hidden"
          (.local fixture.resolution.hiddenScrutinee)
      }
  }
  expectErrorAt "hidden scrutinee branch visibility" hiddenReference
    (.occurrence branchExpression.occurrence) fun reason =>
      reason == .unknownLocal fixture.resolution.hiddenScrutinee

/-- Validate the checked baseline and reject adversarial mutations at every
trust boundary carried by an executable typed source match. -/
def testSourcePatternMatchingTamper : IO Unit := do
  let fixture ← fixture
  testCheckedBaseline fixture
  testRequirementAttachments fixture
  testPatternPayloads fixture
  testPatternEvidence fixture
  testHiddenScrutineeIdentity fixture

end Tests.SourcePatternMatchingTamper
