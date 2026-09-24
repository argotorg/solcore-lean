import Solcore

/-! End-to-end regressions for typed numeric match patterns. -/

set_option autoImplicit false

namespace Tests.SourcePatternMatching

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceProgramExecution Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid source-pattern test module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"source-pattern fixture failed checking: {reprStr errors}")

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
      (program.environment.declaration? signature.id).any fun entry =>
        entry.name == some name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def matchResolutions (function : CheckedFunction) :
    List MatchResolution :=
  function.typedBody.nodes.filterMap fun
    | .statement { form := .matchWith resolution, .. } => some resolution
    | _ => none

private def sourceGroupDepth : MatchPatternSource → Nat
  | .group _ inner => sourceGroupDepth inner + 1
  | _ => 0

private def solvedByBuiltinInt (target : Ty)
    (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate target &&
    match solved.evidence with
    | .implementation (.byImpl goal implementation premises) =>
        goal == solved.predicate && premises.isEmpty &&
          implementation == if target == Ty.word then
            ProgramImplId.builtin .intWord
          else
            ProgramImplId.builtin .intInteger
    | .assumption _ => false

private def expectInferenceError (label content : String)
    (accept : SourceInference.Error → Bool) : IO Unit := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label} had the wrong inference failure"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def testPatternDefaultAndLateConstraint : IO Unit := do
  let program ← checkedProgram (String.intercalate "\n" [
    "function acceptInteger(value: integer) returns (integer) { return value; }",
    "function defaulted() returns (Word) {",
    "  match (1) {",
    "    case (((1))) { return 11; }",
    "    default { return 22; }",
    "  }",
    "}",
    "function lateInteger() returns (integer) {",
    "  let value = 1;",
    "  match (value) {",
    "    case 0 { return acceptInteger(value); }",
    "    default { return value; }",
    "  }",
    "}",
    "function generic<T>(tag: Word, value: T) returns (T) {",
    "  match (tag) {",
    "    case ((0)) { return value; }",
    "    default { return value; }",
    "  }",
    "}",
    "function pick<T>(tag: T, value: T) returns (T) {",
    "  match (tag) {",
    "    case _ { return value; }",
    "  }",
    "}"
  ])
  let defaulted ← checkedNamed program "defaulted"
  let resolution ← match matchResolutions defaulted with
    | [resolution] => pure resolution
    | resolutions => throw (IO.userError
        s!"defaulted retained {resolutions.length} match nodes")
  let pattern ← match resolution.cases with
    | [arm] => pure arm.pattern
    | cases => throw (IO.userError
        s!"defaulted retained {cases.length} explicit cases")
  let patternRequirement ← match pattern.resolution with
    | .integerLiteral (.decimal "1") literal =>
        assertTrue (decide (literal.rawValue = 1 ∧
          literal.targetType = Ty.word ∧
          pattern.type = Ty.word ∧
          pattern.requirements = [literal.requirement] ∧
          resolution.requirements = [literal.requirement] ∧
          sourceGroupDepth pattern.source = 3))
          "grouped pattern carrier lost source, type, or requirement metadata"
        pure literal.requirement
    | other => throw (IO.userError
        s!"defaulted retained the wrong pattern carrier: {reprStr other}")
  assertTrue (decide (patternRequirement.index = 1 ∧
      defaulted.solvedRequirements.map (·.id.index) = [0, 1, 2, 3]) &&
      defaulted.solvedRequirements.all (solvedByBuiltinInt .word))
    "pattern-only defaulting did not close expression and pattern rows as Word"
  let late ← checkedNamed program "lateInteger"
  let latePattern ← match matchResolutions late with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"late integer fixture retained {resolutions.length} malformed matches")
  assertTrue (late.solvedRequirements.length == 2 &&
      late.solvedRequirements.all (solvedByBuiltinInt .integer) &&
      match latePattern.resolution with
      | .integerLiteral _ literal =>
          decide (latePattern.type = .integer ∧
            literal.targetType = .integer)
      | _ => false)
    "body inference did not constrain the pattern before Word defaulting"
  let signature ← signatureNamed program "generic"
  let generic ← checkedNamed program "generic"
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"generic fixture retained {parameters.length} type parameters")
  let specialized ← match SourceSpecialization.specializeFunction signature
      generic [(parameter, .bool)] with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError
        s!"generic match specialization failed: {reprStr error}")
  let specializedPattern ← match matchResolutions specialized.function with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"specialization retained {resolutions.length} malformed matches")
  assertTrue (decide (specialized.function.inferredBodyType = Ty.bool ∧
      specializedPattern.type = Ty.word) &&
      match specializedPattern.resolution with
      | .integerLiteral _ literal => literal.targetType == Ty.word
      | _ => false)
    "specialization did not preserve and close the pattern carrier"
  let pickSignature ← signatureNamed program "pick"
  let pick ← checkedNamed program "pick"
  let pickParameter ← match pickSignature.scheme.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"pick fixture retained {parameters.length} type parameters")
  let specializedPick ← match SourceSpecialization.specializeFunction
      pickSignature pick [(pickParameter, .bool)] with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError
        s!"generic wildcard match specialization failed: {reprStr error}")
  let specializedWildcard ←
    match matchResolutions specializedPick.function with
    | [{ cases := [arm], .. }] => pure arm.pattern
    | resolutions => throw (IO.userError
        s!"wildcard specialization retained {resolutions.length} malformed matches")
  assertTrue (decide (specializedPick.function.inferredBodyType = Ty.bool ∧
      specializedWildcard.type = Ty.bool ∧
      specializedWildcard.resolution = .wildcard ∧
      specializedWildcard.requirements = []))
    "specialization did not substitute a rigid wildcard pattern type"

private def testWildcardOnlyLiteralDefault : IO Unit := do
  let source :=
    "function wildcardOnly() { match (1) { case _ { return; } } }"
  let program ← checkedProgram source
  let checked ← checkedNamed program "wildcardOnly"
  let resolution ← match matchResolutions checked with
    | [resolution] => pure resolution
    | resolutions => throw (IO.userError
        s!"wildcard-only fixture retained {resolutions.length} match nodes")
  let pattern ← match resolution.cases with
    | [arm] => pure arm.pattern
    | cases => throw (IO.userError
        s!"wildcard-only fixture retained {cases.length} match cases")
  let literal ← match checked.typedBody.lookupExpression? resolution.scrutinee with
    | some node =>
        match node.form, node.requirements with
        | .integerLiteral (.decimal "1") literal, [requirement] =>
            if node.type = Ty.word && literal.targetType = Ty.word &&
                literal.requirement = requirement then
              pure literal
            else
              throw (IO.userError
                "wildcard-only scrutinee lost its Word literal metadata")
        | _, _ => throw (IO.userError
            s!"wildcard-only scrutinee retained the wrong node: {reprStr node}")
    | other => throw (IO.userError
        s!"wildcard-only scrutinee retained the wrong node: {reprStr other}")
  assertTrue (decide (pattern.type = Ty.word ∧
      pattern.resolution = .wildcard ∧
      pattern.requirements = [] ∧
      resolution.requirements = [] ∧
      checked.inferredBodyType = Ty.unit ∧
      checked.solvedRequirements.map (·.id) = [literal.requirement]) ∧
      checked.solvedRequirements.all (solvedByBuiltinInt .word))
    "expression defaulting did not close a wildcard-only match as Word"
  let limits : Limits := {
    checkingFuel := 1024
    specializationBudget := 16
    executionFuel := 4096
  }
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "wildcardOnly") limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"wildcard-only match preparation failed: {reprStr error}")
  match prepared.run? [] limits.executionFuel with
  | some (.done .unit []) => pure ()
  | result => throw (IO.userError
      s!"wildcard-only match had runtime result {reprStr result}")

private def testPatternInferenceRejections : IO Unit := do
  expectInferenceError "unreachable arm static checking"
    (String.intercalate "\n" [
      "function bad(tag: Word) returns (Word) {",
      "  match (tag) {",
      "    case _ { return 1; }",
      "    case 0 { return missing; }",
      "  }",
      "}"
    ]) fun error => error matches .unknownVariable "missing"
  expectInferenceError "match branch scope isolation"
    (String.intercalate "\n" [
      "function bad(tag: Word) returns (Word) {",
      "  match (tag) {",
      "    case 0 { let local: Word = 1; return local; }",
      "    default { return local; }",
      "  }",
      "}"
    ]) fun error => error matches .unknownVariable "local"
  expectInferenceError "Bool numeric pattern"
    "function bad(tag: Bool) returns (Word) { match (tag) { case 0 { return 1; } default { return 2; } } }"
    fun error => match error with
      | .nonNumericPatternType _ type => type == Ty.bool
      | _ => false
  expectInferenceError "nominal numeric pattern"
    (String.intercalate "\n" [
      "enum Box { Only }",
      "function bad(tag: Box) returns (Word) {",
      "  match (tag) { case 0 { return 1; } default { return 2; } }",
      "}"
    ]) fun error => match error with
      | .nonNumericPatternType _ (.constructor (.declaration _)) => true
      | _ => false
  expectInferenceError "rigid generic numeric pattern"
    (String.intercalate "\n" [
      "trait Int<T> {}",
      "function bad<T>(tag: T) returns (Word) where T: Int {",
      "  match (tag) { case 0 { return 1; } default { return 2; } }",
      "}"
    ]) fun error => error matches .nonNumericPatternType _ (.parameter _)
  let unsupported : List (String × String × String) := [
    ("string pattern", "case \"text\" { return 1; }", "string literal"),
    ("comptime pattern", "case comptime 0 { return 1; }", "comptime")
  ]
  for (label, arm, kind) in unsupported do
    expectInferenceError label
      (String.intercalate "\n" [
        "enum Box { Only }",
        "function bad(tag: Word) returns (Word) {",
        "  match (tag) {",
        "    " ++ arm,
        "    default { return 2; }",
        "  }",
        "}"
      ]) fun error => match error with
        | .unsupportedPattern _ actual => actual == kind
        | _ => false
  expectInferenceError "uncovered literal match"
    "function bad(tag: Word) returns (Word) { match (tag) { case 0 { return 1; } } }"
    fun error => error matches .nonExhaustiveMatch _
  expectInferenceError "fallthrough case"
    "function bad(tag: Word) returns (Word) { match (tag) { case _ { let value: Word = 1; } } }"
    fun error => error matches .unification _
  expectInferenceError "fallthrough default"
    "function bad(tag: Word) returns (Word) { match (tag) { case 0 { return 1; } default { let value: Word = 2; } } }"
    fun error => error matches .unification _

private def guardWords : Resolved.Expr → List Core.Word
  | .ifE (.binary .wordEq _ (.word literal)) _ rest =>
      literal :: guardWords rest
  | _ => []

private def resolvedLetBinders : Resolved.Expr → List Resolved.LocalId
  | .unit | .bool _ | .word _ | .var _ => []
  | .pair left right | .binary _ left right | .wordLt left right =>
      resolvedLetBinders left ++ resolvedLetBinders right
  | .unary _ operand => resolvedLetBinders operand
  | .letE binder value body =>
      binder :: resolvedLetBinders value ++ resolvedLetBinders body
  | .ifE condition thenBranch elseBranch =>
      resolvedLetBinders condition ++ resolvedLetBinders thenBranch ++
        resolvedLetBinders elseBranch

private def generousLimits : Limits := {
  checkingFuel := 1024
  specializationBudget := 16
  executionFuel := 4096
}

private def assertPreparedResult (label : String) (prepared : PreparedEntry)
    (input expected : Nat) : IO Unit :=
  match prepared.run? [.word (word input)] generousLimits.executionFuel with
  | some (.done (.word actual) []) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} had runtime result {reprStr result}")

private def testModuloOrderingAndPublicExecution : IO Unit := do
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  let source := String.intercalate "\n" [
    "function route(tag: Word) returns (Word) {",
    "  match (tag) {",
    "    case " ++ modulus ++ " { return 10; }",
    "    case 0 { return 20; }",
    "    case " ++ successor ++ " { return 30; }",
    "    case 0x01 { return 40; }",
    "    default { return 50; }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "route") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"modulo match preparation failed: {reprStr error}")
  match prepared.entry.elaborated.inputs.ids,
      prepared.entry.elaborated.resolved with
  | [input], .letE hidden (.var actual) body =>
      assertTrue (decide (actual = input ∧ hidden ≠ input) &&
          guardWords body == [word 0, word 0, word 1, word 1])
        "match lowering lost once-only scrutinee binding or source guard order"
  | _, resolved => throw (IO.userError
      s!"match lowering has the wrong resolved shape: {reprStr resolved}")
  assertPreparedResult "modulo-zero first arm" prepared 0 10
  assertPreparedResult "modulo-one first arm" prepared 1 30
  assertPreparedResult "match default" prepared 2 50
  match run (workspace source) (Seed.named moduleId "route")
      [.word (word 1)] generousLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == word 30)
        "public source execution changed ordered modulo pattern selection"
  | result => throw (IO.userError
      s!"public source match execution failed: {reprStr result}")

private def testDirectCallHiddenLocalCollision : IO Unit := do
  let source := String.intercalate "\n" [
    "function identity(value: Word) returns (Word) { return value; }",
    "function routed(value: Word) returns (Word) {",
    "  match (identity(value)) {",
    "    case 0 { return 7; }",
    "    default { return 9; }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "routed") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"call-backed match preparation failed: {reprStr error}")
  let binders := resolvedLetBinders prepared.entry.elaborated.resolved
  let rootOwned := binders.filter fun binder =>
    decide (binder.owner = prepared.key.declaration)
  assertTrue (decide (binders.eraseDups.length = binders.length) &&
      rootOwned.any (fun binder => binder.binderIndex == 1) &&
      rootOwned.any (fun binder => binder.binderIndex == 2))
    "match hidden local collided with a direct-call temporary"
  assertPreparedResult "call-backed match hit" prepared 0 7
  assertPreparedResult "call-backed match default" prepared 1 9

private def testDiscardedTailStillLowers : IO Unit := do
  let source := String.intercalate "\n" [
    "function helper(value: Word) returns (Word) { return value; }",
    "function early(tag: Word) returns (Word) {",
    "  match (tag) {",
    "    case _ { return 7; }",
    "    case 0 { return helper(8); }",
    "    default { return helper(9); }",
    "  }",
    "}"
  ]
  let moduleId ← mainModule
  let prepared ← match prepare (workspace source)
      (Seed.named moduleId "early") generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"early-wildcard match did not consume its discarded tail: {reprStr error}")
  assertPreparedResult "early wildcard ordered selection" prepared 0 7

/-- Exercise pattern-only defaulting, contextual preservation, specialization,
defensive rejection, modulo lowering, ordered selection, linking, and execution. -/
def testSourcePatternMatching : IO Unit := do
  testPatternDefaultAndLateConstraint
  testWildcardOnlyLiteralDefault
  testPatternInferenceRejections
  testModuloOrderingAndPublicExecution
  testDirectCallHiddenLocalCollision
  testDiscardedTailStillLowers
  IO.println "typed source integer-pattern inference and execution GREEN"

end Tests.SourcePatternMatching
