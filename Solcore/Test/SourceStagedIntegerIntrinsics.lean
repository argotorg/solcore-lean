import Solcore

/-! End-to-end regressions for the first closed staged-integer intrinsic slice. -/

set_option autoImplicit false

namespace Tests.SourceStagedIntegerIntrinsics

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
  | none => throw (IO.userError "invalid staged-integer test module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"staged-integer fixture failed checking: {reprStr errors}")

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
      signature.name == name with
  | some signature => pure signature
  | none => throw (IO.userError s!"signature `{name}` was not found")

private def returnedExpression (function : CheckedFunction) : IO ExpressionId :=
  match function.typedBody.roots with
  | [.statement statement] =>
      match function.typedBody.lookupStatement? statement with
      | some { form := .returnStmt (some expression), .. } => pure expression
      | _ => throw (IO.userError
          "staged-integer fixture root is not a valued return")
  | roots => throw (IO.userError
      s!"staged-integer fixture retained {roots.length} roots")

private def positiveSource : String :=
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  String.intercalate "\n" [
    "function basic() returns (Word) {",
    "  return wordFromInteger(integerSub(10, 3));",
    "}",
    "function negative() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}",
    "function deepNegative() returns (Word) {",
    "  return wordFromInteger(integerSub(0, " ++ successor ++ "));",
    "}",
    "function exactNegativeModulus() returns (Word) {",
    "  return wordFromInteger(integerSub(0, " ++ modulus ++ "));",
    "}",
    "function positiveWrap() returns (Word) {",
    "  return wordFromInteger(integerSub(" ++ successor ++ ", 1));",
    "}",
    "function hexadecimal() returns (Word) {",
    "  return wordFromInteger(integerSub(0x20, 0x01));",
    "}",
    "function directHexadecimal() returns (Word) {",
    "  return wordFromInteger(0x100);",
    "}",
    "function nested() returns (Word) {",
    "  return wordFromInteger(integerSub(integerSub(20, 3), integerSub(9, 4)));",
    "}",
    "function grouped() returns (Word) {",
    "  return wordFromInteger((integerSub((5), (8))));",
    "}",
    "function direct() returns (Word) {",
    "  return wordFromInteger(" ++ successor ++ ");",
    "}"
  ]

private def limits : Limits := {
  checkingFuel := 1024
  specializationBudget := 1
  executionFuel := 4096
}

private def assertPreparedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace positiveSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: staged intrinsic tree was not erased to one Word constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 9)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: public execution changed its Word value or store"

private def builtinIntegerEvidence (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate Ty.integer &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intInteger) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def expectBuiltinCallee (source : TypedSource)
    (callee : ExpressionId) (expected : BuiltinFunctionId) : IO Unit :=
  match source.lookupExpression? callee with
  | some node =>
      match node.form with
      | .reference spelling (.builtinFunction actual) =>
          assertTrue (decide (actual = expected ∧
              node.type = expected.type ∧ spelling = expected.spelling ∧
              node.requirements = [] ∧ node.coercions = []))
            s!"builtin callee `{expected.spelling}` lost its exact identity or type"
      | _ => throw (IO.userError
          s!"builtin callee `{expected.spelling}` changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"builtin callee `{expected.spelling}` changed shape: {reprStr node}")

private def expectIntegerLiteral (function : CheckedFunction)
    (id : ExpressionId) (source : Syntax.CoreLiteralValue)
    (rawValue : Nat) : IO RequirementId := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral actual resolution =>
          assertTrue (decide (node.type = Ty.integer ∧ actual = source ∧
              resolution.rawValue = rawValue ∧
              resolution.targetType = Ty.integer ∧
              node.requirements = [resolution.requirement] ∧
              node.coercions = []))
            "staged integer literal lost its exact source, target, or requirement"
          let solved := function.solvedRequirements.filter fun row =>
            row.id == resolution.requirement
          match solved with
          | [evidence] =>
              assertTrue (builtinIntegerEvidence evidence)
                "staged integer literal retained the wrong Int evidence"
          | _ => throw (IO.userError
              "staged integer literal did not retain unique Int<integer> evidence")
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"staged integer literal changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"staged integer literal changed shape: {reprStr node}")

private def testTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram positiveSource
  let function ← checkedNamed program "negative"
  let root ← returnedExpression function
  let (inner, left, right) ←
    match function.typedBody.lookupExpression? root with
    | some outer =>
        match outer.form with
        | .call callee [inner] (.builtinFunction .wordFromInteger) =>
            assertTrue (decide (outer.type = Ty.word ∧
                outer.requirements = [] ∧ outer.coercions = []))
              "wordFromInteger call lost its exact result metadata"
            expectBuiltinCallee function.typedBody callee .wordFromInteger
            match function.typedBody.lookupExpression? inner with
            | some innerNode =>
                match innerNode.form with
                | .call innerCallee [left, right]
                    (.builtinFunction .integerSub) =>
                    assertTrue (decide (innerNode.type = Ty.integer ∧
                        innerNode.requirements = [] ∧
                        innerNode.coercions = []))
                      "integerSub call lost its exact result metadata"
                    expectBuiltinCallee function.typedBody innerCallee
                      .integerSub
                    pure (inner, left, right)
                | _ => throw (IO.userError
                    s!"integerSub typed call changed form: {reprStr innerNode}")
            | node => throw (IO.userError
                s!"integerSub typed call changed shape: {reprStr node}")
        | _ => throw (IO.userError
            s!"wordFromInteger typed call changed form: {reprStr outer}")
    | node => throw (IO.userError
        s!"wordFromInteger typed call changed shape: {reprStr node}")
  let leftRequirement ← expectIntegerLiteral function left (.decimal "1") 1
  let rightRequirement ← expectIntegerLiteral function right (.decimal "2") 2
  assertTrue (decide (inner ≠ root ∧ left ≠ right ∧
      function.solvedRequirements.map (·.id) =
        [leftRequirement, rightRequirement]) &&
      function.solvedRequirements.all builtinIntegerEvidence)
    "staged intrinsic inference changed literal identity or evidence order"
  match SourceCoreElaboration.evaluateStagedInteger
      function.solvedRequirements function.typedBody inner with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-1 : Int) ∧
          evaluated.consumedRequirements =
            [leftRequirement, rightRequirement]))
        "direct staged evaluation lost signed subtraction or evidence order"
  | .error error => throw (IO.userError
      s!"direct staged evaluation rejected checked input: {reprStr error}")

  let signature ← signatureNamed program "negative"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "builtin functions became source specialization edges"
  | result => throw (IO.userError
      s!"builtin-only worklist did not close in one slot: {reprStr result}")

private def testPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let maximum := Core.Word.maximum
  let zero := Core.Word.zero
  let cases : List (String × Core.Word) := [
    ("basic", Core.Word.ofNatModulo 7),
    ("negative", maximum),
    ("deepNegative", maximum),
    ("exactNegativeModulus", zero),
    ("positiveWrap", zero),
    ("hexadecimal", Core.Word.ofNatModulo 31),
    ("directHexadecimal", Core.Word.ofNatModulo 256),
    ("nested", Core.Word.ofNatModulo 12),
    ("grouped", Core.Word.ofIntModulo (-3)),
    ("direct", Core.Word.ofNatModulo 1)
  ]
  for (name, expected) in cases do
    assertPreparedWord moduleId name expected

private def testSourceDeclarationsShadowBuiltins : IO Unit := do
  let content := String.intercalate "\n" [
    "function integerSub(left: Word, right: Word) returns (Word) {",
    "  return 41;",
    "}",
    "function wordFromInteger(value: Word) returns (Word) { return value; }",
    "function shadowed() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}"
  ]
  let program ← checkedProgram content
  let function ← checkedNamed program "shadowed"
  let builtinCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.builtinFunction function), .. } =>
        some function
    | _ => none
  let declarationCalls := function.typedBody.nodes.filterMap fun
    | .expression { form := .call _ _ (.declaration selected), .. } =>
        some selected.declaration
    | _ => none
  assertTrue (builtinCalls.isEmpty && declarationCalls.length == 2)
    "source declarations did not shadow the lowest-priority builtins"
  let moduleId ← mainModule
  let shadowLimits : Limits := { limits with specializationBudget := 3 }
  match run (workspace content) (Seed.named moduleId "shadowed") []
      shadowLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == Core.Word.ofNatModulo 41)
        "source-declaration shadowing returned the wrong Word"
  | result => throw (IO.userError
      s!"source-declaration shadowing did not execute: {reprStr result}")

private def expectBodyError (label content : String)
    (accept : SourceInference.Error → Bool) : IO Unit := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label}: wrong source-inference error"
  | .ok _ => throw (IO.userError s!"{label}: invalid source was accepted")

private def testInferenceRejections : IO Unit := do
  expectBodyError "integerSub arity"
    "function bad() returns (integer) { return integerSub(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerSub 2 1
  expectBodyError "wordFromInteger arity"
    "function bad() returns (Word) { return wordFromInteger(); }"
    fun error => error == .builtinFunctionArityMismatch .wordFromInteger 1 0
  expectBodyError "integerSub operand type"
    "function bad() returns (Word) { return wordFromInteger(integerSub(true, 1)); }"
    fun error => error matches .unification _
  expectBodyError "wordFromInteger operand type"
    "function bad() returns (Word) { return wordFromInteger(true); }"
    fun error => error matches .unification _

  let blocked := String.intercalate "\n" [
    "function integerSub(left: Bool, right: Bool) returns (Bool) {",
    "  return left;",
    "}",
    "function bad() returns (Word) {",
    "  return wordFromInteger(integerSub(1, 2));",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace blocked) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate == ProgramSignatures.builtinIntPredicate Ty.bool
        | .body { error := .unification _, .. } => true
        | _ => false)
        "an incompatible source declaration produced the wrong failure"
  | .ok _ => throw (IO.userError
      "an incompatible source declaration fell through to the builtin")

private def testRuntimeBoundaryRejections : IO Unit := do
  let dependentProgram ← checkedProgram
    "function dependent(flag: Bool) returns (Word) { return wordFromInteger(flag ? 1 : 2); }"
  let dependent ← checkedNamed dependentProgram "dependent"
  let root ← returnedExpression dependent
  let argument ← match dependent.typedBody.lookupExpression? root with
    | some node =>
        match node.form with
        | .call _ [argument] (.builtinFunction .wordFromInteger) =>
            pure argument
        | _ => throw (IO.userError
            "runtime-dependent fixture lost wordFromInteger call")
    | none => throw (IO.userError
        "runtime-dependent fixture lost its return expression")
  match SourceCoreElaboration.elaborateFunction dependent with
  | .ok _ => throw (IO.userError
      "runtime-dependent staged conditional reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence argument.occurrence ∧
          error.reason = .stagedIntegerExpressionNotClosed))
        s!"runtime-dependent staged conditional produced the wrong error: {reprStr error}"

  let leakingProgram ← checkedProgram
    "function leaking() returns (integer) { return integerSub(1, 2); }"
  let leaking ← checkedNamed leakingProgram "leaking"
  match SourceCoreElaboration.elaborateFunction leaking with
  | .ok _ => throw (IO.userError
      "a staged integer escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site = .declaration leaking.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"integer leakage produced the wrong boundary error: {reprStr error}"

/-- Exercise exact signed staging, modulo projection, builtin identity,
worklist erasure, source shadowing, and inference rejection. -/
def testSourceStagedIntegerIntrinsics : IO Unit := do
  testTypedCarrierAndWorklist
  testPublicExecution
  testSourceDeclarationsShadowBuiltins
  testInferenceRejections
  testRuntimeBoundaryRejections
  IO.println "closed staged integer intrinsics GREEN"

end Tests.SourceStagedIntegerIntrinsics
