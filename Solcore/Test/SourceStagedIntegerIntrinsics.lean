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

private def expandedSource : String :=
  let modulus := toString Core.wordModulus
  let successor := toString (Core.wordModulus + 1)
  let plusFive := toString (Core.wordModulus + 5)
  let plusSeven := toString (Core.wordModulus + 7)
  let halfModulus : Nat := 2 ^ 128
  let half := toString halfModulus
  String.intercalate "\n" [
    "function addHugeNegative() returns (Word) {",
    "  return wordFromInteger(integerAdd(" ++ plusFive ++
      ", integerSub(0, " ++ plusSeven ++ ")));",
    "}",
    "function addNegatives() returns (Word) {",
    "  return wordFromInteger(integerAdd(integerSub(0, 5), integerSub(0, 8)));",
    "}",
    "function arithmeticNested() returns (Word) {",
    "  return wordFromInteger(integerSub(integerAdd(20, integerSub(0, 3)), integerAdd(4, 5)));",
    "}",
    "function mulPower() returns (Word) {",
    "  return wordFromInteger(integerMul(" ++ half ++ ", " ++ half ++ "));",
    "}",
    "function mulNegative() returns (Word) {",
    "  return wordFromInteger(integerMul(integerSub(0, 3), 5));",
    "}",
    "function mulNegativeBoth() returns (Word) {",
    "  return wordFromInteger(integerMul(integerSub(0, 3), integerSub(0, 5)));",
    "}",
    "function mulZero() returns (Word) {",
    "  return wordFromInteger(integerMul(0, integerSub(0, " ++ plusSeven ++ ")));",
    "}",
    "function mulNested() returns (Word) {",
    "  return wordFromInteger(integerMul(integerAdd(7, integerSub(0, 2)), integerSub(6, 3)));",
    "}",
    "function mulEqBeforeModulo() returns (Bool) {",
    "  return integerEq(integerMul(" ++ modulus ++ ", " ++ modulus ++ "), 0);",
    "}",
    "function wordToModulo() returns (Word) {",
    "  return wordFromInteger(wordToInteger(" ++ successor ++ "));",
    "}",
    "function wordToGrouped() returns (Word) {",
    "  return wordFromInteger(wordToInteger((" ++ successor ++ ")));",
    "}",
    "function wordRoundtripNegative() returns (Word) {",
    "  return wordFromInteger(wordToInteger(wordFromInteger(integerSub(0, 1))));",
    "}",
    "function wordBridgeNested() returns (Word) {",
    "  return wordFromInteger(integerAdd(wordToInteger(wordFromInteger(integerSub(0, 3))), 5));",
    "}",
    "function wordLiteralArithmetic() returns (Word) {",
    "  return wordFromInteger(integerAdd(wordToInteger(" ++ successor ++ "), 2));",
    "}",
    "function wordBridgeComparison() returns (Bool) {",
    "  return integerEq(wordToInteger(wordFromInteger(integerSub(0, 1))), integerSub(0, 1));",
    "}",
    "function eqBeforeModulo() returns (Bool) {",
    "  return integerEq(0, " ++ modulus ++ ");",
    "}",
    "function eqSignedExact() returns (Bool) {",
    "  return integerEq(integerAdd(" ++ plusFive ++
      ", integerSub(0, " ++ plusSeven ++ ")), integerSub(0, 2));",
    "}",
    "function ltBeforeModulo() returns (Bool) {",
    "  return integerLt(" ++ successor ++ ", 2);",
    "}",
    "function ltNegative() returns (Bool) {",
    "  return integerLt(integerSub(0, 2), integerSub(0, 1));",
    "}",
    "function ltNegativeReverse() returns (Bool) {",
    "  return integerLt(integerSub(0, 1), integerSub(0, 2));",
    "}",
    "function eqConditional() returns (Word) {",
    "  return integerEq(0, " ++ modulus ++ ") ? 11 : 22;",
    "}",
    "function ltConditional() returns (Word) {",
    "  return integerLt(integerSub(0, 2), integerSub(0, 1)) ? 33 : 44;",
    "}",
    "function typedSpine() returns (Bool) {",
    "  return integerLt(integerAdd(1, 2), integerSub(4, 5));",
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

private def assertPreparedExpandedWord (moduleId : Workspace.ModuleId)
    (name : String) (expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: expanded public preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expected ∧
      prepared.entry.elaborated.core = .word expected))
    s!"{name}: expanded arithmetic was not erased to one Word constant"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 17), .bool false]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: expanded arithmetic changed its result or store"

private def assertPreparedExpandedBool (moduleId : Workspace.ModuleId)
    (name : String) (expected : Bool) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: comparison preparation failed: {reprStr error}")
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .bool expected ∧
      prepared.entry.elaborated.core = .bool expected))
    s!"{name}: staged comparison was not erased to one Bool constant"
  let store : Core.Store := [.bool true, .word (Core.Word.ofNatModulo 23)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.bool expected) store)))
    s!"{name}: staged comparison changed its result or store"

private def assertPreparedExpandedConditional
    (moduleId : Workspace.ModuleId) (name : String) (condition : Bool)
    (thenValue elseValue expected : Core.Word) : IO Unit := do
  let prepared ← match prepare (workspace expandedSource)
      (Seed.named moduleId name) limits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"{name}: comparison conditional preparation failed: {reprStr error}")
  let expectedResolved : Resolved.Expr :=
    .ifE (.bool condition) (.word thenValue) (.word elseValue)
  let expectedCore : Core.Expr :=
    .ifE (.bool condition) (.word thenValue) (.word elseValue)
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    s!"{name}: conditional did not retain its erased Bool condition"
  let store : Core.Store := [.word (Core.Word.ofNatModulo 29)]
  assertTrue (decide (prepared.run? [] limits.executionFuel store =
      some (.done (.word expected) store)))
    s!"{name}: erased comparison did not drive the expected branch"

private def builtinIntegerEvidence (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate Ty.integer &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intInteger) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def builtinWordEvidence (solved : SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate Ty.word &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intWord) premises) =>
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

private def expectBuiltinCall (function : CheckedFunction)
    (id : ExpressionId) (expected : BuiltinFunctionId) :
    IO (List ExpressionId) := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .call callee arguments (.builtinFunction actual) =>
          assertTrue (decide (actual = expected ∧
              arguments.length = expected.parameterTypes.length ∧
              node.type = expected.returnType ∧ node.requirements = [] ∧
              node.coercions = []))
            s!"builtin call `{expected.spelling}` lost its exact signature"
          expectBuiltinCallee function.typedBody callee expected
          pure arguments
      | _ => throw (IO.userError
          s!"builtin call `{expected.spelling}` changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"builtin call `{expected.spelling}` changed shape: {reprStr node}")

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

private def expectWordLiteral (function : CheckedFunction)
    (id : ExpressionId) (source : Syntax.CoreLiteralValue)
    (rawValue : Nat) : IO RequirementId := do
  match function.typedBody.lookupExpression? id with
  | some node =>
      match node.form with
      | .integerLiteral actual resolution =>
          assertTrue (decide (node.type = Ty.word ∧ actual = source ∧
              resolution.rawValue = rawValue ∧
              resolution.targetType = Ty.word ∧
              node.requirements = [resolution.requirement] ∧
              node.coercions = []))
            "staged Word literal lost its exact source, target, or requirement"
          let solved := function.solvedRequirements.filter fun row =>
            row.id == resolution.requirement
          match solved with
          | [evidence] =>
              assertTrue (builtinWordEvidence evidence)
                "staged Word literal retained the wrong Int<Word> evidence"
          | _ => throw (IO.userError
              "staged Word literal did not retain unique Int<Word> evidence")
          pure resolution.requirement
      | _ => throw (IO.userError
          s!"staged Word literal changed form: {reprStr node}")
  | node => throw (IO.userError
      s!"staged Word literal changed shape: {reprStr node}")

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

private def testBuiltinCatalog : IO Unit := do
  let expected : List BuiltinFunctionId := [
    .integerSub,
    .wordFromInteger,
    .integerAdd,
    .integerEq,
    .integerLt,
    .integerMul,
    .wordToInteger
  ]
  assertTrue (decide (BuiltinFunctionId.all = expected) &&
      decide expected.Nodup &&
      decide (expected.map BuiltinFunctionId.spelling).Nodup)
    "builtin function catalog changed order or retained duplicates"
  assertTrue (expected.all fun function =>
      builtinFunctionNamed? function.spelling == some function)
    "builtin function lookup is not total on the supported catalog"
  assertTrue (builtinFunctionNamed? "IntegerAdd" == none &&
      builtinFunctionNamed? "integerUnknown" == none)
    "builtin function lookup stopped being exact and case-sensitive"
  let integerBinary := [Ty.integer, Ty.integer]
  assertTrue (decide (
      BuiltinFunctionId.integerAdd.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerAdd.returnType = Ty.integer ∧
      BuiltinFunctionId.integerAdd.scheme =
        .mono BuiltinFunctionId.integerAdd.type ∧
      BuiltinFunctionId.integerEq.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerEq.returnType = Ty.bool ∧
      BuiltinFunctionId.integerEq.scheme =
        .mono BuiltinFunctionId.integerEq.type ∧
      BuiltinFunctionId.integerLt.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerLt.returnType = Ty.bool ∧
      BuiltinFunctionId.integerLt.scheme =
        .mono BuiltinFunctionId.integerLt.type ∧
      BuiltinFunctionId.integerMul.parameterTypes = integerBinary ∧
      BuiltinFunctionId.integerMul.returnType = Ty.integer ∧
      BuiltinFunctionId.integerMul.scheme =
        .mono BuiltinFunctionId.integerMul.type ∧
      BuiltinFunctionId.wordToInteger.parameterTypes = [Ty.word] ∧
      BuiltinFunctionId.wordToInteger.returnType = Ty.integer ∧
      BuiltinFunctionId.wordToInteger.scheme =
        .mono BuiltinFunctionId.wordToInteger.type))
    "expanded integer builtin signatures changed"

private def testExpandedTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram expandedSource
  let exactAdd ← checkedNamed program "addHugeNegative"
  let exactRoot ← returnedExpression exactAdd
  let outerArguments ← expectBuiltinCall exactAdd exactRoot .wordFromInteger
  let addId ← match outerArguments with
    | [addId] => pure addId
    | arguments => throw (IO.userError
        s!"wordFromInteger retained {arguments.length} arguments")
  let addArguments ← expectBuiltinCall exactAdd addId .integerAdd
  let (large, negative) ← match addArguments with
    | [large, negative] => pure (large, negative)
    | arguments => throw (IO.userError
        s!"integerAdd retained {arguments.length} arguments")
  let subArguments ← expectBuiltinCall exactAdd negative .integerSub
  let (zero, larger) ← match subArguments with
    | [zero, larger] => pure (zero, larger)
    | arguments => throw (IO.userError
        s!"nested integerSub retained {arguments.length} arguments")
  let largeRequirement ← expectIntegerLiteral exactAdd large
    (.decimal (toString (Core.wordModulus + 5))) (Core.wordModulus + 5)
  let zeroRequirement ← expectIntegerLiteral exactAdd zero (.decimal "0") 0
  let largerRequirement ← expectIntegerLiteral exactAdd larger
    (.decimal (toString (Core.wordModulus + 7))) (Core.wordModulus + 7)
  let exactRequirements :=
    [largeRequirement, zeroRequirement, largerRequirement]
  assertTrue (decide (exactAdd.solvedRequirements.map (·.id) =
      exactRequirements))
    "integerAdd changed source-order literal evidence"
  match SourceCoreElaboration.evaluateStagedInteger
      exactAdd.solvedRequirements exactAdd.typedBody addId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-2 : Int) ∧
          evaluated.consumedRequirements = exactRequirements))
        "integerAdd did not preserve an exact huge signed result"
  | .error error => throw (IO.userError
      s!"checked integerAdd did not stage exactly: {reprStr error}")

  let multiplication ← checkedNamed program "mulPower"
  let multiplicationRoot ← returnedExpression multiplication
  let multiplicationOuter ← expectBuiltinCall multiplication
    multiplicationRoot .wordFromInteger
  let multiplicationId ← match multiplicationOuter with
    | [multiplicationId] => pure multiplicationId
    | arguments => throw (IO.userError
        s!"multiplication conversion retained {arguments.length} arguments")
  let multiplicationArguments ← expectBuiltinCall multiplication
    multiplicationId .integerMul
  let (leftPower, rightPower) ← match multiplicationArguments with
    | [leftPower, rightPower] => pure (leftPower, rightPower)
    | arguments => throw (IO.userError
        s!"integerMul retained {arguments.length} arguments")
  let halfModulus : Nat := 2 ^ 128
  let halfSource := Syntax.CoreLiteralValue.decimal (toString halfModulus)
  let leftPowerRequirement ← expectIntegerLiteral multiplication leftPower
    halfSource halfModulus
  let rightPowerRequirement ← expectIntegerLiteral multiplication rightPower
    halfSource halfModulus
  let multiplicationRequirements :=
    [leftPowerRequirement, rightPowerRequirement]
  assertTrue (decide (multiplication.solvedRequirements.map (·.id) =
      multiplicationRequirements))
    "integerMul changed source-order literal evidence"
  match SourceCoreElaboration.evaluateStagedInteger
      multiplication.solvedRequirements multiplication.typedBody
      multiplicationId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Int.ofNat Core.wordModulus ∧
          evaluated.consumedRequirements = multiplicationRequirements))
        "2^128 * 2^128 was not evaluated as exact mathematical 2^256"
  | .error error => throw (IO.userError
      s!"checked integerMul did not stage exactly: {reprStr error}")

  let multiplicationSignature ← signatureNamed program "mulPower"
  let multiplicationRequest : SourceSpecializationWorklist.Request := {
    declaration := multiplicationSignature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [multiplicationRequest] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "integerMul became a source specialization edge"
  | result => throw (IO.userError
      s!"integerMul worklist did not close in one slot: {reprStr result}")

  let negativeMultiplication ← checkedNamed program "mulNegative"
  let negativeRoot ← returnedExpression negativeMultiplication
  let negativeOuter ← expectBuiltinCall negativeMultiplication negativeRoot
    .wordFromInteger
  let negativeMultiplicationId ← match negativeOuter with
    | [id] => pure id
    | arguments => throw (IO.userError
        s!"negative multiplication retained {arguments.length} outer arguments")
  let _ ← expectBuiltinCall negativeMultiplication negativeMultiplicationId
    .integerMul
  match SourceCoreElaboration.evaluateStagedInteger
      negativeMultiplication.solvedRequirements
      negativeMultiplication.typedBody negativeMultiplicationId with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (-15 : Int) ∧
          evaluated.consumedRequirements =
            negativeMultiplication.solvedRequirements.map (·.id)))
        "negative multiplication lost its exact sign or requirement order"
  | .error error => throw (IO.userError
      s!"negative integerMul did not stage exactly: {reprStr error}")

  let equality ← checkedNamed program "eqBeforeModulo"
  let equalityRoot ← returnedExpression equality
  let equalityArguments ← expectBuiltinCall equality equalityRoot .integerEq
  assertTrue (equalityArguments.length == 2)
    "integerEq lost its binary typed-IR shape"

  let spine ← checkedNamed program "typedSpine"
  let spineRoot ← returnedExpression spine
  let comparisonArguments ← expectBuiltinCall spine spineRoot .integerLt
  let (sum, difference) ← match comparisonArguments with
    | [sum, difference] => pure (sum, difference)
    | arguments => throw (IO.userError
        s!"integerLt retained {arguments.length} arguments")
  let sumArguments ← expectBuiltinCall spine sum .integerAdd
  let differenceArguments ← expectBuiltinCall spine difference .integerSub
  let literals ← match sumArguments, differenceArguments with
    | [one, two], [four, five] => pure [
        (one, .decimal "1", 1),
        (two, .decimal "2", 2),
        (four, .decimal "4", 4),
        (five, .decimal "5", 5)
      ]
    | _, _ => throw (IO.userError
        "typed comparison arithmetic lost its binary arguments")
  let mut requirements : List RequirementId := []
  for (id, source, rawValue) in literals do
    requirements := requirements ++
      [← expectIntegerLiteral spine id source rawValue]
  assertTrue (decide (spine.solvedRequirements.map (·.id) = requirements) &&
      spine.solvedRequirements.all builtinIntegerEvidence)
    "expanded comparison changed literal requirement order or evidence"

  let signature ← signatureNamed program "typedSpine"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "expanded builtins became source specialization edges"
  | result => throw (IO.userError
      s!"expanded builtin worklist did not close in one slot: {reprStr result}")

private def testWordToIntegerTypedCarrierAndWorklist : IO Unit := do
  let program ← checkedProgram expandedSource
  let modulo ← checkedNamed program "wordToModulo"
  let moduloRoot ← returnedExpression modulo
  let outerArguments ← expectBuiltinCall modulo moduloRoot .wordFromInteger
  let conversion ← match outerArguments with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"wordToModulo retained {arguments.length} outer arguments")
  let conversionArguments ← expectBuiltinCall modulo conversion .wordToInteger
  let literal ← match conversionArguments with
    | [literal] => pure literal
    | arguments => throw (IO.userError
        s!"wordToInteger retained {arguments.length} arguments")
  let literalRequirement ← expectWordLiteral modulo literal
    (.decimal (toString (Core.wordModulus + 1))) (Core.wordModulus + 1)
  assertTrue (decide (modulo.solvedRequirements.map (·.id) =
      [literalRequirement]) && modulo.solvedRequirements.all builtinWordEvidence)
    "wordToInteger did not retain exact Int<Word> literal evidence"
  match SourceCoreElaboration.evaluateStagedWord modulo.solvedRequirements
      modulo.typedBody literal with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Core.Word.ofNatModulo
          (Core.wordModulus + 1) ∧
          evaluated.consumedRequirements = [literalRequirement]))
        "public staged Word evaluator did not reduce before conversion"
  | .error error => throw (IO.userError
      s!"checked staged Word literal did not evaluate: {reprStr error}")
  match SourceCoreElaboration.evaluateStagedInteger modulo.solvedRequirements
      modulo.typedBody conversion with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (1 : Int) ∧
          evaluated.consumedRequirements = [literalRequirement]))
        "wordToInteger did not expose the modulo-reduced Word as nonnegative Int"
  | .error error => throw (IO.userError
      s!"checked wordToInteger did not evaluate: {reprStr error}")

  let roundtrip ← checkedNamed program "wordRoundtripNegative"
  let roundtripRoot ← returnedExpression roundtrip
  let roundtripOuter ← expectBuiltinCall roundtrip roundtripRoot
    .wordFromInteger
  let roundtripConversion ← match roundtripOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"roundtrip retained {arguments.length} outer arguments")
  let roundtripWord ← expectBuiltinCall roundtrip roundtripConversion
    .wordToInteger
  let nestedWordFrom ← match roundtripWord with
    | [word] => pure word
    | arguments => throw (IO.userError
        s!"roundtrip wordToInteger retained {arguments.length} arguments")
  let _ ← expectBuiltinCall roundtrip nestedWordFrom .wordFromInteger
  match SourceCoreElaboration.evaluateStagedInteger
      roundtrip.solvedRequirements roundtrip.typedBody roundtripConversion with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = Int.ofNat Core.Word.maximum.val ∧
          evaluated.value ≠ (-1 : Int) ∧
          evaluated.consumedRequirements =
            roundtrip.solvedRequirements.map (·.id)))
        "Word roundtrip incorrectly recovered the pre-modulo negative integer"
  | .error error => throw (IO.userError
      s!"checked signed Word roundtrip did not evaluate: {reprStr error}")

  let mixed ← checkedNamed program "wordLiteralArithmetic"
  let mixedRoot ← returnedExpression mixed
  let mixedOuter ← expectBuiltinCall mixed mixedRoot .wordFromInteger
  let mixedAdd ← match mixedOuter with
    | [add] => pure add
    | arguments => throw (IO.userError
        s!"mixed Word arithmetic retained {arguments.length} outer arguments")
  let mixedArguments ← expectBuiltinCall mixed mixedAdd .integerAdd
  let (mixedConversion, mixedIntegerLiteral) ← match mixedArguments with
    | [conversion, literal] => pure (conversion, literal)
    | arguments => throw (IO.userError
        s!"mixed integerAdd retained {arguments.length} arguments")
  let mixedWordArguments ← expectBuiltinCall mixed mixedConversion
    .wordToInteger
  let mixedWordLiteral ← match mixedWordArguments with
    | [literal] => pure literal
    | arguments => throw (IO.userError
        s!"mixed wordToInteger retained {arguments.length} arguments")
  let mixedWordRequirement ← expectWordLiteral mixed mixedWordLiteral
    (.decimal (toString (Core.wordModulus + 1))) (Core.wordModulus + 1)
  let mixedIntegerRequirement ← expectIntegerLiteral mixed
    mixedIntegerLiteral (.decimal "2") 2
  let mixedRequirements := [mixedWordRequirement, mixedIntegerRequirement]
  assertTrue (decide (mixed.solvedRequirements.map (·.id) =
      mixedRequirements))
    "mixed Int<Word>/Int<integer> evidence lost source order"
  match SourceCoreElaboration.evaluateStagedInteger mixed.solvedRequirements
      mixed.typedBody mixedAdd with
  | .ok evaluated =>
      assertTrue (decide (evaluated.value = (3 : Int) ∧
          evaluated.consumedRequirements = mixedRequirements))
        "mixed Word-to-integer arithmetic changed evidence consumption order"
  | .error error => throw (IO.userError
      s!"mixed Word-to-integer arithmetic did not evaluate: {reprStr error}")

  let signature ← signatureNamed program "wordToModulo"
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 1 with
  | .ok (.complete plan) =>
      assertTrue (plan.specializations.length == 1 && plan.callEdges.isEmpty)
        "wordToInteger became a source specialization edge"
  | result => throw (IO.userError
      s!"wordToInteger worklist did not close in one slot: {reprStr result}")

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

private def testExpandedPublicExecution : IO Unit := do
  let moduleId ← mainModule
  let wordCases : List (String × Core.Word) := [
    ("addHugeNegative", Core.Word.ofIntModulo (-2)),
    ("addNegatives", Core.Word.ofIntModulo (-13)),
    ("arithmeticNested", Core.Word.ofNatModulo 8),
    ("mulPower", Core.Word.zero),
    ("mulNegative", Core.Word.ofIntModulo (-15)),
    ("mulNegativeBoth", Core.Word.ofNatModulo 15),
    ("mulZero", Core.Word.zero),
    ("mulNested", Core.Word.ofNatModulo 15),
    ("wordToModulo", Core.Word.ofNatModulo 1),
    ("wordToGrouped", Core.Word.ofNatModulo 1),
    ("wordRoundtripNegative", Core.Word.maximum),
    ("wordBridgeNested", Core.Word.ofNatModulo 2),
    ("wordLiteralArithmetic", Core.Word.ofNatModulo 3)
  ]
  for (name, expected) in wordCases do
    assertPreparedExpandedWord moduleId name expected
  let boolCases : List (String × Bool) := [
    ("eqBeforeModulo", false),
    ("eqSignedExact", true),
    ("ltBeforeModulo", false),
    ("ltNegative", true),
    ("ltNegativeReverse", false),
    ("mulEqBeforeModulo", false),
    ("wordBridgeComparison", false)
  ]
  for (name, expected) in boolCases do
    assertPreparedExpandedBool moduleId name expected
  assertPreparedExpandedConditional moduleId "eqConditional" false
    (Core.Word.ofNatModulo 11) (Core.Word.ofNatModulo 22)
    (Core.Word.ofNatModulo 22)
  assertPreparedExpandedConditional moduleId "ltConditional" true
    (Core.Word.ofNatModulo 33) (Core.Word.ofNatModulo 44)
    (Core.Word.ofNatModulo 33)

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

private def testExpandedSourceDeclarationsShadowBuiltins : IO Unit := do
  let content := String.intercalate "\n" [
    "function integerAdd(left: Word, right: Word) returns (Word) {",
    "  return 40;",
    "}",
    "function integerEq(left: Word, right: Word) returns (Bool) {",
    "  return false;",
    "}",
    "function integerLt(left: Word, right: Word) returns (Bool) {",
    "  return true;",
    "}",
    "function integerMul(left: Word, right: Word) returns (Word) {",
    "  return 41;",
    "}",
    "function wordToInteger(value: Word) returns (Word) {",
    "  return value;",
    "}",
    "function shadowed() returns (Word) {",
    "  return integerEq(integerAdd(1, 2), 40) ? 9 :",
    "    (integerLt(1, 2) ? integerMul(wordToInteger(1), 2) : 42);",
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
  assertTrue (builtinCalls.isEmpty && declarationCalls.length == 5)
    "expanded source declarations did not shadow compiler builtins"
  let moduleId ← mainModule
  let shadowLimits : Limits := { limits with specializationBudget := 6 }
  match run (workspace content) (Seed.named moduleId "shadowed") []
      shadowLimits with
  | .ok (.done (.word actual) []) =>
      assertTrue (actual == Core.Word.ofNatModulo 41)
        "expanded source-declaration shadowing returned the wrong Word"
  | result => throw (IO.userError
      s!"expanded source-declaration shadowing did not execute: {reprStr result}")

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
  expectBodyError "integerAdd arity"
    "function bad() returns (integer) { return integerAdd(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerAdd 2 1
  expectBodyError "integerEq arity"
    "function bad() returns (Bool) { return integerEq(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerEq 2 1
  expectBodyError "integerLt arity"
    "function bad() returns (Bool) { return integerLt(); }"
    fun error => error == .builtinFunctionArityMismatch .integerLt 2 0
  expectBodyError "integerMul arity"
    "function bad() returns (integer) { return integerMul(1); }"
    fun error => error == .builtinFunctionArityMismatch .integerMul 2 1
  expectBodyError "wordToInteger arity"
    "function bad() returns (integer) { return wordToInteger(); }"
    fun error => error == .builtinFunctionArityMismatch .wordToInteger 1 0
  expectBodyError "integerAdd operand type"
    "function bad() returns (integer) { return integerAdd(true, 1); }"
    fun error => error matches .unification _
  expectBodyError "integerEq operand type"
    "function bad() returns (Bool) { return integerEq(true, 1); }"
    fun error => error matches .unification _
  expectBodyError "integerLt operand type"
    "function bad() returns (Bool) { return integerLt(1, false); }"
    fun error => error matches .unification _
  expectBodyError "integerMul operand type"
    "function bad() returns (integer) { return integerMul(false, 1); }"
    fun error => error matches .unification _
  expectBodyError "wordToInteger operand type"
    "function bad() returns (integer) { return wordToInteger(false); }"
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

  let expectExpandedNoFallback (name declaration body : String) : IO Unit := do
    let content := String.intercalate "\n" [declaration, body]
    match SourceInference.loadAndCheckProgram (workspace content) with
    | .error errors =>
        assertTrue (errors.any fun error => match error with
          | .body { error := .noTraitImplementation predicate, .. } =>
              predicate == ProgramSignatures.builtinIntPredicate Ty.bool
          | .body { error := .unification _, .. } => true
          | _ => false)
          s!"{name}: incompatible source declaration produced the wrong failure"
    | .ok _ => throw (IO.userError
        s!"{name}: incompatible source declaration fell through to builtin")
  expectExpandedNoFallback "integerAdd"
    "function integerAdd(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Word) { return wordFromInteger(integerAdd(1, 2)); }"
  expectExpandedNoFallback "integerEq"
    "function integerEq(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Bool) { return integerEq(1, 2); }"
  expectExpandedNoFallback "integerLt"
    "function integerLt(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Bool) { return integerLt(1, 2); }"
  expectExpandedNoFallback "integerMul"
    "function integerMul(left: Bool, right: Bool) returns (Bool) { return left; }"
    "function bad() returns (Word) { return wordFromInteger(integerMul(1, 2)); }"
  expectExpandedNoFallback "wordToInteger"
    "function wordToInteger(value: Bool) returns (Bool) { return value; }"
    "function bad() returns (Word) { return wordFromInteger(wordToInteger(1)); }"

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

  let multiplicationLeakProgram ← checkedProgram
    "function leakingMul() returns (integer) { return integerMul(2, 3); }"
  let multiplicationLeak ← checkedNamed multiplicationLeakProgram "leakingMul"
  match SourceCoreElaboration.elaborateFunction multiplicationLeak with
  | .ok _ => throw (IO.userError
      "integerMul escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site =
          .declaration multiplicationLeak.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"integerMul leakage produced the wrong error: {reprStr error}"

  let wordLeakProgram ← checkedProgram
    "function leakingWord() returns (integer) { return wordToInteger(1); }"
  let wordLeak ← checkedNamed wordLeakProgram "leakingWord"
  match SourceCoreElaboration.elaborateFunction wordLeak with
  | .ok _ => throw (IO.userError
      "wordToInteger escaped into the runtime function boundary")
  | .error error =>
      assertTrue (decide (error.site = .declaration wordLeak.declaration ∧
          error.reason = .unsupportedType Ty.integer))
        s!"wordToInteger leakage produced the wrong error: {reprStr error}"

  let localWordProgram ← checkedProgram
    "function localWord(value: Word) returns (Word) { return wordFromInteger(wordToInteger(value)); }"
  let localWord ← checkedNamed localWordProgram "localWord"
  let localRoot ← returnedExpression localWord
  let localOuter ← expectBuiltinCall localWord localRoot .wordFromInteger
  let localConversion ← match localOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"local Word fixture retained {arguments.length} outer arguments")
  let localArguments ← expectBuiltinCall localWord localConversion
    .wordToInteger
  let localReference ← match localArguments with
    | [reference] => pure reference
    | arguments => throw (IO.userError
        s!"local wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction localWord with
  | .ok _ => throw (IO.userError
      "runtime Word local was accepted by closed staged conversion")
  | .error error =>
      assertTrue (decide (error.site = .occurrence localReference.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"runtime Word local produced the wrong staged error: {reprStr error}"

  let wordOperatorProgram ← checkedProgram
    "function wordOperator() returns (Word) { return wordFromInteger(wordToInteger(1 + 2)); }"
  let wordOperator ← checkedNamed wordOperatorProgram "wordOperator"
  let operatorRoot ← returnedExpression wordOperator
  let operatorOuter ← expectBuiltinCall wordOperator operatorRoot
    .wordFromInteger
  let operatorConversion ← match operatorOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"Word operator fixture retained {arguments.length} outer arguments")
  let operatorArguments ← expectBuiltinCall wordOperator operatorConversion
    .wordToInteger
  let operatorExpression ← match operatorArguments with
    | [expression] => pure expression
    | arguments => throw (IO.userError
        s!"operator wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction wordOperator with
  | .ok _ => throw (IO.userError
      "general runtime Word operator was accepted by staged conversion")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence operatorExpression.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"runtime Word operator produced the wrong staged error: {reprStr error}"

  let sourceCallProgram ← checkedProgram (String.intercalate "\n" [
    "function sourceWord() returns (Word) { return 7; }",
    "function stagedCall() returns (Word) {",
    "  return wordFromInteger(wordToInteger(sourceWord()));",
    "}"
  ])
  let sourceCall ← checkedNamed sourceCallProgram "stagedCall"
  let sourceCallRoot ← returnedExpression sourceCall
  let sourceCallOuter ← expectBuiltinCall sourceCall sourceCallRoot
    .wordFromInteger
  let sourceCallConversion ← match sourceCallOuter with
    | [conversion] => pure conversion
    | arguments => throw (IO.userError
        s!"source-call fixture retained {arguments.length} outer arguments")
  let sourceCallArguments ← expectBuiltinCall sourceCall sourceCallConversion
    .wordToInteger
  let sourceCallExpression ← match sourceCallArguments with
    | [expression] => pure expression
    | arguments => throw (IO.userError
        s!"source-call wordToInteger retained {arguments.length} arguments")
  match SourceCoreElaboration.elaborateFunction sourceCall with
  | .ok _ => throw (IO.userError
      "ordinary Word-returning source call entered staged conversion")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence sourceCallExpression.occurrence ∧
          error.reason = .stagedWordExpressionNotClosed))
        s!"Word-returning source call produced the wrong staged error: {reprStr error}"

  let comparisonProgram ← checkedProgram
    "function dependentEq(flag: Bool) returns (Bool) { return integerEq(flag ? 1 : 2, 1); }"
  let comparison ← checkedNamed comparisonProgram "dependentEq"
  let comparisonRoot ← returnedExpression comparison
  let comparisonArguments ← expectBuiltinCall comparison comparisonRoot .integerEq
  let dependentArgument ← match comparisonArguments with
    | dependentArgument :: _ => pure dependentArgument
    | [] => throw (IO.userError
        "runtime-dependent comparison lost its first argument")
  match SourceCoreElaboration.elaborateFunction comparison with
  | .ok _ => throw (IO.userError
      "runtime-dependent staged comparison reached Semantic Core")
  | .error error =>
      assertTrue (decide (error.site =
          .occurrence dependentArgument.occurrence ∧
          error.reason = .stagedIntegerExpressionNotClosed))
        s!"runtime-dependent comparison produced the wrong error: {reprStr error}"

/-- Exercise exact signed staging, modulo projection, builtin identity,
worklist erasure, source shadowing, and inference rejection. -/
def testSourceStagedIntegerIntrinsics : IO Unit := do
  testBuiltinCatalog
  testTypedCarrierAndWorklist
  testExpandedTypedCarrierAndWorklist
  testWordToIntegerTypedCarrierAndWorklist
  testPublicExecution
  testExpandedPublicExecution
  testSourceDeclarationsShadowBuiltins
  testExpandedSourceDeclarationsShadowBuiltins
  testInferenceRejections
  testRuntimeBoundaryRejections
  IO.println "closed staged integer intrinsics GREEN"

end Tests.SourceStagedIntegerIntrinsics
