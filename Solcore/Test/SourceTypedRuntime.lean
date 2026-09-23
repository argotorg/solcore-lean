import Solcore.Frontend.SourceTypedRuntime

/-!
End-to-end regressions for the phase-7 typed-source runtime.

Every executable fixture crosses the real raw-workspace, program-checking, and
finite-specialization boundaries before it reaches `SourceTypedRuntime.run`.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntime

open Solcore Solcore.Frontend Solcore.TypeSystem

namespace Runtime

open Solcore.Frontend.SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"typed-runtime fixture failed checking: {reprStr errors}")

private def signatureNamed (program : CheckedProgram) (name : String) :
    IO ProgramFunctionSignature :=
  match program.signatures.functions.filter fun signature =>
      signature.name == name with
  | [signature] => pure signature
  | signatures => throw (IO.userError
      s!"expected one signature named `{name}`, found {signatures.length}")

private structure Prepared where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  key : SourceSpecialization.SpecializationKey

private def prepareNamed (program : CheckedProgram) (name : String)
    (budget : Nat := 32) : IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] budget with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => pure { program, plan, key }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared)
    (arguments : List Value := []) (fuel : Nat := 4096) : RunResult :=
  SourceTypedRuntime.run prepared.program.signatures prepared.plan prepared.key
    arguments fuel

private def rewriteEntryNodes (prepared : Prepared)
    (rewrite : List SourceInference.Node → List SourceInference.Node) : Prepared :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = prepared.key then
      { specialized with
        function := {
          specialized.function with
          typedBody := {
            specialized.function.typedBody with
            nodes := rewrite specialized.function.typedBody.nodes
          }
        }
      }
    else
      specialized
  { prepared with plan := { prepared.plan with specializations } }

private def rewriteEntryFunction (prepared : Prepared)
    (rewrite : SourceInference.CheckedFunction →
      SourceInference.CheckedFunction) : Prepared :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = prepared.key then
      { specialized with function := rewrite specialized.function }
    else
      specialized
  { prepared with plan := { prepared.plan with specializations } }

private def rewriteFirstExpression
    (rewrite : SourceInference.ExpressionNode → SourceInference.ExpressionNode) :
    List SourceInference.Node → List SourceInference.Node
  | [] => []
  | .expression node :: rest => .expression (rewrite node) :: rest
  | node :: rest => node :: rewriteFirstExpression rewrite rest

private def rewriteFirstIndirectCall
    (rewrite : SourceInference.IndirectCallResolution →
      SourceInference.IndirectCallResolution) :
    List SourceInference.Node → List SourceInference.Node
  | [] => []
  | .expression node :: rest =>
      match node.form with
      | .call callee arguments (.indirect metadata) =>
          .expression {
            node with
            form := .call callee arguments (.indirect (rewrite metadata))
          } :: rest
      | _ => .expression node :: rewriteFirstIndirectCall rewrite rest
  | node :: rest => node :: rewriteFirstIndirectCall rewrite rest

private def firstSingletonLambdaTail? :
    List SourceInference.Node → Option SourceInference.StatementId
  | [] => none
  | .expression node :: rest =>
      match node.form with
      | .lambda _ _ [statement] => some statement
      | _ => firstSingletonLambdaTail? rest
  | _ :: rest => firstSingletonLambdaTail? rest

/-- The surface parser intentionally requires semicolons inside lambda blocks.
This test-only rewrite starts from a checked lambda with an explicit return and
forges the equivalent resolved-carrier tail-expression shape, so the runtime
path is covered without broadening the parser contract. -/
private def rewriteFirstLambdaReturnAsImplicitTail
    (nodes : List SourceInference.Node) : List SourceInference.Node :=
  match firstSingletonLambdaTail? nodes with
  | none => nodes
  | some tail => nodes.map fun node =>
      match node with
      | .statement statement =>
          if statement.id = tail then
            match statement.form with
            | .returnStmt (some expression) =>
                .statement {
                  statement with
                  form := .expression expression false
                }
            | _ => node
          else
            node
      | _ => node

private def expectWord (label : String) (expected : Nat) : RunResult → IO Unit
  | .done (.word actual) _ =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectProxyWord (label : String) : RunResult → IO Unit
  | .done (.proxy type) _ =>
      assertTrue (decide (type = Ty.word)) s!"{label} returned the wrong proxy"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectShallowHeap (label : String)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done _ state => do
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def source : String := String.intercalate "\n" [
  "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
  "enum StagedBox { Open(integer) }",
  "function sumTree(tree: Tree<Word>) returns (Word) {",
  "  match (tree) {",
  "    case .Leaf(value) { return value; }",
  "    case .Pair(.Leaf(left), .Leaf(right)) { return left + right; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function descend(value: Word) returns (Tree<Word>) {",
  "  return value == 0 ? .Leaf(9) : descend(value - 1);",
  "}",
  "function makeNested() returns (Tree<Word>) {",
  "  return Tree.Pair(.Leaf(11), .Leaf(22));",
  "}",
  "function nominalCall() returns (Word) {",
  "  let nested: Tree<Word> = makeNested();",
  "  return sumTree(nested) + sumTree(descend(3));",
  "}",
  "function acceptTree(tree: Tree<Word>) returns (Word) {",
  "  return 13;",
  "}",
  "function acceptStagedBox(value: StagedBox) returns (Word) {",
  "  return 17;",
  "}",
  "function tupleMatch() returns (Word) {",
  "  let tree: Tree<Word> = .Leaf(7);",
  "  match (tree, true) {",
  "    case (.Leaf(value), flag) { return flag ? value : 0; }",
  "    default { return 1; }",
  "  }",
  "}",
  "function assignments() returns (Word) {",
  "  let local: Word = 5;",
  "  local += 3;",
  "  local ~=;",
  "  return local;",
  "}",
  "function mappings() returns (Word) {",
  "  let table: mapping(Word => Word);",
  "  let before: Word = table[7];",
  "  table[7] = 4;",
  "  table[7] += 3;",
  "  let nested: mapping(Word => mapping(Word => Word));",
  "  nested[1][2] = 9;",
  "  return before + table[7] + nested[1][2];",
  "}",
  "function loops() returns (Word) {",
  "  let total: Word = 0;",
  "  let i: Word = 0;",
  "  while (i < 5) {",
  "    i += 1;",
  "    if (i == 2) { continue; }",
  "    if (i == 4) { break; }",
  "    total += i;",
  "  }",
  "  for (let j: Word = 0; j < 4; j += 1) {",
  "    if (j == 1) { continue; }",
  "    if (j == 3) { break; }",
  "    total += j;",
  "  }",
  "  return total;",
  "}",
  "function sharedCapture() returns (Word) {",
  "  let captured: Word = 1;",
  "  let read = lam() -> Word { return captured; };",
  "  captured = 9;",
  "  return read();",
  "}",
  "function assignmentOrder() returns (Word) {",
  "  let order: Word = 0;",
  "  let table: mapping(Word => Word);",
  "  let indexer = lam() -> Word { order = order * 10 + 1; return 5; };",
  "  let rhs = lam() -> Word { order = order * 10 + 2; return 7; };",
  "  table[indexer()] = rhs();",
  "  return order * 100 + table[5];",
  "}",
  "function proxyValue() returns (@Word) { return @Word; }",
  "function callProduct() returns (Word) {",
  "  let f = lam(pair: (Word, Bool)) -> Word { return 1; };",
  "  return f((2, true));",
  "}",
  "function callSplit() returns (Word) {",
  "  let f = lam(left: Word, right: Bool) -> Word { return left; };",
  "  return f(2, true);",
  "}",
  "function implicitTail() returns (Word) { 40 + 2 }",
  "function closureImplicitTail() returns (Word) {",
  "  let f = lam(value: Word) -> Word { return value + 1; };",
  "  return f(41);",
  "}",
  "function spin(value: Word) returns (Word) { return spin(value); }"
]

private def testNominalConstructionAndRecursiveCalls
    (program : CheckedProgram) : IO Unit := do
  let nested ← prepareNamed program "makeNested"
  match runPrepared nested with
  | .done (.constructed _ [
        .constructed _ [.word left],
        .constructed _ [.word right]]) _ =>
      assertTrue (left == word 11 && right == word 22)
        "recursive generic enum construction changed its payloads"
  | result => throw (IO.userError
      s!"recursive generic enum construction returned {reprStr result}")
  let descend ← prepareNamed program "descend"
  match runPrepared descend [.word (word 3)] with
  | .done (.constructed _ [.word actual]) _ =>
      assertTrue (actual == word 9)
        "direct recursive call changed its nominal result"
  | result => throw (IO.userError
      s!"direct recursive nominal call returned {reprStr result}")

private def testNestedMatchingAndCalls (program : CheckedProgram) : IO Unit := do
  let nominal ← prepareNamed program "nominalCall"
  expectWord "recursive nominal call" 42 (runPrepared nominal)
  let tuple ← prepareNamed program "tupleMatch"
  expectWord "tuple/constructor/binder match" 7 (runPrepared tuple)

private def testAssignmentsMappingsAndControl
    (program : CheckedProgram) : IO Unit := do
  let assignments ← prepareNamed program "assignments"
  let expected := Core.Word.maximum.sub (word 8) |>.val
  let assignmentResult := runPrepared assignments
  expectWord "compound and bit-not assignment" expected
    assignmentResult
  expectShallowHeap "compound and bit-not assignment" assignments.plan
    assignmentResult
  let mappings ← prepareNamed program "mappings"
  let mappingResult := runPrepared mappings
  expectWord "empty and nested mapping" 16 mappingResult
  expectShallowHeap "empty and nested mapping" mappings.plan mappingResult
  let loops ← prepareNamed program "loops"
  expectWord "for/while break/continue" 6 (runPrepared loops  [] 8192)

private def testClosuresOrderProxyAndFuel
    (program : CheckedProgram) : IO Unit := do
  let capture ← prepareNamed program "sharedCapture"
  expectWord "shared-cell closure capture" 9 (runPrepared capture)
  let order ← prepareNamed program "assignmentOrder"
  expectWord "assignment target-before-RHS order" 1207
    (runPrepared order [] 8192)
  let proxy ← prepareNamed program "proxyValue"
  expectProxyWord "proxy value" (runPrepared proxy)
  let implicitTail ← prepareNamed program "implicitTail"
  expectWord "top-level implicit tail return" 42 (runPrepared implicitTail)
  let closureImplicitTail ← prepareNamed program "closureImplicitTail"
  let closureImplicitTail := rewriteEntryNodes closureImplicitTail
    rewriteFirstLambdaReturnAsImplicitTail
  expectWord "closure implicit tail return" 42
    (runPrepared closureImplicitTail)
  let spin ← prepareNamed program "spin"
  match runPrepared spin [.word (word 1)] 3 with
  | .outOfFuel _ => pure ()
  | result => throw (IO.userError
      s!"recursive low-fuel call did not exhaust: {reprStr result}")

private def treeData (program : CheckedProgram) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter fun dataType =>
      dataType.name == "Tree" with
  | [dataType] => pure dataType
  | dataTypes => throw (IO.userError
      s!"expected one Tree signature, found {dataTypes.length}")

private def leafConstructor (dataType : ProgramDataSignature) :
    IO ProgramDataConstructorSignature :=
  match dataType.constructors.filter fun constructor =>
      constructor.name == "Leaf" with
  | [constructor] => pure constructor
  | constructors => throw (IO.userError
      s!"expected one Leaf constructor, found {constructors.length}")

private def stagedBoxData (program : CheckedProgram) :
    IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter fun dataType =>
      dataType.name == "StagedBox" with
  | [dataType] => pure dataType
  | dataTypes => throw (IO.userError
      s!"expected one StagedBox signature, found {dataTypes.length}")

private def stagedBoxConstructor (dataType : ProgramDataSignature) :
    IO ProgramDataConstructorSignature :=
  match dataType.constructors.filter fun constructor =>
      constructor.name == "Open" with
  | [constructor] => pure constructor
  | constructors => throw (IO.userError
      s!"expected one StagedBox.Open constructor, found {constructors.length}")

private def testNominalInputValidation (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "acceptTree"
  let dataType ← treeData program
  let leaf ← leafConstructor dataType
  let parameter ← match dataType.parameters with
    | [parameter] => pure parameter
    | parameters => throw (IO.userError
        s!"Tree retained {parameters.length} type parameters")
  let substitution : ParameterSubstitution := [(parameter, .word)]
  let resultType := Ty.nominal dataType.id [.word]
  let legitimate : SourceInference.DataConstructorInstantiation := {
    constructor := leaf.id
    parameterSubstitution := substitution
    payloadTypes := [.word]
    resultType
  }
  expectWord "validated nominal input" 13 <| runPrepared prepared
    [.constructed legitimate [.word (word 13)]]
  let forged := {
    legitimate with
    constructor := {
      dataType := dataType.id
      constructorIndex := leaf.id.constructorIndex + 100
    }
  }
  match runPrepared prepared [.constructed forged [.word (word 13)]] with
  | .fault (.typeMismatch expected actual) _ =>
      assertTrue (decide (expected = resultType ∧ actual = some resultType))
        "forged constructor failed for an unrelated input type"
  | result => throw (IO.userError
      s!"forged constructor input was not rejected: {reprStr result}")

  let stagedPrepared ← prepareNamed program "acceptStagedBox"
  let stagedData ← stagedBoxData program
  let stagedConstructor ← stagedBoxConstructor stagedData
  let stagedResultType := Ty.nominal stagedData.id []
  let stagedInstantiation : SourceInference.DataConstructorInstantiation := {
    constructor := stagedConstructor.id
    parameterSubstitution := []
    payloadTypes := stagedConstructor.payloadTypes
    resultType := stagedResultType
  }
  match runPrepared stagedPrepared
      [.constructed stagedInstantiation [.integer 13]] with
  | .fault (.unsupportedStagedInput expected) { heap := [] } =>
      assertTrue (decide (expected = stagedResultType))
        "staged constructor input lost its authoritative nominal type"
  | .fault error state => throw (IO.userError
      s!"staged constructor input mutated state before rejection: {reprStr error}, {reprStr state}")
  | result => throw (IO.userError
      s!"staged constructor input was not rejected: {reprStr result}")

private def expectPreExecutionFault (label : String)
    (accept : RuntimeError → Bool) : RunResult → IO Unit
  | .fault error { heap := [] } =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | .fault error state => throw (IO.userError
      s!"{label} mutated state before rejecting metadata: {reprStr error}, {reprStr state}")
  | result => throw (IO.userError
      s!"{label} did not reject tampered metadata: {reprStr result}")

private def testTamperedExecutableMetadata
    (program : CheckedProgram) : IO Unit := do
  let fakeRequirement : SourceInference.RequirementId := { index := 1000000 }
  let proxy ← prepareNamed program "proxyValue"
  let withRequirement := rewriteEntryNodes proxy <| rewriteFirstExpression
    fun node => { node with requirements := [fakeRequirement] }
  expectPreExecutionFault "unsupported expression requirement"
    (fun error => error == .unsupportedRequirements [fakeRequirement])
    (runPrepared withRequirement)

  let fakeCoercion : SourceInference.CoercionStep := {
    requirement := fakeRequirement
    source := .word
    target := .word
  }
  let withResultCoercion := rewriteEntryNodes proxy <| rewriteFirstExpression
    fun node => { node with coercions := [fakeCoercion] }
  expectPreExecutionFault "unsupported result coercion"
    (fun error => error matches .unsupportedExpressionCoercions _)
    (runPrepared withResultCoercion)

  let capture ← prepareNamed program "sharedCapture"
  let withArgumentCoercion := rewriteEntryNodes capture <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCoercions := [fakeCoercion]
    }
  expectPreExecutionFault "unsupported indirect argument coercion"
    (fun error => error matches .unsupportedIndirectCoercions _)
    (runPrepared withArgumentCoercion)

  let inconsistentResult := rewriteEntryFunction proxy fun function =>
    { function with inferredBodyType := .bool }
  expectPreExecutionFault "inconsistent inferred result type"
    (fun error => match error with
      | .inferredResultTypeMismatch key declared inferred =>
          decide (key = proxy.key ∧ declared = .proxy .word ∧ inferred = .bool)
      | _ => false)
    (runPrepared inconsistentResult)

private def testIndirectArgumentCountMetadata
    (program : CheckedProgram) : IO Unit := do
  let product ← prepareNamed program "callProduct"
  let forgedProduct := rewriteEntryNodes product <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCount := 2
    }
  expectPreExecutionFault "single product argument count"
    (fun error => match error with
      | .argumentArityMismatch 2 1 => true
      | _ => false)
    (runPrepared forgedProduct)

  let split ← prepareNamed program "callSplit"
  let forgedSplit := rewriteEntryNodes split <|
    rewriteFirstIndirectCall fun metadata => {
      metadata with argumentCount := 1
    }
  expectPreExecutionFault "multiple argument count"
    (fun error => match error with
      | .argumentArityMismatch 1 2 => true
      | _ => false)
    (runPrepared forgedSplit)

private def letBinderNamed
    (specialized : SourceSpecialization.SpecializedFunction) (name : String) :
    IO SourceInference.TypedBinder :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder _, .. } =>
          if binder.name == name then some binder else none
      | _ => none with
  | [binder] => pure binder
  | binders => throw (IO.userError
      s!"expected one let binder named `{name}`, found {binders.length}")

private def entrySpecialization (prepared : Prepared) :
    IO SourceSpecialization.SpecializedFunction :=
  match prepared.plan.specializations.filter fun specialized =>
      decide (specialized.key = prepared.key) with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"entry retained {specializations.length} specializations")

private def testAssignmentRootsAreDeferred
    (program : CheckedProgram) : IO Unit := do
  let assignments ← prepareNamed program "assignments"
  let specialized ← entrySpecialization assignments
  let localBinder ← letBinderNamed specialized "local"
  assertTrue
    (specialized.stageAnalysis.binderStage? localBinder.id ==
      some SourceStageAnalysis.Stage.deferred)
    "a directly assigned local retained a non-deferred stage"

  let capture ← prepareNamed program "sharedCapture"
  let specialized ← entrySpecialization capture
  let captured ← letBinderNamed specialized "captured"
  assertTrue
    (specialized.stageAnalysis.binderStage? captured.id ==
      some SourceStageAnalysis.Stage.deferred)
    "a closure-captured assignment root retained a non-deferred stage"

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testNominalConstructionAndRecursiveCalls program
  testNestedMatchingAndCalls program
  testAssignmentsMappingsAndControl program
  testClosuresOrderProxyAndFuel program
  testNominalInputValidation program
  testTamperedExecutableMetadata program
  testIndirectArgumentCountMetadata program
  testAssignmentRootsAreDeferred program
  IO.println "phase-7 typed-source runtime GREEN"

end Runtime

/-- Exercise the phase-7 execution surface through its real frontend and
specialization plan. -/
def testSourceTypedRuntime : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntime
