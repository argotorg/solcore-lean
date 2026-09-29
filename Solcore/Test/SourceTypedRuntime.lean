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

/-- A forged occurrence view of a non-callable value cannot claim executable
plan provenance merely because its principal value has trivial provenance. -/
private theorem nonClosureInstantiationHasNoPlanCode
    (plan : SourceSpecializationWorklist.Plan)
    (substitution : TypeSystem.Substitution) :
    ¬ (Value.instantiated substitution [] .unit).HasPlanCode plan := by
  intro code
  exact (Value.HasPlanCode.instantiated_origin code).2

/-- The public constructor theorem for an occurrence view also exposes the
exact substituted-source provenance required by indirect execution. -/
private theorem closureInstantiationExposesSubstitutedOrigin
    (plan : SourceSpecializationWorklist.Plan)
    (parameters : List SourceInference.TypedBinder) (resultType : Ty)
    (body : List SourceInference.StatementId)
    (source : SourceInference.TypedSource)
    (owner : SourceSpecialization.SpecializationKey)
    (captured : SourceTypedRuntime.Environment)
    (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (substitution : TypeSystem.Substitution)
    (code : Value.HasPlanCode
      (.closure parameters resultType body source owner captured evidence) plan) :
    Value.HasInstantiatedPlanCode
      (.closure parameters resultType body source owner captured evidence)
      substitution plan := by
  exact (Value.HasPlanCode.instantiated_origin
    (Value.HasPlanCode.instantiated substitution code)).2

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
  "function localPolymorphism(flag: Bool) returns (Word, Bool) {",
  "  let identity = lam(value) { return flag ? value : value; };",
  "  return (identity(41), identity(flag));",
  "}",
  "function genericIdentity<T>(value: T) returns (T) { return value; }",
  "trait Proof<T> {}",
  "impl Proof<Word> {}",
  "trait Eq<T> {}",
  "impl Eq<Word> where Word: Proof {}",
  "impl Eq<Bool> {}",
  "trait Mark<T> {}",
  "impl Mark<Word> {}",
  "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
  "function relay<T>(value: T) returns (T) where T: Eq { return keep(value); }",
  "function nestedConstrained(value: Word) returns (Word) { return relay(value); }",
  "function repeat<T>(value: T, count: Word) returns (T) where T: Eq {",
  "  return count == 0 ? value : repeat(value, count - 1);",
  "}",
  "function recursiveConstrained(value: Word) returns (Word) {",
  "  return repeat(value, 3);",
  "}",
  "function closureRelay<T>(value: T) returns (T) where T: Eq {",
  "  let invoke = lam(inner: T) -> T { return keep(inner); };",
  "  return invoke(value);",
  "}",
  "function closureConstrained(value: Word) returns (Word) {",
  "  return closureRelay(value);",
  "}",
  "function keepBoth<T>(value: T) returns (T) where T: Eq, T: Mark {",
  "  return value;",
  "}",
  "function relayBoth<T>(value: T) returns (T) where T: Mark, T: Eq {",
  "  return keepBoth(value);",
  "}",
  "function orderedConstrained(value: Word) returns (Word) {",
  "  return relayBoth(value);",
  "}",
  "function qualifiedLocalProof(flag: Bool) returns (Word, Bool) {",
  "  let f = lam(value) { return keep(value); };",
  "  return (f(53), f(flag));",
  "}",
  "function keepAs<T, U>(guard: T, value: U) returns (U) where T: Eq { return value; }",
  "function localProof(flag: Bool) returns (Word, Bool) {",
  "  let f = lam(value) { return keepAs(1, value); };",
  "  return (f(2), f(flag));",
  "}",
  "function localGenericCalls(flag: Bool) returns (Word, Bool) {",
  "  let applyIdentity = lam(value) { return genericIdentity(value); };",
  "  return (applyIdentity(43), applyIdentity(flag));",
  "}",
  "function localGenericAliasEscape(flag: Bool) returns (Word, Bool) {",
  "  let applyIdentity = lam(value) { return genericIdentity(value); };",
  "  let asWord: function(Word) returns(Word) = applyIdentity;",
  "  let asBool: function(Bool) returns(Bool) = applyIdentity;",
  "  return (asWord(47), asBool(flag));",
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

private def testLocalLetPolymorphism (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "localPolymorphism"
  let result := runPrepared prepared [.bool true]
  match result with
  | .done (.product (.word actual) (.bool selected)) _ =>
      assertTrue (actual == word 41 && selected)
        "one principal local lambda was not instantiated at Word and Bool"
  | other => throw (IO.userError
      s!"local let-polymorphism returned {reprStr other}")
  expectShallowHeap "local let-polymorphism" prepared.plan result

private def testQualifiedLocalLetPolymorphism
    (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "qualifiedLocalProof"
  let result := runPrepared prepared [.bool true]
  match result with
  | .done (.product (.word actual) (.bool selected)) _ =>
      assertTrue (actual == word 53 && selected)
        "qualified local scheme did not select independent Word/Bool evidence"
  | other => throw (IO.userError
      s!"qualified local let-polymorphism returned {reprStr other}")
  expectShallowHeap "qualified local let-polymorphism" prepared.plan result

private def expectWordBool (label : String) (expectedWord : Nat)
    (expectedBool : Bool) : RunResult → IO Unit
  | .done (.product (.word actualWord) (.bool actualBool)) _ =>
      assertTrue (actualWord == word expectedWord && actualBool == expectedBool)
        s!"{label} returned the wrong Word/Bool pair"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def assertContextualGenericPlan (label : String)
    (prepared : Prepared) : IO Unit := do
  assertTrue (prepared.plan.specializations.length == 3)
    s!"{label} did not retain entry plus two identity specializations"
  let edges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key)
  assertTrue (edges.length == 2)
    s!"{label} did not retain two concrete edges for the local lambda call"
  match edges with
  | [wordEdge, boolEdge] =>
      assertTrue (wordEdge.occurrence == boolEdge.occurrence)
        s!"{label} split one contextual call across different occurrences"
      assertTrue (wordEdge.callee != boolEdge.callee)
        s!"{label} collapsed Word and Bool calls to one specialization"
      let arguments := edges.map (fun edge => edge.callee.arguments)
      assertTrue (arguments.contains [.word] && arguments.contains [.bool])
        s!"{label} did not retain Word and Bool specialization keys"
  | _ => throw (IO.userError s!"{label} retained an impossible edge shape")

private def expectRuntimeFault (label : String)
    (accept : RuntimeError → Bool) : RunResult → IO Unit
  | .fault error _ =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | result => throw (IO.userError
      s!"{label} did not reject tampered metadata: {reprStr result}")

private def testContextualGenericEdgeTampering
    (prepared : Prepared) : IO Unit := do
  let wordEdges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key ∧ edge.callee.arguments = [.word])
  let wordEdge ← match wordEdges with
    | [edge] => pure edge
    | edges => throw (IO.userError
        s!"contextual generic plan retained {edges.length} Word edges")

  let duplicate := {
    prepared with
    plan := {
      prepared.plan with
      callEdges := wordEdge :: prepared.plan.callEdges
    }
  }
  expectRuntimeFault "duplicate contextual generic edge"
    (fun error => match error with
      | .duplicateCallEdge caller occurrence 2 =>
          decide (caller = prepared.key ∧ occurrence = wordEdge.occurrence)
      | _ => false)
    (runPrepared duplicate [.bool true])

  let missing := {
    prepared with
    plan := {
      prepared.plan with
      callEdges := prepared.plan.callEdges.filter fun edge =>
        decide (edge != wordEdge)
    }
  }
  expectRuntimeFault "missing contextual generic edge"
    (fun error => match error with
      | .missingCallEdge caller occurrence =>
          decide (caller = prepared.key ∧ occurrence = wordEdge.occurrence)
      | _ => false)
    (runPrepared missing [.bool true])

private def testContextualLocalGenericCalls
    (program : CheckedProgram) : IO Unit := do
  let direct ← prepareNamed program "localGenericCalls"
  assertContextualGenericPlan "contextual local generic call" direct
  let directResult := runPrepared direct [.bool true]
  expectWordBool "contextual local generic call" 43 true directResult
  expectShallowHeap "contextual local generic call" direct.plan directResult
  testContextualGenericEdgeTampering direct

  let escaped ← prepareNamed program "localGenericAliasEscape"
  assertContextualGenericPlan "ground alias escape" escaped
  let escapedResult := runPrepared escaped [.bool false]
  expectWordBool "ground alias escape" 47 false escapedResult
  expectShallowHeap "ground alias escape" escaped.plan escapedResult

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

private def expectPlanValidationFault (label : String)
    (accept : RuntimeError → Bool) : Except RuntimeError Unit → IO Unit
  | .error error =>
      assertTrue (accept error) s!"{label} reported {reprStr error}"
  | .ok () => throw (IO.userError
      s!"{label} did not reject tampered plan metadata")

private def testTamperedExecutableMetadata
    (program : CheckedProgram) : IO Unit := do
  let original ← prepareNamed program "implicitTail"
  let impostor ← prepareNamed program "loops"
  let impostorFunction ←
    match impostor.plan.specializations.filter fun specialized =>
        decide (specialized.key = impostor.key) with
    | [specialized] => pure specialized.function
    | specializations => throw (IO.userError
        s!"impostor plan retained {specializations.length} entry specializations")
  let withImpostorBody := rewriteEntryFunction original fun _ =>
    impostorFunction
  expectPreExecutionFault "specialization ownership mismatch"
    (fun error => match error with
      | .specializationOwnershipMismatch key declaration
          functionDeclaration typedBodyOwner =>
          decide (key = original.key ∧
            declaration = original.key.declaration ∧
            functionDeclaration = impostor.key.declaration ∧
            typedBodyOwner = impostor.key.declaration)
      | _ => false)
    (runPrepared withImpostorBody)

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

private def rewriteEntryExpressionAt (prepared : Prepared)
    (target : SourceInference.ExpressionId)
    (rewrite : SourceInference.ExpressionNode →
      SourceInference.ExpressionNode) : Prepared :=
  rewriteEntryNodes prepared fun nodes => nodes.map fun node =>
    match node with
    | .expression expression =>
        if expression.id == target then .expression (rewrite expression)
        else node
    | _ => node

private def rewriteEntryLetBinder (prepared : Prepared)
    (target : Resolved.LocalId)
    (rewrite : SourceInference.TypedBinder → SourceInference.TypedBinder) :
    Prepared :=
  rewriteEntryNodes prepared fun nodes => nodes.map fun node =>
    match node with
    | .statement statement@{ form := .letDecl binder initializer, .. } =>
        if binder.id == target then
          .statement { statement with
            form := .letDecl (rewrite binder) initializer }
        else
          node
    | _ => node

private structure QualifiedLocalFixture where
  prepared : Prepared
  binder : SourceInference.TypedBinder
  initializer : SourceInference.ExpressionId
  template : SourceInference.LocalSchemeRequirement
  templateSolved : SourceInference.SolvedRequirement
  call : SourceInference.ExpressionNode
  callee : SourceInference.ExpressionId
  reference : SourceInference.ExpressionNode
  actualRequirement : SourceInference.RequirementId
  actualSolved : SourceInference.SolvedRequirement

private def qualifiedLocalFixture
    (program : CheckedProgram) : IO QualifiedLocalFixture := do
  let prepared ← prepareNamed program "qualifiedLocalProof"
  let specialized ← entrySpecialization prepared
  let binder ← letBinderNamed specialized "f"
  let initializer ← match specialized.function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl candidate (some initializer), .. } =>
          if candidate.id == binder.id then some initializer else none
      | _ => none with
    | [initializer] => pure initializer
    | initializers => throw (IO.userError
        s!"qualified f retained {initializers.length} initializers")
  let template ← match binder.schemeRequirements with
    | [template] => pure template
    | requirements => throw (IO.userError
        s!"qualified f retained {requirements.length} template requirements")
  let templateSolved ← match specialized.function.solvedRequirements.filter
      fun solved => solved.id == template.templateRequirement with
    | [solved] => pure solved
    | solved => throw (IO.userError
        s!"qualified f retained {solved.length} template solutions")
  let call ← match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .call _ _ (.declaration _), .. } =>
          if node.requirements.contains template.templateRequirement then
            some node
          else
            none
      | _ => none with
    | [call] => pure call
    | calls => throw (IO.userError
        s!"qualified f retained {calls.length} template call uses")
  let callee ← match call.form with
    | .call callee _ (.declaration _) => pure callee
    | _ => throw (IO.userError "qualified template call changed form")
  let references := specialized.function.typedBody.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local id), .. } =>
        if id == binder.id then some node else none
    | _ => none
  let reference ← match references.find? fun node =>
      decide (node.rawType = .function .word .word) with
    | some reference => pure reference
    | none => throw (IO.userError "qualified f lost its Word reference")
  let actualRequirement ← match reference.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"qualified Word reference retained {requirements.length} requirements")
  let actualSolved ← match specialized.function.solvedRequirements.filter
      fun solved => solved.id == actualRequirement with
    | [solved] => pure solved
    | solved => throw (IO.userError
        s!"qualified Word reference retained {solved.length} solutions")
  pure {
    prepared, binder, initializer, template, templateSolved, call, callee, reference,
    actualRequirement, actualSolved
  }

private structure ConstrainedCallFixture where
  prepared : Prepared
  occurrence : SourceInference.ExpressionId
  requirement : SourceInference.RequirementId
  predicate : ProgramPredicate
  solved : SourceInference.SolvedRequirement
  callee : SourceSpecialization.SpecializationKey

private def constrainedCallFixture
    (program : CheckedProgram) : IO ConstrainedCallFixture := do
  let prepared ← prepareNamed program "localProof"
  let specialized ← entrySpecialization prepared
  let edges := prepared.plan.callEdges.filter fun edge =>
    decide (edge.caller = prepared.key)
  let (firstEdge, secondEdge) ← match edges with
    | [first, second] => pure (first, second)
    | edges => throw (IO.userError
        s!"localProof retained {edges.length} contextual call edges")
  assertTrue (firstEdge.occurrence == secondEdge.occurrence &&
      firstEdge.callee != secondEdge.callee &&
      edges.eraseDups.length == 2)
    "localProof did not retain two distinct edges for one call occurrence"
  let arguments := edges.map (fun edge => edge.callee.arguments)
  assertTrue (arguments.contains [.word, .word] &&
      arguments.contains [.word, .bool])
    "localProof lost its keepAs<Word, Word/Bool> specializations"
  let occurrence := firstEdge.occurrence
  let (node, instantiation) ← match
      specialized.function.typedBody.lookupExpression? occurrence with
    | some node@{ form := .call _ _ (.declaration instantiation), .. } =>
        pure (node, instantiation)
    | some node => throw (IO.userError
        s!"localProof contextual occurrence changed form: {reprStr node.form}")
    | none => throw (IO.userError
        "localProof contextual call occurrence was absent")
  let requirement ← match node.requirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"localProof call retained {requirements.length} requirements")
  let predicate ← match instantiation.predicates with
    | [predicate] => pure predicate
    | predicates => throw (IO.userError
        s!"localProof call retained {predicates.length} predicates")
  let solved ← match specialized.function.solvedRequirements.filter fun row =>
      row.id == requirement with
    | [solved] => pure solved
    | rows => throw (IO.userError
        s!"localProof retained {rows.length} solved rows for its call")
  let implementationEvidence := match solved.evidence with
    | .implementation _ => true
    | .assumption _ => false
  assertTrue (decide (solved.predicate = predicate) && implementationEvidence)
    "localProof did not retain solved implementation evidence"
  for edge in edges do
    let callee ← match prepared.plan.specializations.filter fun candidate =>
        decide (candidate.key = edge.callee) with
      | [callee] => pure callee
      | callees => throw (IO.userError
          s!"localProof retained {callees.length} copies of a constrained callee")
    assertTrue (decide (callee.assumptions = [predicate]))
      "localProof constrained callee lost its Eq<Word> assumption"
  pure {
    prepared
    occurrence
    requirement
    predicate
    solved
    callee := firstEdge.callee
  }

private def rewriteEntrySolvedEvidence (prepared : Prepared)
    (requirement : SourceInference.RequirementId)
    (evidence : SourceInference.PredicateEvidence) : Prepared :=
  rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == requirement then { solved with evidence }
      else solved
  }

private def testContextualCallRequirementValidation
    (program : CheckedProgram) : IO Unit := do
  let fixture ← constrainedCallFixture program
  let prepared := fixture.prepared
  let result := runPrepared prepared [.bool true]
  expectWordBool "contextual constrained local call" 2 true result
  expectShallowHeap "contextual constrained local call" prepared.plan result

  let missingCallRequirement := rewriteEntryExpressionAt prepared
    fixture.occurrence fun node => { node with requirements := [] }
  expectPreExecutionFault "missing direct-call requirement"
    (fun error => match error with
      | .callRequirementCountMismatch caller occurrence 1 0 =>
          decide (caller = prepared.key ∧ occurrence = fixture.occurrence)
      | _ => false)
    (runPrepared missingCallRequirement [.bool true])

  let duplicateCallRequirement := rewriteEntryExpressionAt prepared
    fixture.occurrence fun node =>
      match node.form with
      | .call callee arguments (.declaration instantiation) => {
          node with
          requirements := [fixture.requirement, fixture.requirement]
          form := .call callee arguments (.declaration {
            instantiation with
            predicates := [fixture.predicate, fixture.predicate]
          })
        }
      | _ => node
  expectPreExecutionFault "duplicate direct-call requirement"
    (fun error => match error with
      | .duplicateCallRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (runPrepared duplicateCallRequirement [.bool true])

  let missingSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.filter fun solved =>
      solved.id != fixture.requirement
  }
  expectPreExecutionFault "missing direct-call solution"
    (fun error => match error with
      | .missingSolvedRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (runPrepared missingSolved [.bool true])

  let duplicateSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := fixture.solved :: function.solvedRequirements
  }
  expectPreExecutionFault "duplicate direct-call solutions"
    (fun error => match error with
      | .duplicateSolvedRequirements caller occurrence requirement 2 =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement)
      | _ => false)
    (runPrepared duplicateSolved [.bool true])

  let wrongPredicate : ProgramPredicate := {
    fixture.predicate with subject := .bool
  }
  let predicateMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with predicate := wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call predicate mismatch"
    (fun error => match error with
      | .callRequirementPredicateMismatch caller occurrence requirement
          expected actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            expected = fixture.predicate ∧ actual = wrongPredicate)
      | _ => false)
    (runPrepared predicateMismatch [.bool true])

  let goalMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with evidence := .assumption wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call evidence-goal mismatch"
    (fun error => match error with
      | .callRequirementEvidenceGoalMismatch caller occurrence requirement
          expected actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            expected = fixture.predicate ∧ actual = wrongPredicate)
      | _ => false)
    (runPrepared goalMismatch [.bool true])

  let assumptionEvidence := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.requirement then
        { solved with evidence := .assumption fixture.predicate }
      else
        solved
  }
  expectPreExecutionFault "direct-call assumption evidence"
    (fun error => match error with
      | .unsupportedCallAssumptionEvidence caller occurrence requirement
          predicate =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            predicate = fixture.predicate)
      | _ => false)
    (runPrepared assumptionEvidence [.bool true])

  let (implementation, premise) ← match fixture.solved.evidence with
    | .implementation (.byImpl goal implementation [premise]) => do
        assertTrue (decide (goal = fixture.predicate))
          "localProof outer evidence lost its Eq<Word> goal"
        pure (implementation, premise)
    | evidence => throw (IO.userError
        s!"localProof expected one nested implementation premise, found {reprStr evidence}")
  let (premiseGoal, premiseImplementation) ← match premise with
    | .byImpl goal implementation [] => pure (goal, implementation)
    | premise => throw (IO.userError
        s!"localProof expected one premise-free Proof<Word> evidence, found {reprStr premise}")
  assertTrue (implementation != premiseImplementation &&
      decide (premiseGoal != fixture.predicate))
    "localProof did not retain distinct Eq and Proof implementation evidence"

  let wrongImplementationEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate premiseImplementation [premise])
  let wrongImplementation := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongImplementationEvidence
  expectPreExecutionFault "unselected direct-call implementation"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = premiseImplementation)
      | _ => false)
    (runPrepared wrongImplementation [.bool true])

  let missingPremiseEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation [])
  let missingPremise := rewriteEntrySolvedEvidence prepared
    fixture.requirement missingPremiseEvidence
  expectPreExecutionFault "missing direct-call evidence premise"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (runPrepared missingPremise [.bool true])

  let wrongPremiseGoal : TypedTraitResolution.Evidence :=
    .byImpl fixture.predicate premiseImplementation []
  let wrongPremiseGoalEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation
      [wrongPremiseGoal])
  let wrongPremiseGoal := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongPremiseGoalEvidence
  expectPreExecutionFault "direct-call evidence premise goal"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (runPrepared wrongPremiseGoal [.bool true])

  let wrongPremiseImplementation : TypedTraitResolution.Evidence :=
    .byImpl premiseGoal implementation []
  let wrongPremiseImplementationEvidence :
      SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.predicate implementation
      [wrongPremiseImplementation])
  let wrongPremiseImplementation := rewriteEntrySolvedEvidence prepared
    fixture.requirement wrongPremiseImplementationEvidence
  expectPreExecutionFault "direct-call evidence premise implementation"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal actual =>
          decide (caller = prepared.key ∧
            occurrence = fixture.occurrence ∧
            requirement = fixture.requirement ∧
            goal = fixture.predicate ∧ actual = implementation)
      | _ => false)
    (runPrepared wrongPremiseImplementation [.bool true])

  let constrainedSeed : Prepared := {
    prepared with
    plan := {
      prepared.plan with
      seedKeys := fixture.callee :: prepared.plan.seedKeys
    }
  }
  expectPlanValidationFault "constrained public seed"
    (fun error => match error with
      | .unresolvedAssumptions key assumptions =>
          decide (key = fixture.callee ∧ assumptions = [fixture.predicate])
      | _ => false)
    (SourceTypedRuntime.validateExecutablePlan constrainedSeed.plan)

  let constrainedReference : Prepared := {
    prepared with
    plan := {
      prepared.plan with
      referenceEdges := {
        caller := prepared.key
        occurrence := fixture.occurrence
        callee := fixture.callee
      } :: prepared.plan.referenceEdges
    }
  }
  expectPlanValidationFault "constrained first-class reference"
    (fun error => match error with
      | .unresolvedAssumptions key assumptions =>
          decide (key = fixture.callee ∧ assumptions = [fixture.predicate])
      | _ => false)
    (SourceTypedRuntime.validateExecutablePlan constrainedReference.plan)

private def specializationNamedInPlan (program : CheckedProgram)
    (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed program name
  match prepared.plan.specializations.filter fun specialized =>
      specialized.declaration == signature.id with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"`{name}` retained {specializations.length} specializations")

private def hasImplementationEvidence
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  specialized.function.solvedRequirements.any fun solved =>
    solved.evidence matches .implementation _

private def hasAssumptionEvidence
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  specialized.function.solvedRequirements.any fun solved =>
    solved.evidence matches .assumption _

/-- A closed root supplies implementation evidence to a generic relay, which
then forwards its own assumption to a second generic callee.  The recursive
case verifies that the same closed dictionary survives a self edge, and the
closure case verifies that deferred code captures the dictionary at creation
rather than borrowing it from its eventual invoker. -/
private def testRuntimeEvidenceForwarding
    (program : CheckedProgram) : IO Unit := do
  let nested ← prepareNamed program "nestedConstrained"
  let nestedRoot ← entrySpecialization nested
  let relay ← specializationNamedInPlan program nested "relay"
  let keep ← specializationNamedInPlan program nested "keep"
  assertTrue (hasImplementationEvidence nestedRoot &&
      hasAssumptionEvidence relay && relay.assumptions.length == 1 &&
      keep.assumptions.length == 1)
    "nested constrained calls lost their implementation/assumption chain"
  expectWord "nested runtime evidence forwarding" 61
    (runPrepared nested [.word (word 61)])

  let recursive ← prepareNamed program "recursiveConstrained"
  let repeated ← specializationNamedInPlan program recursive "repeat"
  let selfEdges := recursive.plan.callEdges.filter fun edge =>
    decide (edge.caller = repeated.key ∧ edge.callee = repeated.key)
  assertTrue (selfEdges.length == 1 && hasAssumptionEvidence repeated &&
      repeated.assumptions.length == 1)
    "constrained recursion lost its self edge or caller assumption"
  expectWord "recursive runtime evidence forwarding" 67
    (runPrepared recursive [.word (word 67)])
  match runPrepared recursive [.word (word 67)] 1 with
  | .outOfFuel _ => pure ()
  | result => throw (IO.userError
      s!"constrained recursion ignored its fuel boundary: {reprStr result}")

  let closure ← prepareNamed program "closureConstrained"
  let closureRelay ← specializationNamedInPlan program closure "closureRelay"
  assertTrue (hasAssumptionEvidence closureRelay &&
      closureRelay.assumptions.length == 1)
    "constrained closure lost its retained caller assumption"
  expectWord "captured runtime evidence forwarding" 71
    (runPrepared closure [.word (word 71)])

  let ordered ← prepareNamed program "orderedConstrained"
  let relayBoth ← specializationNamedInPlan program ordered "relayBoth"
  let keepBoth ← specializationNamedInPlan program ordered "keepBoth"
  assertTrue (relayBoth.assumptions.length == 2 &&
      keepBoth.assumptions.length == 2 &&
      decide (relayBoth.assumptions.reverse = keepBoth.assumptions) &&
      hasAssumptionEvidence relayBoth)
    "callee-ordered runtime evidence lost or reused caller predicate order"
  expectWord "callee-ordered runtime evidence forwarding" 79
    (runPrepared ordered [.word (word 79)])

private def testQualifiedLocalRequirementValidation
    (program : CheckedProgram) : IO Unit := do
  let fixture ← qualifiedLocalFixture program
  let prepared := fixture.prepared

  let missingActual := rewriteEntryExpressionAt prepared fixture.reference.id
    fun node => { node with requirements := [] }
  expectPreExecutionFault "missing qualified-local actual requirement"
    (fun error => match error with
      | .localSchemeRequirementCountMismatch caller occurrence binder 1 0 =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id)
      | _ => false)
    (runPrepared missingActual [.bool true])

  let missingSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.filter fun solved =>
      solved.id != fixture.actualRequirement
  }
  expectPreExecutionFault "missing qualified-local actual solution"
    (fun error => match error with
      | .missingSolvedRequirement caller occurrence requirement =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (runPrepared missingSolved [.bool true])

  let duplicateSolved := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := fixture.actualSolved :: function.solvedRequirements
  }
  expectPreExecutionFault "duplicate qualified-local actual solutions"
    (fun error => match error with
      | .duplicateSolvedRequirements caller occurrence requirement 2 =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (runPrepared duplicateSolved [.bool true])

  let wrongPredicate : ProgramPredicate := {
    fixture.actualSolved.predicate with subject := .bool
  }
  let predicateMismatch := rewriteEntryFunction prepared fun function => {
    function with
    solvedRequirements := function.solvedRequirements.map fun solved =>
      if solved.id == fixture.actualRequirement then
        { solved with predicate := wrongPredicate }
      else
        solved
  }
  expectPreExecutionFault "qualified-local actual predicate mismatch"
    (fun error => match error with
      | .callRequirementPredicateMismatch caller occurrence requirement _ actual =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement ∧ actual = wrongPredicate)
      | _ => false)
    (runPrepared predicateMismatch [.bool true])

  let assumption := rewriteEntrySolvedEvidence prepared
    fixture.actualRequirement (.assumption fixture.actualSolved.predicate)
  expectPreExecutionFault "qualified-local actual assumption evidence"
    (fun error => match error with
      | .localSchemeActualExpectedImplementation caller occurrence binder
          requirement =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id ∧
            requirement = fixture.actualRequirement)
      | _ => false)
    (runPrepared assumption [.bool true])

  let forgedEvidence : SourceInference.PredicateEvidence :=
    .implementation (.byImpl fixture.actualSolved.predicate
      (.builtin .intWord) [])
  let forged := rewriteEntrySolvedEvidence prepared fixture.actualRequirement
    forgedEvidence
  expectPreExecutionFault "forged qualified-local implementation evidence"
    (fun error => match error with
      | .callEvidenceNotSelected caller occurrence requirement goal _ =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            requirement = fixture.actualRequirement ∧
            goal = fixture.actualSolved.predicate)
      | _ => false)
    (runPrepared forged [.bool true])

  let duplicateTemplate := rewriteEntryLetBinder prepared fixture.binder.id
    fun binder => {
      binder with
      schemeRequirements := binder.schemeRequirements ++ [fixture.template]
    }
  expectPreExecutionFault "duplicate qualified-local template"
    (fun error => match error with
      | .duplicateLocalSchemeTemplateRequirement caller occurrence binder
          requirement =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id ∧
            requirement = fixture.template.templateRequirement)
      | _ => false)
    (runPrepared duplicateTemplate [.bool true])

  let unusedId : SourceInference.RequirementId := {
    index := fixture.template.templateRequirement.index + 1000000
  }
  let unusedTemplate := rewriteEntryLetBinder prepared fixture.binder.id
    fun binder => {
      binder with
      schemeRequirements := binder.schemeRequirements ++ [{
        fixture.template with templateRequirement := unusedId
      }]
    }
  expectPreExecutionFault "unused qualified-local template"
    (fun error => match error with
      | .unsupportedLocalSchemeTemplateUse caller binder requirement =>
          decide (caller = prepared.key ∧ binder = fixture.binder.id ∧
            requirement = unusedId)
      | _ => false)
    (runPrepared unusedTemplate [.bool true])

  let escapedReference := rewriteEntryFunction prepared fun function => {
    function with
    typedBody := {
      function.typedBody with
      roots := .expression fixture.reference.id :: function.typedBody.roots
    }
  }
  expectPreExecutionFault "escaped qualified-local reference"
    (fun error => match error with
      | .unsupportedQualifiedLocalReference caller occurrence binder =>
          decide (caller = prepared.key ∧ occurrence = fixture.reference.id ∧
            binder = fixture.binder.id)
      | _ => false)
    (runPrepared escapedReference [.bool true])

  let escapedCallee := rewriteEntryFunction prepared fun function => {
    function with
    typedBody := {
      function.typedBody with
      roots := .expression fixture.callee :: function.typedBody.roots
    }
  }
  expectPreExecutionFault "escaped constrained declaration reference"
    (fun error => match error with
      | .unsupportedConstrainedDeclarationReference caller call callee =>
          decide (caller = prepared.key ∧ call = fixture.call.id ∧
            callee = fixture.callee)
      | _ => false)
    (runPrepared escapedCallee [.bool true])

  let escapedInitializer := rewriteEntryFunction prepared fun function => {
    function with
    typedBody := {
      function.typedBody with
      roots := .expression fixture.initializer :: function.typedBody.roots
    }
  }
  expectPreExecutionFault "escaped qualified-local initializer"
    (fun error => match error with
      | .unsupportedQualifiedLocalInitializer caller binder initializer =>
          decide (caller = prepared.key ∧ binder = fixture.binder.id ∧
            initializer = fixture.initializer)
      | _ => false)
    (runPrepared escapedInitializer [.bool true])

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
  testLocalLetPolymorphism program
  testQualifiedLocalLetPolymorphism program
  testContextualLocalGenericCalls program
  testContextualCallRequirementValidation program
  testRuntimeEvidenceForwarding program
  testQualifiedLocalRequirementValidation program
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
