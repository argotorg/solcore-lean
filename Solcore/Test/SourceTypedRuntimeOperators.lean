import Solcore.Frontend.SourceTypedRuntime
import Solcore.Frontend.SourceCompiler

/-!
Focused end-to-end regressions for evidence-selected unary and binary methods
in the typed-source runtime.

The fixtures cross raw workspace checking and finite specialization before
execution.  They also exercise method-local mutation, helper closure, caller-
owned method predicates, result coercion, and rejection before heap mutation.
-/

set_option autoImplicit false

namespace Tests.SourceTypedRuntimeOperators

open Solcore Solcore.Frontend Solcore.TypeSystem
open Solcore.Frontend.SourceCompiler

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

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError "invalid typed-runtime operator module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"typed-runtime operator fixture failed checking: {reprStr errors}")

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

private def prepareNamed (program : CheckedProgram) (name : String) :
    IO Prepared := do
  let signature ← signatureNamed program name
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 64 with
  | .ok (.complete plan) =>
      match plan.seedKeys with
      | [key] => pure { program, plan, key }
      | keys => throw (IO.userError
          s!"`{name}` retained {keys.length} seed keys")
  | .ok outcome => throw (IO.userError
      s!"`{name}` specialization did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"`{name}` specialization failed: {reprStr error}")

private def runPrepared (prepared : Prepared) : RunResult :=
  SourceTypedRuntime.run prepared.program prepared.plan prepared.key [] 8192

private def expectWordAndShallowHeap (label : String) (expected : Nat)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.word actual) state => do
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectBoolAndShallowHeap (label : String) (expected : Bool)
    (plan : SourceSpecializationWorklist.Plan) : RunResult → IO Unit
  | .done (.bool actual) state => do
      assertTrue (actual == expected) s!"{label} returned the wrong Bool"
      for cell in state.heap do
        match cell.value with
        | none => pure ()
        | some value =>
            assertTrue (decide (value.type? plan = some cell.type))
              s!"{label} left an initialized cell with a mismatched type"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def source : String := String.intercalate "\n" [
  "trait Witness<T> {}",
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T) where T: Witness;",
  "}",
  "trait BitNot<T> {",
  "  function bnot(value: T) returns (T) where T: Witness;",
  "}",
  "trait Eq<T> {",
  "  function eq(left: T, right: T) returns (Bool) where T: Witness;",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "enum Token { A, B, C }",
  "impl Witness<Token> {}",
  "impl Witness<Word> {}",
  "function rotate(value: Token) returns (Token) {",
  "  match (value) {",
  "    case .A { return .B; }",
  "    case .B { return .C; }",
  "    default { return .A; }",
  "  }",
  "}",
  "impl Add<Token> {",
  "  function add(left: Token, right: Token) returns (Token)",
  "      where Token: Witness {",
  "    let scratch: mapping(Word => Bool);",
  "    scratch[0] = false;",
  "    scratch[0] = true;",
  "    return scratch[0] ? rotate(right) : left;",
  "  }",
  "}",
  "impl BitNot<Token> {",
  "  function bnot(value: Token) returns (Token)",
  "      where Token: Witness {",
  "    let result: Token = value;",
  "    result = rotate(result);",
  "    return result;",
  "  }",
  "}",
  "impl Eq<Token> {",
  "  function eq(left: Token, right: Token) returns (Bool)",
  "      where Token: Witness {",
  "    return true;",
  "  }",
  "}",
  "impl Eq<Word> {",
  "  function eq(left: Word, right: Word) returns (Bool)",
  "      where Word: Witness {",
  "    return false;",
  "  }",
  "}",
  "impl Coerce<Token, Word> {",
  "  function coerce(value: Token) returns (Word) {",
  "    match (value) {",
  "      case .C { return 59; }",
  "      default { return 0; }",
  "    }",
  "  }",
  "}",
  "function viaAdd<T>(left: T, right: T) returns (T)",
  "    where T: Add, T: Witness {",
  "  return left + right;",
  "}",
  "function viaBitNot<T>(value: T) returns (T)",
  "    where T: BitNot, T: Witness {",
  "  return ~value;",
  "}",
  "function viaEq<T>(left: T, right: T) returns (Bool)",
  "    where T: Eq, T: Witness {",
  "  return left == right;",
  "}",
  "function binaryEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  let result: Token = viaAdd(left, right);",
  "  match (result) {",
  "    case .C { return 31; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function unaryEntry() returns (Word) {",
  "  let value: Token = .C;",
  "  let result: Token = viaBitNot(value);",
  "  match (result) {",
  "    case .A { return 41; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function equalityEntry() returns (Bool) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return viaEq(left, right);",
  "}",
  "function wordEqualityEntry() returns (Bool) {",
  "  let left: Word = 7;",
  "  let right: Word = 7;",
  "  return viaEq(left, right);",
  "}",
  "function coercedOperatorEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return left + right;",
  "}"
]

private def specializationNamed (prepared : Prepared) (name : String) :
    IO SourceSpecialization.SpecializedFunction := do
  let signature ← signatureNamed prepared.program name
  match prepared.plan.specializations.filter fun specialized =>
      decide (specialized.key.declaration = signature.id) with
  | [specialized] => pure specialized
  | specializations => throw (IO.userError
      s!"expected one `{name}` specialization, found {specializations.length}")

private def addNode
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO SourceInference.ExpressionNode :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .binary _ .add _, .. } => some node
      | _ => none with
  | [node] => pure node
  | nodes => throw (IO.userError
      s!"expected one selected addition, found {nodes.length}")

private def equalityNode
    (specialized : SourceSpecialization.SpecializedFunction) :
    IO SourceInference.ExpressionNode :=
  match specialized.function.typedBody.nodes.filterMap fun
      | .expression node@{ form := .binary _ .equal _, .. } => some node
      | _ => none with
  | [node] => pure node
  | nodes => throw (IO.userError
      s!"expected one selected equality, found {nodes.length}")

private def exactSolved (specialized : SourceSpecialization.SpecializedFunction)
    (requirement : SourceInference.RequirementId) :
    IO SourceInference.SolvedRequirement :=
  match specialized.function.solvedRequirements.filter fun solved =>
      solved.id == requirement with
  | [solved] => pure solved
  | solved => throw (IO.userError
      s!"expected one solved requirement, found {solved.length}")

private def predicateTraitName? (program : CheckedProgram)
    (predicate : ProgramPredicate) : Option String :=
  match predicate.trait with
  | .builtin _ => none
  | .declaration id =>
      (program.signatures.traits.find? fun trait =>
        decide (trait.id = id)).map (fun trait => trait.name)

private structure AddAssumptionFixture where
  prepared : Prepared
  specialized : SourceSpecialization.SpecializedFunction
  node : SourceInference.ExpressionNode
  primaryRequirement : SourceInference.RequirementId
  methodRequirement : SourceInference.RequirementId
  primarySolved : SourceInference.SolvedRequirement
  methodSolved : SourceInference.SolvedRequirement

private def addAssumptionFixture (program : CheckedProgram) :
    IO AddAssumptionFixture := do
  let prepared ← prepareNamed program "binaryEntry"
  let specialized ← specializationNamed prepared "viaAdd"
  let node ← addNode specialized
  let (primaryRequirement, methodRequirement) ← match node.requirements with
    | [primary, method] => pure (primary, method)
    | requirements => throw (IO.userError
        s!"selected addition retained {requirements.length} requirements")
  let primarySolved ← exactSolved specialized primaryRequirement
  let methodSolved ← exactSolved specialized methodRequirement
  let primaryAssumption := match primarySolved.evidence with
    | .assumption predicate => predicate == primarySolved.predicate
    | .implementation _ => false
  let methodAssumption := match methodSolved.evidence with
    | .assumption predicate => predicate == methodSolved.predicate
    | .implementation _ => false
  assertTrue (primaryAssumption && methodAssumption &&
      predicateTraitName? program primarySolved.predicate == some "Add" &&
      predicateTraitName? program methodSolved.predicate == some "Witness")
    "generic addition did not retain Add then Witness caller assumptions"
  pure {
    prepared
    specialized
    node
    primaryRequirement
    methodRequirement
    primarySolved
    methodSolved
  }

private def rewriteSpecializationFunction (prepared : Prepared)
    (key : SourceSpecialization.SpecializationKey)
    (rewrite : SourceInference.CheckedFunction → SourceInference.CheckedFunction) :
    Prepared :=
  let specializations := prepared.plan.specializations.map fun specialized =>
    if specialized.key = key then
      { specialized with function := rewrite specialized.function }
    else
      specialized
  { prepared with plan := { prepared.plan with specializations } }

private def rewriteSpecializationExpression (prepared : Prepared)
    (key : SourceSpecialization.SpecializationKey)
    (target : SourceInference.ExpressionId)
    (rewrite : SourceInference.ExpressionNode →
      SourceInference.ExpressionNode) : Prepared :=
  rewriteSpecializationFunction prepared key fun function => {
    function with
    typedBody := {
      function.typedBody with
      nodes := function.typedBody.nodes.map fun node =>
        match node with
        | .expression expression =>
            if expression.id == target then .expression (rewrite expression)
            else node
        | .statement _ => node
    }
  }

private def expectSentinelFault (label : String)
    (accept : RuntimeError → Bool) : RunResult → IO Unit
  | .fault error { heap := [{ type := actualType, value := none }] } => do
      assertTrue (accept error) s!"{label} reported {reprStr error}"
      assertTrue (actualType == Ty.word)
        s!"{label} changed the sentinel type to {reprStr actualType}"
  | .fault error state => throw (IO.userError
      s!"{label} changed the initial state: {reprStr error}, {reprStr state}")
  | result => throw (IO.userError
      s!"{label} did not reject before execution: {reprStr result}")

private def runTampered (prepared : Prepared) : RunResult :=
  let initialState : RuntimeState := {
    heap := [{ type := .word, value := none }]
  }
  SourceTypedRuntime.runWithValidationFuel prepared.program prepared.plan
    prepared.key [] 4096 8192 initialState

private def testSelectedOperatorMethods (program : CheckedProgram) : IO Unit := do
  let binary ← prepareNamed program "binaryEntry"
  expectWordAndShallowHeap "selected binary operator method" 31 binary.plan
    (runPrepared binary)
  let unary ← prepareNamed program "unaryEntry"
  expectWordAndShallowHeap "selected unary operator method" 41 unary.plan
    (runPrepared unary)
  let equality ← prepareNamed program "equalityEntry"
  expectBoolAndShallowHeap "selected Bool-result operator method" true
    equality.plan (runPrepared equality)
  let wordEquality ← prepareNamed program "wordEqualityEntry"
  expectBoolAndShallowHeap "selected Word equality override" false
    wordEquality.plan (runPrepared wordEquality)

private def testOperatorResultCoercion (program : CheckedProgram) : IO Unit := do
  let prepared ← prepareNamed program "coercedOperatorEntry"
  expectWordAndShallowHeap "operator raw result followed by Coerce" 59
    prepared.plan (runPrepared prepared)

private def testPublicCompiler (program : CheckedProgram) : IO Unit := do
  let moduleId ← mainModule
  let compileOptions : CompileOptions := {
    specializationBudget := 64
    stagingFuel := 256
  }
  let compiled ← match compileChecked program
      (Seed.named moduleId "binaryEntry") compileOptions with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError
        s!"public operator compilation failed: {reprStr error}")
  assertTrue (decide (compiled.backend = .core))
    "stateful selected operator did not choose the Core backend"
  let runOptions : RunOptions := {
    inputValidationFuel := 64
    executionFuel := 8192
  }
  match compiled.runCore [] runOptions with
  | .ok (.coreLanguageResult (.succeeded (.word actual) store)) => do
      assertTrue (actual == word 31 && !store.isEmpty)
        "public stateful operator execution lost its result or heap effects"
  | result => throw (IO.userError
      s!"public stateful operator execution returned {reprStr result}")

private def testOperatorPreflight (program : CheckedProgram) : IO Unit := do
  let fixture ← addAssumptionFixture program
  let missingMethodRequirement := rewriteSpecializationExpression
    fixture.prepared fixture.specialized.key fixture.node.id fun node =>
      { node with requirements := [fixture.primaryRequirement] }
  expectSentinelFault "missing binary method requirement"
    (fun error => match error with
      | .binaryRequirementCountMismatch caller occurrence 2 1 =>
          decide (caller = fixture.specialized.key ∧
            occurrence = fixture.node.id)
      | _ => false)
    (runTampered missingMethodRequirement)

  let mismatchedEvidence := rewriteSpecializationFunction fixture.prepared
    fixture.specialized.key fun function => {
      function with
      solvedRequirements := function.solvedRequirements.map fun solved =>
        if solved.id == fixture.methodRequirement then
          { solved with evidence := .assumption fixture.primarySolved.predicate }
        else
          solved
    }
  expectSentinelFault "mismatched binary method evidence"
    (fun error => match error with
      | .callRequirementEvidenceGoalMismatch caller occurrence requirement
          expected actual =>
          decide (caller = fixture.specialized.key ∧
            occurrence = fixture.node.id ∧
            requirement = fixture.methodRequirement ∧
            expected = fixture.methodSolved.predicate ∧
            actual = fixture.primarySolved.predicate)
      | _ => false)
    (runTampered mismatchedEvidence)

  let equalityPrepared ← prepareNamed program "equalityEntry"
  let equalitySpecialized ← specializationNamed equalityPrepared "viaEq"
  let equality ← equalityNode equalitySpecialized
  let equalitySubject ← match equality.requirements with
    | primary :: _ => do
        let solved ← exactSolved equalitySpecialized primary
        pure solved.predicate.subject
    | [] => throw (IO.userError
        "selected equality retained no primary requirement")
  let strippedEquality := rewriteSpecializationExpression equalityPrepared
    equalitySpecialized.key equality.id fun node =>
      { node with requirements := [] }
  expectSentinelFault "stripped custom equality requirements"
    (fun error => match error with
      | .runtimeBinaryInputTypesMismatch caller occurrence expected actual =>
          decide (caller = equalitySpecialized.key ∧
            occurrence = equality.id ∧
            expected = [Ty.word, Ty.word] ∧
            actual = [equalitySubject, equalitySubject])
      | _ => false)
    (runTampered strippedEquality)

  let wordEqualityPrepared ← prepareNamed program "wordEqualityEntry"
  let wordEqualitySpecialized ← specializationNamed wordEqualityPrepared "viaEq"
  let wordEquality ← equalityNode wordEqualitySpecialized
  let wordRequirement ← match wordEquality.requirements with
    | [primary, _method] => pure primary
    | requirements => throw (IO.userError
        s!"specialized Word equality retained {requirements.length} requirements")
  let wordSolved ← exactSolved wordEqualitySpecialized wordRequirement
  assertTrue (decide (wordSolved.predicate.subject = Ty.word))
    "generic equality did not specialize its trait requirement to Word"
  let strippedWordEquality := rewriteSpecializationExpression
    wordEqualityPrepared wordEqualitySpecialized.key wordEquality.id fun node =>
      { node with requirements := [] }
  expectSentinelFault "stripped specialized Word equality requirements"
    (fun error => match error with
      | .nonCanonicalInputPlan => true
      | _ => false)
    (runTampered strippedWordEquality)

private def testAll : IO Unit := do
  let program ← checkedProgram source
  testSelectedOperatorMethods program
  testOperatorPreflight program
  testOperatorResultCoercion program
  testPublicCompiler program
  IO.println "typed-source runtime operators GREEN"

end Runtime

def testSourceTypedRuntimeOperators : IO Unit :=
  Runtime.testAll

end Tests.SourceTypedRuntimeOperators
