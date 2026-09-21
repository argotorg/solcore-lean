import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceStageAnalysis

/-!
Executable regressions for scope-aware source-stage classification.

The fixture deliberately observes binders through their stable local IDs and
expressions through their occurrence IDs.  It therefore checks the semantic
sidecar without relying on the incidental order of the typed-source node table.
-/

set_option autoImplicit false

namespace Tests.SourceStageClassification

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceStageAnalysis

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def fixtureSource : String := String.intercalate "\n" [
  "function plain(value: Word) returns (Word) { return value; }",
  "function staged(comptime required: Bool, flexible: Word) returns (comptime<Word>) { return flexible; }",
  "function integerResult(value: Word) returns (integer) { return 1; }",
  "function classify(comptime fixed: Word, runtime: Word, flag: Bool) returns (Word) {",
  "  let ct = 1;",
  "  let ctAlias = fixed;",
  "  let runtimeAlias = runtime;",
  "  let runtimeAlias2 = runtimeAlias;",
  "  let deferred = plain(1);",
  "  let deferredAlias = deferred;",
  "  let stagedCt = staged(true, 2);",
  "  let stagedDeferred = staged(true, runtime);",
  "  let implicitCt = integerResult(ct);",
  "  let implicitDeferred = integerResult(runtime);",
  "  let groupRuntime: Word = (runtime);",
  "  let unaryCt: Word = ~ct;",
  "  let binaryCt: Word = ct + 1;",
  "  let binaryRuntime: Word = runtime + 1;",
  "  let tupleCt = (ct, stagedCt);",
  "  let tupleDeferred = (ct, deferred);",
  "  let tupleRuntime = (deferred, runtimeAlias);",
  "  let condCt = true ? ct : stagedCt;",
  "  let condDeferred = true ? ct : deferred;",
  "  let condRuntime = true ? ct : runtimeAlias;",
  "  let runtimeGuard = flag ? ct : stagedCt;",
  "  return runtimeAlias2;",
  "}",
  "function lambdaStages() returns (Word) {",
  "  let stagedLambda = lam(comptime value: Word) -> Word { return value; };",
  "  let runtimeLambda = lam(value: Word) -> Word { return value; };",
  "  return 0;",
  "}",
  "function matchStages(tag: Word, zero: Word, other: Word) returns (Word) {",
  "  match (tag) {",
  "    case 0 { return zero; }",
  "    case _ { return other; }",
  "  }",
  "}"
]

private def checkedProgram : IO CheckedProgram := do
  match checkProgram (workspace fixtureSource) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"source-stage fixture failed checking: {reprStr errors}")

private def functionNamed (program : CheckedProgram) (name : String) :
    IO CheckedFunction := do
  let signatures := program.signatures.functions.filter fun signature =>
    signature.name == name
  let signature ← match signatures with
    | [signature] => pure signature
    | _ => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let functions := program.functions.filter fun function =>
    function.declaration == signature.id
  match functions with
  | [function] => pure function
  | _ => throw (IO.userError
      s!"expected one checked body named `{name}`, found {functions.length}")

private def analyzeOrThrow (label : String) (function : CheckedFunction) :
    IO Analysis := do
  match analyzeFunction function with
  | .ok analysis => pure analysis
  | .error error => throw (IO.userError
      s!"{label}: source-stage analysis failed: {reprStr error}")

private def expectAnalysisError (label : String)
    (actual : Except SourceStageAnalysis.Error Analysis)
    (expected : SourceStageAnalysis.Error) : IO Unit :=
  match actual with
  | .ok analysis => throw (IO.userError
      s!"{label}: malformed typed source was accepted: {reprStr analysis}")
  | .error error =>
      assertTrue (decide (error = expected))
        s!"{label}: expected {reprStr expected}, found {reprStr error}"

private def inputNamed (function : CheckedFunction) (name : String) :
    IO TypedBinder :=
  match function.typedBody.inputs.filter fun binder => binder.name == name with
  | [binder] => pure binder
  | binders => throw (IO.userError
      s!"expected one input named `{name}`, found {binders.length}")

private def initializedLetNamed (function : CheckedFunction) (name : String) :
    IO (TypedBinder × ExpressionId) := do
  let bindings := function.typedBody.nodes.filterMap fun
    | .statement statement =>
        match statement.form with
        | .letDecl binder (some initializer) =>
            if binder.name == name then some (binder, initializer) else none
        | _ => none
    | .expression _ => none
  match bindings with
  | [binding] => pure binding
  | _ => throw (IO.userError
      s!"expected one initialized let named `{name}`, found {bindings.length}")

private def expectBinderStage (label : String) (analysis : Analysis)
    (binder : TypedBinder) (expected : Stage) : IO Unit :=
  assertTrue (analysis.binderStage? binder.id == some expected)
    s!"{label}: expected binder stage {reprStr expected}, found {reprStr (analysis.binderStage? binder.id)}"

private def expectExpressionStage (label : String) (analysis : Analysis)
    (expression : ExpressionId) (expected : Stage) : IO Unit :=
  assertTrue (analysis.expressionStage? expression == some expected)
    s!"{label}: expected expression stage {reprStr expected}, found {reprStr (analysis.expressionStage? expression)}"

private def expectInputStage (function : CheckedFunction) (analysis : Analysis)
    (name : String) (expected : Stage) : IO Unit := do
  let binder ← inputNamed function name
  expectBinderStage s!"input `{name}`" analysis binder expected

private def expectLetStage (function : CheckedFunction) (analysis : Analysis)
    (name : String) (expected : Stage) : IO Unit := do
  let (binder, initializer) ← initializedLetNamed function name
  expectBinderStage s!"let `{name}`" analysis binder expected
  expectExpressionStage s!"initializer of `{name}`" analysis initializer expected

private def expectCallCalleeDeferred (function : CheckedFunction)
    (analysis : Analysis) (name : String) : IO Unit := do
  let (_, initializer) ← initializedLetNamed function name
  let node ← match function.typedBody.lookupExpression? initializer with
    | some node => pure node
    | none => throw (IO.userError
        s!"initializer of `{name}` is absent from the typed source")
  let callee ← match node.form with
    | .call callee _ _ => pure callee
    | form => throw (IO.userError
        s!"initializer of `{name}` is not a call: {reprStr form}")
  expectExpressionStage s!"callee reference of `{name}`" analysis callee
    .deferred

private structure LambdaObservation where
  expression : ExpressionId
  parameter : TypedBinder
  returned : ExpressionId

private def lambdaLetNamed (function : CheckedFunction) (name : String) :
    IO LambdaObservation := do
  let (_, initializer) ← initializedLetNamed function name
  let node ← match function.typedBody.lookupExpression? initializer with
    | some node => pure node
    | none => throw (IO.userError
        s!"initializer of `{name}` is absent from the typed source")
  let (parameter, body) ← match node.form with
    | .lambda [parameter] _ body => pure (parameter, body)
    | form => throw (IO.userError
        s!"initializer of `{name}` is not a unary lambda: {reprStr form}")
  let returned ← match body with
    | [statement] =>
        match function.typedBody.lookupStatement? statement with
        | some { form := .returnStmt (some returned), .. } => pure returned
        | some statement => throw (IO.userError
            s!"body of `{name}` is not a value return: {reprStr statement.form}")
        | none => throw (IO.userError
            s!"body statement of `{name}` is absent from the typed source")
    | statements => throw (IO.userError
        s!"expected one body statement for `{name}`, found {statements.length}")
  pure { expression := initializer, parameter, returned }

private def testJoin : IO Unit := do
  assertTrue (Stage.join [] == .comptime)
    "the empty stage join was not comptime"
  assertTrue (Stage.join [.comptime, .comptime] == .comptime)
    "an all-comptime stage join was not comptime"
  assertTrue (Stage.join [.comptime, .deferred] == .deferred)
    "a mixed comptime/deferred stage join was not deferred"
  assertTrue (Stage.join [.deferred, .runtime] == .runtime)
    "a stage join containing runtime was not runtime"

private def testInputClassification (program : CheckedProgram) : IO Unit := do
  let plain ← functionNamed program "plain"
  let plainAnalysis ← analyzeOrThrow "plain" plain
  expectInputStage plain plainAnalysis "value" .runtime

  let staged ← functionNamed program "staged"
  let stagedAnalysis ← analyzeOrThrow "staged" staged
  expectInputStage staged stagedAnalysis "required" .comptime
  expectInputStage staged stagedAnalysis "flexible" .comptime

  let integerResult ← functionNamed program "integerResult"
  let integerResultAnalysis ← analyzeOrThrow "integerResult" integerResult
  expectInputStage integerResult integerResultAnalysis "value" .comptime

  let classify ← functionNamed program "classify"
  let classifyAnalysis ← analyzeOrThrow "classify" classify
  expectInputStage classify classifyAnalysis "fixed" .comptime
  expectInputStage classify classifyAnalysis "runtime" .runtime
  expectInputStage classify classifyAnalysis "flag" .runtime

private def testLetAndCallClassification
    (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let analysis ← analyzeOrThrow "classify" function

  expectLetStage function analysis "ct" .comptime
  expectLetStage function analysis "ctAlias" .comptime
  expectLetStage function analysis "runtimeAlias" .runtime
  expectLetStage function analysis "runtimeAlias2" .runtime
  expectLetStage function analysis "deferred" .deferred
  expectLetStage function analysis "deferredAlias" .deferred

  expectLetStage function analysis "stagedCt" .comptime
  expectLetStage function analysis "stagedDeferred" .deferred
  expectLetStage function analysis "implicitCt" .comptime
  expectLetStage function analysis "implicitDeferred" .deferred
  expectLetStage function analysis "groupRuntime" .runtime
  expectLetStage function analysis "unaryCt" .comptime
  expectLetStage function analysis "binaryCt" .comptime
  expectLetStage function analysis "binaryRuntime" .runtime
  expectCallCalleeDeferred function analysis "deferred"
  expectCallCalleeDeferred function analysis "stagedCt"
  expectCallCalleeDeferred function analysis "stagedDeferred"
  expectCallCalleeDeferred function analysis "implicitCt"

private def testJoinClassification (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let analysis ← analyzeOrThrow "classify" function

  expectLetStage function analysis "tupleCt" .comptime
  expectLetStage function analysis "tupleDeferred" .deferred
  expectLetStage function analysis "tupleRuntime" .runtime
  expectLetStage function analysis "condCt" .comptime
  expectLetStage function analysis "condDeferred" .deferred
  expectLetStage function analysis "condRuntime" .runtime
  expectLetStage function analysis "runtimeGuard" .runtime

private def testLambdaClassification (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "lambdaStages"
  let analysis ← analyzeOrThrow "lambdaStages" function
  let staged ← lambdaLetNamed function "stagedLambda"
  let runtime ← lambdaLetNamed function "runtimeLambda"

  assertTrue staged.parameter.comptime
    "an explicit comptime lambda marker was not retained on its typed binder"
  assertTrue (!runtime.parameter.comptime)
    "an ordinary lambda parameter unexpectedly retained a comptime marker"
  expectBinderStage "comptime lambda parameter" analysis staged.parameter
    .comptime
  expectExpressionStage "comptime lambda body reference" analysis
    staged.returned .comptime
  expectExpressionStage "comptime lambda expression" analysis
    staged.expression .deferred
  expectBinderStage "runtime lambda parameter" analysis runtime.parameter
    .runtime
  expectExpressionStage "runtime lambda body reference" analysis
    runtime.returned .runtime
  expectExpressionStage "runtime lambda expression" analysis
    runtime.expression .deferred

private def testHiddenMatchBinderIsNotLexical
    (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "matchStages"
  let _ ← analyzeOrThrow "matchStages" function
  let resolution ← match function.typedBody.roots with
    | [.statement root] =>
        match function.typedBody.lookupStatement? root with
        | some { form := .matchWith resolution, .. } => pure resolution
        | _ => throw (IO.userError "matchStages lost its match root")
    | roots => throw (IO.userError
        s!"matchStages retained {roots.length} roots")
  let returned ← match resolution.cases with
    | first :: _ =>
        match first.body with
        | [statement] =>
            match function.typedBody.lookupStatement? statement with
            | some { form := .returnStmt (some expression), .. } =>
                pure expression
            | _ => throw (IO.userError
                "matchStages first arm lost its value return")
        | body => throw (IO.userError
            s!"matchStages first arm retained {body.length} statements")
    | [] => throw (IO.userError "matchStages retained no match cases")
  let forged : CheckedFunction := {
    function with typedBody := {
      function.typedBody with
      nodes := function.typedBody.nodes.map fun
        | .expression node =>
            if node.id = returned then
              .expression { node with
                form := .reference "hidden" (.local resolution.hiddenScrutinee)
              }
            else
              .expression node
        | .statement node => .statement node
    }
  }
  expectAnalysisError "hidden match binder visibility"
    (analyzeFunction forged)
    (.unknownLocal returned resolution.hiddenScrutinee)

private def testMalformedCarriers (program : CheckedProgram) : IO Unit := do
  let function ← functionNamed program "classify"
  let other ← functionNamed program "plain"

  let wrongOwner : CheckedFunction := {
    function with typedBody := {
      function.typedBody with owner := other.declaration
    }
  }
  expectAnalysisError "typed-source owner mismatch"
    (analyzeFunction wrongOwner)
    (.sourceOwnerMismatch function.declaration other.declaration)

  match function.typedBody.nodes with
  | [] => throw (IO.userError
      "classify unexpectedly retained an empty typed-source table")
  | node :: _ =>
      let duplicated : CheckedFunction := {
        function with typedBody := {
          function.typedBody with nodes := node :: function.typedBody.nodes
        }
      }
      expectAnalysisError "duplicate occurrence"
        (analyzeFunction duplicated)
        (.duplicateOccurrence node.occurrenceId)

  match function.typedBody.inputs with
  | [] => throw (IO.userError "classify unexpectedly retained no inputs")
  | input :: _ =>
      let duplicated : CheckedFunction := {
        function with typedBody := {
          function.typedBody with
          inputs := input :: function.typedBody.inputs
        }
      }
      expectAnalysisError "duplicate binder"
        (analyzeFunction duplicated)
        (.duplicateBinder input.id)

/-- Exercise the public join and scope-aware function analysis over a checked
source fixture containing all three source stages. -/
def testSourceStageClassification : IO Unit := do
  testJoin
  let program ← checkedProgram
  testInputClassification program
  testLetAndCallClassification program
  testJoinClassification program
  testLambdaClassification program
  testHiddenMatchBinderIsNotLexical program
  testMalformedCarriers program

end Tests.SourceStageClassification
