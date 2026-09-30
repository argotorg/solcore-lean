import Solcore.Frontend.SourceCoreFunctions
import Solcore.Frontend.SourceCoreRecursiveEntry

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreFunctions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function dec(value: Word) returns (Word) { return value - 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { let f: function(Word) returns (Word) = inc; return consume(f, value); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function nestedCapture(value: Word) returns (Word) {",
    " let outer: function(Word) returns (function() returns (Word)) = lam(delta: Word) -> function() returns (Word) {",
    "   return lam() -> Word { return inc(value + delta); }; };",
    " let inner: function() returns (Word) = outer(3); value = 9; return inner(); }",
    "function failBeforeArgument() returns (Word) {",
    " let f: function(Word) returns (Word); let marker: Word = 0;",
    " let argument: function() returns (Word) = lam() -> Word { marker = 9; return marker; }; return f(argument()); }",
    "function argumentFailure() returns (Word) {",
    " let f: function(Word) returns (Word) = lam(value: Word) -> Word { return value; };",
    " let absent: Word; return f(absent); }",
    "function names() returns (function(Word) returns (Word), function(Word) returns (Word)) { return (inc, dec); }",
    "function sameName() returns (function(Word) returns (Word), function(Word) returns (Word)) { return (inc, inc); }",
    "function lambdaGlobal(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word { return inc(n) + value; }; return f(2); }",
    "function closureLoop(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word {",
    "   while (n > 0) { value = inc(value); n = n - 1; } return value; }; return f(3); }",
    "function principal() returns (Word) { let id = lam(value) { return value; }; return id(4); }"
  ] }]
}

private def bodyLowerer : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } fuel source scope statements result reasonAt fellThrough escaped

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"function-value fixture missing: {name}")

private def preparePlan (program : CheckedProgram) (name : String) : IO SourceCoreCalls.Plan := do
  let plan ← match SourceSpecializationWorklist.run program [← request program name] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"function-value worklist failed: {reprStr result}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"function-value plan preparation failed: {reprStr error}")

private def signature (function : SourceSpecialization.SpecializedFunction) : IO SourceCoreCalls.Signature := do
  match function.function.type with
  | .function parameter result =>
      match SourceCoreFunctionTypes.lowerType (.declaration function.key.declaration) parameter,
          SourceCoreFunctionTypes.lowerType (.declaration function.key.declaration) result with
      | .ok parameterType, .ok resultType => pure { key := function.key, parameterType, resultType }
      | _, _ => throw (IO.userError "function-value signature projection failed")
  | _ => throw (IO.userError "function-value fixture is not a function")

private def parameters (source : TypedSource) : IO (List (TypedBinder × Core.Ty) × SourceCoreBasic.Scope) := do
  source.inputs.foldlM (fun (parameters, scope) binder => do
    match SourceCoreFunctionTypes.lowerBinder source scope binder with
    | .ok type => pure (parameters ++ [(binder, type)], (binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"function-value input rejected: {reprStr error}")) ([], [])

private structure Compiled where
  plan : SourceCoreCalls.Plan
  entry : SourceSpecialization.SpecializedFunction
  globals : List SourceCoreCalls.Signature
  diagnostics : SourceCoreProgramFaultSites.Program
  type : Core.Ty
  body : Core.Expr

/-- A closed test harness installs exactly the compiled raw globals and invokes
one root. Production entry/interface generalization is owned by its own module. -/
private def compile (program : CheckedProgram) (name : String) (arguments : List SourceCoreBasic.LoweredExpr) : IO Compiled := do
  let plan ← preparePlan program name
  let root ← match plan.seedKeys with
    | [root] => pure root
    | _ => throw (IO.userError "function-value fixture must have one seed")
  let ordered := plan.specializations.reverse
  let globals ← ordered.mapM signature
  let diagnostics ← match SourceCoreProgramFaultSites.prepare plan root with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"function-value diagnostic preparation failed: {reprStr error}")
  let closures ← ordered.mapM fun function => do
    let signature ← signature function
    let sites ← match diagnostics.find? function.key with
      | some sites => pure sites
      | none => throw (IO.userError "function-value sites missing")
    let source := function.function.typedBody
    let (parameters, scope) ← parameters source
    let context : SourceCoreFunctions.Context := {
      plan, globals, owner := function.key, administrativePrefix := 1
      solvedRequirements := function.function.solvedRequirements
      internalReason := Core.Word.zero
    }
    let statements ← source.roots.mapM fun
      | .statement id => pure id
      | .expression _ => throw (IO.userError "function-value fixture has expression root")
    let body ← match bodyLowerer
        (fun fuel source scope id reasonAt =>
          SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer fuel context source scope id reasonAt)
        100 source scope statements signature.resultType sites.table.reasonAt sites.fellThroughReason sites.table.escapedReason with
      | .ok body => pure body
      | .error error => throw (IO.userError s!"function-value body rejected: {reprStr error}")
    let body := SourceCoreFunctions.bindParameters parameters signature.resultType body
    pure (Core.Expr.lambda signature.parameterType (Core.LanguageResult.resultType signature.resultType) body)
  let (entry, index) ← match ordered.zipIdx.find? (fun item => decide (item.1.key = root)) with
    | some entry => pure entry
    | none => throw (IO.userError "function-value root missing")
  let signature ← signature entry
  let arguments := SourceCoreCalls.packArguments arguments
  assertTrue (decide (arguments.type = signature.parameterType)) "test argument bundle type mismatch"
  let body := SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures (SourceCoreCalls.call signature index arguments.expression Core.Word.zero))
  assertTrue (decide (Core.infer? [] body = some (Core.LanguageResult.resultType signature.resultType)))
    "function-value closed harness failed Core checker"
  pure { plan, entry, globals, diagnostics, type := signature.resultType, body }

private def argument (value : Nat) : SourceCoreBasic.LoweredExpr :=
  ⟨.word, Core.LanguageResult.success (.word (word value))⟩

private def execute (compiled : Compiled) (fuel : Nat := 20000) : Core.LanguageResult.Observation :=
  Core.LanguageResult.observeResult (Core.runStateful fuel (.initial compiled.body [] []))

private def success (compiled : Compiled) (expected : Core.Value) : IO Core.Store := do
  match execute compiled with
  | .succeeded actual store =>
      assertTrue (actual == expected) "function-value result mismatch"
      pure store
  | result => throw (IO.userError s!"function-value execution failed: {reprStr result}")

private def testFunctionValues (program : CheckedProgram) : IO Unit := do
  discard <| success (← compile program "named" [argument 4]) (scalar 5)
  let shared ← compile program "shared" [argument 4]
  let store ← success shared (.pair (scalar 6) (scalar 9))
  assertTrue (store[shared.globals.length]? == some (present (scalar 9)))
    "two closures did not share the same mutable captured parameter"
  let selfCell ← compile program "selfCell" [argument 7]
  let store ← success selfCell (scalar 7)
  assertTrue (store.length == selfCell.globals.length + 6) "self-cell calls lost parameter allocation identity"
  match execute selfCell 15 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.LanguageResult.observeResult (Core.runStateful 20000 checkpoint) == execute selfCell 20015)
        "capturing self-cell checkpoint did not resume consistently"
  | _ => throw (IO.userError "capturing self-cell execution did not suspend")
  discard <| success (← compile program "nestedCapture" [argument 4]) (scalar 13)
  discard <| success (← compile program "lambdaGlobal" [argument 8]) (scalar 11)
  discard <| success (← compile program "closureLoop" [argument 8]) (scalar 11)
  for (name, same) in [("sameName", true), ("names", false)] do
    let compiled ← compile program name []
    match execute compiled with
    | .succeeded (.pair (.pair (.inRight .unit (.word left)) _) (.pair (.inRight .unit (.word right)) _)) _ =>
        assertTrue ((left == right) == same) "named identities were not deterministic and distinct"
        assertTrue (left != Core.Word.zero && right != Core.Word.zero) "named identity used the reserved zero value"
    | result => throw (IO.userError s!"named reference did not return tagged functions: {reprStr result}")

private def testIndirectFailure (program : CheckedProgram) : IO Unit := do
  let compiled ← compile program "failBeforeArgument" []
  match execute compiled with
  | .failed reason store =>
      let node ← match compiled.entry.function.typedBody.nodes.findSome? fun
        | .expression node@{ form := .reference "f" (.local _), .. } => some node
        | _ => none with
      | some node => pure node
      | none => throw (IO.userError "uninitialized function read missing")
      let sites ← match compiled.diagnostics.find? compiled.entry.key with
        | some sites => pure sites
        | none => throw (IO.userError "root diagnostic table missing")
      assertTrue (reason == sites.table.reasonAt node.id) "indirect callee failure lost its source site"
      assertTrue (store[compiled.globals.length + 1]? == some (present (scalar 0)))
        "indirect call evaluated argument effects after its callee failed"
  | result => throw (IO.userError s!"uninitialized function did not fail: {reprStr result}")
  let compiled ← compile program "argumentFailure" []
  match execute compiled with
  | .failed _ store =>
      assertTrue (store.length == compiled.globals.length + 2)
        "failed indirect argument allocated the callee parameter"
  | result => throw (IO.userError s!"uninitialized indirect argument did not fail: {reprStr result}")

private def testTypesAndBoundaries (program : CheckedProgram) : IO Unit := do
  let namedRequest ← request program "named"
  let site := SourceCoreElaboration.ErrorSite.declaration namedRequest.declaration
  let higherOrder : TypeSystem.Ty := .function (.product (.function .word .bool) .word) (.function .unit .word)
  match SourceCoreFunctionTypes.lowerType site higherOrder with
  | .ok actual =>
      assertTrue (decide (actual = Core.TaggedFunction.functionType
        (.product (Core.TaggedFunction.functionType .word .bool) .word)
        (Core.TaggedFunction.functionType .unit .word))) "recursive function type projection changed shape"
  | .error error => throw (IO.userError s!"higher-order type projection failed: {reprStr error}")
  for type in ([.integer, .mapping .word .word, .proxy .word, .comptime .word] : List TypeSystem.Ty) do
    match SourceCoreFunctionTypes.lowerType site type with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unsupported general type entered the function profile")
  let principalPlan ← preparePlan program "principal"
  let principalRequest ← request program "principal"
  let principal ← match principalPlan.specializations.find? (fun function =>
      function.key = { declaration := principalRequest.declaration, arguments := [] }) with
    | some function => pure function
    | none => throw (IO.userError "principal fixture missing")
  let binder ← match principal.function.typedBody.nodes.findSome? fun
    | .statement { form := .letDecl binder _, .. } => some binder
    | _ => none with
    | some binder => pure binder
    | none => throw (IO.userError "principal local binder missing")
  match SourceCoreFunctionTypes.lowerBinder principal.function.typedBody [] binder with
  | .error (.polymorphicBinding _) => pure ()
  | _ => throw (IO.userError "principal polymorphic binding entered the monomorphic profile")

private def testMetadata (program : CheckedProgram) : IO Unit := do
  let names ← compile program "names" []
  let source := names.entry.function.typedBody
  let reference ← match source.nodes.findSome? fun
    | .expression node@{ form := .reference _ (.declaration _), .. } => some node
    | _ => none with
    | some node => pure node
    | none => throw (IO.userError "named reference fixture missing")
  let context : SourceCoreFunctions.Context := {
    plan := names.plan, owner := names.entry.key, globals := names.globals
    administrativePrefix := 0, solvedRequirements := names.entry.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let checkReference (context : SourceCoreFunctions.Context) : IO Unit := do
    match SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer 100 context source [] reference.id
        (fun _ => word 81) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "forged named reference metadata was accepted")
  checkReference { context with plan := { names.plan with referenceEdges := [] } }
  checkReference { context with plan := { names.plan with referenceEdges := names.plan.referenceEdges ++ names.plan.referenceEdges } }
  checkReference { context with globals := [] }
  checkReference { context with globals := names.globals.map fun signature => { signature with resultType := .bool } }
  let indirectPlan ← preparePlan program "consume"
  let caller ← match indirectPlan.specializations with
    | [caller] => pure caller
    | _ => throw (IO.userError "indirect fixture plan changed")
  let source := caller.function.typedBody
  let (_, scope) ← parameters source
  let node ← match source.nodes.findSome? fun
    | .expression node@{ form := .call _ _ (.indirect _), .. } => some node
    | _ => none with
    | some node => pure node
    | none => throw (IO.userError "indirect fixture occurrence missing")
  let context : SourceCoreFunctions.Context := {
    plan := indirectPlan, owner := caller.key, globals := [← signature caller]
    administrativePrefix := 1, solvedRequirements := caller.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lower (source : TypedSource) := SourceCoreFunctions.lowerExpressionWithReasons bodyLowerer 100 context
    source scope node.id (fun _ => word 82)
  match lower source with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"unmodified indirect metadata rejected: {reprStr error}")
  let alter (update : IndirectCallResolution → IndirectCallResolution) : TypedSource :=
    { source with nodes := source.nodes.map fun
      | .expression expression => if expression.id = node.id then match expression.form with
        | .call callee arguments (.indirect metadata) =>
            .expression { expression with form := .call callee arguments (.indirect (update metadata)) }
        | _ => .expression expression
        else .expression expression
      | node => node }
  for source in [
      alter (fun metadata => { metadata with argumentCount := metadata.argumentCount + 1 }),
      alter (fun metadata => { metadata with argumentTypeBeforeCoercion := .bool }),
      alter (fun metadata => { metadata with argumentTypeAfterCoercion := .bool }),
      alter (fun metadata => { metadata with argumentCoercions := [{ requirement := ⟨888⟩, source := .word, target := .word }] })] do
    match lower source with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "forged indirect metadata was accepted")
  let badRecursiveInitializer : Workspace.RawWorkspace := {
    entry := "bad.solc", externalLibraries := []
    mainSources := [{ path := "bad.solc", content :=
      "function bad() returns (Word) { let f: function() returns (Word) = lam() -> Word { return f(); }; return f(); }" }]
  }
  match checkProgram badRecursiveInitializer with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "source scope unexpectedly made an initializer's binding recursive")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"function-value source fixtures failed: {reprStr errors}")
  testFunctionValues program
  testIndirectFailure program
  testTypesAndBoundaries program
  testMetadata program

end Tests.SourceCoreFunctions
