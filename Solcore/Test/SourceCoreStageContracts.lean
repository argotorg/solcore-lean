import Solcore.Frontend.SourceCoreStageContracts
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.TaggedFunction

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreStageContracts.Sidecar.mk
#check_failure Solcore.Frontend.SourceCoreStageContracts.Contract.mk
#check_failure Solcore.Frontend.SourceCoreStageContracts.Guard.mk
#check_failure fun (sidecar : Solcore.Frontend.SourceCoreStageContracts.Sidecar) => { sidecar with caller := sidecar.caller }
#check_failure fun (contract : Solcore.Frontend.SourceCoreStageContracts.Contract) => { contract with stagedResult := false }

/-! Parsed, checked callable contracts retain old stage decisions, including
accepted programs whose indirect invocation faults before evaluating arguments.
Native checks distinguish callee effects, skipped argument effects, and callee
failure priority. The whole source compiler routing is a separate owner. -/

set_option autoImplicit false

namespace Tests.SourceCoreStageContracts

open Solcore Solcore.Frontend SourceInference SourceCoreStageContracts

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function markedEffects(comptime seed: Word) returns (comptime<Word>) {",
    " let total: Word = seed; let table: mapping(Word => Word);",
    " let bump = lam(comptime delta: Word) -> Word { total += delta; table[0] = total; return table[0]; };",
    " return bump(3); }",
    "function markedClosureClosed() returns (Word) {",
    " let f = lam(comptime value: Word) -> Word { return value; }; return f(21); }",
    "function markedClosureRuntime(value: Word) returns (Word) {",
    " let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
    "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
    "function markedGlobalClosed() returns (Word) { let f = markedGlobal; return f(22); }",
    "function markedGlobalRuntime(value: Word) returns (Word) { let f = markedGlobal; return f(value); }",
    "function markedResult(comptime value: Word) returns (comptime<Word>) { return value; }",
    "function markedResultIndirectBlocked() returns (Word) { let f = markedResult; return f(23); }",
    "function markedResultIndirectStaged() returns (comptime<Word>) { let f = markedResult; return f(24); }",
    "function many(flag: Bool, value: Word) returns (Word) {",
    " let f = lam(comptime staged: Word, flag: Bool, comptime other: Word) -> Word { return staged; };",
    " return f(1, flag, value); }",
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function tupleParameter() returns (Word) {",
    " let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }"
  ] }] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"staging fixture missing: {name}")

private def plan (program : CheckedProgram) (name : String) : IO Plan := do
  let key ← key program name
  let source ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"staging worklist failed: {reprStr other}")
  match SourceCompilationPlan.prepareExecutablePlanEvidence program source with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"staging preparation failed: {reprStr error}")

private def sidecar (program : CheckedProgram) (plan : Plan) (name : String) : IO Sidecar := do
  let key ← key program name
  match prepareSidecar plan key with
  | .ok sidecar => pure sidecar
  | .error error => throw (IO.userError s!"staging sidecar failed: {reprStr error}")

private def call (sidecar : Sidecar) : IO ExpressionNode :=
  match sidecar.source.nodes.filterMap (fun
    | .expression node@{ form := .call _ _ (.indirect _), .. } => some node
    | _ => none) with
  | [node] => pure node
  | _ => throw (IO.userError "staging fixture must contain one indirect call")

private def lambda (sidecar : Sidecar) : IO ExpressionNode :=
  match sidecar.source.nodes.filterMap (fun
    | .expression node@{ form := .lambda _ _ _, .. } => some node
    | _ => none) with
  | [node] => pure node
  | _ => throw (IO.userError "staging fixture must contain one lambda")

private def guard (sidecar : Sidecar) (contract : Contract) : IO Guard := do
  let node ← call sidecar
  match prepareGuard sidecar node.id contract with
  | .ok guard => pure guard
  | .error error => throw (IO.userError s!"staging guard preparation failed: {reprStr error}")

private def lambdaGuard (program : CheckedProgram) (name : String) : IO Guard := do
  let plan ← plan program name
  let sidecar ← sidecar program plan name
  let node ← lambda sidecar
  let contract ← match Contract.lambda sidecar node.id with
    | .ok contract => pure contract
    | .error error => throw (IO.userError s!"staging lambda contract failed: {reprStr error}")
  guard sidecar contract

private def namedGuard (program : CheckedProgram) (name target : String) : IO Guard := do
  let plan ← plan program name
  let sidecar ← sidecar program plan name
  let target ← key program target
  let contract ← match Contract.named plan target with
    | .ok contract => pure contract
    | .error error => throw (IO.userError s!"staging named contract failed: {reprStr error}")
  guard sidecar contract

private def calleeType : Core.Ty := Core.TaggedFunction.functionType .word .word

private def callee (failure : Bool) : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 1)))
    (if failure then Core.LanguageResult.failure calleeType (.word (word 72))
     else Core.LanguageResult.success
       (Core.TaggedFunction.anonymous (.lambda .word (Core.LanguageResult.resultType .word)
         (Core.LanguageResult.success (.var 0)))))

/-- This is the argument/body portion, under the successful callee binder. -/
private def arguments : Core.Expr :=
  .letE (.storeCell (.var 1) (.word (word 99)))
    (Core.LanguageResult.success (.word (word 7)))

private def native (guard : Guard) (failure : Bool) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (.newCell .word (.word (word 0)))
    (guard.lower .word (callee failure) arguments (fun _ => word 71))
}

private theorem native_typed (guard : Guard) (failure : Bool) :
    Core.HasType [] (native guard failure).body (Core.LanguageResult.resultType .word) := by
  apply Core.HasType.letE (Core.HasType.newCell Core.HasType.word)
  apply Guard.lower_hasType guard (fun _ => word 71) .word
  · apply Core.HasType.letE (Core.HasType.storeCell (.var rfl) .word)
    cases failure
    · exact Core.LanguageResult.success_hasType
        (Core.TaggedFunction.anonymous_hasType
          (.lambda .word (Core.LanguageResult.resultType_wellFormed .word)
            (Core.LanguageResult.success_hasType (.var rfl))))
    · exact Core.LanguageResult.failure_hasType
        (Core.TaggedFunction.functionType_wellFormed .word .word) .word
  · exact .letE (.storeCell (.var rfl) .word) (Core.LanguageResult.success_hasType .word)

example (guard : Guard) :
    SourceStageAnalysis.FunctionAnalysisCertificate guard.sidecar.caller.function
      guard.sidecar.caller.stageAnalysis := guard.sidecar.certificate

example (guard : Guard) :
    SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner = guard.decision :=
  guard.decision_exact

example (guard : Guard) (failure : Bool) (fuel : Nat) :
    ((native guard failure).runStateful fuel).HasType (Core.LanguageResult.resultType .word) :=
  Core.well_typed_runStateful_has_type (Core.initial_state_has_type (native_typed guard failure)) fuel

example (guard : Guard) (failure : Bool) (spent additional : Nat) (checkpoint : Core.State)
    (exhausted : (native guard failure).runStateful spent = .outOfFuel checkpoint) :
    (Core.runStateful additional checkpoint).HasType (Core.LanguageResult.resultType .word) ∧
      Core.runStateful additional checkpoint = (native guard failure).runStateful (spent + additional) :=
  Core.well_typed_runStateful_resume_has_type
    (Core.initial_state_has_type (native_typed guard failure)) exhausted additional

private def checkNative (guard : Guard) (rejected : Bool) : IO Unit := do
  for failure in [false, true] do
    let program := native guard failure
    assertTrue program.check "stage guard failed native type checking"
    let value := if failure then Core.Value.inLeft .word (.word (word 72))
      else if rejected then .inLeft .word (.word (word 71)) else .inRight .word (.word (word 7))
    let heap := if failure || rejected then [Core.Value.word (word 1)] else [.word (word 99)]
    assertTrue (program.runStateful 100 == .done value heap)
      "stage guard changed callee effects, argument suppression, or callee failure priority"
    match program.runStateful 8 with
    | .outOfFuel checkpoint =>
        assertTrue (Core.runStateful 92 checkpoint == .done value heap)
          "stage guard changed on checkpoint resumption"
    | _ => throw (IO.userError "stage guard must suspend at fuel eight")

private def accepted (receipt : Guard) : Bool :=
  match receipt.decision with | .ok () => true | .error _ => false

private def argumentFault (receipt : Guard) (index : Nat) (argument : ExpressionId) : Bool :=
  match receipt.decision with
  | .error (.comptimeArgumentStageMismatch caller use actualIndex actualArgument actualStage) =>
      caller == receipt.sidecar.caller.key && use == receipt.node.id && actualIndex == index &&
      actualArgument == argument && actualStage == .runtime
  | _ => false

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staging fixture checking failed: {reprStr error}")
  for name in ["markedEffects", "markedClosureClosed"] do
    let receipt ← lambdaGuard program name
    assertTrue (accepted receipt && receipt.contract.parameterStages == [true])
      "closed/effectful staged callable changed its existing accepted guard"
    checkNative receipt false
  for name in ["markedClosureRuntime", "many"] do
    let receipt ← lambdaGuard program name
    let expectedIndex := if name == "many" then 2 else 0
    let expectedArgument ← match receipt.arguments[expectedIndex]? with
      | some argument => pure argument
      | none => throw (IO.userError "staging fixture missing its failing argument")
    assertTrue (argumentFault receipt expectedIndex expectedArgument)
      "staging argument fault lost original caller, site, index, argument, or stage"
    if name == "many" then
      assertTrue (receipt.contract.parameterStages == [true, false, true])
        "staging contract flattened arbitrary parameter arity"
    checkNative receipt true
  for (name, target) in [("markedGlobalClosed", "markedGlobal"), ("markedResultIndirectStaged", "markedResult")] do
    let receipt ← namedGuard program name target
    assertTrue (accepted receipt) "accepted named staged contract became rejected"
    checkNative receipt false
  let runtime ← namedGuard program "markedGlobalRuntime" "markedGlobal"
  let argument ← match runtime.arguments.head? with
    | some argument => pure argument
    | none => throw (IO.userError "named staging fixture lost its argument")
  assertTrue (argumentFault runtime 0 argument) "named stage argument fault changed"
  checkNative runtime true
  let result ← namedGuard program "markedResultIndirectBlocked" "markedResult"
  assertTrue (match result.decision with
    | .error (.comptimeResultStageMismatch caller use owner stage) =>
        caller == result.sidecar.caller.key && use == result.node.id && owner == result.contract.owner && stage == .deferred
    | _ => false) "named staged result fault changed"
  checkNative result true
  let malformed := { result.sidecar.plan with specializations := result.sidecar.plan.specializations.map fun specialized =>
    if specialized.key == result.sidecar.caller.key then
      { specialized with stageAnalysis := { expressions := [], binders := [] } }
    else specialized }
  assertTrue (match prepareSidecar malformed result.sidecar.caller.key with
    | .error _ => true | _ => false) "edited caller stage table acquired a sealed receipt"
  assertTrue (match prepareGuard runtime.sidecar runtime.node.id result.contract with
    | .error .planMismatch => true | _ => false) "contract from another plan passed caller authentication"
  let lambdaReceipt ← lambdaGuard program "markedClosureClosed"
  let notCall ← lambda lambdaReceipt.sidecar
  assertTrue (match prepareGuard lambdaReceipt.sidecar notCall.id lambdaReceipt.contract with
    | .error (.expectedIndirectCall _) => true | _ => false)
    "lambda occurrence was accepted as a callsite"
  let tuple ← lambdaGuard program "tupleParameter"
  assertTrue (match tuple.decision with
    | .error (.argumentArityMismatch expected actual) => expected == 0 && actual == 1
    | _ => false) "one tuple parameter and two source arguments lost the existing preargument arity fault"
  checkNative tuple true
  let polymorphicPlan ← plan program "polymorphic"
  let polymorphicSidecar ← sidecar program polymorphicPlan "polymorphic"
  let polyLambda ← lambda polymorphicSidecar
  assertTrue (match Contract.lambda polymorphicSidecar polyLambda.id with
    | .error (.openLambda _) => true | _ => false)
    "open lambda metadata was projected without an authenticated local context"
  let data ← match SourceCoreDataCatalog.prepare program.signatures 64 [.word, .bool] with
    | .ok data => pure data
    | .error error => throw (IO.userError s!"staged polymorphic catalog failed: {reprStr error}")
  let catalog ← match SourceCoreLocalPolymorphism.prepare data polymorphicPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"staged polymorphic instances failed: {reprStr error}")
  let binding ← match catalog.bindings.filter (·.binder.name == "f") with
    | [binding] => pure binding
    | _ => throw (IO.userError "staged polymorphic binding missing")
  assertTrue (binding.instances.length == 2) "staged polymorphic fixture lost its Word/Bool contexts"
  for candidate in binding.instances do
    let prepared ← match SourceCoreLocalEvidence.prepare program polymorphicPlan candidate with
      | .ok prepared => pure prepared
      | .error error => throw (IO.userError s!"staged local context failed: {reprStr error}")
    let contract ← match Contract.contextualLambda polymorphicSidecar prepared polyLambda.id with
      | .ok contract => pure contract
      | .error error => throw (IO.userError s!"staged contextual lambda failed: {reprStr error}")
    let expectedParameter ← match candidate.origin.substitution.apply binding.binder.scheme.body with
      | .function parameter _ => pure parameter
      | _ => throw (IO.userError "staged local instance lost its function type")
    assertTrue (contract.parameters.map (·.scheme.body) == [expectedParameter]
      && contract.parameterStages == [false]) "staged contextual contract lost its exact concrete parameter"
    assertTrue (match Contract.contextualLambda lambdaReceipt.sidecar prepared notCall.id with
      | .error (.contextualCallerMismatch _) => true | _ => false)
      "local context from another caller acquired a stage contract"

end Tests.SourceCoreStageContracts
