import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBodyMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual body/parameter/hook equations and finite builtin body trees close a
fixed selected method dictionary. Reflection produces the independent source
coercion step; this does not assert uniqueness of every possible source dictionary.
The runtime fixtures retain method evidence, input allocation, effects and faults. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Tests.SourceCoreCallableCoercionMethodBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableCoercionMethodFrame (Frame BodyOutcome)
open CallableCoercionMethodBody
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)

/-- The real method context retains residual type variables. A trait's two
head types are not a claim about its method's runtime parameter count. -/
theorem method_context_residual (program : CheckedProgram) (method : ExecutableImplMethods.CheckedMethod) :
    (bodyInstance program method).context.residualTypeVariables = true := rfl

theorem accepted_source_frame {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (receipt : CallableCoercionSourceSelection.Certificate program caller node available step method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary)
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (completeRecord : named.specialized = method.specialized) :
    Dynamic.OperatorMethodSelected (SourceSemantics.Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) ∧
    CallableCoercionMethodFrame.Frame (bodyInstance program method) (CallableCoercionMethodFrame.view (bodyInstance program method) (environment dictionary) compiled.statements) :=
  CallableCoercionMethodFrame.of_compilation loadedAccepted receipt formed range signatures ledger assumptions resolved covered materialized compiled completeRecord

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source
    (bindings.reverse.map fun binding => (binding.1.id, binding.2)) function.body output reasonAt fellThrough escaped = .ok body)
  (projection : values.checked.catalog.project function.resultType = .ok output)
  (syntaxTree : BuiltinLexicalStatements.Syntax function.source context true function.body function.resultType)
  {flow : Expr}
  (emitted : body = CompatibleStatements.finish output flow fellThrough escaped)
  (tree : BuiltinLexicalStatements.Tree layouts owner active prepared.layout.frame allocationGlobals onError
    readFuel values function.source solved reasonAt context
    (bindings.reverse.map fun binding => (binding.1.id, binding.2)) true function.body function.resultType output flow)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

  {sourceBody : Dynamic.BodyInstance}
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)


include bodyAccepted projection syntaxTree emitted tree parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem accepted_method_preserves {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
    {input : Dynamic.Value} {nativeInput : Value} {reason : Word}
    (sourceArgument : arguments = [input]) (nativeArgument : nativeArguments = [nativeInput])
    (entry : actual = nativeInput :: captured)
    (installed : Installed call code ξ callerEnvironment captured store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before [input] outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke callerEnvironment reason call store (.inRight .word nativeInput) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨certificate⟩ := BuiltinNamedBody.of_tree bodyAccepted projection syntaxTree emitted tree
  exact invoke_preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) sourceArgument nativeArgument entry installed trace

include bodyAccepted projection syntaxTree emitted tree parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem accepted_method_reflects {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
    {input : Dynamic.Value} {nativeInput : Value} {reason : Word}
    (sourceArgument : arguments = [input]) (nativeArgument : nativeArguments = [nativeInput])
    (entry : actual = nativeInput :: captured)
    (installed : Installed call code ξ callerEnvironment captured store)
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {step : CoercionStep}
    (selected : Dynamic.OperatorMethodSelected program sourceContext evidence "Coerce" "coerce"
      step.requirements sourceBody function.evidence)
    {value : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.Invoke callerEnvironment reason call store (.inRight .word nativeInput) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      (match outcome with
      | .value output => Dynamic.CoercionStepExecutes program sourceContext evidence before step input output after
      | .fault reason => Dynamic.CoercionStepFaults program sourceContext evidence before step input reason after) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨certificate⟩ := BuiltinNamedBody.of_tree bodyAccepted projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, sourceOutcome, rest⟩ := invoke_reflects
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) sourceArgument nativeArgument entry installed completed
  refine ⟨outcome, after, finalMap, finalWorld, ?_, rest⟩
  cases sourceOutcome with
  | value invokes => exact .method selected invokes
  | fault fails => exact .method selected fails

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let m: mapping(Bool => Word); let first = m[value]; { let shadow: Word = first + 6; shadow; } if (value) { return first + 19; } let gap: Word; return gap; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker { let converted: Word = flag; return converted; }",
    "function early() returns (Word) where Bool: Marker { let missing: Bool; let converted: Word = missing; return converted; }"
  ]}] }

private def methodAt (entry : SourceCompilerFeatureSupport.Entry) : IO ExecutableImplMethods.CheckedMethod := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "method caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      for step in node.coercions do
        let method ← SourceCompilerFeatureSupport.get "actual coercion method"
          (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
        let dictionary ← SourceCompilerFeatureSupport.get "actual method dictionary"
          (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
        let selected ← SourceCompilerFeatureSupport.get "selected full method"
          (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
        let emitted ← match base.functions.find? (·.signature.key == method.specialized.key) with
          | some emitted => pure emitted | none => throw (IO.userError "method native row missing")
        let trait ← match base.sourceProgram.signatures.traits.find? (·.name == "Coerce") with
          | some trait => pure trait | none => throw (IO.userError "Coerce trait missing")
        SourceCompilerFeatureSupport.require
          (selected == method.specialized && emitted.specialized == selected &&
            selected.function.typedBody.inputs.length == 1 && emitted.inputs.length == 1 &&
            trait.parameters.length == 2 && emitted.signature.parameterType == .bool && emitted.signature.resultType == .word)
          "method full record, trait type arity or runtime arity changed"
        SourceCompilerFeatureSupport.require
          (method.traitPredicates.all caller.assumptions.contains && dictionary.length == 3 &&
            dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]? &&
            dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions)
          "covered dictionary full order/duplicates changed"
        return method
  throw (IO.userError "caller has no actual method coercion")

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"method {label} source cell order/effects changed: {reprStr state.heap}"

private def publicFaultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let completed ← SourceCompilerFeatureSupport.get "method public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match completed with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "method public outcome must fail")
  let baseline ← SourceCompilerFeatureSupport.get "method fault snapshot" (← session.snapshot 2048)
  for budget in [0, 31, 97] do
    let started ← SourceCompilerFeatureSupport.get "method suspended public call"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | outcome => pure outcome
    match resumed with
    | .failed resumed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "method resumed fault snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (resumed == reason && reprStr snapshot.cells == reprStr baseline.cells)
        "method resumed fault changed diagnostic or complete source heap"
    | _ => throw (IO.userError "method resumed call changed failure")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "method body checker" (checkProgram workspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "covered"
  let method ← methodAt entry
  let gap ← match (SourceCoreDataPlaces.declaredBinders method.specialized.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "actual method gap missing")
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← methodAt early
  let word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
  for budget in [0, 31, 300000] do
    for flag in [true, false] do
      let started ← entry.audit [.bool flag] budget
      let resumed ← SourceCompilerFeatureSupport.get "method native resume" (started.resume 300000)
      let priorCells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
        [(.bool, some (.bool flag)), (.bool, some (.bool flag)),
         (.mapping .bool .word, some (.mapping .bool .word [])),
         (.word, some (word 0)), (.word, some (word 6))]
      match resumed.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (flag && reprStr value == reprStr (word 19)) "method success changed"
        cells state (priorCells ++ [(.word, some (word 19))]) "returned"
      | .fault (.uninitializedLocal actual) state =>
        SourceCompilerFeatureSupport.require (!flag && actual == gap) "method body fault changed origin"
        cells state (priorCells ++ [(.word, none)]) "fault"
      | other => throw (IO.userError s!"method outcome changed: {reprStr other}")
    let started ← early.audit [] budget
    let resumed ← SourceCompilerFeatureSupport.get "method pre-call fault resume" (started.resume 300000)
    match resumed.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.bool, none)] "pre-call fault"
    | other => throw (IO.userError s!"method pre-call fault changed: {reprStr other}")
  entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 19) 31
  publicFaultResume entry [.bool false]
  publicFaultResume early []
  IO.println "coercion method body: actual dictionary/arity, marked parameters, scoped scalar body, exact fault effects and public resume GREEN"

end Tests.SourceCoreCallableCoercionMethodBodyMeaning
