import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
import Solcore.Test.SourceCompilerFeatureSupport

/-! The reached declaration's actual Valid witness closes ordinary raw-call
admission with unchanged caller type scopes, including residually open bodies.
The concrete formal consumers reuse catalog mutual meaning, ordered argument
Trees and actual catalog/method authority. No range proof is guessed from
admissibility, a native type, or the absence of signature predicates. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCallAdmission
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (typed : ExpressionHasType source context id node.type)
  (children : DataExpressionSequence.Tree source
    (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
    scope arguments (header.bindings.map (fun binder => binder.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted

section OpenScope
private def openContext (signatures : ProgramSignatures) : SourceSemantics.Context :=
  {SourceSemantics.Context.ofSignatures signatures with
    typeVariables := [⟨7⟩], residualTypeVariables := true}

/-- An actual instantiated header remains valid in a context with a nonempty
flexible scope and residual variables. Neither scope is rewritten to closed. -/
theorem actual_open_header {checked : CallableAncestryPairedLookup.Checked}
    {base : CallableAncestryPairedLookup.Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : RecursiveNamedCatalog.Header prepared values ambient.definitions program) :
    SourceSemantics.DeclarationInstantiation.Valid (openContext program.signatures) header.instantiation ∧
      (openContext program.signatures).typeVariables = [⟨7⟩] ∧
      (openContext program.signatures).residualTypeVariables = true := by
  refine ⟨CallableCoercionRawNamedCallAdmission.header_valid header rfl ?_, rfl, rfl⟩
  constructor
  · exact List.nodup_nil
  · intro parameter member
    cases member
end OpenScope

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, Bool> { function coerce(value: Word) returns (Bool) { let seen = value; if (value == 0) { let coercionGap: Bool; return coercionGap; } return value == 1; } }",
    "function choose<A, B>(left: A, right: B) returns (B) { return right; }",
    "function relay<T>(value: T) returns (T) { return value; }",
    "function fixed(value: Word) returns (Word) { return choose(true, value); }",
    "function fixedRelay(value: Word) returns (Word) { return choose(true, relay(value)); }",
    "function fixedFail() returns (Word) { let before: Word = 61; let rawGap: Word; return rawGap; }",
    "function convert(value: Word) returns (Bool) { return fixed(value); }",
    "function nested(value: Word) returns (Bool) { return fixedRelay(value); }",
    "function early() returns (Bool) { return fixedFail(); }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return fixed(value); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"open admission ordered cells changed: {reprStr state.heap}"

/-- Audit actual retained two-parameter metadata, full selected records, and
unchanged declaration contexts. The parser/checker and cached compiler run here;
these observations do not themselves manufacture a semantic Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (genericExpected : Bool) (pathExpected : Nat) : IO Unit := do
  let base := entry.cached.indexed.base
  let mut genericCount := 0
  let mut pathCount := 0
  for named in base.functions do
    let selected ← SourceCompilerFeatureSupport.get "admission complete selected record"
      (SourceCompilationPlan.exactSpecialization base.plan named.signature.key)
    require (selected == named.specialized) "admission selected record changed"
    let context := declarationContext base.sourceProgram.signatures selected.function.typedBody.owner []
      selected.assumptions selected.function.solvedRequirements
    require (context.residualTypeVariables && context.typeVariables.isEmpty && context.typeParameters.isEmpty &&
      context.solvedRequirements == selected.function.solvedRequirements && context.assumptions == selected.assumptions)
      "actual declaration context was silently closed or reordered"
    for item in selected.function.typedBody.nodes do
      if let .expression node := item then
        if let .call _ arguments (.declaration instantiation) := node.form then
          let target ← SourceCompilerFeatureSupport.get "admission target"
            (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
          let key ← SourceCompilerFeatureSupport.get "admission edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id target)
          let callee ← SourceCompilerFeatureSupport.get "admission callee"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation callee &&
            arguments.length == callee.function.typedBody.inputs.length)
            "admission full original instantiation/domain/order changed"
          if instantiation.parameterSubstitution.length == 2 then
            require (instantiation.parameterSubstitution.map Prod.fst == (callee.parameterSubstitution.map Prod.fst).reverse &&
              instantiation.parameterSubstitution.map Prod.fst != callee.parameterSubstitution.map Prod.fst &&
              instantiation.parameterSubstitution.map Prod.snd == [.word, .bool] && instantiation.predicates.isEmpty)
              "two-parameter retained reverse order/complete values changed"
            genericCount := genericCount + 1
          if !node.coercions.isEmpty then
            require (node.rawType == .word && node.type == .bool && node.coercions.length == 1 && callee.assumptions.isEmpty)
              "ordinary raw result/output path boundary changed"
            pathCount := pathCount + 1
  require ((genericCount > 0) == genericExpected) "actual generic ordinary callee disappeared"
  require (pathCount == pathExpected) "actual raw call output path count changed"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"open admission gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "open admission fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "open admission expected fault")
  let expected ← SourceCompilerFeatureSupport.get "open admission fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "open admission suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "open admission resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "open admission public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "open admission fault resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "open admission checker" (checkProgram workspace 1024)
  let convert ← SourceCompilerFeatureSupport.compileNamed program "convert"
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  inspect convert true 1
  inspect nested true 1
  inspect early false 1
  inspect empty true 0
  let convertGap ← gap convert "coercionGap"
  let nestedGap ← gap nested "coercionGap"
  let rawGap ← gap early "rawGap"
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, extra, expectedGap) in [(convert, false, convertGap), (nested, true, nestedGap)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "open admission resume" (started.resume 500000)
        let initial := [(.word, some (word input)), (.word, some (word input))] ++
          (if extra then [(.word, some (word input))] else []) ++
          [(.bool, some (.bool true)), (.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
        match finished.observation with
        | .done value state =>
          require (input != 0 && reprStr value == reprStr (SourceTypedRuntime.Value.bool (input == 1)))
            "open admission successful result changed"
          cells state initial
        | .fault (.uninitializedLocal actualGap) state =>
          require (input == 0 && actualGap == expectedGap) "open admission unexpected coercion fault"
          cells state (initial ++ [(.bool, none)])
        | other => throw (IO.userError s!"open admission unexpected result: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "open admission early resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal actualGap) state =>
      require (actualGap == rawGap) "open admission raw first fault changed"
      cells state [(.word, some (word 61)), (.word, none)]
    | other => throw (IO.userError s!"open admission early result: {reprStr other}")
    let started ← empty.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let finished ← SourceCompilerFeatureSupport.get "open admission empty resume" (started.resume 500000)
    match finished.observation with
    | .done value state =>
      require (reprStr value == reprStr (word 17)) "open admission empty result changed"
      cells state [(.word, some (word 17)), (.word, some (word 17)), (.bool, some (.bool true)), (.word, some (word 17))]
    | other => throw (IO.userError s!"open admission empty result: {reprStr other}")
  convert.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  nested.checkResume [SourceCompilerFeatureSupport.scalar 2] (.bool false) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  faultResume convert [.word Word.zero]
  faultResume nested [.word Word.zero]
  faultResume early []
  IO.println "raw named admission: actual open declaration contexts/full reversed generic metadata, raw/output/empty paths, ordered full cells and public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCallAdmission
