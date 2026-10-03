import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual scalar argument callbacks close the final raw-call argument Trees.
The concrete semantic consumers retain the original parent requirements/output
path, reached full header, actual BodyState profiles and catalog/method Entry.
No raw/child/body runtime law or pre-run of the source is an input. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCallScalarArguments
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
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents
    assignments diagnostics compilation native parent skipInitializer)
  (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionConditionals.Syntax source argument)
  (ordinary : CompatibleExpressionConditionals.Ordinary source localCatalog compilation.owner)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
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
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
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
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallScalarArguments.of_contextual receipt childEq reached sourceTypes sourceUnique sourceSignatures typed syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
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
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
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
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallScalarArguments.of_contextual receipt childEq reached sourceTypes sourceUnique sourceSignatures typed syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
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


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, Bool> { function coerce(value: Word) returns (Bool) { let seen = value; if (value == 0) { let coercionGap: Bool; return coercionGap; } return value == 1; } }",
    "function choose<A, B>(unused: A, value: B) returns (B) { return value; }",
    "function relay<T>(value: T) returns (T) { return value; }",
    "function last(a: Word, b: Word, c: Word) returns (Word) { return c; }",
    "function one() returns (Word) { return 1; }",
    "function converted(value: Word) returns (Bool) { return choose((value == 1), (value + 0)); }",
    "function lazy(value: Word) returns (Bool) { let rawGap: Word; return choose(!false, value == 1 ? (value + 0) : rawGap); }",
    "function first(value: Word) returns (Bool) { let firstGap: Bool; let secondGap: Word; return choose(firstGap, secondGap); }",
    "function second(value: Word) returns (Bool) { let secondGap: Word; return choose(value == 1, secondGap); }",
    "function paired(value: Word) returns (Bool) { return choose((value, true), value); }",
    "function empty(value: Word) returns (Word) where Word: Marker { return choose(false, value + 1); }",
    "function repeated(value: Word) returns (Bool) { return last(value, value, value); }",
    "function zero() returns (Bool) { return one(); }",
    "function single(value: Word) returns (Bool) { return relay(value); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"scalar arguments ordered cells changed: {reprStr state.heap}"

private def scalarSyntax (source : TypedSource) : Nat → ExpressionId → Bool
  | 0, _ => false
  | fuel + 1, id => match source.lookupExpression? id with
    | none => false
    | some node => match node.form with
      | .literal _ | .integerLiteral _ _ | .reference _ (.builtinBoolean _) | .reference _ (.local _) => true
      | .group inner | .unary _ inner => scalarSyntax source fuel inner
      | .tuple [left, right] | .binary left _ right => scalarSyntax source fuel left && scalarSyntax source fuel right
      | .conditional condition left right => scalarSyntax source fuel condition && scalarSyntax source fuel left && scalarSyntax source fuel right
      | _ => false

/-- Re-enter the production contextual callback at the actual final lexical
scope. Check complete selected metadata and exactly the ordered argument code;
this runtime audit does not manufacture source typing or a semantic Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (arity pathCount : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "scalar arguments caller missing")
  let caller := named.specialized
  let source := caller.function.typedBody
  let context := declarationContext base.sourceProgram.signatures source.owner [] caller.assumptions caller.function.solvedRequirements
  require (context.residualTypeVariables && context.typeVariables.isEmpty && context.solvedRequirements == caller.function.solvedRequirements)
    "scalar arguments actual caller context changed"
  let scope ← get "scalar arguments scope" ((SourceCoreDataPlaces.declaredBinders source).reverse.mapM fun binder => do
    let type ← entry.cached.compatible.checked.catalog.project binder.scheme.body
    pure (binder.id, type))
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "scalar arguments diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "scalar arguments own diagnostics missing")
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let reasonAt := diagnostics.reasonAt named.signature.key
  let available ← get "scalar arguments available" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call callee arguments (.declaration instantiation) := node.form then
        require (arguments.length == arity && arguments.all (scalarSyntax source 100) && node.coercions.length == pathCount)
          s!"scalar arguments original syntax/arity/path changed: key={reprStr entry.key}, args={reprStr arguments}, scalar={reprStr (arguments.map (scalarSyntax source 100))}, path={node.coercions.length}"
        discard <| get "scalar arguments callee" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
        let target ← get "scalar arguments target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "scalar arguments edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let selected ← get "scalar arguments record" (SourceCompilationPlan.exactSpecialization base.plan key)
        require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation selected && selected.assumptions.isEmpty &&
          instantiation.parameterSubstitution.map Prod.fst == (selected.parameterSubstitution.map Prod.fst).reverse &&
          selected.function.typedBody.inputs.length == arity)
          "scalar arguments full original metadata/order changed"
        let dictionary ← get "scalar arguments dictionary" (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
        require dictionary.isEmpty "scalar arguments ordinary dictionary changed"
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "scalar arguments actual global not singleton")
        let codes ← get "scalar arguments ordered mapM" (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
        let sourceTypes ← get "scalar arguments raw types" (selected.function.typedBody.inputs.mapM fun binder =>
          entry.cached.compatible.checked.catalog.project binder.scheme.body)
        require (codes.map (·.type) == sourceTypes && signature.parameterType == (SourceCoreCalls.packArguments codes).type)
          "scalar arguments actual native vector changed"
        let raw : SourceCoreBasic.LoweredExpr := ⟨signature.resultType, SourceCoreCalls.call signature
          (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let expected ← get "scalar arguments suffix" (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType
          compilation caller available scope node policy raw node.coercions)
        let result ← get "scalar arguments actual outer" (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType
          caller compilation child 150 source scope node.id reasonAt policy)
        require (result == some expected) "scalar arguments actual parent code changed"
        let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
          (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        require (Core.infer? nativeContext expected.expression indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
          "scalar arguments actual native code is ill typed"
        count := count + 1
  require (count == 1) "scalar arguments reached direct site missing"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"scalar arguments gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "scalar arguments fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "scalar arguments expected fault")
  let expected ← SourceCompilerFeatureSupport.get "scalar arguments fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "scalar arguments suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "scalar arguments resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "scalar arguments public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "scalar arguments fault resume changed outcome")


def run : IO Unit := do
  let program ← get "scalar arguments checker" (checkProgram workspace 1024)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  let lazy ← SourceCompilerFeatureSupport.compileNamed program "lazy"
  let first ← SourceCompilerFeatureSupport.compileNamed program "first"
  let second ← SourceCompilerFeatureSupport.compileNamed program "second"
  let paired ← SourceCompilerFeatureSupport.compileNamed program "paired"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let repeated ← SourceCompilerFeatureSupport.compileNamed program "repeated"
  let zero ← SourceCompilerFeatureSupport.compileNamed program "zero"
  let single ← SourceCompilerFeatureSupport.compileNamed program "single"
  for entry in [converted, lazy, first, second, paired] do inspect entry 2 1
  inspect empty 2 0
  inspect repeated 3 1
  inspect zero 0 1
  inspect single 1 1
  let coercionGap ← gap converted "coercionGap"
  let rawGap ← gap lazy "rawGap"
  let firstGap ← gap first "firstGap"
  let secondGap ← gap second "secondGap"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (converted, [SourceCompilerFeatureSupport.scalar 2], .bool false, [(.word, some (word 2)), (.bool, some (.bool false)), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (lazy, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, none), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (paired, [SourceCompilerFeatureSupport.scalar 2], .bool false, [(.word, some (word 2)), (.product .word .bool, some (.product (word 2) (.bool true))), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (empty, [SourceCompilerFeatureSupport.scalar 17], word 18, [(.word, some (word 17)), (.bool, some (.bool false)), (.word, some (word 18))]),
    (repeated, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (zero, [], .bool true, [(.word, some (word 1)), (.word, some (word 1))]),
    (single, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))])]
  let failures : List (SourceCompilerFeatureSupport.Entry × Nat × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, 0, coercionGap, [(.word, some (word 0)), (.bool, some (.bool false)), (.word, some (word 0)), (.word, some (word 0)), (.word, some (word 0)), (.bool, none)]),
    (lazy, 2, rawGap, [(.word, some (word 2)), (.word, none)]),
    (first, 1, firstGap, [(.word, some (word 1)), (.bool, none), (.word, none)]),
    (second, 1, secondGap, [(.word, some (word 1)), (.word, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "scalar arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "scalar arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"scalar arguments success failed: {reprStr other}")
    for (entry, input, expectedGap, expectedCells) in failures do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← get "scalar arguments failure resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "scalar arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"scalar arguments fault changed: {reprStr other}")
  converted.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  lazy.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 18)) 41
  repeated.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  zero.checkResume [] (.bool true) 41
  for (entry, input, _, _) in failures do faultResume entry [.word (Word.ofNatModulo input)]
  IO.println "scalar raw named arguments: actual ordered callbacks/full metadata, empty/single/packed arguments, lazy and first/later faults, complete heaps/public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCallScalarArguments
