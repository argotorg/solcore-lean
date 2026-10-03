import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Authenticated children retain the actual special hook, ordered arguments,
and nonempty caller evidence. The final consumers build their Tree from actual
contextual acceptance and close runtime children through catalog mutual meaning.
Callee profiles still use the existing ordinary grammar; raw source typing,
constructor formation, reached headers, and real runtime Entry remain explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableAuthenticatedNamedCalls
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableCoercionExpressionCertificates
open CallableAuthenticatedNamedCallCertificates

section Accepted
variable {checked : Checked} {base : Base checked}
  {ancestry : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
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

variable {caller : SourceSpecialization.SpecializedFunction}
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode} {output : Lowered}
  (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
  (nonempty : caller.assumptions ≠ [])
  (coverage : Coverage headers compilerProgram caller compilation source scope reasonAt)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (nativeSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
  (ordinary : CompatibleExpressionBuiltins.Ordinary source localCatalog compilation.owner)
  (notInitializer : ∀ id node callee arguments instantiation, source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → Syntax source id →
    localCatalog.bindings.find? (fun binding => decide (binding.caller = compilation.owner ∧ binding.initializer = id)) = none)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (projectPolicy : representation.expressions.projectType = SourceCoreCompatibleDataExpressions.projectType values.checked)
  (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
  (typed : ExpressionHasType source context id node.type)
  (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents assignments
    diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok output)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  callerSelected nonempty coverage sourceTypes sourceSignatures nativeSignatures declarations constructorValid ordinary notInitializer
  readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted in
/-- The actual contextual hook supplies every child certificate. No raw or
body runtime law is a premise of this source-to-native consumer. -/
theorem accepted_preserves :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (fun current identifier code => current = scope ∧ identifier = id ∧ code = output)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have tree := tree_of_contextual callerSelected nonempty coverage sourceTypes sourceUnique sourceSignatures nativeSignatures
    declarations constructorValid ordinary notInitializer readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted
  intro current identifier code ⟨rfl, rfl, rfl⟩ root
  exact CallableAuthenticatedNamedCallMeaning.preserves functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing tree

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  callerSelected nonempty coverage sourceTypes sourceSignatures nativeSignatures declarations constructorValid ordinary notInitializer
  readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted in
/-- Reflection measures the actual completion; an independent source run and
preservation are not inputs. The source context's residual flag is untouched. -/
theorem accepted_reflects :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (fun current identifier code => current = scope ∧ identifier = id ∧ code = output)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have tree := tree_of_contextual callerSelected nonempty coverage sourceTypes sourceUnique sourceSignatures nativeSignatures
    declarations constructorValid ordinary notInitializer readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted
  intro current identifier code ⟨rfl, rfl, rfl⟩ root
  exact CallableAuthenticatedNamedCallMeaning.reflects functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing tree
end Accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function first(value: Word) returns (Word) { let firstEffect: Word = 41; return value; }",
    "function second(value: Word) returns (Word) { let secondEffect: Word = 43; return value; }",
    "function join(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 47; return right; }",
    "function fail() returns (Word) { let beforeFault: Word = 53; let missing: Word; return missing; }",
    "function failBody(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 59; let bodyGap: Word; return bodyGap; }",
    "function zero() returns (Word) { let zeroEffect: Word = 61; return 11; }",
    "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
    "function walk(value: Word, depth: Word) returns (Word) { if (depth == 0) { return value; } return walk(value, depth - 1); }",
    "function nested(value: Word) returns (Word) where Word: Marker { return join(first(value), second(first(value))); }",
    "function repeated(value: Word) returns (Word) where Word: Marker { return join(first(value), first(value)); }",
    "function firstFault() returns (Word) where Word: Marker { return join(fail(), second(9)); }",
    "function laterFault() returns (Word) where Word: Marker { return join(first(7), fail()); }",
    "function bodyFault() returns (Word) where Word: Marker { return failBody(first(7), second(9)); }",
    "function empty() returns (Word) where Word: Marker { return zero(); }",
    "function generic(value: Word) returns (Word) where Word: Marker { return choose(first(value), false); }",
    "function recursive() returns (Word) where Word: Marker { return walk(first(7), 2); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def scalar := SourceCompilerFeatureSupport.scalar
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

/-- Each authenticated site is inspected in its real nonempty caller. The
actual contextual compiler is compared with its emitted ordinary call code;
only reached callees are required to be ordinary. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (expectedCalls : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "authenticated caller missing")
  let caller := named.specialized
  require (!caller.assumptions.isEmpty) "authenticated fixture lost its nonempty caller"
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals,
    administrativePrefix := 1, solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let source := caller.function.typedBody
  let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
  let diagnostics ← match base.diagnostics with
    | some value => pure value.program | none => throw (IO.userError "authenticated diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "authenticated own diagnostics missing")
  let reasonAt := diagnostics.reasonAt named.signature.key
  let lower := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let callables := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let available ← get "authenticated caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call _ arguments (.declaration instantiation) := node.form then
        require (node.coercions.isEmpty && node.requirements.isEmpty) "authenticated empty path/requirements changed"
        let output ← get "authenticated actual contextual acceptance" (lower 150 source scope node.id reasonAt)
        let selectedTarget ← get "authenticated exact target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "authenticated actual edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id selectedTarget)
        let selected ← get "authenticated full selected specialization" (SourceCompilationPlan.exactSpecialization base.plan key)
        let dictionary ← get "authenticated actual dictionary"
          (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
        discard <| get "authenticated dictionary check"
          (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions dictionary)
        let (signature, slot) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "authenticated reached global not singleton")
        let reached ← match base.functions.filter (·.signature.key == key) with
          | [row] => pure row | _ => throw (IO.userError "authenticated reached Header not singleton")
        require (reached.specialized == selected && reached.signature == signature && selected.assumptions.isEmpty && dictionary.isEmpty &&
          reprStr instantiation == reprStr (CallableNamedCanonicalOrder.retainedInstantiation selected))
          "authenticated full reached record/retained metadata/ordinary dictionary changed"
        let loweredArgs ← get "authenticated ordered children" (arguments.mapM (fun id => lower 149 source scope id reasonAt))
        let packed := SourceCoreCalls.packArguments loweredArgs
        let expected := SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + slot)
          packed.expression compilation.internalReason
        require (loweredArgs.map (·.type) == reached.inputs.map Prod.snd && packed.type == signature.parameterType &&
          output.type == signature.resultType && output.expression == expected)
          "authenticated ordered argument code/native vector/call slot changed"
        let hooked ← get "authenticated actual evidence special hook"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation
            lower 149 source scope node.id reasonAt callables)
        require (hooked == some output) "actual evidence hook did not select the contextual code"
        match SourceCoreFunctions.selectedSignature representation.expressions compilation source node instantiation false with
        | .error (.callPreparation (.unresolvedAssumptions owner assumptions)) =>
          require (owner == compilation.owner && assumptions == caller.assumptions) "ordinary guard rejected a different caller"
        | _ => throw (IO.userError "ordinary none branch incorrectly accepted nonempty caller")
        let nativeContext := scope.map (fun row => OptionalCell.referenceType row.2) ++ .unit ::
          (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        require (Core.infer? nativeContext output.expression indexed.layouts.definitions == some (LanguageResult.resultType output.type))
          "authenticated emitted native code failed independent checking"
        count := count + 1
  require (count == expectedCalls) s!"authenticated site count changed: {count}/{expectedCalls}"

private def cells (state : SourceTypedRuntime.RuntimeState) (expected : List (Option Nat)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) ==
    reprStr (expected.map fun value => (TypeSystem.Ty.word, value.map word)))
    s!"authenticated full source heap changed: {reprStr state.heap}"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  match (entry.cached.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "authenticated fault binder not unique")

private def publicResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← get "authenticated complete public call" (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  for budget in [0, 41, 137] do
    let started ← get "authenticated suspended public call"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048 | outcome => pure outcome
    match finished, resumed with
    | .succeeded expected, .succeeded actual =>
      let before ← get "authenticated complete public snapshot" (← expected.session.snapshot 2048)
      let after ← get "authenticated resumed public snapshot" (← actual.session.snapshot 2048)
      require (expected.value == actual.value && reprStr before.cells == reprStr after.cells)
        "authenticated success resume changed value/full native store"
    | .failed expected beforeSession, .failed actual afterSession =>
      let before ← get "authenticated complete public fault snapshot" (← beforeSession.snapshot 2048)
      let after ← get "authenticated resumed public fault snapshot" (← afterSession.snapshot 2048)
      require (expected == actual && reprStr before.cells == reprStr after.cells)
        "authenticated failure resume changed reason/full native store"
    | _, _ => throw (IO.userError "authenticated resume changed public outcome")

def run : IO Unit := do
  let program ← get "authenticated fixture check" (checkProgram workspace 1024)
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  let repeated ← SourceCompilerFeatureSupport.compileNamed program "repeated"
  let firstFault ← SourceCompilerFeatureSupport.compileNamed program "firstFault"
  let laterFault ← SourceCompilerFeatureSupport.compileNamed program "laterFault"
  let bodyFault ← SourceCompilerFeatureSupport.compileNamed program "bodyFault"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let generic ← SourceCompilerFeatureSupport.compileNamed program "generic"
  let recursive ← SourceCompilerFeatureSupport.compileNamed program "recursive"
  for (entry, count) in [(nested, 4), (repeated, 3), (firstFault, 3), (laterFault, 3), (bodyFault, 3), (empty, 1), (generic, 2), (recursive, 2)] do
    inspect entry count
  let firstGap ← gap firstFault "missing"
  let laterGap ← gap laterFault "missing"
  let bodyGap ← gap bodyFault "bodyGap"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCoreExecution.Value × Nat × List (Option Nat)) := [
    (nested, [scalar 7], 7, [some 7, some 7, some 41, some 7, some 41, some 7, some 43, some 7, some 7, some 47]),
    (repeated, [scalar 7], 7, [some 7, some 7, some 41, some 7, some 41, some 7, some 7, some 47]),
    (empty, [], 11, [some 61]),
    (recursive, [], 7, [some 7, some 41, some 7, some 2, some 7, some 1, some 7, some 0])]
  let failures : List (SourceCompilerFeatureSupport.Entry × Resolved.LocalId × List (Option Nat)) := [
    (firstFault, firstGap, [some 53, none]),
    (laterFault, laterGap, [some 7, some 41, some 53, none]),
    (bodyFault, bodyGap, [some 7, some 41, some 9, some 43, some 7, some 9, some 59, none])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, heap) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "authenticated source observation resume" (started.resume 500000)
      match finished.observation with
      | .done value state => require (reprStr value == reprStr (word expected)) "authenticated value changed"; cells state heap
      | other => throw (IO.userError s!"authenticated expected success: {reprStr other}")
    for (entry, binder, heap) in failures do
      let started ← entry.audit [] budget
      let finished ← get "authenticated fault source observation resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actual) state => require (actual == binder) "authenticated first fault changed"; cells state heap
      | other => throw (IO.userError s!"authenticated expected fault: {reprStr other}")
    let genericRun ← generic.audit [scalar 7] budget
    let genericRun ← get "authenticated generic resume" (genericRun.resume 500000)
    match genericRun.observation with
    | .done value state =>
      require (reprStr value == reprStr (word 7) &&
        reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr
          [(TypeSystem.Ty.word, some (word 7)), (.word, some (word 7)), (.word, some (word 41)),
           (.word, some (word 7)), (.bool, some (SourceTypedRuntime.Value.bool false))])
        "authenticated generic full heap/raw parameter order changed"
    | other => throw (IO.userError s!"authenticated generic failed: {reprStr other}")
  for (entry, arguments, _, _) in successes do publicResume entry arguments
  for (entry, _, _) in failures do publicResume entry []
  publicResume generic [scalar 7]
  IO.println "authenticated named children: actual nonempty caller hook/full records/ordered nested args/first faults/full heaps/resume GREEN"

end Tests.SourceCoreCallableAuthenticatedNamedCalls
