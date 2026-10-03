import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual reached selection closes full named argument Trees without covering
unrelated global methods. The original ordered source metadata, separate
occurrence order, empty caller assumptions, constructor raw ranges, source
typing and installed catalog authority remain explicit. The tests do not
reinterpret authenticated special calls as ordinary emissions. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreRecursiveNamedReachedExpressions
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem sequence
    {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {readFuel : Nat} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List Lowered}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM (fun id => child fuel source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → child fuel source scope id reasonAt = .ok code →
      Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code) :
    DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope ids types codes ∧ types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨.nil, rfl⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at accepted
      obtain ⟨code, first, accepted⟩ := bind_ok accepted
      obtain ⟨restCodes, rest, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have tree := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨remaining, projected⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      have sequence : DataExpressionSequence.Tree source
          (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
          scope (id :: ids) (type :: types) (code :: restCodes) := by
        cases remaining with
        | nil => exact sourceType ▸ .single found tree
        | single nextFound nextTree => exact sourceType ▸ .cons found tree (.single nextFound nextTree)
        | cons nextFound nextTree tailTree => exact sourceType ▸ .cons found tree (.cons nextFound nextTree tailTree)
      refine ⟨sequence, ?_⟩
      simp [List.mapM_cons, ← sourceType, RecursiveNamedExpressionCompilerCertificates.tree_projected tree found, projected, bind, Except.bind]


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
  (programTyped : ProgramWellFormed (Program.ofChecked compilerProgram))
  (nativeProjections : ∀ memberHeader, memberHeader ∈ headers →
    (memberHeader.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (memberHeader.bindings.map Prod.snd))
  (ordinaryEvidence : ∀ memberHeader, memberHeader ∈ headers → memberHeader.function.evidence = [])
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (nativeSignatures : context.signatures = values.checked.signatures)
  (typed : ExpressionHasType source context id node.type)
  (lexical : context.typeVariables = [])
  {admitted : ExpressionId → Prop}
  (admission : RecursiveNamedExpressionCompilerCertificates.Admission source admitted)
  (coverage : RecursiveNamedCallSelectionCertificates.ReachedCoverage headers compilation source admitted)
  (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → RecursiveNamedCallSelectionCertificates.Ordered compilation.plan instantiation)
  (constructorRanges : CompatibleExpressionInstantiationLaws.ConstructorRanges source
    (fun id => admitted id ∨ CompatibleExpressionBuiltins.Syntax source id))
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents
    assignments diagnostics compilation (some native) none skipInitializer)
  (allowed : ∀ argument, argument ∈ arguments → admitted argument)
  (ordinary : RecursiveNamedExpressionCompilerCertificates.Ordinary source localCatalog compilation.owner admitted)
  (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok callerFunction)
  (callerClosed : callerFunction.assumptions = [])
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
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges admission coverage order childEq allowed ordinary callerSelected callerClosed declarations readPolicy lowerPolicy leafPolicy
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
  have sourceTypes := RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures nativeProjections ordinaryEvidence
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes sourceUnique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) sourceUnique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      RecursiveNamedSelectedExpressionFactory.tree_of_contextual_at admission coverage sourceTypes order ordinary callerSelected callerClosed
        sourceUnique lexical constructorRanges sourceSignatures declarations nativeSignatures (allowed argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
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
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges admission coverage order childEq allowed ordinary callerSelected callerClosed declarations readPolicy lowerPolicy leafPolicy
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
  have sourceTypes := RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures nativeProjections ordinaryEvidence
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes sourceUnique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) sourceUnique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      RecursiveNamedSelectedExpressionFactory.tree_of_contextual_at admission coverage sourceTypes order ordinary callerSelected callerClosed
        sourceUnique lexical constructorRanges sourceSignatures declarations nativeSignatures (allowed argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
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



section Boundaries
open RecursiveNamedCallSelectionCertificates
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {definitions : DataEnvironment} {program : SourceSemantics.Program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource}

theorem empty_domain (plan : compilation.plan = base.plan) :
    ReachedCoverage ([] : Inventory prepared values definitions program) compilation source (fun _ => False) := by
  refine ⟨plan, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ allowed
    exact False.elim allowed
  · simp

theorem unrelated_global_not_covered {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (slot : compilation.globals[index]? = some signature)
    (selected : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    ¬ Coverage ([] : Inventory prepared values definitions program) compilation := by
  intro coverage
  obtain ⟨header, member, _⟩ := coverage.slots index signature specialized slot selected
  cases member
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, integer> { function coerce(value: Word) returns (integer) { let seen = value; if (value == 0) { let coercionGap: integer; return coercionGap; } return wordToInteger(value); } }",
    "function choose<A, B>(unused: A, value: B) returns (B) { return value; }",
    "function tag<T>(value: T) returns (T) { let seen = value; return value; }",
    "function flag(value: Word) returns (Bool) { let seen = value; return value == 1; }",
    "function failWord(value: Word) returns (Word) { let nestedGap: Word; return nestedGap; }",
    "function last(a: Word, b: Word, c: Word) returns (Word) { return c; }",
    "function one() returns (Word) { return 1; }",
    "function good(value: Word) returns (integer) { return choose(flag(value), tag(value)); }",
    "function first(value: Word) returns (integer) { return choose(failWord(value), tag(value)); }",
    "function later(value: Word) returns (integer) { return choose(tag(value), failWord(value)); }",
    "function single(value: Word) returns (integer) { return tag(tag(value)); }",
    "function repeated(value: Word) returns (integer) { return last(tag(value), tag(value), tag(value)); }",
    "function zero() returns (integer) { return one(); }",
    "function empty(value: Word) returns (Word) { return choose(flag(value), tag(value)); }",
    "function boxed(value: Word) returns (integer) { return choose(Box(tag(value)), tag(value)); }",
    "function builtin(value: Word) returns (integer) { return choose(integerEq(wordToInteger(tag(value)), wordToInteger(1)), tag(value)); }",
    "function lazy(value: Word) returns (integer) { return choose(flag(value), value == 1 ? tag(value) : failWord(value)); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"reached arguments ordered cells changed: {reprStr state.heap}"

/-- Audit real child callbacks and selected records. A method slot is kept in
the global list and deliberately is not interpreted as an ordinary Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (outerName : String)
    (arity pathCount nestedCount : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "reached arguments caller missing")
  let caller := named.specialized
  let source := caller.function.typedBody
  let context := declarationContext base.sourceProgram.signatures source.owner [] caller.assumptions caller.function.solvedRequirements
  require (context.residualTypeVariables && context.typeVariables.isEmpty && context.solvedRequirements == caller.function.solvedRequirements)
    "reached arguments actual caller context changed"
  let scope ← get "reached arguments scope" ((SourceCoreDataPlaces.declaredBinders source).reverse.mapM fun binder => do
    let type ← entry.cached.compatible.checked.catalog.project binder.scheme.body
    pure (binder.id, type))
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "reached arguments diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "reached arguments own diagnostics missing")
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let reasonAt := diagnostics.reasonAt named.signature.key
  let available ← get "reached arguments available" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  require caller.assumptions.isEmpty "reached arguments require the actual closed caller"
  let ordinaryPolicy := {representation.expressions with callables := policy}
  let mut outerCount := 0
  let mut reachedCount := 0
  let mut methodCount := 0
  for signature in base.globals do
    let selected ← get "reached global full record" (SourceCompilationPlan.exactSpecialization base.plan signature.key)
    if !(base.sourceProgram.signatures.functions.any (·.id == selected.key.declaration)) then
      methodCount := methodCount + 1
  for item in source.nodes do
    if let .expression node := item then
      if let .call callee arguments (.declaration instantiation) := node.form then
        let target ← get "reached target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "reached edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let selected ← get "reached record" (SourceCompilationPlan.exactSpecialization base.plan key)
        let declared ← match base.sourceProgram.signatures.functions.find? (·.id == selected.key.declaration) with
          | some signature => pure signature | none => throw (IO.userError "reached call is not an ordinary declaration")
        let isOuter := declared.name == outerName && node.coercions.length == pathCount
        require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation selected && selected.assumptions.isEmpty &&
          instantiation.parameterSubstitution.map Prod.fst == (selected.parameterSubstitution.map Prod.fst).reverse &&
          selected.function.typedBody.inputs.length == arguments.length) "reached full metadata/domain/arity changed"
        discard <| get "reached direct callee" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "reached global not singleton")
        let codes ← get "reached ordered mapM" (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
        let projected ← get "reached ordered native types" (selected.function.typedBody.inputs.mapM fun binder =>
          entry.cached.compatible.checked.catalog.project binder.scheme.body)
        require (codes.map (·.type) == projected && signature.parameterType == (SourceCoreCalls.packArguments codes).type)
          "reached ordered code/native vector mismatch"
        let raw : SourceCoreBasic.LoweredExpr := ⟨signature.resultType, SourceCoreCalls.call signature
          (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let special ← get "reached actual special" (SourceCoreEvidence.lowerWithProjector base.sourceProgram
          representation.expressions.projectType caller compilation child 150 source scope node.id reasonAt policy)
        if isOuter && pathCount > 0 then
          require (arguments.length == arity) "reached parent arity changed"
          let expected ← get "reached actual suffix" (SourceCoreEvidence.applyCoercions base.sourceProgram
            representation.expressions.projectType compilation caller available scope node policy raw node.coercions)
          require (special == some expected) "reached actual outer emission mismatch"
          let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
            (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
          require (Core.infer? nativeContext expected.expression indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
            "reached actual parent native typing changed"
          outerCount := outerCount + 1
        else
          require (special == none && node.coercions.isEmpty && node.requirements.isEmpty)
            "reached ordinary child cannot use authenticated special emission"
          let (selectedIndex, selectedSignature) ← get "reached ordinary selectedSignature"
            (SourceCoreFunctions.selectedSignature ordinaryPolicy compilation source node instantiation false)
          require (selectedIndex == index && selectedSignature == signature) "reached ordinary full signature changed"
          let full ← match base.functions[index]? with
            | some full => pure full | none => throw (IO.userError "reached actual ordinary row missing")
          require (full.signature == signature && full.specialized == selected) "reached full prepared row changed"
          let code ← get "reached original contextual child" (child 151 source scope node.id reasonAt)
          require (code == raw) "reached original ordinary child/code changed"
          if isOuter then outerCount := outerCount + 1 else reachedCount := reachedCount + 1
  require (outerCount == 1 && reachedCount == nestedCount) s!"reached site count changed {outerCount}/{reachedCount}"
  require (methodCount == pathCount) s!"reached unrelated method count changed {methodCount}"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"reached arguments gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "reached arguments fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "reached arguments expected fault")
  let expected ← SourceCompilerFeatureSupport.get "reached arguments fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "reached arguments suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "reached arguments resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "reached arguments public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "reached arguments fault resume changed outcome")


private def words (n count : Nat) : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
  List.replicate count (.word, some (word n))

def run : IO Unit := do
  let program ← get "reached arguments checker" (checkProgram workspace 1024)
  let entries ← ["good", "first", "later", "single", "repeated", "zero", "empty", "boxed", "builtin", "lazy"].mapM
    (SourceCompilerFeatureSupport.compileNamed program)
  let [good, first, later, single, repeated, zero, empty, data, builtin, lazy] := entries
    | throw (IO.userError "reached fixture entries missing")
  inspect good "choose" 2 1 2
  inspect first "choose" 2 1 2
  inspect later "choose" 2 1 2
  inspect single "tag" 1 1 1
  inspect repeated "last" 3 1 3
  inspect zero "one" 0 1 0
  inspect empty "choose" 2 0 2
  inspect data "choose" 2 1 2
  inspect builtin "choose" 2 1 2
  inspect lazy "choose" 2 1 3
  let coercionGap ← gap good "coercionGap"
  let nestedGap ← gap first "nestedGap"
  let lazyGap ← gap lazy "nestedGap"
  let laterGap ← gap later "nestedGap"
  let named ← match data.cached.indexed.base.functions.find? (·.signature.key == data.key) with
    | some named => pure named | none => throw (IO.userError "reached data root missing")
  let ctor ← match named.specialized.function.typedBody.nodes.filterMap (fun item => match item with
    | .expression node => match node.form with | .constructor instantiation _ => some (node.type, instantiation) | _ => none
    | _ => none) with
    | [row] => pure row | _ => throw (IO.userError "reached constructor missing")
  require (ctor.2.parameterSubstitution.map Prod.snd == [.word]) "reached complete constructor raw range changed"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (good, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3),
    (single, [SourceCompilerFeatureSupport.scalar 2], .integer 2, words 2 7),
    (repeated, [SourceCompilerFeatureSupport.scalar 3], .integer 3, words 3 12),
    (zero, [], .integer 1, words 1 2),
    (empty, [SourceCompilerFeatureSupport.scalar 2], word 2, words 2 5 ++ [(.bool, some (.bool false))] ++ words 2 1),
    (data, [SourceCompilerFeatureSupport.scalar 7], .integer 7, words 7 5 ++ [(ctor.1, some (.constructed ctor.2 [word 7]))] ++ words 7 3),
    (builtin, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3),
    (lazy, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3)]
  let failures : List (SourceCompilerFeatureSupport.Entry × Nat × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (first, 1, nestedGap, words 1 2 ++ [(.word, none)]),
    (later, 1, laterGap, words 1 4 ++ [(.word, none)]),
    (lazy, 2, lazyGap, words 2 4 ++ [(.word, none)]),
    (good, 0, coercionGap, words 0 5 ++ [(.bool, some (.bool false))] ++ words 0 3 ++ [(.integer, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "reached arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "reached arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"reached arguments success failed: {reprStr other}")
    for (entry, input, expectedGap, expectedCells) in failures do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← get "reached arguments fault resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "reached arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"reached arguments fault changed: {reprStr other}")
  for (entry, arguments, expected, _) in successes do
    let nativeExpected : SourceCoreExecution.Value := match expected with | .word w => .word w | .integer i => .integer i | _ => .unit
    entry.checkResume arguments nativeExpected 41
  for (entry, input, _, _) in failures do faultResume entry [SourceCompilerFeatureSupport.scalar input]
  IO.println "reached expressions: actual named/builtin ordered children with uncovered method slots, full metadata, first/later/path faults, complete heaps/resume GREEN"

end Tests.SourceCoreRecursiveNamedReachedExpressions
