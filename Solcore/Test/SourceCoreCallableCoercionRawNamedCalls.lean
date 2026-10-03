import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual outer ordinary calls use the reached full header and original-source
ordered argument Trees. The formal consumers close argument/body runtime laws
through catalog mutual induction. Initial authority and static profiles remain
explicit; no coverage of all coercion-method globals is claimed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCalls
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
  (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
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
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes closed residual typed children nativeTypes
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
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallCertificates.of_tree receipt reached sourceTypes sourceUnique closed residual typed children nativeTypes
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
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes closed residual typed children nativeTypes
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
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallCertificates.of_tree receipt reached sourceTypes sourceUnique closed residual typed children nativeTypes
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
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function identity(value: Word) returns (Word) { let rawEffect: Word = 19; return value; }",
    "function rawFail() returns (Word) { let rawEffect: Word = 23; let rawGap: Word; return rawGap; }",
    "function first(value: Word) returns (Word) { let firstEffect: Word = 41; return value; }",
    "function second(value: Word) returns (Word) { let secondEffect: Word = 43; return value; }",
    "function combine(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 47; return right; }",
    "function failBody(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 53; let bodyGap: Word; return bodyGap; }",
    "function recurse(value: Word, depth: Word) returns (Word) { if (depth == 0) { return value; } return recurse(value, depth - 1); }",
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(first(7), second(value)); return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = combine(first(7), second(value)); return result; }",
    "function recursive(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = recurse(value, 2); return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(rawFail(), second(1)); return result; }",
    "function secondFault() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(first(7), rawFail()); return result; }",
    "function bodyFault() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = failBody(first(7), second(1)); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained constructors used by the three output edges. -/
private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def audit (entry : SourceCompilerFeatureSupport.Entry) (targetName : String) :
    IO (DataConstructorInstantiation × DataConstructorInstantiation × List Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "source path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "source path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let constructor ← constructorFor base.sourceProgram "Box"
  let target ← constructorFor base.sourceProgram targetName
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 3) "actual coercion path lost its three edges"
        let mut goals : List TypeSystem.Ty := []
        for step in node.coercions do
          let method ← SourceCompilerFeatureSupport.get "path method"
            (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
          let dictionary ← SourceCompilerFeatureSupport.get "path dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
          let key ← SourceCompilerFeatureSupport.get "path edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id method.specialized.key)
          let selected ← SourceCompilerFeatureSupport.get "path full selected record"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          let emitted ← match base.functions.find? (·.signature.key == key) with
            | some emitted => pure emitted | none => throw (IO.userError "path native row missing")
          SourceCompilerFeatureSupport.require (selected == method.specialized && emitted.specialized == selected &&
            emitted.inputs.length == 1 && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions &&
            method.traitPredicates.all caller.assumptions.contains)
            "path full record / ordered repeated dictionary / caller coverage changed"
          goals := goals ++ [step.source, step.target]
          let declared := (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
            (fun binder => binder.name == "firstGap" || binder.name == "secondGap" || binder.name == "lastGap")
          match declared with
          | [binder] => gaps := gaps ++ [binder.id]
          | [] =>
            SourceCompilerFeatureSupport.require (step.target == target.resultType && targetName == "Final")
              "only successful terminal method may lack a gap"
          | _ => throw (IO.userError "source path ambiguous method gap")
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType, constructor.resultType, target.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let indexed := entry.cached.indexed
        let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
        let diagnostics ← match base.diagnostics with
          | some diagnostics => pure diagnostics.program
          | none => throw (IO.userError "outer diagnostics missing")
        let diagnostics := match base.callableContext with
          | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
          | none => diagnostics
        let own ← match diagnostics.base.find? named.signature.key with
          | some own => pure own | none => throw (IO.userError "outer caller diagnostics missing")
        let source := caller.function.typedBody
        let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
        let reasonAt := diagnostics.reasonAt named.signature.key
        let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
          base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
        let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
        let result ← SourceCompilerFeatureSupport.get "actual outer lowerWithProjector"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
            150 source scope node.id reasonAt policy)
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "coerced outer delegated unexpectedly")
        let raw ← match node.form with
          | .call callee arguments (.declaration instantiation) => do
            discard <| SourceCompilerFeatureSupport.get "actual callee metadata"
              (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
            let dictionary ← SourceCompilerFeatureSupport.get "actual direct dictionary"
              (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
            let target ← SourceCompilerFeatureSupport.get "actual direct target"
              (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
            let key ← SourceCompilerFeatureSupport.get "actual direct edge"
              (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
            let selected ← SourceCompilerFeatureSupport.get "actual direct full record"
              (SourceCompilationPlan.exactSpecialization base.plan key)
            discard <| SourceCompilerFeatureSupport.get "actual direct authentication"
              (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions dictionary)
            let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
              | [row] => pure row | _ => throw (IO.userError "actual direct global is not singleton")
            let native ← match base.functions.filter (·.signature.key == key) with
              | [native] => pure native | _ => throw (IO.userError "ordinary reached header is not singleton")
            SourceCompilerFeatureSupport.require (native.specialized == selected && native.signature == signature &&
              selected.assumptions.isEmpty && dictionary.isEmpty && arguments.length == 2)
              "reached ordinary full record/signature/empty dictionary/two arguments changed"
            let loweredArgs ← SourceCompilerFeatureSupport.get "actual ordered direct children"
              (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
            let packed := SourceCoreCalls.packArguments loweredArgs
            SourceCompilerFeatureSupport.require (signature.parameterType == packed.type &&
              arguments.length == selected.function.typedBody.inputs.length) "actual direct arity changed"
            pure ⟨signature.resultType, SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + index)
              packed.expression compilation.internalReason⟩
          | _ => throw (IO.userError s!"outer test unhandled raw form: {reprStr node.form}")
        let replayed ← SourceCompilerFeatureSupport.get "outer same applyCoercions suffix"
          (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType compilation caller available
            scope node policy raw node.coercions)
        SourceCompilerFeatureSupport.require (replayed == lowered) "outer actual operand/suffix code changed"
        let outputType ← SourceCompilerFeatureSupport.get "outer result projection"
          (entry.cached.compatible.checked.catalog.project target.resultType)
        let nativeContext := scope.map (fun row => OptionalCell.referenceType row.2) ++
          .unit :: (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? nativeContext lowered.expression indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "outer actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual three-step path not reached"
  SourceCompilerFeatureSupport.require (gaps.length == (if targetName == "Final" then 2 else 3))
    "source path method fault positions changed"
  pure (constructor, target, gaps)

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")

private def auditBypass (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "bypass caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let mut count := 0
  for item in named.specialized.function.typedBody.nodes do
    if let .expression node := item then
      if let .call _ _ (.declaration _) := node.form then
        let actual := SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
          compilation (fun _ _ _ id _ => .error (.missingExpression id)) 100 named.specialized.function.typedBody [] node.id (fun _ => Word.zero)
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && node.requirements.isEmpty && (match actual with | .ok none => true | _ => false))
          "empty evidence path must bypass before calling even a rejecting child"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "bypass actual direct occurrence missing"

private def auditSelectedEmpty (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "empty selected caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let source := named.specialized.function.typedBody
  let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
  let child : SourceCoreEvidence.Child := fun fuel source scope id reasonAt => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call _ arguments (.declaration instantiation) := node.form then
        let result ← SourceCompilerFeatureSupport.get "empty selected actual outer"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
            compilation child 100 source scope node.id (fun _ => Word.zero))
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "caller-owned empty suffix lost its authentication")
        let target ← SourceCompilerFeatureSupport.get "empty selected target"
          (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← SourceCompilerFeatureSupport.get "empty selected edge"
          (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "empty selected globals changed")
        let args ← SourceCompilerFeatureSupport.get "empty selected ordered args"
          (arguments.mapM (fun id => child 100 source scope id (fun _ => Word.zero)))
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && !named.specialized.assumptions.isEmpty &&
          lowered.type == signature.resultType && lowered.expression == SourceCoreCalls.call signature
            (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments args).expression compilation.internalReason)
          "empty selected suffix changed raw call code or metadata"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "empty selected direct occurrence missing"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"raw named gap {name} was not unique")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "raw named checker" (checkProgram workspace 1024)
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let (box, final, pathGaps) ← audit direct "Final"
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let recursive ← SourceCompilerFeatureSupport.compileNamed program "recursive"
  let _ ← audit recursive "Final"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let secondFault ← SourceCompilerFeatureSupport.compileNamed program "secondFault"
  let _ ← audit secondFault "Final"
  let bodyFault ← SourceCompilerFeatureSupport.compileNamed program "bodyFault"
  let _ ← audit bodyFault "Final"
  let earlyGap ← gap early "rawGap"
  let secondGap ← gap secondFault "rawGap"
  let bodyGap ← gap bodyFault "bodyGap"
  let emptySelected ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  auditSelectedEmpty emptySelected
  let bypass ← SourceCompilerFeatureSupport.compileNamed program "bypass"
  auditBypass bypass
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault, recursiveCall) in [(direct, false, false), (late, true, false), (recursive, false, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "raw named resume" (started.resume 500000)
        let rawPrefix := if recursiveCall then
          [(.word, some (word input)), (.word, some (word 2)),
           (.word, some (word input)), (.word, some (word 1)),
           (.word, some (word input)), (.word, some (word 0))]
          else [(.word, some (word 7)), (.word, some (word 41)),
            (.word, some (word input)), (.word, some (word 43)),
            (.word, some (word 7)), (.word, some (word input)), (.word, some (word 47))]
        let firstCells := [(.word, some (word input))] ++ rawPrefix ++ [(.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "raw named result changed"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "ordered args/body/all methods"
        | .fault (.uninitializedLocal id) state =>
          if input == 0 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[0]?) "raw named first path fault changed"
            cells state (firstCells ++ [(.bool, none)]) "first method / two skipped"
          else if input == 2 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[1]?) "raw named middle path fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle method / final skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1 && some id == lateGaps[2]?)
              "raw named final path fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "final method"
        | other => throw (IO.userError s!"raw named unexpected: {reprStr other}")
    for (entry, expectedGap, expectedCells) in [
      (early, earlyGap, [(.word, some (word 23)), (.word, none)]),
      (secondFault, secondGap, [(.word, some (word 7)), (.word, some (word 41)), (.word, some (word 23)), (.word, none)]),
      (bodyFault, bodyGap, [(.word, some (word 7)), (.word, some (word 41)), (.word, some (word 1)), (.word, some (word 43)),
        (.word, some (word 7)), (.word, some (word 1)), (.word, some (word 53)), (.word, none)])] do
      let started ← entry.audit [] budget
      let finished ← SourceCompilerFeatureSupport.get "raw named prefix resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        SourceCompilerFeatureSupport.require (actualGap == expectedGap) "raw named first failure binder changed"
        cells state expectedCells "raw failure / all path skipped"
      | other => throw (IO.userError s!"raw named prefix unexpected: {reprStr other}")
    for entry in [emptySelected, bypass] do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar 17] budget
      let finished ← SourceCompilerFeatureSupport.get "raw named empty suffix resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty named result changed"
        cells state [(.word, some (word 17)), (.word, some (word 17)), (.word, some (word 19))] "empty suffix"
      | other => throw (IO.userError s!"raw named empty suffix unexpected: {reprStr other}")
  emptySelected.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  bypass.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  direct.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  recursive.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume direct [.word Word.zero]
  faultResume direct [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  faultResume secondFault []
  faultResume bodyFault []
  IO.println "raw named coercions: actual full ordinary selection/ordered arguments, nested and recursive bodies, empty/first/middle/last paths, argument/body faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCalls
