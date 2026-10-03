import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual outer acceptance retains raw arguments, selected slots and emitted
suffixes. The formal consumers keep the original raw-form laws explicit; they
do not claim recursive expression meaning. Runtime checks cover real delegated
and direct output coercions, ordered effects and resumed fault prefixes. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionExpressions
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning

section Receipt
variable {program : CheckedProgram} {project : Projector} {callerFunction : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}

theorem direct_result_from_outer
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program project callerFunction compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    ∃ receipt : Direct program project callerFunction compilation child fuel source scope id callee arguments instantiation reasonAt policy node output,
      CallableNamedMetadata.Matches receipt.selection.specialized instantiation ∧
      arguments.mapM (fun argument => child fuel source scope argument reasonAt) = .ok receipt.loweredArguments ∧
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) = [(receipt.native.signature, receipt.native.index)] ∧
      receipt.operand = ⟨receipt.native.signature.resultType, SourceCoreCalls.call receipt.native.signature
        (scope.length + compilation.administrativePrefix + receipt.native.index)
        (SourceCoreCalls.packArguments receipt.loweredArguments).expression compilation.internalReason⟩ := by
  obtain ⟨receipt⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form accepted
  exact ⟨receipt, receipt.selection.metadata, receipt.argumentsAccepted, receipt.native.global, receipt.native.emitted⟩

theorem delegated_result_from_outer {ordinary : List RequirementId}
    (found : source.lookupExpression? id = some node)
    (ordinaryAccepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ordinary)
    (delegates : Delegates node ordinary)
    (accepted : SourceCoreEvidence.lowerWithProjector program project callerFunction compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    ∃ receipt : Delegated program project callerFunction compilation child fuel source scope id reasonAt policy node output,
      child fuel (SourceCoreEvidence.withNode source (rawNode node receipt.ordinary)) scope id reasonAt = .ok receipt.operand ∧
      SourceCoreEvidence.applyCoercions program project compilation callerFunction receipt.available scope node policy receipt.operand node.coercions = .ok output := by
  obtain ⟨receipt⟩ := CallableCoercionExpressionCertificates.delegated_of_accepted found ordinaryAccepted delegates accepted
  exact ⟨receipt, receipt.childAccepted, receipt.suffix.accepted⟩
end Receipt

section Meaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments instantiation reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry in
/-- Preserve an independent whole source outcome with its original raw form and
ordered coercions. The raw law is the remaining expression-grammar interface. -/
theorem direct_expression_preserves
    (unique : NodeOccurrencesUnique source)
    (rawMeaning : RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain ledger entry unique (by intros; simp [receipt.form]) rawMeaning trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry in
/-- Reflect only finite completion of the real emitted expression. The source
form and path derivations retain their separate heaps and independent costs. -/
theorem direct_expression_reflects
    (rawMeaning : RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain entry rawMeaning completed

end Meaning

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
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = identity(value); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }",
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value + 0; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value + 0; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = rawFail(); return result; }",
    "function empty(value: Word) returns (Word) { return value; }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained three-edge list and replay the actual compiler
helper against the sealed plan. This also checks each full dictionary in order. -/
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
          | .group _ | .binary .. =>
            let ordinary ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
              | some ordinary => pure ordinary | none => throw (IO.userError "outer raw ordinary requirements absent")
            SourceCompilerFeatureSupport.get "actual sanitized delegated child"
              (child 150 (SourceCoreEvidence.withNode source (CallableCoercionExpressionCertificates.rawNode node ordinary)) scope node.id reasonAt)
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
  SourceCompilerFeatureSupport.require found "actual two-step path not reached"
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

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source paths checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (box, final, pathGaps) ← audit path "Final"
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let _ ← audit direct "Final"
  let bypass ← SourceCompilerFeatureSupport.compileNamed program "bypass"
  auditBypass bypass
  let emptySelected ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  auditSelectedEmpty emptySelected
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (direct, false), (late, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "source path resume" (started.resume 500000)
        let rawPrefix := if entry.key == direct.key then [(.word, some (word input)), (.word, some (word 19))] else []
        let firstCells := [(.word, some (word input))] ++ rawPrefix ++ [(.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "source path result changed"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "all three methods"
        | .fault (.uninitializedLocal id) state =>
          if input == 0 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[0]?) "source path first fault changed"
            cells state (firstCells ++ [(.bool, none)]) "first fault / two methods skipped"
          else if input == 2 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[1]?) "source path middle fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle fault / last method skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1 && some id == lateGaps[2]?)
              "source path final fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "third method fault"
        | other => throw (IO.userError s!"source path unexpected: {reprStr other}")
    let selectedStarted ← emptySelected.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let selectedFinished ← SourceCompilerFeatureSupport.get "empty selected resume" (selectedStarted.resume 500000)
    match selectedFinished.observation with
    | .done value state =>
      SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty selected result changed"
      cells state [(.word, some (word 17)), (.word, some (word 17)), (.word, some (word 19))] "empty selected actual call only"
    | other => throw (IO.userError s!"empty selected unexpected: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "source path operand resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, some (word 23)), (.word, none)] "operand / all three methods skipped"
    | other => throw (IO.userError s!"source path operand unexpected: {reprStr other}")
    let started ← empty.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let finished ← SourceCompilerFeatureSupport.get "empty path resume" (started.resume 500000)
    match finished.observation with
    | .done value state =>
      SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty path result changed"
      cells state [(.word, some (word 17))] "empty path"
    | other => throw (IO.userError s!"empty path unexpected: {reprStr other}")
  let emptyCaller ← match empty.cached.indexed.base.functions.find? (·.signature.key == empty.key) with
    | some named => pure named.specialized
    | none => throw (IO.userError "empty path caller missing")
  SourceCompilerFeatureSupport.require
    (emptyCaller.function.typedBody.nodes.all fun item => match item with
      | .expression node => node.coercions.isEmpty
      | _ => true) "empty path unexpectedly emitted coercions"
  emptySelected.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  bypass.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  direct.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  IO.println "coercion expressions: actual delegated/direct acceptance, raw children/global slots, ordered suffix code, operand/first/middle/last faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionExpressions
