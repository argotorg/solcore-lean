import Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Two actual emitted methods consume concrete builtin body certificates.
Source traces use the actual selected dictionaries, without assuming dictionary
uniqueness. Native completion needs no source body premise. Runtime checks
exercise two-step paths, first and later faults, exact cells and resumed calls. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionPathMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableCoercionMethodEntries CallableCoercionPathMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {first second : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ [first, second], ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ [first, second], ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))


variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}


include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem two_step_preserves
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {middle : Dynamic.Heap} {converted result : Dynamic.Value}
    (firstBody : Dynamic.BodyInvokes program first.sourceBody first.function.evidence before [input] converted middle)
    (secondBody : Dynamic.BodyInvokes program second.sourceBody second.function.evidence middle [converted] result after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome [first, second] before input (.value result) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.value result) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand (.cons firstBody (.cons secondBody .nil))

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem two_step_reflects
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace [first, second] before input outcome after ∧ PathOutcome [first, second] before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_reflects functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand completed

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem first_fault_skips_second
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (fault : Dynamic.SemanticFault)
    (failed : Dynamic.BodyFaults program first.sourceBody first.function.evidence before [input] fault after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome [first, second] before input (.fault fault) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.fault fault) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand (.fault failed)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "function path(value: Word) returns (Box) where Word: Marker, Word: Marker, Bool: Marker { let result: Box = value; return result; }",
    "function early() returns (Box) where Word: Marker, Bool: Marker { let missing: Word; let result: Box = missing; return result; }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained two-edge list and replay the actual compiler
helper against the sealed plan. This also checks each full dictionary in order. -/
private def audit (entry : SourceCompilerFeatureSupport.Entry) :
    IO (DataConstructorInstantiation × Resolved.LocalId × Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let box ← match base.sourceProgram.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "path Box missing")
  let constructor ← match box.constructors with
    | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal box.id []))
    | _ => throw (IO.userError "path Box constructor missing")
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 2) "actual coercion path lost its two edges"
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
          let gap ← match (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
              (fun binder => binder.name == "firstGap" || binder.name == "secondGap") with
            | [binder] => pure binder.id | _ => throw (IO.userError "path exact gap binder missing")
          gaps := gaps ++ [gap]
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let lowered ← SourceCompilerFeatureSupport.get "path actual applyCoercions"
          (SourceCoreEvidence.applyCoercions base.sourceProgram (SourceCoreCompatibleDataExpressions.projectType entry.cached.compatible.checked) compilation caller available
            [] node {} ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 1))⟩ node.coercions)
        let outputType ← SourceCompilerFeatureSupport.get "path result projection"
          (entry.cached.compatible.checked.catalog.project constructor.resultType)
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? (.unit :: base.globals.map SourceCoreCalls.Signature.referenceType) lowered.expression
            entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "path actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual two-step path not reached"
  match gaps with
  | [first, second] => pure (constructor, first, second)
  | _ => throw (IO.userError "path did not select exactly two method gaps")

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

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "path checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (constructor, firstGap, secondGap) ← audit path
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early
  let output := SourceTypedRuntime.Value.constructed constructor [.bool true]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      let started ← path.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← SourceCompilerFeatureSupport.get "path resume" (started.resume 500000)
      let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
      let secondCells := [(.bool, some (.bool (input == 1))),
        (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
      match finished.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (input == 1 && reprStr value == reprStr output) "path result changed"
        cells state (firstCells ++ secondCells ++ [(constructor.resultType, some output)]) "two-step success"
      | .fault (.uninitializedLocal id) state =>
        if input == 0 then
          SourceCompilerFeatureSupport.require (id == firstGap) "first path fault changed"
          cells state (firstCells ++ [(.bool, none)]) "first method / suffix skipped"
        else
          SourceCompilerFeatureSupport.require (input == 2 && id == secondGap) "later path fault changed"
          cells state (firstCells ++ secondCells ++ [(constructor.resultType, none)]) "second method"
      | other => throw (IO.userError s!"path unexpected outcome: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "path operand fault resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, none)] "operand / both methods skipped"
    | other => throw (IO.userError s!"path operand unexpected outcome: {reprStr other}")
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume early []
  IO.println "coercion path: actual two steps, ordered dictionaries/full records, first/later fault stores and resume GREEN"

end Tests.SourceCoreCallableCoercionPathMeaning
