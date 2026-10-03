import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! Arbitrary independent source paths consume the actual emitted list, without
selected-dictionary annotations. Runtime tests retain three actual method edges,
ordered repeated evidence, all failure prefixes and exact resumed stores. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionSourcePaths
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram} {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {method : MethodProfile (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {rest : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {ξ : Renaming} {input output : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input (method :: rest) output calls)



variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

variable {inputCode outputCode : SourceCoreBasic.LoweredExpr}

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem independent_success
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {sourceResult : Dynamic.Value}
    (trace : Dynamic.CoercionPathExecutes (Program.ofChecked compilerProgram) context evidence before (methods.map (·.step)) input sourceResult after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input (.value sourceResult) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.value sourceResult) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionSourcePathMeaning.emitted_preserves checkedAccepted ledger functions extension definitions registered
    faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand trace

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem independent_fault
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {fault : Dynamic.SemanticFault}
    (trace : Dynamic.CoercionPathFaults (Program.ofChecked compilerProgram) context evidence before (methods.map (·.step)) input fault after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input (.fault fault) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.fault fault) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionSourcePathMeaning.emitted_preserves checkedAccepted ledger functions extension definitions registered
    faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand trace

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem completed_reflects
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionSourcePathMeaning.emitted_reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing emitted chain entry heaps represented operand completed

/-- Repeated IDs need only their actual singleton row, never list Nodup or a
validity/uniqueness assertion for unrelated ledger rows. -/
theorem repeated_requirement_safe {compiler : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment} {context : SourceSemantics.Context}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence}
    {callerEvidence result : Dynamic.EvidenceEnvironment} {goals : List ProgramPredicate} {failed : RequirementId}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence compiler caller node available id goal = .ok raw)
    (produces : Dynamic.RequirementsProduceEnvironment context callerEvidence [id, id] goals result)
    (fault : Dynamic.RequirementListFaults context callerEvidence [id, id] failed) : False := by
  apply CallableCoercionRequirementSafety.excludes_list_fault ?_ produces fault
  intro key member
  have same : key = id := by simpa using member
  subst key
  exact CallableCoercionSelectionIdentity.primary_unique ledger accepted

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
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let missing: Word; let result: Final = missing; return result; }",
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
        let lowered ← SourceCompilerFeatureSupport.get "path actual applyCoercions"
          (SourceCoreEvidence.applyCoercions base.sourceProgram (SourceCoreCompatibleDataExpressions.projectType entry.cached.compatible.checked) compilation caller available
            [] node {} ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 1))⟩ node.coercions)
        let outputType ← SourceCompilerFeatureSupport.get "path result projection"
          (entry.cached.compatible.checked.catalog.project target.resultType)
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? (.unit :: base.globals.map SourceCoreCalls.Signature.referenceType) lowered.expression
            entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "path actual native code/ordered globals type mismatch"
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

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source paths checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (box, final, pathGaps) ← audit path "Final"
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (late, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "source path resume" (started.resume 500000)
        let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
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
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "source path operand resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, none)] "operand / all three methods skipped"
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
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  IO.println "source coercion paths: arbitrary source selectors, actual ordered three-edge records/dictionaries, first/middle/last faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionSourcePaths
