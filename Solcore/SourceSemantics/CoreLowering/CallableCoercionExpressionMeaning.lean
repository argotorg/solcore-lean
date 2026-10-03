import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates

/-! Outer coercions compose with laws for the original uncoerced expression
form. These laws are explicit theorem arguments, including the original owned
requirements; no whole-expression meaning is a field of a compiler receipt.
The raw sanitizer's child semantics and recursive grammar closure are separate
obligations. Generalized local reads are outside this nonlocal interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates

def RawOutcome (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (node : ExpressionNode) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value value => Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value after
  | .fault reason => Dynamic.ExpressionFormFaults program context evidence source environment before
      node.form node.requirements node.coercions reason after

def Path (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (steps : List CoercionStep) (value : Dynamic.Value)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionPathExecutes program context evidence before steps value result after
  | .fault reason => Dynamic.CoercionPathFaults program context evidence before steps value reason after

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (node : ExpressionNode) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | rawFault {reason after}
      (raw : RawOutcome program context evidence source environment before node (.fault reason) after) :
      Trace program context evidence source environment before node (.fault reason) after
  | path {value middle outcome after}
      (raw : RawOutcome program context evidence source environment before node (.value value) middle)
      (path : Path program context evidence middle node.coercions value outcome after) :
      Trace program context evidence source environment before node outcome after

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem source_inv {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    Trace program context evidence source environment before node outcome after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw path
    | generalizedLocal other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form other raw => exact .rawFault (contains_unique unique other contains ▸ raw)
    | coercion other raw failed =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw failed
    | generalizedLocalRequirement other form _ _ _ _ _ _ _ | generalizedLocalCoercion other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)

theorem Trace.source {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (trace : Trace program context evidence source environment before node outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | rawFault raw => exact .fault (.form (lookupExpression?_sound found) raw)
  | path raw path =>
    cases outcome with
    | value value => exact .value (.intro (lookupExpression?_sound found) raw path)
    | fault reason => exact .fault (.coercion (lookupExpression?_sound found) raw path)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

/-- A pointwise law for the original raw form, not for an already coerced
ExpressionEvaluates outcome and not for a rewritten source graph. -/
def RawFormPreserves (faults : FunctionCalls.FaultRep) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) (node : ExpressionNode)
    (ξ : Renaming) (operand : Lowered) : Prop :=
  ∀ {outcome after}, RawOutcome (Program.ofChecked compilerProgram) context evidence source environment before node outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (operand.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.rawType operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Completion reflection for that same original raw form. -/
def RawFormReflects (faults : FunctionCalls.FaultRep) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) (node : ExpressionNode)
    (ξ : Renaming) (operand : Lowered) : Prop :=
  ∀ {value finalStore}, Evaluates caller store (operand.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      RawOutcome (Program.ofChecked compilerProgram) context evidence source environment before node outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.rawType operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

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
  (receipt : Output compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry in
/-- Preserve an independent whole source outcome with its original raw form and
ordered coercions. The raw law is the remaining expression-grammar interface. -/
theorem preserves
    (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
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
  cases source_inv receipt.found unique notLocal trace with
  | rawFault raw =>
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning raw
    cases related with
    | @fault reason token represented =>
      refine ⟨.inLeft output.type (.word token), finalStore, finalMap, finalWorld, (emitted.spine.renamed_completed_iff ξ).mpr ?_, ?_, heaps,
        maps, worlds, admin, metadata, ⟨entry.extend maps worlds admin metadata⟩⟩
      · refine ⟨_, _, evaluated, ?_⟩
        rw [← emitted.calls_eq]
        simpa only [chain.final_type] using CallableCoercionSpine.Runs.failure caller compilation.internalReason finalStore receipt.operand.type (.word token) (methods.map (·.call))
      · exact .fault represented
  | @path value middle outcome after raw path =>
    obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning raw
    cases related with
    | value represented =>
      have pathTrace : PathOutcome methods middle value outcome after := by
        cases outcome <;> simpa only [PathOutcome, Path, steps] using path
      obtain ⟨result, finalStore, finalMap, finalWorld, completed, _, related, finalHeaps, tailMaps, tailWorlds, tailAdmin, tailMetadata, finalEntry⟩ :=
        CallableCoercionSourcePathMeaning.emitted_preserves checkedAccepted ledger functions extension definitions registered faithful observations runtimeViews
          uninitialized missing emitted chain (entry.extend maps worlds admin metadata) heaps represented evaluated pathTrace
      exact ⟨_, _, _, _, completed, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
        admin.trans tailAdmin, metadata.trans tailMetadata, finalEntry⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry in
/-- Reflect only finite completion of the real emitted expression. The source
form and path derivations retain their separate heaps and independent costs. -/
theorem reflects
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
  obtain ⟨native, middleStore, evaluated, runs⟩ := (emitted.spine.renamed_completed_iff ξ).mp completed
  obtain ⟨rawOutcome, middle, middleMap, middleWorld, raw, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning evaluated
  cases related with
  | fault represented =>
    rw [← emitted.calls_eq] at runs
    obtain ⟨rfl, rfl⟩ := failed_runs runs
    refine ⟨_, _, _, _, (Trace.rawFault raw).source receipt.found, ?_, heaps, maps, worlds, admin, metadata,
      ⟨entry.extend maps worlds admin metadata⟩⟩
    rw [chain.final_type]
    exact .fault represented
  | @value sourceValue nativeValue represented =>
    obtain ⟨outcome, after, finalMap, finalWorld, path, related, finalHeaps, tailMaps, tailWorlds, tailAdmin, tailMetadata, finalEntry⟩ :=
      CallableCoercionSourcePathMeaning.emitted_reflects functions extension definitions registered faithful observations runtimeViews
        uninitialized missing emitted chain (entry.extend maps worlds admin metadata) heaps represented evaluated completed
    have pathTrace : Path (Program.ofChecked compilerProgram) context evidence middle node.coercions sourceValue outcome after := by
      cases outcome <;> simpa only [PathOutcome, Path, steps] using path
    exact ⟨_, _, _, _, (Trace.path raw pathTrace).source receipt.found, related, finalHeaps, maps.trans tailMaps,
      worlds.trans tailWorlds, admin.trans tailAdmin, metadata.trans tailMetadata, finalEntry⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
