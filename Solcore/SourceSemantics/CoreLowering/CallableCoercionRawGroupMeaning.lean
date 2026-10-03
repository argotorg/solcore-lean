import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning

/-! Concrete builtin child meaning closes the original group's raw-form laws.
The source node retains its complete output path and ordered requirements.
Reflection uses only native completion and child reflection, never preservation
or a prior source execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning CallableCoercionRawGroupCertificates

/-- Group evaluation exposes the original child's whole outcome. This does
not erase the child's own metadata or change the surrounding source graph. -/
theorem raw_inv {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {inner : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (form : node.form = .group inner)
    (trace : RawOutcome program context evidence source environment before node outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after := by
  cases outcome with
  | value value =>
    change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ at trace
    rw [form] at trace
    cases trace with | group _ evaluated => exact .value evaluated
  | fault reason =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ at trace
    rw [form] at trace
    cases trace with | group _ failed => exact .fault failed

theorem raw_intro {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {inner : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (form : node.form = .group inner) (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after) :
    RawOutcome program context evidence source environment before node outcome after := by
  cases trace with
  | value evaluated =>
    change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .group layout evaluated
  | fault failed =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .group layout failed

section Raw
variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {compilerProgram : CheckedProgram} {evidence : Dynamic.EvidenceEnvironment}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {scope : Scope} {node : ExpressionNode} {inner : ExpressionId} {operand : Lowered}
  (child : Child readFuel values source context solved reasonAt scope node inner operand)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical caller : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)

include extension faithful observations runtimeViews valid uninitialized missing child environments heaps locals agrees actualTyped in
theorem raw_preserves (unique : NodeOccurrencesUnique source) :
    RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ operand := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, admin, metadata⟩ :=
    CompatibleExpressionBuiltins.preserves functions extension faithful observations runtimeViews
      (Program.ofChecked compilerProgram) evidence valid unique uninitialized missing child.tree child.found
      environments heaps locals agrees actualTyped (raw_inv child.form trace)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, child.rawType.symm ▸ represented,
    finalHeaps, maps, worlds, admin, metadata⟩

include extension faithful observations runtimeViews valid uninitialized missing child environments heaps locals agrees actualTyped in
theorem raw_reflects :
    RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ operand := by
  intro value finalStore evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, admin, metadata⟩ :=
    CompatibleExpressionBuiltins.reflects functions extension faithful observations runtimeViews
      (Program.ofChecked compilerProgram) evidence valid uninitialized missing child.tree child.found
      environments heaps locals agrees actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, raw_intro child.form child.layout trace,
    child.rawType.symm ▸ represented, finalHeaps, maps, worlds, admin, metadata⟩
end Raw

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
  (receipt : Delegated compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)


variable {readFuel : Nat} {inner : ExpressionId} {solved : List SolvedRequirement}
  (childTree : Child readFuel values source context solved reasonAt scope node inner receipt.operand)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (rawUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (rawMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {administrative : Core.Context} {canonical : Environment} {actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry childTree valid rawUninitialized rawMissing environments heaps locals agrees actualTyped in
theorem preserves
    (unique : NodeOccurrencesUnique source)
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
    uninitialized missing receipt.toOutput emitted steps chain ledger entry unique (by intros; simp [childTree.form])
    (raw_preserves functions extension faithful observations runtimeViews valid rawUninitialized rawMissing childTree
      environments heaps locals agrees actualTyped unique) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry childTree valid rawUninitialized rawMissing environments heaps locals agrees actualTyped in
theorem reflects
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
    uninitialized missing receipt.toOutput emitted steps chain entry
    (raw_reflects functions extension faithful observations runtimeViews valid rawUninitialized rawMissing childTree
      environments heaps locals agrees actualTyped) completed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
