import Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety

/-! Any independent finite source coercion path drives the actual ordered
compiler calls. Real selected rows exclude requirement faults; arbitrary source
method dictionaries pass unchanged to the concrete body theorem. Initial saved
captures, frame history and operand evaluation remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
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

section Step
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
  (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {value : Dynamic.Value} {native : Value}
  (entry : Entry methods ambient.definitions caller mapping world before store)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (represented : ValueRep values.checked registry functions mapping world method.step.source value native method.call.signature.parameterType)

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem step_preserves {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.CoercionStepExecutes (Program.ofChecked compilerProgram) context evidence before method.step value sourceResult after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults (.value sourceResult) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  cases trace with
  | primitive absent _ => exact False.elim (absent _ _ method.selected)
  | method selected invoked =>
    exact CallableCoercionSelectedInvocation.preserves checkedAccepted ledger emitted functions extension definitions registered
      faithful observations runtimeViews uninitialized missing member entry heaps represented selected (.value invoked) reason

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem step_fault_preserves {fault : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.CoercionStepFaults (Program.ofChecked compilerProgram) context evidence before method.step value fault after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults (.fault fault) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  cases trace with
  | requirement failed =>
    cases emitted with
    | cons actual _ _ _ _ =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger actual.selectedMethod method.selected failed)
  | primitiveInput absent _ _ => exact False.elim (absent _ _ method.selected)
  | method selected failed =>
    exact CallableCoercionSelectedInvocation.preserves checkedAccepted ledger emitted functions extension definitions registered
      faithful observations runtimeViews uninitialized missing member entry heaps represented selected (.fault failed) reason

end Step

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

private theorem path_cons {before after : Dynamic.Heap} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : PathOutcome (method :: rest) before input outcome after) :
    (∃ middle value, Dynamic.CoercionStepExecutes (Program.ofChecked compilerProgram) context evidence
      before method.step input value middle ∧ PathOutcome rest middle value outcome after) ∨
    (∃ reason, outcome = .fault reason ∧ Dynamic.CoercionStepFaults (Program.ofChecked compilerProgram)
      context evidence before method.step input reason after) := by
  cases outcome with
  | value result =>
    cases trace with
    | cons head tail => exact .inl ⟨_, _, head, tail⟩
  | fault reason =>
    cases trace with
    | head failed => exact .inr ⟨_, rfl, failed⟩
    | tail head failed => exact .inl ⟨_, _, head, failed⟩

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews in
/-- Preserve the original independent path, including its exact successful
prefix and first fault. No selected-dictionary annotation is required. -/
theorem preserves
    (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    {outcome : Dynamic.ExpressionOutcome} (trace : PathOutcome methods before input outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  induction chain generalizing inputCode outputCode calls mapping world before after store input native outcome with
  | nil source type =>
    cases outcome with
    | value value =>
      cases trace
      exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry⟩⟩
    | fault reason => cases trace
  | @cons method rest target output chain ih =>
    cases emitted with
    | cons actual slot record dictionary tailEmitted =>
      have emitted := Emitted.cons actual slot record dictionary tailEmitted
      rcases path_cons trace with ⟨middle, converted, head, tail⟩ | ⟨failed, rfl, head⟩
      · obtain ⟨result, middleStore, middleMap, middleWorld, invoked, related, middleHeaps, maps, worlds, frame, metadata, ⟨nextEntry⟩⟩ :=
          step_preserves checkedAccepted ledger emitted functions extension definitions registered faithful observations runtimeViews
            uninitialized missing (List.mem_cons_self) entry heaps represented head reason
        cases related with
        | value middleRepresented =>
          obtain ⟨result, finalStore, finalMap, finalWorld, runs, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, _⟩ :=
            ih (fun method member => uninitialized method (List.mem_cons_of_mem _ member))
              (fun method member => missing method (List.mem_cons_of_mem _ member)) tailEmitted
              (nextEntry.restrict (fun _ member => List.mem_cons_of_mem _ member)) middleHeaps middleRepresented tail
          exact ⟨_, _, _, _, .cons invoked runs, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
            frame.trans tailFrame, metadata.trans tailMetadata,
            ⟨entry.extend (maps.trans tailMaps) (worlds.trans tailWorlds) (frame.trans tailFrame) (metadata.trans tailMetadata)⟩⟩
      · obtain ⟨result, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
          step_fault_preserves checkedAccepted ledger emitted functions extension definitions registered faithful observations runtimeViews
            uninitialized missing (List.mem_cons_self) entry heaps represented head reason
        cases related with
        | fault faultRep =>
          refine ⟨_, _, _, _, .cons invoked (CallableCoercionSpine.Runs.failure caller reason finalStore _ _ _),
            ?_, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
          rw [chain.final_type]
          exact .fault faultRep

variable {inputCode outputCode : SourceCoreBasic.LoweredExpr}

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem emitted_preserves
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {outcome : Dynamic.ExpressionOutcome} (trace : PathOutcome methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves checkedAccepted ledger functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented trace compilation.internalReason
  refine ⟨_, _, _, _, (emitted.spine.renamed_completed_iff ξ).mpr ?_, trace, related,
    finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
  exact ⟨_, _, operand, emitted.calls_eq ▸ runs⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem emitted_reflects
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
  obtain ⟨outcome, after, finalMap, finalWorld, _, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    CallableCoercionPathMeaning.emitted_reflects functions extension definitions registered faithful observations runtimeViews
      uninitialized missing emitted chain entry heaps represented operand completed
  exact ⟨_, _, _, _, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
