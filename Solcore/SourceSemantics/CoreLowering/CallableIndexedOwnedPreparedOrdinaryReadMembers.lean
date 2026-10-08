import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryStoredMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix

/-! Initialized local reads retain a known prepared member at the genuine raw
cell type. The reported occurrence type remains its own runtime view. Actual
callee traces are associated by determinism without rerunning their producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedPreparedOrdinaryFormedMembers
open CallableIndexedOwnedPreparedOrdinaryStoredMembers
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {sourceValue : Dynamic.Value} {nativeValue : Value} {type : Ty}
  {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

/-- The real binder and initialized cell exclude the reached empty witness. -/
theorem initialized_policy
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    UninitializedPolicy certificate context environment heap faults := by
  intro other cell witness
  have same := witness.lookup.functional lookup
  subst other
  obtain ⟨_, target, reference, read, nativeRead⟩ := stored
  have same := witness.read.functional read
  subst cell
  cases witness.empty

/-- Genuine lexical and stored receipts construct the exact initialized
Source/native read; no heap-relation inverse supplies the qualified member. -/
theorem initialized_traces
    (binding : StaticBinding certificate context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    type = certificate.type ∧
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source environment heap
      id sourceValue heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word nativeValue) store := by
  rcases certificate with ⟨node, readType, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  dsimp only at *
  obtain ⟨member, target, reference, read, nativeRead⟩ := stored
  obtain ⟨other, cell, otherLookup, otherRead, cellType, _⟩ := locals.lookup binding.declared
  have same := otherLookup.functional lookup
  subst other
  have same := otherRead.functional read
  subst cell
  have nominal : raw = declared.scheme.body := cellType
  have notMapping : ¬ ∃ key value, declared.scheme.body = .mapping key value := by
    intro ⟨key, value, mapped⟩
    have mapped : raw = .mapping key value := nominal.trans mapped
    cases member with
    | ordinary i owner history origin prefixContext globals referenceIndex typed => cases mapped
  obtain ⟨selectedTarget, nativeLookup, selectedReference⟩ := environments.lookup_visible lookup slot
  have same : selectedTarget = target := Option.some.inj (selectedReference.mapped.symm.trans reference.mapped)
  subst selectedTarget
  have sameType : type = readType := by
    exact (Ty.sum.inj (Option.some.inj (reference.typed.symm.trans selectedReference.typed))).2
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id sourceValue heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap node.form [] [] sourceValue heap :=
      form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl
    exact .intro (lookupExpression?_sound metadata.found)
      (by rw [metadata.requirements, metadata.coercions]; exact formTrace)
      (by rw [metadata.coercions]; exact .nil)
  refine ⟨sameType, sourceTrace, ?_⟩
  cases emitted with
  | ordinary _ =>
    change Evaluates actual store (OptionalCell.read readType (.var (ξ index)) reason)
      (.inRight .word nativeValue) store
    exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
  | mapping declared _ => exact False.elim (notMapping ⟨_, _, declared⟩)

/-- One original read producer retains its broad result, heap/frame/metadata
and the same initialized qualifier. Its empty-cell policy is derived above. -/
theorem read_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value sourceValue) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word nativeValue) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      mapping world certificate.node.type certificate.type faults (.value sourceValue) (.inRight .word nativeValue) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      mapping world heap store ∧
    AdministrativePreserved mapping store mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type := by
  obtain ⟨_, sourceTrace, nativeTrace⟩ := initialized_traces certificate binding environments locals agrees stored lookup
  obtain ⟨outcome, after, result, finalStore, actualSource, actualNative, related, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding environments heaps locals agrees
      (initialized_policy certificate stored lookup)
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative nativeTrace
  subst result
  subst finalStore
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl actualSource (.value sourceTrace)
  subst outcome
  subst after
  exact ⟨actualSource, actualNative, related, finalHeaps, frame, metadata, stored⟩

section Parent
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {compilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel compilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)

/-- Associate the same already-produced callee tuple with the initialized read.
This constructs no second first-child producer and keeps the original post. -/
theorem at_value_post
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {sourceSize : Nat} {calleeValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (sourceTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld) :
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld ∧
    calleeValue = sourceValue ∧ after = heap ∧ carrier = nativeValue ∧ calleeStore = store ∧
    FormedAt headers keys registry faults calleeMap calleeWorld raw calleeValue carrier type := by
  obtain ⟨_, expectedSource, expectedNative⟩ :=
    initialized_traces certificate binding environments locals agrees stored lookup
  have actualNative := post.1
  rw [sameCode] at actualNative
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative expectedNative
  have sameNative : carrier = nativeValue := (Value.inRight.inj sameResult).2
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl (.value sourceTrace.sound) (.value expectedSource)
  have sameSource : calleeValue = sourceValue := Dynamic.ExpressionOutcome.value.inj sameOutcome
  have member : FormedAt headers keys registry faults calleeMap calleeWorld raw calleeValue carrier type := by
    rw [sameSource, sameNative]
    exact stored.1.extend post.2.2.2.1 post.2.2.2.2.1
  exact ⟨post, sameSource, sameHeap, sameNative, sameStore, member⟩

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceTypes : List TypeSystem.Ty}

/-- This is the original full callee tuple, with a known member beside that
same tuple. Its strict native/Source witnesses, gate and conditional resolver
are retained literally, including the unresolved prior alternatives. -/
def QualifiedValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize calleeValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    (∀ (function : Dynamic.Closure), calleeValue = .closure function →
      CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := carrier) (type := compiler.calleeCode.type) ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site id ids metadata
          compiler.original dispatch.row),
        CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.ClosureResolutionWithEffects
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
          compiler prepared initial dispatch budget value finalStore) ∧
    FormedAt headers keys registry faults finalMap finalWorld raw calleeValue carrier type

/-- Retain the genuine parent prefix and attach its known initialized member
at the very same native/Source post; the callee producer is not rerun. -/
theorem at_value_prefix
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location raw sourceValue nativeValue type)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {budget : Nat} {value : Value} {finalStore : Store}
    (produced : CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∧
    QualifiedValuePrefix (registry := registry) (faults := faults) (raw := raw) (type := type) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler initial prepared budget value finalStore := by
  obtain ⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
    completed, smaller, sourceTrace, post, gate, resolver⟩ := produced
  obtain ⟨samePost, _, _, _, _, member⟩ := at_value_post certificate bridge profile compiler initial
    sameCode binding unique environments locals agrees stored lookup sourceTrace post
  exact ⟨⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, post, gate, resolver⟩,
    nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, samePost, gate, resolver, member⟩
end Parent

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers
