import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads

/-! Admitted expression Trees close literal, builtin, composite, data, tuple
and genuine named ordinary/direct call children through the existing support
fold. Named callees have authentic static profiles with False expression
certificates and syntax: this bounded callee grammar supports accepted nil,
absent-let, block and return-unit forms. All call parameter/body callbacks are
proved internally at the real ParameterReceipt. No general mixed family or
indirect-call closure is claimed, and no execution law is an endpoint premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedClosedNamedBodies
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}

/-- Canonical slots accompany the same actual full pool. The return operation
wraps that actual reached pool and changes none of its ordered records. -/
def caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨⟨reached, initial.property⟩, rfl, related⟩

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)

private abbrev calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (some evidence) headers compilation source context

/-- The original full compiler Tree with ordinary literal receipts. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) fuel (.initial compiled.compatible.checked)
    source context solved reasonAt

/-- The same original Tree keeps exact selected runtime numeric receipts. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
    (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
    (reasonAt := reasonAt) (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
private theorem preserves_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size size (Nat.le_refl _)
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child within children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size child within children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique idsUnique
      sameLayouts escaped profiles owners size child within
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => source_bodies functions owner wellFormed (sameLayouts header member)
        extension faithful observations size)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
private theorem reflects_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked) (source := source) (context := context) (solved := solved)
        (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size size (Nat.le_refl _)
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed sourceRuntime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child within children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) size child within children
    exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
      (functions := functions) (owner := owner) (runtime := true) evidence (caller (headers := headers) (compilation := compilation) owner) wellFormed sourceRuntime covers unique
      sameLayouts escaped profiles size child within
      (fun smaller strict => children smaller (Nat.le_of_lt strict))
      (fun header member => native_bodies functions owner wellFormed (sameLayouts header member)
        extension faithful observations functionTypes size)

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
/-- Genuine ordinary literal and callee-profile receipts close the whole
original Tree internally at every source size and actual admitted input. -/
theorem preserves_at (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (Tree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique owners idsUnique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) size
    ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
/-- Native completion returns its independent Source size and the same actual
reached caller with successful admission; no Source trace is assumed. -/
theorem reflects_at (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (Tree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) size
    ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts escaped profiles in
/-- Runtime numeric leaves use their exact original selected ledger rows. -/
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  preserves_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique owners idsUnique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults) size

include extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts escaped profiles in
/-- Runtime reflection retains independent Source and native grades and every
original ledger row beside its actual returned pool. -/
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots (caller (headers := headers) (compilation := compilation) owner))
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  reflects_with_literals functions extension faithful observations functionTypes owner evidence wellFormed
    sourceRuntime covers unique uninitialized missing sameLayouts escaped profiles
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults) size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionTreeBounds
