import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectCalls

/-! Meaning of the extended receipt tree. First-subset roots use the existing
structural bounds; a direct call goes through the direct-call head, with its
arguments from the subset bounds and its evidence from the call's empty
requirements. The application of each admitted callee header below the grade
is the input that the row lemma supplies. The caller carrier retains the global
slots at the body's administrative prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedExpressionTrees (Tree)
open CellAwareInvocationAcceptedCallTrees (CallTree)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
universe u

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) :
    stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys) {compilation : SourceCoreFunctions.Context}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
    registry)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  {called : DeclarationInstantiation → Prop}

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Every extended receipt tree preserves its staged Source execution at
every grade, given the application of every admitted callee header below the
grade. -/
theorem preserves_call_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CallTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) :
    PreservesAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  cases tree with
  | tree tree =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree callerBridge.forgetSlots functions
      extension sameLedger faults uninitialized selectedBodies runtime covers tree size ⟨rfl, rfl, rfl⟩
  | call receipt port requirements monomorphic selected arguments =>
    intro current child code point node found typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    have stored := tree_types arguments unique typing
    have ordered := rows.1 ▸ stored ▸ arguments
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (fun current child code => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt
          current child code) faults size := by
      intro smaller _ argumentScope argument argumentCode argumentTree
      exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree callerBridge.forgetSlots functions extension
        sameLedger faults uninitialized selectedBodies runtime covers argumentTree smaller ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.preserves owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ found typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Native completion of every extended receipt tree reconstructs its staged
Source execution, given the native application of every admitted callee header
below the grade. -/
theorem reflects_call_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CallTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) :
    ReflectsAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  cases tree with
  | tree tree =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree callerBridge.forgetSlots functions
      extension sameLedger faults uninitialized selectedBodies runtime covers tree size ⟨rfl, rfl, rfl⟩
  | call receipt port requirements monomorphic selected arguments =>
    intro current child code point node found typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    have stored := tree_types arguments unique typing
    have ordered := rows.1 ▸ stored ▸ arguments
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (fun current child code => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt
          current child code) faults size := by
      intro smaller _ argumentScope argument argumentCode argumentTree
      exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree callerBridge.forgetSlots functions extension
        sameLedger faults uninitialized selectedBodies runtime covers argumentTree smaller ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.reflects owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ found typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallBounds
