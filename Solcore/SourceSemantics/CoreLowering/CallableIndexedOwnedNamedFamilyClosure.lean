import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds

/-! Authentic named profiles close the actual body and expression families.
The original static Tree fold supplies all expression children, and the shared
measured body fold supplies strictly smaller callees. Complete evidence and
parameter entries remain intact; no execution meaning is a factory premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedExpressionTreeBounds
open CallableIndexedOwnedNamedBodyBounds (stableCondition)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

section Expressions
variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {compilation : SourceCoreFunctions.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes unique owners uninitialized missing sameLayouts in
/-- Ordinary static call heads are included pointwise in the full evidence
head. The original Tree fold receives actual children and callee witnesses. -/
private theorem ordinary_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  have meaning : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
    apply RecursiveNamedExpressionTreeBounds.preserves_at_with_state
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := program) (registry := registry) (source := source) (context := context)
      (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (faults := faults)
      (literals := fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)
      functions evidence (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) budget size within

    · intro child childWithin
      exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing
              (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults))) child)
    · intro childCertificate child childWithin children
      apply head_preserves_at_with_calls functions extension faithful observations functionTypes evidence unique missing owner
        (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) compilation.administrativePrefix budget child childWithin children
      have full : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          program context evidence source
          (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
            (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
            headers compilation source context evidence childCertificate) faults child :=
        PreservesAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
          (CallableIndexedOwnedExpressionHeads.preserves_at_with
            (certificate := childCertificate) functions owner sameLayouts (stableCondition functions owner)
            (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
            budget child childWithin (CompatibleRuntimeContextValidity.of_ordinary valid).runtime.idsUnique unique owners
            (fun smaller smallerWithin => preserves_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)
      intro current id code head
      exact full (.ordinary head)

  intro scope id lowered tree
  exact meaning ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes uninitialized missing sameLayouts in
/-- Native ordinary heads use the same full evidence adapter pointwise, with
independently measured Source children and the exact reached actual pool. -/
private theorem ordinary_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  have meaning : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
    apply RecursiveNamedExpressionTreeBounds.reflects_at_with_state
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := program) (registry := registry) (source := source) (context := context)
      (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (faults := faults)
      (literals := fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)
      functions evidence (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) budget size within

    · intro child childWithin
      exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing
              (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults))) child)
    · intro childCertificate child childWithin children
      apply head_reflects_at_with_calls functions extension faithful observations functionTypes evidence missing owner
        (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) compilation.administrativePrefix budget child childWithin children
      have full : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          program context evidence source
          (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
            (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
            headers compilation source context evidence childCertificate) faults child :=
        ReflectsAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
          (CallableIndexedOwnedExpressionHeads.reflects_at_with
            (certificate := childCertificate) functions owner sameLayouts (stableCondition functions owner)
            (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
            budget child childWithin
            (fun smaller smallerWithin => reflects_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)
      intro current id code head
      exact full (.ordinary head)

  intro scope id lowered tree
  exact meaning ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes unique owners uninitialized missing sameLayouts in
private theorem expressions_preserve (runtime : Bool)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  cases runtime with
  | false => exact ordinary_preserves functions extension faithful observations functionTypes owner sameLayouts unique owners uninitialized missing valid budget size within bodies
  | true =>
    exact CallableIndexedOwnedExpressionTreeBounds.preserves_at_runtime functions extension faithful observations functionTypes evidence unique owners
      uninitialized missing owner sameLayouts (stableCondition functions owner)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      valid.ledger valid.runtime budget size within bodies

include extension faithful observations functionTypes uninitialized missing sameLayouts in
private theorem expressions_reflect (runtime : Bool)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  cases runtime with
  | false => exact ordinary_reflects functions extension faithful observations functionTypes owner sameLayouts uninitialized missing valid budget size within bodies
  | true =>
    exact CallableIndexedOwnedExpressionTreeBounds.reflects_at_runtime functions extension faithful observations functionTypes evidence
      uninitialized missing owner sameLayouts (stableCondition functions owner)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      valid.ledger valid.runtime budget size within bodies
end Expressions

section Families
variable (runtime : Bool)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled program → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = owner.key.capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : NativeFrame} {ghost : GhostFrame},
      BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true runtime diagnosticPolicy headers header (compilation header)
        header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations functionTypes sameLayouts owners uninitialized missing escaped prefixMatches profiles in
/-- Authentic static profiles and actual parameter entries close all named
callee bodies through the existing measured mutual family. -/
theorem preserves_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (stableCondition functions owner header) size := by
  apply CallableIndexedOwnedNamedBodyBounds.preserves_at_with_family functions owner runtime extension faithful observations
    sameLayouts escaped
    (fun header context => RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime header.function.evidence
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry _allowed
      exact profiles header member entry) ?_ size
  intro header member context valid budget child within below
  rw [← prefixMatches header member]
  exact expressions_preserve (compilation := compilation header) (fuel := header.readFuel)
    functions extension faithful observations functionTypes owner sameLayouts header.unique owners
    (uninitialized header member) (missing header member) runtime valid budget child within below

include extension faithful observations functionTypes sameLayouts uninitialized missing escaped prefixMatches profiles in
/-- Original native grades choose the strict callees; the Source grade and
actual body post are returned by the same shared family. -/
theorem reflects_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (stableCondition functions owner header) size := by
  apply CallableIndexedOwnedNamedBodyBounds.reflects_at_with_family functions owner runtime extension faithful observations functionTypes
    sameLayouts escaped
    (fun header context => RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime header.function.evidence
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry _allowed
      exact profiles header member entry) ?_ size
  intro header member context valid budget child within below
  rw [← prefixMatches header member]
  exact expressions_reflect (compilation := compilation header) (fuel := header.readFuel)
    functions extension faithful observations functionTypes owner sameLayouts
    (uninitialized header member) (missing header member) runtime valid budget child within below

section Callers
variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes sameLayouts owners uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing in
/-- The whole caller Tree may call any member, including itself or a mutual
callee. The shared body family closes every strictly smaller call internally. -/
theorem expression_preserves_at (size : Nat) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerCompilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers callerCompilation fuel source context solved reasonAt) faults size := by
  exact expressions_preserve functions extension faithful observations functionTypes owner sameLayouts sourceUnique owners
    callerUninitialized callerMissing runtime valid size size (Nat.le_refl _) (by
      intro header member child _smaller
      exact preserves_at functions extension faithful observations functionTypes owner sameLayouts runtime owners
        uninitialized missing escaped prefixMatches profiles child header member)

include extension faithful observations functionTypes sameLayouts uninitialized missing escaped prefixMatches profiles
  valid callerUninitialized callerMissing in
/-- Completed native callers obtain independently graded Source traces and
actual restored pools from the same closed named body and expression families. -/
theorem expression_reflects_at (size : Nat) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerCompilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers callerCompilation fuel source context solved reasonAt) faults size := by
  exact expressions_reflect functions extension faithful observations functionTypes owner sameLayouts
    callerUninitialized callerMissing runtime valid size size (Nat.le_refl _) (by
      intro header member child _smaller
      exact reflects_at functions extension faithful observations functionTypes owner sameLayouts runtime
        uninitialized missing escaped prefixMatches profiles child header member)
end Callers
end Families
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure
