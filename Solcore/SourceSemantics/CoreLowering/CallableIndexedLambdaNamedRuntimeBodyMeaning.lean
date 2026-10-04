import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewNamedRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel

/-! The canonical lambda body retains the actual view's named emission and
same caller dictionary. Its expression proof reuses the existing finite Tree
fold and catalog mutual induction. Source and native grades remain independent;
actual closure installation and restoration are handled by the entry adapters. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableLambdaViewNamedRuntimeCertificates


open CallableIndexedLambdaValues CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableLambdaViewEdits CallableLambdaBodyReachability

/-- The lexical support records actual nodes; execution remains restricted by
its separate concrete expression certificates. -/
def Nodes (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node

section BodyReceipt
variable {values : ValuesContext} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) {program : Program}
  {headers : Inventory prepared.ancestry values prepared.layouts.definitions program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

abbrev Body (headers : Inventory prepared.ancestry values prepared.layouts.definitions program)
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  CallableIndexedLambdaStaticBodySupport.BodyWith Nodes
    (fun fuel source context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation fuel source context
      code.compilation.solvedRequirements code.reasonAt) code program registry faults

/-- The actual compiler-view tree is reindexed through the one static fold.
Original emissions and Direct acceptance retain the actual ordered child action;
only reached node lookup and static typing return to the canonical source. -/
theorem of_tree
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : LocalView function.source code.view changed)
    (avoids : Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (Nodes code.view)
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (some function.evidence) headers code.compilation readFuel code.view context
        code.compilation.solvedRequirements code.reasonAt)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body headers code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧ body.flow = flow := by
  have unchanged := LocalView.refl code.view
  have fresh : Avoids code.view (function.body.map NodeId.statement) [] := by intro id member; cases member
  obtain ⟨actual, actualSites⟩ := CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    (afterSyntax := Nodes code.view)
    (after := fun context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared)
      function.evidence headers code.compilation readFuel code.view context code.compilation.solvedRequirements code.reasonAt)
    (tree := tree)
    unchanged fresh (edited.metadata.unique unique)
    (fun _ _ receipt => receipt)
    (fun _ _ _ _ reached receipt => CallableLambdaViewNamedRuntimeCertificates.transport unchanged fresh receipt reached)
    sites (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  obtain ⟨body, sameContext, sameFuel, samePolicy, sameFlow, _⟩ :=
    CallableIndexedLambdaStaticBodySupport.BodyWith.of_tree
      (expressionSyntax := Nodes)
      (certificates := fun fuel source context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation fuel source context
        code.compilation.solvedRequirements code.reasonAt)
      code inputs frame readFuel policy callback edited avoids unique sameLedger
      (fun id reached receipt => by
        obtain ⟨node, found⟩ := receipt
        exact ⟨node, (expression_lookup edited avoids reached).trans found⟩)
      (fun _ _ _ _ reached receipt =>
        CallableLambdaViewNamedRuntimeCertificates.canonical_transport
          ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
          (avoids.view edited.metadata) receipt (reached.metadata edited.metadata))
      projection generated actualSites
  exact ⟨body, sameContext, sameFuel, samePolicy, sameFlow⟩

/-- Same-D static fields feed the shared flow/finish kernel. -/
def Body.toKernel (body : Body headers code program registry faults) :
    CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (Nodes function.source)
      (fun context => Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation body.readFuel function.source context
        code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared)
      administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites, initialValid := body.valid,
    projection := body.projection, unique := body.unique, emitted := body.emitted }
/-- The legacy builtin record keeps its original fields and constructor. -/
def builtin_kernel (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults) :
    CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (CompatibleExpressionBuiltins.Syntax function.source)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate body.readFuel values function.source context
        code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared)
      administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites, initialValid := body.valid,
    projection := body.projection, unique := body.unique, emitted := body.emitted }

end BodyReceipt

section Heads
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {compilation : SourceCoreFunctions.Context}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (P : ProtectedExpressionMeaning.Entry) (transport : ProtectedExpressionMeaning.Transport P)
  (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
    protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
  (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
  (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header (conditions header))

include transport catalog authorized in
private theorem head_preserves
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P := by
  intro scope id lowered head
  cases head with
  | authenticated head =>
    exact RecursiveNamedCallEvidenceHeads.preserves_at_for functions P transport catalog conditions authorized
      budget size within idsUnique unique owners arguments bodies head
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_preserves_bounded_for functions receipt.sequence receipt.nativeTypes packed
        P transport (conditions receipt.header) (authorized receipt.header receipt.member) budget arguments (bodies receipt.header receipt.member)
        owners receipt.member caller installed environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented

include transport catalog authorized in
private theorem head_reflects
    (budget size : Nat) (within : size ≤ budget)
    (arguments : RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence certificate) faults P := by
  intro scope id lowered head
  cases head with
  | authenticated head =>
    exact RecursiveNamedCallEvidenceHeads.reflects_at_for functions P transport catalog conditions authorized
      budget size within arguments bodies head
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_reflects_bounded_for functions receipt.sequence receipt.nativeTypes packed
        P transport (conditions receipt.header) (authorized receipt.header receipt.member) budget arguments (bodies receipt.header receipt.member)
        receipt.member caller installed environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes valid unique owners uninitialized missing transport catalog authorized in
private theorem expressions_preserves (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  exact RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for
    functions extension faithful observations functionTypes evidence unique uninitialized missing
    (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) P
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults)
    budget size within (by
      intro certificate child childWithin children
      exact RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls
        functions extension faithful observations functionTypes evidence unique missing P transport
        (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) budget child childWithin children
        (head_preserves functions P transport catalog conditions authorized budget child childWithin valid.runtime.idsUnique unique owners
          (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies))

include extension faithful observations functionTypes valid uninitialized missing transport catalog authorized in
private theorem expressions_reflects (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  exact RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for
    functions extension faithful observations functionTypes evidence uninitialized missing
    (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) P
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults)
    budget size within (by
      intro certificate child childWithin children
      exact RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls
        functions extension faithful observations functionTypes evidence missing P transport
        (CallableLambdaViewNamedRuntimeCertificates.Head headers compilation source context evidence) budget child childWithin children
        (head_reflects functions P transport catalog conditions authorized budget child childWithin
          (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies))

end Heads


section ClosedCatalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The catalog contains static profiles for every actual named parameter
state, at each header's own complete dictionary. No body execution is a field. -/
structure CatalogFamily (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix : Nat) (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context
  expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1
  profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults
  uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id)
  missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag)
  escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped

variable (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (family : CatalogFamily headers locations capturePrefix functions registry faults)
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (P : ProtectedExpressionMeaning.Entry) (transport : ProtectedExpressionMeaning.Transport P)
  (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
    protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)

include extension faithful observations functionTypes owners family valid unique uninitialized missing transport catalog in
/-- Same-D canonical expression preservation closes every named body through
the one existing catalog strong induction. The protected source entry remains
independent of the lambda's native type and installed ghost. -/
theorem expressions_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.preserves_at_runtime_evidence
    functions extension faithful observations functionTypes owners family.uninitialized family.missing family.escaped
    family.prefixMatches family.profiles
  intro scope id lowered receipt
  exact expressions_preserves (fuel := fuel) functions P transport catalog (fun _ => fun _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial)
    extension faithful observations functionTypes valid unique owners uninitialized missing budget size within (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
      exact bodies child header member entry trace) receipt

include extension faithful observations functionTypes family valid uninitialized missing transport catalog in
/-- Reflection uses only original native children. The catalog strong induction
returns independently measured source traces for the same full dictionaries. -/
theorem expressions_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificates evidence headers compilation fuel source context solved reasonAt) faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.reflects_at_runtime_evidence
    functions extension faithful observations functionTypes family.uninitialized family.missing family.escaped
    family.prefixMatches family.profiles
  intro scope id lowered receipt
  exact expressions_reflects (fuel := fuel) functions P transport catalog (fun _ => fun _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial)
    extension faithful observations functionTypes valid uninitialized missing budget size within (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodies child header member entry trace) receipt
end ClosedCatalog


section NamedExecution
variable {values : ValuesContext} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) (history : History code) {program : Program}
  {headers : Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body headers code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (family : CatalogFamily headers locations capturePrefix functions registry faults)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

private abbrev sourceEntry
    (headers : Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix : Nat) :
    ProtectedExpressionMeaning.Entry := CallableIndexedLambdaCatalogEntries.protectedEntry code history headers locations
  capturePrefix code.compilation.administrativePrefix

include body extension observations functionTypes owners family uninitialized missing escaped in
/-- The source grade is the original parent-supplied body grade. Named callee
meaning is closed by CatalogFamily's static profiles and the existing mutual
induction; the lambda ghost remains in its independent source entry. -/
theorem Body.preserves_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      environment canonical prepared.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode prepared.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : sourceEntry code history headers locations capturePrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      sourceEntry code history headers locations capturePrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation
          body.readFuel function.source context code.compilation.solvedRequirements code.reasonAt) faults (sourceEntry code history headers locations capturePrefix)) := by
    intro context valid child within
    exact expressions_preserves_at functions extension (identity_faithful prepared) observations functionTypes owners
      family valid body.unique uninitialized missing (sourceEntry code history headers locations capturePrefix)
      CallableIndexedLambdaCatalogEntries.transport (fun ⟨entry⟩ => ⟨entry.catalog⟩) budget child within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.preserves_sized functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program
      (identity_faithful prepared) observations escaped
      CallableIndexedLambdaCatalogEntries.transport CallableIndexedLambdaCatalogEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, entry⟩

include body extension observations functionTypes family uninitialized missing escaped in
/-- Reflection consumes the original native body witness. No source execution
or preservation theorem is used to obtain its independent source grade. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      environment canonical prepared.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode prepared.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : sourceEntry code history headers locations capturePrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      sourceEntry code history headers locations capturePrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (Certificates (ambient := CallableIndexedAmbient.ambientDefinitions prepared) function.evidence headers code.compilation
          body.readFuel function.source context code.compilation.solvedRequirements code.reasonAt) faults (sourceEntry code history headers locations capturePrefix)) := by
    intro context valid child smaller
    exact expressions_reflects_at functions extension (identity_faithful prepared) observations functionTypes
      family valid uninitialized missing (sourceEntry code history headers locations capturePrefix)
      CallableIndexedLambdaCatalogEntries.transport (fun ⟨entry⟩ => ⟨entry.catalog⟩) budget child (Nat.le_of_lt smaller)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.reflects_sized functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program
      (identity_faithful prepared) observations functionTypes escaped
      CallableIndexedLambdaCatalogEntries.transport CallableIndexedLambdaCatalogEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, entry⟩
end NamedExecution

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
