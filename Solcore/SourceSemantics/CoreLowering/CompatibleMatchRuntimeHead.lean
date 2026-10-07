import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeads
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeSelection
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeControlBounds

/-! Actual accepted ordered match heads use the complete runtime ledger.
The same arm certificates produce numeric literal support internally. Expression
and selected-body meanings remain explicit pointwise bounded interfaces; this
unit does not close a whole statement grammar, Header or catalog body. The
original source and Core sizes, full heaps, captures and Entry are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeHead
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ selected => exact default_selected selected
termination_by cases.length

private theorem runtime_binders {owner : Resolved.DeclarationId} {parent child : SourceSemantics.Context}
    {binders : List TypedBinder} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (extended : BindersExtend owner parent binders child)
    (valid : CompatibleRuntimeContextValidity.Valid solved parent evidence) :
    CompatibleRuntimeContextValidity.Valid solved child evidence := by
  induction extended with
  | nil => exact valid
  | cons head tail ih => exact ih (valid.extend head)

private theorem numeric_requirement {compilation : SourceCoreCompatibleDataMatches.Context}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (sameLedger : compilation.solvedRequirements = solved)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (numeric : IntegerLiteralResolution) (selected : CompatibleMatchRuntimeSelection.LiteralRows compilation numeric) :
    RequirementProves context numeric.requirement numeric.predicate := by
  obtain ⟨implementation, selected⟩ := selected
  exact selected.proves (valid.ledger.trans sameLedger.symm) valid.runtime

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = compilation.signatures)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  {solved : List SolvedRequirement} (sameLedger : compilation.solvedRequirements = solved) {administrative : Core.Context} {faults : FunctionCalls.FaultRep}

universe u v

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem Stateful.head_preserves_bounded (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (acquire : ∀ location native, guard location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
    (validity : SourceSemantics.Context → Prop)
    (validity_binders : ∀ {binders target}, BindersExtend source.owner context binders target →
      validity context → validity target)
    (runtimeOf : validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
    (expressionMeaning : validity context →
      ∀ child, child < budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults child)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Stateful.Head.HeadPreservesAtFor protocol guard functions program evidence validity (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial guarded executed
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  apply CompatibleMatchPreservation.Stateful.Certificate.preserves_bounded_for onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique
    validity _ signatures
    (numeric_requirement sameLedger (runtimeOf contextValid)) (CompatibleMatchRuntimeSelection.of_certificate restricted)
    validity_binders catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded protocol guard producer stateBindings acquire ?_ ?_ ?_ contextValid
    environments heaps locals agrees actualTyped reference read unmapped initial guarded executed
  · intro contextValid childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact expressionMeaning contextValid childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected) scopeIds)

include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem Stateful.head_reflects_bounded (budget size : Nat) (bounded : size ≤ budget) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (acquire : ∀ location native, guard location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
    (validity : SourceSemantics.Context → Prop)
    (validity_binders : ∀ {binders target}, BindersExtend source.owner context binders target →
      validity context → validity target)
    (runtimeOf : validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
    (expressionMeaning : validity context →
      ∀ child, child < budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults child)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Stateful.Head.HeadReflectsAtFor protocol guard functions program evidence validity (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native result
    environments heaps locals agrees actualTyped reference read unmapped initial guarded completed
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  apply CompatibleMatchReflection.Stateful.Certificate.reflects_bounded_for onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary)
    validity _ signatures
    (numeric_requirement sameLedger (runtimeOf contextValid)) (CompatibleMatchRuntimeSelection.of_certificate restricted)
    validity_binders catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded protocol guard producer stateBindings acquire ?_ ?_ ?_ contextValid
    environments heaps locals agrees actualTyped reference read unmapped initial guarded completed
  · intro contextValid childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact expressionMeaning contextValid childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected) scopeIds)


include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped in
theorem head_preserves_bounded (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleRuntimeContextValidity.Valid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program evidence
        (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAtFor (entry := entry) functions program evidence
        (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial executed
  let bindings := ProtectedStateMatchBodyContracts.legacyBindings entryBindings
  let producer := ProtectedStateTransition.MarkedAllocation.of_administrative
    (ProtectedStateTransition.Lexical.legacyProtocol entry)
    (ProtectedStateTransition.Lexical.legacyTransport transport) bindings layouts frame
    (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
  obtain ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _post⟩ :=
    Stateful.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary
      signatures catalogValid found casesTyped defaultTyped sameLedger unique budget size bounded
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) producer bindings
      (fun _ _ _ => fun _ _ => True.intro)
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (fun extended valid => runtime_binders extended valid) (fun valid => valid)
      (fun valid child smaller => ProtectedStateMatchBodyContracts.legacy_expression_preserves
        transport (expressionMeaning valid child smaller))
      (fun request member childContext related child smaller =>
        RecursiveNamedImperativeFor.Control.Compatibility.legacy_preserves functions program evidence transport
          (children request member childContext related child smaller))
      contextValid environments heaps locals agrees actualTyped reference read unmapped ⟨initial⟩ trivial executed
  exact ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩


include allocator definitions registered extension ordinary signatures sameLedger catalogValid found casesTyped defaultTyped in
theorem head_reflects_bounded (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleRuntimeContextValidity.Valid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program evidence
        (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAtFor (entry := entry) functions program evidence
        (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (values := compilation.values) (source := source)
      (context := context) (registry := registry) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native result
    environments heaps locals agrees actualTyped reference read unmapped initial completed
  let bindings := ProtectedStateMatchBodyContracts.legacyBindings entryBindings
  let producer := ProtectedStateTransition.MarkedAllocation.of_administrative
    (ProtectedStateTransition.Lexical.legacyProtocol entry)
    (ProtectedStateTransition.Lexical.legacyTransport transport) bindings layouts frame
    (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, traced, restored, represented, finalHeaps, maps, worlds, frame, metadata, _post⟩ :=
    Stateful.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary
      signatures catalogValid found casesTyped defaultTyped sameLedger budget size bounded
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) producer bindings
      (fun _ _ _ => fun _ _ => True.intro)
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (fun extended valid => runtime_binders extended valid) (fun valid => valid)
      (fun valid child smaller => ProtectedStateMatchBodyContracts.legacy_expression_reflects
        transport (expressionMeaning valid child smaller))
      (fun request member childContext related child smaller =>
        RecursiveNamedImperativeFor.Control.Compatibility.legacy_reflects functions program evidence transport
          (children request member childContext related child smaller))
      contextValid environments heaps locals agrees actualTyped reference read unmapped ⟨initial⟩ trivial completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, traced, restored, represented, finalHeaps, maps, worlds, frame, metadata⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchRuntimeHead
