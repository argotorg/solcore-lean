import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeads
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds

/-! Protected finite match heads consume only smaller expression and selected
body contracts. The original source and Core budgets remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
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
  (valid : CompatiblePatternLeaves.ContextValid compilation context)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  {solved : List SolvedRequirement} {administrative : Core.Context} {faults : FunctionCalls.FaultRep}

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem head_preserves_bounded (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchPreservation.Certificate.preserves_bounded onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded transport entryBindings
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

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem head_reflects_bounded (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchReflection.Certificate.reflects_bounded onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded transport entryBindings
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


end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
