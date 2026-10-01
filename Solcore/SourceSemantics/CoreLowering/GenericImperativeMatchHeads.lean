import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchReflection

/-! The emitted match fixes one scrutinee expression. Restricting its static
receipt to that expression supplies local uniqueness without requiring every
certificate for the same source occurrence to have identical native code.
Selected bodies consume the finite request receipt and independent arm context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren

/-- A graph of the single child actually emitted at this match site. -/
def Singleton (scope : Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : ExpressionCertificate :=
  fun actualScope actualId actual => actualScope = scope ∧ actualId = id ∧ actual = lowered

theorem Certificate.singleton {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {type : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
      expressionCertificate bodyCertificate code) :
    ∃ lowered, expressionCertificate scope resolution.scrutinee lowered ∧
      CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
        (Singleton scope resolution.scrutinee lowered) bodyCertificate code := by
  cases receipt with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
    exact ⟨_, expression, .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned
      scrutineeFound projection ⟨rfl, rfl, rfl⟩ sameType arms fallback branches hiddenCompiled⟩

theorem singleton_preserves {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FunctionCalls.FaultRep}
    {expressionCertificate : ExpressionCertificate} {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source expressionCertificate faults)
    (certified : expressionCertificate scope id lowered) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Singleton scope id lowered) faults := by
  intro actualScope actualId actual singleton
  rcases singleton with ⟨rfl, rfl, rfl⟩
  exact meaning certified

theorem singleton_reflects {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FunctionCalls.FaultRep}
    {expressionCertificate : ExpressionCertificate} {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source expressionCertificate faults)
    (certified : expressionCertificate scope id lowered) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Singleton scope id lowered) faults := by
  intro actualScope actualId actual singleton
  rcases singleton with ⟨rfl, rfl, rfl⟩
  exact meaning certified

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
theorem head_preserves (unique : NodeOccurrencesUnique source)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ContextFor source context node.type resolution.cases resolution.defaultBody request childContext →
      TypedLexicalWhile.Preserves functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        false request.statements expected type request.code) :
    TypedLexicalWhile.HeadPreserves functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchPreservation.Certificate.preserves onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same)
  · intro contextValid
    exact singleton_preserves (expressionMeaning contextValid) child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body selected bodySelected
      armContext staticFinal facts extended bodyTyped
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ContextFor.selected_arm_at ⟨_, statements, body⟩ rfl casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body selected bodySelected
      staticFinal facts bodyTyped
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected))

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem head_reflects (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ContextFor source context node.type resolution.cases resolution.defaultBody request childContext →
      TypedLexicalWhile.Reflects functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        false request.statements expected type request.code) :
    TypedLexicalWhile.HeadReflects functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchReflection.Certificate.reflects onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same)
  · intro contextValid
    exact singleton_reflects (expressionMeaning contextValid) child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body selected bodySelected
      armContext staticFinal facts extended bodyTyped
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ContextFor.selected_arm_at ⟨_, statements, body⟩ rfl casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body selected bodySelected
      staticFinal facts bodyTyped
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected))

end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
