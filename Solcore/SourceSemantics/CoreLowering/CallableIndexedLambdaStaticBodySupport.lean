import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates

/-! Same-code static body receipts are independent of their expression grammar.
The actual compiler view supplies flow acceptance and finish equality. Static
occurrence certificates return to the canonical source through the one finite
transport fold. Rank belongs only to nested lambda receipt tokens; named calls
retain arbitrary recursion through the catalog and acquire no rank condition.
This unit supplies no body execution law or call-time catalog authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open CallableLambdaViewEdits CallableLambdaBodyReachability

theorem context_valid {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements) :
    CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements inputs.context function.evidence := by
  exact (CompatibleRuntimeContextValidity.Valid.mk sameLedger frame.code.requirement_ledger frame.evidence_covers).mono inputs.extended

structure BodyWith
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate) {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    extends CallableIndexedLambdaEntryPrefix.Context code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  actualTree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
    (expressionSyntax code.view)
    (certificates readFuel code.view)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  actualSites : actualTree.CatalogSites .reachable registry faults
  tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function.source
    (expressionSyntax function.source)
    (certificates readFuel function.source)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source


theorem BodyWith.of_tree
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate} {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (syntaxTransport : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      expressionSyntax code.view id → expressionSyntax function.source id)
    (expressions : ∀ context scope id lowered,
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      certificates readFuel code.view context scope id lowered →
      certificates readFuel function.source context scope id lowered)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (expressionSyntax code.view)
      (certificates readFuel code.view)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : BodyWith expressionSyntax certificates code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧
      body.flow = flow ∧ HEq body.actualTree tree := by
  have reverse : LocalView code.view function.source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  obtain ⟨canonical, canonicalSites⟩ := CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    reverse (avoids.view edited.metadata) (edited.metadata.unique unique)
    (fun id reached receipt => syntaxTransport id (reached.metadata edited.metadata.symm) receipt)
    (fun context scope id lowered reached receipt => expressions context scope id lowered
      (reached.metadata edited.metadata.symm) receipt)
    sites (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact ⟨{
    toContext := inputs
    frame := frame
    readFuel := readFuel
    policy := policy
    callback := callback
    flow := flow
    generated := generated
    projection := projection
    emitted := Except.ok.inj accepted.symm
    actualTree := tree
    actualSites := sites
    tree := canonical
    sites := canonicalSites
    valid := context_valid code inputs frame sameLedger
    unique := unique }, rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Acceptance is retained at the actual compiler view. The canonical Tree
needs no second lowering success. -/
theorem BodyWith.accepted
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : BodyWith expressionSyntax certificates code program registry faults) :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body :=
  CallableIndexedLambdaSemanticInvocation.loops_accepted code body.policy body.callback

/-- A family is indexed by actual Code. Its rank may restrict nested lambda
leaves without imposing an order on named catalog calls. -/
abbrev SupportAt
    (expressionSyntax : Nat → TypedSource → ExpressionId → Prop)
    (certificates : Nat → Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (rank : Nat) {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  BodyWith (expressionSyntax rank) (certificates rank) code program registry faults

/-- This token records a smaller static body only at a literal lambda site.
Its source, context, occurrence and emitted expression are explicit receipts. -/
structure NestedLambda
    {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked)
    (support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → Code prepared function scope administrative → Type)
    (rank : Nat) (source : TypedSource) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  function : Dynamic.Closure
  administrative : Core.Context
  code : Code prepared function scope administrative
  sourceEq : function.source = source
  contextEq : function.context = context
  identifier : code.id = id
  emitted : code.lowered = lowered
  sourceType : code.sourceNode.type = FunctionValues.sourceType function
  requirements : code.sourceNode.requirements = []
  coercions : code.sourceNode.coercions = []
  childRank : Nat
  smaller : childRank < rank
  body : support childRank code

/-- Ordinary and authenticated named calls remain in the existing family.
Only literal lambda tokens contain a static rank comparison. -/
inductive CallsWith
    {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked)
    (support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → Code prepared function scope administrative → Type)
    (rank : Nat) (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (source : TypedSource) (context : SourceSemantics.Context)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | existing {id lowered} (head : calls children scope id lowered) :
      CallsWith prepared support rank calls source context children scope id lowered
  | lambda {id lowered} (head : NestedLambda prepared support rank source context scope id lowered) :
      CallsWith prepared support rank calls source context children scope id lowered

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
