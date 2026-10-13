import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping

/-! Nested formation derives the inner frame from the actual outer closure's
Source typing and reached lexical context. Both views keep the original body
nodes, and the original policy supplies the exact emitted inner Site. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableLambdaBodyReachability

private theorem reached_body {source : TypedSource} {roots : List NodeId}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (parent : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    {target : NodeId} (reached : Reaches source (body.map NodeId.statement) target) :
    Reaches source roots target := by
  induction reached with
  | root member => exact .expression parent found (by simpa only [form, ExpressionForm.references] using member)
  | expression _ selected edge ih => exact .expression ih selected edge
  | statement _ selected edge ih => exact .statement ih selected edge

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {captured : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function captured administrative)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {childFuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}

include provenance in
theorem of_expression
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty} {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : id.occurrence.owner = function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed support.caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked function.source id = .ok (node, reported))
    (returnFound : function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (fields : Dynamic.RuntimeContextFields support.body.context sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope sourceContext)
    (sourceTyped : ExpressionHasType function.source sourceContext id node.type)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody childFuel
      code.compilation code.view scope id code.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) support.caller)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      support.caller sourceContext child.evidence scope id lowered) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaProducer.of_expression
    (sourceContext := sourceContext) (evidence := child.evidence) code support provenance profile
    found form owner requirements coercions ordinary read reached accepted nativeTyped
  let inner := closure support.caller.named parameters result [statement] sourceContext child.evidence []
  have original : inner.source = function.source := support.source.symm
  have actualFound : function.source.lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, support.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  have innerTyped : ExpressionHasType inner.source sourceContext id produced.site.code.sourceNode.type := by
    simpa only [original, sameNode] using sourceTyped
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts inner id produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [original] using support.unique)
      (by simpa only [original] using actualFound) produced.site.code.sourceForm innerTyped (sameNode ▸ coercions)
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) inner.context inner.source := by
    change Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext inner.source
    rw [original]
    exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      support.body.frame support.body.extended).1).transport fields
  have covers : inner.evidence.Covers inner.context := by
    change child.evidence.Covers sourceContext
    rw [stages.evidence selected]
    exact fields.covers support.body.valid.covers
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership inner.source := by
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate support.caller wellFormed
    rw [original, support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : inner.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation, ← support.compilation]
    exact fields.solvedRequirements.trans support.body.valid.ledger
  have invocationSource : child.source = inner.source := (stages.source selected).trans original.symm
  have innerReturn : inner.source.lookupStatement? statement = some returnNode := by simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression inner.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound innerReturn) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have inside : Reaches function.source (function.body.map NodeId.statement) (.expression expression) :=
    reached_body reached found form (.statement (.root (by simp)) returnFound
      (by simp only [returnForm, StatementForm.references]; simp))
  have childOriginal : function.source.lookupExpression? expression = some readNode := by
    simpa only [original] using childFound
  have viewFound : produced.site.code.view.lookupStatement? statement = some returnNode := by
    rw [view]
    exact code.viewOfSource.symm.statement returnFound
  have viewRead : produced.site.code.view.lookupExpression? expression = some readNode := by
    rw [view]
    exact (provenance.body_view expression inside).symm.trans childOriginal
  have viewTyped : ExpressionHasType produced.site.code.view inputs.context expression readNode.type := by
    rw [view]
    exact CallableLambdaViewStaticTyping.expression
      (CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource)
      (CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view) support.unique
      (by simpa only [original] using childTyped) inside
  obtain ⟨loweredBody, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return_view
    produced.site.code produced.recipe inputs frame ledger profile rfl innerReturn returnForm returnType
    childFound childType childTyped viewFound viewRead viewTyped
  have bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code := by
    intro childId childReached
    have path : Reaches function.source ([statement].map NodeId.statement) (.expression childId) := by
      change Reaches inner.source ([statement].map NodeId.statement) (.expression childId) at childReached
      rw [original] at childReached
      exact childReached
    rw [view]
    exact original ▸ provenance.body_view childId (reached_body reached found form path)
  have bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code support.caller.named := by
    intro childId childReached
    have path : Reaches function.source ([statement].map NodeId.statement) (.expression childId) := by
      change Reaches inner.source ([statement].map NodeId.statement) (.expression childId) at childReached
      rw [original] at childReached
      exact childReached
    rw [reason]
    exact provenance.body_reasons childId (reached_body reached found form path)
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer support.caller produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression loweredBody) body bodyView bodyReasons
    (by simpa only [support.source] using declarations) syntaxTree facts.sourceType facts.ordinary facts.coercions⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
