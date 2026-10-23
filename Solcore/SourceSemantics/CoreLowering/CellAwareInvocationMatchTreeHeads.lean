import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchSequences
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds

/-! The actual finite compiler requests close the match head's selected branch
ports. Source contexts and numeric pattern evidence come from original pattern
typing; the genuine marked allocator supplies the actual hidden and arm cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CellAwareInvocationMatchSequences
universe u

private theorem arms_sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {source semanticSource : TypedSource} {site scope expected bodyCertificate cases arms}
    (certificates : CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate cases arms)
    {context : SourceSemantics.Context} {control : ControlContext} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (typed : MatchCasesHaveType semanticSource control context expected cases caseFacts) :
    CompatibleMatchDecision.Arms.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificates := by
  induction certificates generalizing caseFacts with
  | nil => exact .nil
  | cons pattern native body tail ih =>
      cases typed with
      | cons head remaining =>
          cases head with
          | intro patternTyped extended bodyTyped =>
              exact .cons (patternCertificate := pattern) (typed := native) (bodyCertified := body) (CompatibleMatchTypedLiteralSites.pattern_sites pattern signatures patternTyped) (ih remaining)

private theorem sites
    {compilation : SourceCoreCompatibleDataMatches.Context} {source semanticSource : TypedSource} {scope id resolution resultType internalReason expressionCertificate bodyCertificate code}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {context : SourceSemantics.Context} {control : ControlContext} {node : ExpressionNode} {caseFacts : List BodyFacts}
    (signatures : context.signatures = compilation.signatures)
    (found : source.lookupExpression? resolution.scrutinee = some node)
    (typed : MatchCasesHaveType semanticSource control context node.type resolution.cases caseFacts) :
    CompatibleMatchDecision.Certificate.LiteralSites
      (fun numeric => RequirementProves context numeric.requirement numeric.predicate) certificate := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
      have same := Option.some.inj (scrutineeFound.symm.trans found)
      cases same
      exact .matchWith (read := read) (statementTypeValid := allowed) (form := form) (requirements := requirements)
        (hiddenOwned := hiddenOwned) (hiddenFresh := hiddenFresh) (scrutineeOwned := scrutineeOwned)
        (scrutineeFound := scrutineeFound) (projection := projection) (expression := expression) (sameType := sameType)
        (fallbackCertificate := fallback) (branchesCertified := branches) (hiddenCompiled := hiddenCompiled)
        (arms_sites arms signatures typed)


/-- No branch execution is assumed: each authentic finite request is supplied
by the surrounding compiler-tree induction at its exact Source context. -/
theorem reflects {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active onError)))
  (definitions : compiled.indexed.layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : compiled.indexed.ancestry.layout.frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) allocationSource scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  (sourceEq : invocation.source = index.source)
  {compilerNode : ExpressionNode}
  (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
  (sameSourceType : compilerNode.type = node.type)
  {statement : StatementNode}
  (statementFound : index.source.lookupStatement? id = some statement)
  (statementForm : statement.form = .matchWith resolution)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    callerProtocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

    (_children : ∀ childSize, childSize < budget →
      ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge childContext
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
        stages invocation faults administrative request.scope false request.statements expected type request.code budget) :
    MatchReflects (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store finalStore ξ value
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  refine CellAwareInvocationMatchReflection.reflects
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions index sourceEq onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary)
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (sites restricted signatures compilerFound (sameSourceType.symm ▸ casesTyped)) catalog found typed compilerFound sameSourceType statementFound statementForm
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget producer bindings
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

theorem preserves {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active onError)))
  (definitions : compiled.indexed.layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : compiled.indexed.ancestry.layout.frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) allocationSource scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  (sourceEq : invocation.source = index.source)
  {compilerNode : ExpressionNode}
  (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
  (sameSourceType : compilerNode.type = node.type)
  {statement : StatementNode}
  (statementFound : index.source.lookupStatement? id = some statement)
  (statementForm : statement.form = .matchWith resolution)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    callerProtocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

    (_unique : NodeOccurrencesUnique invocation.source)
    (_children : ∀ childSize, childSize < budget →
      PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge childContext
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
        stages invocation faults administrative request.scope false request.statements expected type request.code budget) :
    MatchPreserves (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store ξ
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
  refine CellAwareInvocationMatchPreservation.preserves
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions index sourceEq onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) _unique
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (sites restricted signatures compilerFound (sameSourceType.symm ▸ casesTyped)) catalog found typed compilerFound sameSourceType statementFound statementForm
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget producer bindings
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready trace
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchTreeHeads
