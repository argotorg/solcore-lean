import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds

/-! The actual finite compiler requests close the match head's selected branch
ports. Source contexts and numeric pattern evidence come from original pattern
typing; the genuine marked allocator supplies the actual hidden and arm cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CallableIndexedOwnedAdmittedStagedMatchSequences
universe u

/-- No branch execution is assumed: each authentic finite request is supplied
by the surrounding compiler-tree induction at its exact Source context. -/
theorem reflects {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  (definitions : layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) invocation.source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat) (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

    (_children : ∀ childSize, childSize < budget →
      ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
        (stages := stages) (invocation := invocation) (faults := faults)
        bridge functions condition childContext request.scope request.statements expected type request.code budget) :
    MatchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  refine CallableIndexedOwnedAdmittedStagedMatchReflection.reflects
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary)
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (CompatibleMatchTypedLiteralSites.Certificate.sites restricted signatures found casesTyped) catalog found typed
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget condition producer bindings acquire
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
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
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  (definitions : layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) invocation.source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat) (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

    (_unique : NodeOccurrencesUnique invocation.source)
    (_children : ∀ childSize, childSize < budget →
      PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
        (stages := stages) (invocation := invocation) (faults := faults)
        bridge functions condition childContext request.scope request.statements expected type request.code budget) :
    MatchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
  refine CallableIndexedOwnedAdmittedStagedMatchPreservation.preserves
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) _unique
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (CompatibleMatchTypedLiteralSites.Certificate.sites restricted signatures found casesTyped) catalog found typed
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget condition producer bindings acquire
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
