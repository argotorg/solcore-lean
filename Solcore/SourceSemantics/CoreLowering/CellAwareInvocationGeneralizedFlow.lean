import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! The actual generalized allocation composes with its remaining statement
flow. Both directions retain the same descriptor attachment, physical frame
and strict continuation grade. Lambda shape observations used for reflection
are explicit until supplied by the actual initializer's source receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open TypedLexicalWhile (initializedRequest sequence)

private theorem head_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements source context (id :: rest)) :
    ∃ control final facts, StatementHasType source control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩


section RequestSource

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  {allocationSource : TypedSource}
  (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest allocationSource scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest allocationSource scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same sourceEq registered bindings in
theorem preserves_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have found := index.statement_read_reached site.reached read
  obtain ⟨tailSize, function, location, bound, sameSize, captures, allocated, remainingTrace⟩ :=
    CellAwareGeneralizedSourceInversion.generalized (by simpa only [sourceEq] using unique)
      (by simpa only [sourceEq] using found) form polymorphic
      (by simpa only [sourceEq] using extended) trace
  have capturesNamed : Dynamic.GeneralizedClosureCaptures context index.source environment binder initializer function := by
    simpa only [sourceEq] using captures
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime locals headTyped
    found form polymorphic capturesNamed
  have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
  obtain ⟨values, marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationGeneralizedPrefix.complete_at_source bridge artifact checked entry unique site read form
      projected generated issuer declaration polymorphic extended
      ordinary nativeTyped allocation annotation same producer registered environments heaps locals agrees actualTyped
      initial admitted authority physical (ready initial physical.read) capturesNamed functionTyped allocated type body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    tail _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := lowered.type)
    (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState
  refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, represented, finalHeaps,
    effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState post

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects_at_source (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    completed
  let function := Dynamic.GeneralizedClosure.ofDirectLambda context index.source environment binder initializer
    parameters result lambdaBody
  have captures : Dynamic.GeneralizedClosureCaptures context index.source environment binder initializer function :=
    .directLambda (lookupExpression?_sound initializerFound) initializerForm
      (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
  let location : Dynamic.Location := ⟨before.cells.length⟩
  let bound : Dynamic.Heap := ⟨before.cells ++ [⟨function.binder.scheme.body, none, some function⟩]⟩
  have allocated : Dynamic.Heap.AllocatesGeneralized before function location bound := .append
  have unique := runtime.graph.nodeOccurrencesUnique
  have found := index.statement_read_reached site.reached read
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime locals headTyped
    found form polymorphic captures
  obtain ⟨values, marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareInvocationGeneralizedPrefix.complete_at_source bridge artifact checked entry unique site read form
      projected generated issuer declaration polymorphic extended
      ordinary nativeTyped allocation annotation same producer registered environments heaps locals agrees actualTyped
      initial admitted authority physical (ready initial physical.read) captures functionTyped allocated type body
  obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
    tail _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
  let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := binder.id) (type := lowered.type)
    (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
    .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form
      (by simpa only [sourceEq] using captures) polymorphic (by simpa only [sourceEq] using extended) allocated trace,
    represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
    effect.metadata.trans metadata, effect.trans finalEffect, finalState,
    protocol.trans related (protocol.trans tailRelated (bindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := lowered.type)
      (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState)), ?_⟩
  exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) tailState post

end RequestSource

section Legacy

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)
  {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {mode : Bool} {id : StatementId} {node : StatementNode}
  {binder : TypedBinder} {initializer : ExpressionId} {rest : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {childFuel : Nat} {reasonAt : ExpressionId → Word} {stored payload : Ty}
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (entry : index.ResidualEntry) (site : index.Site (.statement id))
  (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
  (form : node.form = .letDecl binder (some initializer))
  (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
  (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
  (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs childFuel scope initializer reasonAt))
  (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
    (fun actual => decide (actual.id = binder.id)) = [binder])
  (polymorphic : binder.scheme.quantified ≠ [])
  (extended : BinderExtends index.source.owner context binder nextContext)
  (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
  (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
  (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
    (initializedRequest index.source scope binder lowered.type))
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
    whole.indexed.base.globals.length
    (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
    (initializedRequest index.source scope binder lowered.type))
  (same : annotation.original = allocation.expression)
  (sourceEq : invocation.source = index.source)


include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same sourceEq registered bindings in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
  apply preserves_at_source (allocationSource := index.source) <;> first | assumption | rfl

variable {initializerNode : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {lambdaBody : List StatementId}
  (initializerFound : index.source.lookupExpression? initializer = some initializerNode)
  (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
  (valueType : initializerNode.type = binder.scheme.body)
  (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])

include artifact checked entry site read form projected generated issuer declaration polymorphic
  extended ordinary nativeTyped allocation annotation same sourceEq registered bindings
  initializerFound initializerForm valueType requirements coercions in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge nextContext model index producer registry invocation faults
      administrative ((binder.id, lowered.type) :: scope) mode rest expected type body budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost
      (attachment := GeneralizedLocalCapturedScopes.Attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (sequence type lowered.expression annotation.expression body) budget := by
  apply reflects_at_source (allocationSource := index.source) <;> first | assumption | rfl


end Legacy

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedFlow
