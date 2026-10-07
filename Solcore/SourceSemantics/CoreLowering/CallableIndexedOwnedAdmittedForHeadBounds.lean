import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeInitializerSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection

/-! The original initializer and loop inversion receipts compose the exact
admitted header tail with its actual loop post. Restoration retains that same
pool and the genuine Source contexts; no evaluation induction is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open ProtectedStateImperativeCatalogReady RecursiveNamedImperativeFor
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open RecursiveNamedLexicalContracts.Stateful.WithReady (PostReady)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  (validity : SourceSemantics.Context → Prop)
  (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
  (covers : ∀ context, validity context → evidence.Covers context)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)

abbrev PreservingGoal := RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity) (certificates := certificates) (diagnosticPolicy := diagnosticPolicy)
  functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
  (frame := frame) (globals := globals) (onError := onError) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

abbrev ReflectingGoal := RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity) (certificates := certificates) (diagnosticPolicy := diagnosticPolicy)
  functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
  (frame := frame) (globals := globals) (onError := onError) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

theorem restore_post {context finalContext : SourceSemantics.Context}
    {scope tailScope : Scope} {canonical tailCanonical : Environment}
    (returnTo : ProtectedForHeader.Stateful.WithReady.ReadyReturn callerProtocol
      (readiness bridge) context scope canonical finalContext tailScope tailCanonical)
    (environment : Dynamic.Environment) {mapping : LocationMap} {world : StoreTyping}
    {after : Dynamic.Heap} {store : Store}
    (reached : callerProtocol.State ⟨tailScope, mapping, world, after, store, tailCanonical⟩)
    {outcome : Dynamic.ControlOutcome}
    (post : PostReady (readiness bridge) finalContext outcome reached) :
    PostReady (readiness bridge) context (Dynamic.restoreControl environment outcome) (returnTo.restore reached) := by
  cases outcome with
  | fallthrough | returned | breaking | continuing => exact returnTo.restore_ready reached post
  | fault => exact (readiness bridge).fault_after reached (returnTo.restore reached) post (.refl _ _)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem header_preserves
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (child : PreservingGoal bridge functions evidence guard validity budget diagnosticPolicy
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope (.initializers items condition post statements) expected type code) :
    AtMost budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith
      callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity size (context := context) (scope := scope)
      (source := source) (registry := registry) (faults := faults) (frameLayout := frame)
      (globals := globals) (administrative := administrative) id expected type code) := by
  intro size bounded valid parentFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
  have static := ProtectedStateImperativeInitializerSourceSites.for_parent unique parentFacts found form
  obtain ⟨header, errors⟩ := child static
  obtain ⟨control, staticFinal, _bodyFinal, _bodyFacts, _postFinal, _syntaxTree,
    itemsTyped, _conditionTyped, _bodyTyped, _postTyped⟩ := static
  cases trace with
  | control executed =>
    obtain ⟨rfl, initialSize, loopSize, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop, initialSmall, loopSmall⟩ :=
      ForSourceAt.success_at unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := ContextTransport.loop_context loop
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, tailReady, agreement, _same, _originalAdmission, _finalAdmission, _typedExtension, _finalLocals⟩ :=
      CallableIndexedOwnedAdmittedForHeaderBounds.preserves_prefix_bounded_for (solved := [])
        bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed
        validity runtime covers extend budget meaning header valid itemsTyped
        environments heaps locals agrees actualTyped reference read unmapped initial guarded ready initialization
        (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
      (tail.certificate.2) _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate tailReady (.control loop)
    obtain ⟨loopState, loopRelated, loopReady⟩ := loopTransition
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
      frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, callerProtocol.trans headerRelated (callerProtocol.trans loopRelated (returnTo.related loopState)), restore_post bridge returnTo environment loopState loopReady⟩⟩
  | fault failed =>
    rcases ForSourceAt.fault_at unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, _, fault, smaller⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata, transition⟩ :=
        CallableIndexedOwnedAdmittedForHeaderBounds.preserves_fault_reachable_bounded_for
        bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed
        validity runtime covers extend budget meaning header (GenericForHeader.Tree.ErrorsFor.reachable errors) valid itemsTyped
        environments heaps locals agrees actualTyped reference read unmapped initial guarded ready fault
        (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata, transition⟩
    · obtain ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, initialization, loop, initialSmall, loopSmall⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, tailReady, agreement, _same, _originalAdmission, _finalAdmission, _typedExtension, _finalLocals⟩ :=
        CallableIndexedOwnedAdmittedForHeaderBounds.preserves_prefix_bounded_for (solved := [])
        bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed
        validity runtime covers extend budget meaning header valid itemsTyped
        environments heaps locals agrees actualTyped reference read unmapped initial guarded ready initialization
        (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
        (tail.certificate.2) _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate tailReady (.fault loop)
      obtain ⟨loopState, loopRelated, loopReady⟩ := loopTransition
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
        frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, callerProtocol.trans headerRelated (callerProtocol.trans loopRelated (returnTo.related loopState)), restore_post bridge returnTo environment loopState loopReady⟩⟩


include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem header_reflects (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (child : ReflectingGoal bridge functions evidence guard validity budget diagnosticPolicy
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope (.initializers items condition post statements) expected type code) :
    Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith
      callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity size (context := context) (scope := scope)
      (source := source) (registry := registry) (faults := faults) (frameLayout := frame)
      (globals := globals) (administrative := administrative) id expected type code) := by
  intro size bounded valid parentFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
  have static := ProtectedStateImperativeInitializerSourceSites.for_parent unique parentFacts found form
  obtain ⟨header, errors⟩ := child static
  obtain ⟨control, staticFinal, _bodyFinal, _bodyFacts, _postFinal, _syntaxTree,
    itemsTyped, _conditionTyped, _bodyTyped, _postTyped⟩ := static
  have result := CallableIndexedOwnedAdmittedForHeaderBounds.reflects_reachable_bounded_for (solved := [])
    bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed
    validity runtime covers extend budget functionTypes reflection header (GenericForHeader.Tree.ErrorsFor.reachable errors)
    valid itemsTyped environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated (Nat.le_of_lt bounded)
  cases result with
  | @continues initialSize remainingSize initialContext initialEnvironment initialized tail trace maps worlds frame metadata headerRelated returnReceipt tailReady remaining smaller =>
    obtain ⟨returnTo⟩ := returnReceipt
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, loop, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
      (tail.certificate.2) _ (Nat.le_trans smaller (Nat.le_of_lt bounded)) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate tailReady remaining
    obtain ⟨loopState, loopRelated, loopReady⟩ := loopTransition
    refine ⟨SourceExecutionSize.stepSize [initialSize, sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
      restore_rep represented environment, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
      frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, callerProtocol.trans headerRelated (callerProtocol.trans loopRelated (returnTo.related loopState)), restore_post bridge returnTo environment loopState loopReady⟩⟩
    cases loop with
    | control loop => exact .control (.forLoop (lookupStatement?_sound found) form trace loop)
    | fault loop => exact .fault (.forIteration (lookupStatement?_sound found) form trace loop)
  | fault trace same matched heaps maps worlds frame metadata transition =>
    subst value
    exact ⟨_, _, _, _, _, .fault (.forInitializer (lookupStatement?_sound found) form trace),
      (by intro next impossible; cases impossible), .fault matched, heaps, maps, worlds, frame, metadata, transition⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
