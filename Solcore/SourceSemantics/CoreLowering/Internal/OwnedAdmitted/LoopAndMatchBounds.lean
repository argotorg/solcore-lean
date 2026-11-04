import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReceiptOperations
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ImperativeMatches
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchSelection

/-!
# Admitted profile: loops, matches and data heads

Bounds and readiness of loops and matches, data heads, compositions and catalog producers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
/-! Genuine parent typing supplies only its actual ordered operand row. The
shared readiness composition proof passes each child's exact successful state
to the next child or selected branch. Its returned witness is retained when
original Source preservation supplies the parent's full post admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}

/-- Only actual operand slots receive Source typing and child admission. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate) faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _⟩ :=
    RecursiveNamedExpressionCompositionsBounds.Stateful.WithReady.Head.preserves_at functions program evidence
      callerProtocol (Admission bridge context) budget size bounded unique tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.PreservesAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.preserves_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- The real reflected Source trace keeps its independent grade and certifies
post admission at the exact reached native witness. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate) faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _⟩ :=
    RecursiveNamedExpressionCompositionsBounds.Stateful.WithReady.Head.reflects_at functions program evidence
      callerProtocol (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.ReflectsAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.reflects_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      environments heaps locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds
/-! Constructor, member and index heads consume genuine Source typing at their
actual input. Index's exact successful base post supplies key admission; its
terminal helper retains the same Source heap. The returned full parent trace
establishes post admission at that same reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {calls : CompatibleExpressionCalls.CallHeads} {reasonAt : ExpressionId → Word}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include transport extension faithful functionLeaves functionTypes missing

/-- Genuine parent typing supplies the original operand row independently of
the constructor's generated payload vector and native child types. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady.Head.preserves_at functions extension faithful
      functionLeaves functionTypes program evidence unique missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.PreservesAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.preserves_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Native reflection keeps its independent whole Source grade and actual
terminal witness before Source preservation supplies success-only admission. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady.Head.reflects_raw_at functions extension faithful
      functionLeaves functionTypes program evidence missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.ReflectsAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.reflects_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sized frame⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
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

open ProtectedStateImperativeCatalogPayload (HeaderReceiptFamily)

abbrev PreservingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

abbrev ReflectingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

include unique in
theorem header_preserves_with_receipt
    (R : HeaderReceiptFamily)
    (prefixAt : CallableIndexedOwnedHeaderReceiptOperations.PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence guard validity budget R)
    (faultsAt : CallableIndexedOwnedHeaderReceiptOperations.FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (child : PreservingGoalWithReceipt bridge functions evidence guard validity budget R
      (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax)
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
  have header := child static
  obtain ⟨control, staticFinal, _bodyFinal, _bodyFacts, _postFinal, _syntaxTree,
    itemsTyped, _conditionTyped, _bodyTyped, _postTyped⟩ := static
  cases trace with
  | control executed =>
    obtain ⟨rfl, initialSize, loopSize, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop, initialSmall, loopSmall⟩ :=
      ForSourceAt.success_at unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := ContextTransport.loop_context loop
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, tailReady, agreement, _same, _originalAdmission, _finalAdmission, _typedExtension, _finalLocals⟩ :=
      prefixAt header valid itemsTyped
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
        faultsAt header valid itemsTyped
        environments heaps locals agrees actualTyped reference read unmapped initial guarded ready fault
        (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata, transition⟩
    · obtain ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, initialization, loop, initialSmall, loopSmall⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, headerRelated, ⟨returnTo⟩, tailReady, agreement, _same, _originalAdmission, _finalAdmission, _typedExtension, _finalLocals⟩ :=
        prefixAt header valid itemsTyped
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
  exact header_preserves_with_receipt (unique := unique) bridge functions evidence guard validity budget
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_PrefixAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_FaultAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    found form child

include unique in
theorem header_reflects_with_receipt
    (R : HeaderReceiptFamily)
    (reflected : CallableIndexedOwnedHeaderReceiptOperations.ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (child : ReflectingGoalWithReceipt bridge functions evidence guard validity budget R
      (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax)
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
  have header := child static
  obtain ⟨control, staticFinal, _bodyFinal, _bodyFacts, _postFinal, _syntaxTree,
    itemsTyped, _conditionTyped, _bodyTyped, _postTyped⟩ := static
  have result := reflected header
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
  exact header_reflects_with_receipt (unique := unique) bridge functions evidence guard validity budget
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_ReflectsAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy functionTypes reflection)
    found form child

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness
/-! The real native self-cell activation retains the original Source heap.
Its actual administrative effects authenticate every reached row's history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- This producer uses the exact activation endpoint's Source heap index and
real administrative preservation. The reached state and records stay intact. -/
theorem activation : ProtectedWhile.Body.Stateful.WithReady.ActivationTransfers callerProtocol
    (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) where
  ready := by
    intro context scope mapping world heap store canonical actual type condition body reason initial reached
      frame _related _records admitted
    exact ⟨admitted.heap,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
/-! Authentic Source statement syntax and typing supply the real condition
and loop-body sites. Admitted children run at the exact retained states from
the existing measured while proofs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedLoopContracts (Below)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open TypedLexicalWhile (Scope ValuesContext)

private theorem body_syntax {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements) :
    ProtectedStateImperativeSourceSites.Facts source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, syntaxTree, _typed⟩ := facts
  cases syntaxTree
  case body syntaxTree =>
    cases syntaxTree <;> simp_all
  all_goals simp_all [ProtectedStateImperativeSourceSites.Facts]

/-- Only the authentic parent while occurrence projects condition and body
facts; original Source typing remains independent of the lowered Core type. -/
theorem sites {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode) :
    ProtectedStateLexicalSourceSites.ExpressionFacts source context condition conditionNode ∧
      ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax context false statements expected := by
  have bodySyntax := body_syntax facts found form
  obtain ⟨_mode, _rest, _syntaxTree, statementsTyped⟩ := facts
  obtain ⟨conditionTyped, bodyTyped⟩ := ProtectedStateImperativeTypedSourceSites.while_loop unique
    (ProtectedStateImperativeTypedSourceSites.head statementsTyped) found form
  obtain ⟨original, contains, sameType⟩ := conditionTyped.stored_type
  have sameNode : original = conditionNode :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans conditionFound)
  subst original
  exact ⟨by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using conditionTyped,
    bodySyntax, bodyTyped⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (guard : Location → NativeFrame → Prop)
  {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport callerProtocol)

include transport in
theorem preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid sourceFacts
  obtain ⟨conditionFacts, bodyFacts⟩ := sites unique sourceFacts found form conditionFound
  exact ProtectedWhile.Body.Stateful.WithReady.while_preserves_bounded_for
    (protocol := callerProtocol) (guard := guard) (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedWhileReadiness.activation bridge)
    functions program evidence transport validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning child smaller))
    found form conditionFound conditionFacts bodyFacts conditionTree typed unique correct size bounded valid True.intro

include transport in
theorem reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid sourceFacts
  obtain ⟨conditionFacts, bodyFacts⟩ := sites unique sourceFacts found form conditionFound
  exact ProtectedWhile.Body.Stateful.WithReady.while_reflects_bounded_for
    (protocol := callerProtocol) (guard := guard) (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedWhileReadiness.activation bridge)
    functions program evidence transport validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning child smaller))
    found form conditionFound conditionFacts bodyFacts conditionTree typed correct bodyCannotFault size bounded valid True.intro

include transport in
/-- The authentic same-code body compiler Tree discharges the separate Source
control-fault restriction through its existing proved control shape. -/
theorem reflects_bounded_from_tree_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (bodyTree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values source
      expressionSyntax certificates ambient.definitions administrative context scope
      (.statements false statements) expected type code) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  exact reflects_bounded_for bridge guard functions evidence transport validity budget meaning
    found form conditionFound conditionTree typed unique correct
    (fun executed => bodyTree.control_not_fault unique executed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness
/-! Genuine Source allocations instantiate match readiness at the actual
selection post. Each restore consumes the same reached body state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- The actual hidden and binder Source allocations establish deep heap
typing; the actual administrative receipt authenticates reached row history. -/
theorem prefix_transfers (source : TypedSource) :
    ProtectedStateMatchReady.PrefixTransfers callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) source where
  hidden := by
    intro initial reached first last context type value location admitted valueTyped allocated frame
    exact CallableIndexedOwnedMatchAdmission.after_hidden bridge first last admitted valueTyped allocated frame
  arm := by
    intro initial reached first last context armContext control resolution type caseFacts value hidden
      location statements bindings environment armEnvironment admitted valueTyped hiddenAllocated
      casesTyped selected extended allocated frame
    exact (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge first last
      admitted valueTyped hiddenAllocated casesTyped selected extended allocated frame).1
  restore_arm := by
    intro scope selectedScope canonical selectedCanonical returnTo context armContext binders extended
      mapping world heap store state admitted
    exact CallableIndexedOwnedMatchPrefixAdmission.restore_arm bridge returnTo extended state admitted
  restore_parent := by
    intro scope selectedScope canonical selectedCanonical returnTo context mapping world heap store state admitted
    exact CallableIndexedOwnedMatchPrefixAdmission.restore_parent bridge returnTo state admitted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
/-! Original Source match typing supplies the scrutinee and selected bodies.
Admitted children run at the exact states from the shared match proofs, including
the combined marked prefix and the actual body post restored to its caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates

/-- Raw Source typing is normalized only through its actual stored node. The
native projection and marker binder type do not determine these judgments. -/
theorem sites {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typed : ProtectedStateImperativeTypedSourceSites.Head source context id)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee) :
    ∃ control caseFacts,
      ProtectedStateLexicalSourceSites.ExpressionFacts source context resolution.scrutinee scrutinee ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      ∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts := by
  obtain ⟨control, rawType, caseFacts, expressionTyped, casesTyped, defaultTyped⟩ :=
    CallableIndexedOwnedMatchAdmission.typing_of_head unique typed found form
  obtain ⟨original, contains, sameType⟩ := expressionTyped.stored_type
  have sameNode : original = scrutinee :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans scrutineeFound)
  subst original
  exact ⟨control, caseFacts,
    by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using expressionTyped,
    by simpa only [sameType] using casesTyped,
    defaultTyped⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}
  (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {scope : Scope} {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
  (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    expressionCertificate bodyCertificate code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
  (unique : NodeOccurrencesUnique source)
  (validity : SourceSemantics.Context → Prop) (literals : IntegerLiteralResolution → Prop)
  (signatures : context.signatures = compilation.signatures)
  (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
  (literalSites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
  (validity_binders : ∀ {binders target}, BindersExtend source.owner context binders target → validity context → validity target)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {statementNode : StatementNode} (statementFound : source.lookupStatement? id = some statementNode)
  (statementForm : statementNode.form = .matchWith resolution)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {lowered : SourceCoreBasic.LoweredExpr}
  (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
  (stateBindings : Bindings callerProtocol)
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

include allocator definitions registered extended certificate ordinary unique signatures numericRequirements literalSites
  validity_binders catalogValid statementFound statementForm found uniqueExpression producer stateBindings acquire in
theorem preserves_bounded_for (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : validity context → ∀ child, child < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        context evidence source expressionCertificate faults child)
    (armMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.ArmPreservesBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults))
    (defaultMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.DefaultPreservesBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults)) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (fun context id _ => ProtectedStateImperativeTypedSourceSites.Head source context id)
      functions program evidence validity (values := compilation.values) (source := source) (context := context)
      (administrative := administrative) (frameLayout := frame) (globals := globals) (registry := registry)
      (faults := faults) size (scope := scope) id expected type code := by
  intro valid parentTyped
  obtain ⟨control, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
    sites unique parentTyped statementFound statementForm found
  exact CompatibleMatchPreservation.Stateful.WithReady.Certificate.preserves_bounded_for
    onError allocator functions definitions registered extended certificate ordinary unique validity literals signatures
    numericRequirements literalSites validity_binders catalogValid found uniqueExpression casesTyped (fun {statements} present => defaultTyped statements present) budget size bounded
    callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (CallableIndexedOwnedAdmittedMatchReadiness.prefix_transfers bridge source)
    (ProtectedStateLexicalSourceSites.ExpressionFacts source) scrutineeTyped guard producer stateBindings acquire
    (fun valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (expressionMeaning valid child smaller))
    (armMeaning control) (defaultMeaning control) valid True.intro

include allocator definitions registered extended certificate ordinary unique signatures numericRequirements literalSites
  validity_binders catalogValid statementFound statementForm found uniqueExpression producer stateBindings acquire in
theorem reflects_bounded_for (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : validity context → ∀ child, child < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        context evidence source expressionCertificate faults child)
    (armMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.ArmReflectsBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults))
    (defaultMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.DefaultReflectsBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults)) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (fun context id _ => ProtectedStateImperativeTypedSourceSites.Head source context id)
      functions program evidence validity (values := compilation.values) (source := source) (context := context)
      (administrative := administrative) (frameLayout := frame) (globals := globals) (registry := registry)
      (faults := faults) size (scope := scope) id expected type code := by
  intro valid parentTyped
  obtain ⟨control, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
    sites unique parentTyped statementFound statementForm found
  exact CompatibleMatchReflection.Stateful.WithReady.Certificate.reflects_bounded_for
    onError allocator functions definitions registered extended certificate ordinary validity literals signatures
    numericRequirements literalSites validity_binders catalogValid found uniqueExpression casesTyped (fun {statements} present => defaultTyped statements present) budget size bounded
    callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (CallableIndexedOwnedAdmittedMatchReadiness.prefix_transfers bridge source)
    (ProtectedStateLexicalSourceSites.ExpressionFacts source) scrutineeTyped guard producer stateBindings acquire
    (fun valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (expressionMeaning valid child smaller))
    (armMeaning control) (defaultMeaning control) valid True.intro

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
/-! Authentic finite catalog recipes consume only their actual smaller child
results. Source facts identify visited contexts; the existing loop and post
producers keep the exact reached pools and independent Source/native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedStateImperativeCatalogReady
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
theorem match_child_syntax {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context childContext : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode} {expected : TypeSystem.Ty}
    {request : GenericMatchChildren.Request} {hiddenIds : List Resolved.LocalId}
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (related : GenericMatchChildren.ScopedContextFor source context hiddenIds scrutinee.type
      resolution.cases resolution.defaultBody request childContext) :
    GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected := by
  obtain ⟨mode, rest, syntaxTree, _typed⟩ := facts
  cases syntaxTree
  case matchWith _found _form _sourceType _scrutineeFound _scrutineeTyped _scrutineeSyntax _casesTyped _defaultTyped _hiddenOrdinary _armsOrdinary children _remaining =>
    simp_all
    apply_assumption
    exact related.forget
  case terminalMatch _unique _found _form _sourceType _scrutineeFound _scrutineeTyped _scrutineeSyntax _casesTyped _defaultTyped _hiddenOrdinary _armsOrdinary children _stops =>
    simp_all
    apply_assumption
    exact related.forget
  case body syntaxTree => cases syntaxTree <;> simp_all
  all_goals simp_all

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
  {solved : List SolvedRequirement}
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)

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

open ProtectedStateImperativeCatalogPayload (HeaderReceiptFamily)

abbrev PreservingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

abbrev ReflectingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

include stateTransport unique in
theorem preserving_loops_with_receipts
    (R : HeaderReceiptFamily)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (postSuccess : CallableIndexedOwnedPostReceiptOperations.PrefixAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) bridge functions evidence guard validity budget HP)
    (postFault : CallableIndexedOwnedPostReceiptOperations.FaultAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget HP)
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      HP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    obtain ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩ := loopFacts
    have packet : CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax context condition post statements expected :=
      ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩
    intro size bounded valid
    refine (CallableIndexedOwnedAdmittedForBounds.loop_preserves_bounded_for bridge guard functions evidence stateTransport validity budget
      (meaning context valid) packet conditionFound conditionTree typed unique
      (fun size smaller => child size (Nat.le_of_lt smaller)) ?_ ?_) size bounded valid
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before after store finalContext finalEnvironment state native read guarded ready continued trace
      exact postSuccess postTree postErrors valid postTyped agrees reference
        state read guarded ready continued trace (Nat.le_of_lt smaller)
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before after store finalContext reason state native read guarded ready continued trace
      exact postFault postTree postErrors
        valid postTyped agrees reference state read guarded ready continued trace (Nat.le_of_lt smaller)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem preserving_loops
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingLoops callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      diagnosticPolicy (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    exact preserving_loops_with_receipts (stateTransport := stateTransport) (unique := unique) bridge functions evidence guard validity budget
      (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree)
      (CallableIndexedOwnedPostReceiptOperations.prefixat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_PrefixAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning))
      (CallableIndexedOwnedPostReceiptOperations.faultat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_FaultAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning))
      meaning
      (.mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child) loopFacts

include stateTransport unique in
theorem reflecting_loops_with_receipts
    (R : HeaderReceiptFamily)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (postReflection : CallableIndexedOwnedPostReceiptOperations.ReflectsAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget HP)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      HP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    obtain ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩ := loopFacts
    have packet : CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax context condition post statements expected :=
      ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩
    intro size bounded valid
    refine (CallableIndexedOwnedAdmittedForBounds.loop_reflects_bounded_from_tree_for bridge guard functions evidence stateTransport validity budget
      (reflection context valid) packet conditionFound conditionTree typed unique child ?_ bodyTree) size bounded valid
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before store finalStore value state native read guarded ready continued evaluated
      exact postReflection postTree postErrors
        valid postTyped agrees reference state read guarded ready continued evaluated (Nat.le_of_lt smaller)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem reflecting_loops (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingLoops callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      diagnosticPolicy (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    exact reflecting_loops_with_receipts (stateTransport := stateTransport) (unique := unique) bridge functions evidence guard validity budget
      (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree)
      (CallableIndexedOwnedPostReceiptOperations.reflectsat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_ReflectsAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy functionTypes reflection))
      reflection
      (.mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child) loopFacts

include definitions registered extension producer acquire stateTransport stateBindings unique extend runtimeOf in
theorem preserving_heads_with_receipts
    (R : HeaderReceiptFamily)
    (headerPrefix : CallableIndexedOwnedHeaderReceiptOperations.PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence guard validity budget R)
    (headerFault : CallableIndexedOwnedHeaderReceiptOperations.FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope id expected type code recipe
  cases recipe with
  | whileLoop found form conditionFound conditionType conditionTree bodyTree typed child =>
    intro size bounded valid
    exact (CallableIndexedOwnedAdmittedWhileBounds.preserves_bounded_for bridge guard functions evidence stateTransport validity budget
      (meaning context valid) found form conditionFound conditionTree typed unique
      (fun childSize less => child childSize (Nat.le_of_lt less))) size bounded valid
  | forLoop found form child =>
    exact CallableIndexedOwnedAdmittedForHeadBounds.header_preserves_with_receipt
      (unique := unique) bridge functions evidence guard validity budget R headerPrefix headerFault found form child
  | @matchWith node resolution scrutineeNode _expected _type _code selfReason originalControl caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalog patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded valid parentFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
      environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
    have parentTyped : ProtectedStateImperativeTypedSourceSites.Head source context id := by
      obtain ⟨mode, rest, _syntax, typed⟩ := parentFacts
      exact ProtectedStateImperativeTypedSourceSites.head typed
    obtain ⟨lowered, certified, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
    refine CallableIndexedOwnedAdmittedMatchBounds.preserves_bounded_for (expected := expected) (faults := faults) (administrative := administrative)
      bridge onError allocator functions definitions registered extension evidence restricted
      (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique validity
      (CompatibleMatchRuntimeSelection.LiteralRows _) patternContext.signatures
      (fun numeric selected => ?_) (CompatibleMatchRuntimeSelection.of_certificate restricted)
      (fun extended valid => RecursiveNamedImperativeFor.ContextTransport.binders validity extend valid extended)
      catalog found form scrutineeFound (fun _ singleton => singleton.2.2) guard producer stateBindings acquire
      budget size bounded ?_ ?_ ?_ valid
      parentTyped environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
    · obtain ⟨implementation, selected⟩ := selected
      exact selected.proves patternContext.ledger (runtimeOf context valid).runtime
    · intro valid childSize less actualScope actualId actualCode singleton node found sourceTyped mapping world administrativeContext inputEnvironment canonical actual actualContext before store ξ outcome after operandEnvs heaps locals agrees typed state admission trace
      rcases singleton with ⟨rfl, rfl, rfl⟩
      exact meaning context valid childSize less certified found sourceTyped (mapping := mapping) (world := world) (administrativeContext := administrativeContext) (environment := inputEnvironment) (canonical := canonical) (actual := actual) (actualContext := actualContext) (before := before) (store := store) (ξ := ξ) operandEnvs heaps locals agrees typed state admission trace
    · intro control sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        armContext staticFinal facts extended bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before after store ξ contextLocation native outcome finalContext
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := GenericMatchChildren.selected_arm_ids bodySelected
      rw [sameScope] at scopeIds
      cases bodySelected with
      | arm binders allocated certified =>
        have selectedContext := GenericMatchChildren.ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended
        exact child ⟨_, statements, body⟩ certified armContext selectedContext childSize (Nat.le_of_lt less) valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace
    · intro control sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        staticFinal facts bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before after store ξ contextLocation native outcome finalContext
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := (GenericMatchChildren.selected_default_ids bodySelected).trans sameScope
      cases bodySelected with
      | default certified =>
        have selectedContext : GenericMatchChildren.ScopedContextFor source context
            (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody ⟨_, statements, body⟩ context :=
          .default selected.defaultBody_eq scopeIds
        exact child ⟨_, statements, body⟩ certified context selectedContext childSize (Nat.le_of_lt less) valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend runtimeOf in
theorem preserving_heads
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact preserving_heads_with_receipts bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_PrefixAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_FaultAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    meaning

include definitions registered extension producer acquire stateTransport stateBindings unique extend runtimeOf in
theorem reflecting_heads_with_receipts
    (R : HeaderReceiptFamily)
    (headerReflection : CallableIndexedOwnedHeaderReceiptOperations.ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope id expected type code recipe
  cases recipe with
  | whileLoop found form conditionFound conditionType conditionTree bodyTree typed child =>
    intro size bounded valid
    exact (CallableIndexedOwnedAdmittedWhileBounds.reflects_bounded_from_tree_for bridge guard functions evidence stateTransport validity budget
      (reflection context valid) found form conditionFound conditionTree typed unique
      (fun childSize less => child childSize less) bodyTree) size (Nat.le_of_lt bounded) valid
  | forLoop found form child =>
    exact CallableIndexedOwnedAdmittedForHeadBounds.header_reflects_with_receipt
      (unique := unique) bridge functions evidence guard validity budget R headerReflection found form child
  | @matchWith node resolution scrutineeNode _expected _type _code selfReason originalControl caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalog patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded valid parentFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
    have parentTyped : ProtectedStateImperativeTypedSourceSites.Head source context id := by
      obtain ⟨mode, rest, _syntax, typed⟩ := parentFacts
      exact ProtectedStateImperativeTypedSourceSites.head typed
    obtain ⟨lowered, certified, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
    refine CallableIndexedOwnedAdmittedMatchBounds.reflects_bounded_for (expected := expected) (faults := faults) (administrative := administrative)
      bridge onError allocator functions definitions registered extension evidence restricted
      (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique validity
      (CompatibleMatchRuntimeSelection.LiteralRows _) patternContext.signatures
      (fun numeric selected => ?_) (CompatibleMatchRuntimeSelection.of_certificate restricted)
      (fun extended valid => RecursiveNamedImperativeFor.ContextTransport.binders validity extend valid extended)
      catalog found form scrutineeFound (fun _ singleton => singleton.2.2) guard producer stateBindings acquire
      budget size (Nat.le_of_lt bounded) ?_ ?_ ?_ valid
      parentTyped environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
    · obtain ⟨implementation, selected⟩ := selected
      exact selected.proves patternContext.ledger (runtimeOf context valid).runtime
    · intro valid childSize less actualScope actualId actualCode singleton node found sourceTyped mapping world administrativeContext inputEnvironment canonical actual actualContext before store ξ value finalStore operandEnvs heaps locals agrees typed state admission trace
      rcases singleton with ⟨rfl, rfl, rfl⟩
      exact reflection context valid childSize less certified found sourceTyped (mapping := mapping) (world := world) (administrativeContext := administrativeContext) (environment := inputEnvironment) (canonical := canonical) (actual := actual) (actualContext := actualContext) (before := before) (store := store) (ξ := ξ) operandEnvs heaps locals agrees typed state admission trace
    · intro control sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        armContext staticFinal facts extended bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := GenericMatchChildren.selected_arm_ids bodySelected
      rw [sameScope] at scopeIds
      cases bodySelected with
      | arm binders allocated certified =>
        have selectedContext := GenericMatchChildren.ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended
        exact child ⟨_, statements, body⟩ certified armContext selectedContext childSize less valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace
    · intro control sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        staticFinal facts bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := (GenericMatchChildren.selected_default_ids bodySelected).trans sameScope
      cases bodySelected with
      | default certified =>
        have selectedContext : GenericMatchChildren.ScopedContextFor source context
            (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody ⟨_, statements, body⟩ context :=
          .default selected.defaultBody_eq scopeIds
        exact child ⟨_, statements, body⟩ certified context selectedContext childSize less valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend runtimeOf in
theorem reflecting_heads (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact reflecting_heads_with_receipts bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_ReflectsAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy functionTypes reflection)
    reflection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
end
