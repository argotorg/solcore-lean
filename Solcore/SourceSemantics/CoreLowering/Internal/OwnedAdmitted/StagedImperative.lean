import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedMatches
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection

/-!
# Admitted staged profile: imperative statements

Scoped imperative flow, lexical preservation, positions and footers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
/-! The actual function footer consumes lexical flow without changing its
heap, returned value, or nested failure. Only an accepted unit fallthrough
uses the original unit fallback. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedAdmittedStagedLexicalFlow (Represents result)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CallableIndexedOwnedAdmittedStagedTerminalBody.code type (flow.rename ξ) escaped
        ((fallback type fellThrough).rename ξ) := by
  simpa only [CompatibleStatements.finish, CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
    (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename type flow escaped (fallback type fellThrough) ξ)

/-- A represented completed flow selects the same literal finish branch. -/
theorem evaluates {compiled : SourceCoreUnifiedCompilation.Compiled}
    {receiving : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty} {type : Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.BodyOutcome}
    {value : Value} {actual : Environment} {before after : Store} {flow : Expr}
    (represented : Represents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world raw type faults outcome value)
    (evaluated : Evaluates actual before flow value after)
    (fellThrough escaped : Word) (ξ : Renaming) :
    ∃ native, Evaluates actual before
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code type flow escaped ((fallback type fellThrough).rename ξ))
        native after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        mapping world raw type faults (result outcome) native := by
  cases represented with
  | returned payload =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.returned payload) evaluated escaped
  | fault matched =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.fault matched) evaluated escaped
  | fallthrough environment rawUnit coreUnit =>
      subst raw
      subst type
      refine ⟨.inRight .word .unit, ?_, .value .unit⟩
      have fallbackEq : (fallback .unit fellThrough).rename ξ = .inRight .word .unit := by
        simp [fallback, LanguageResult.success, Expr.rename]
      rw [fallbackEq]
      exact LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated)
        (by simpa [Expr.weakenAt] using
          (show Evaluates (.unit :: .inLeft .unit .unit :: actual) after
            (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit))

theorem outcome_eq {type : TypeSystem.Ty} {body : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome}
    (matched : Staging.Recursive.BodyResult type body outcome) : outcome = result body := by
  cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
/-! The same compiler tree contains statement sequences and for initializer
prefixes. Each position carries its original Source typing and its own trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

def InitializerTyping (source : TypedSource) (context : SourceSemantics.Context)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) : Prop :=
  ∃ control loopContext postContext bodyFinal bodyFacts,
    ForItemsHaveType source control context items loopContext ∧
    ExpressionHasType source loopContext test .bool ∧
    StatementsHaveType source control.enterLoop loopContext statements bodyFinal bodyFacts ∧
    ForItemsHaveType source control.enterLoop loopContext post postContext

def PositionTyping (source : TypedSource) (context : SourceSemantics.Context) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => ProtectedStateImperativeTypedSourceSites.Statements source context statements
  | .initializers items test post statements => InitializerTyping source context items test post statements

namespace InitializerTyping
variable {source : TypedSource} {context nextContext : SourceSemantics.Context}
  {test : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {rest : List ForItemForm}

theorem nil (typed : InitializerTyping source context [] test post statements) :
    ∃ control, ExpressionHasType source context test .bool ∧
      ProtectedStateImperativeTypedSourceSites.Statements source context statements ∧
      CallableIndexedOwnedPreparedStagedForItemsTyping.Facts source control context post := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial
  exact ⟨control.enterLoop, condition, ⟨control.enterLoop, bodyFinal, bodyFacts, body⟩, postContext, post⟩

theorem absent {binder : TypedBinder}
    (typed : InitializerTyping source context (.letDecl binder none :: rest) test post statements)
    (extended : BinderExtends source.owner context binder nextContext) :
    InitializerTyping source nextContext rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | letUninitialized _ _ actual =>
      cases Dynamic.BinderExtends.functional extended actual
      exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩

theorem initialized {binder : TypedBinder} {expression : ExpressionId}
    (typed : InitializerTyping source context (.letDecl binder (some expression) :: rest) test post statements)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext) :
    InitializerTyping source nextContext rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | letInitialized _ _ _ actual =>
      cases Dynamic.BinderExtends.functional extended actual
      exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩
    | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim

theorem expression {expression : ExpressionId}
    (typed : InitializerTyping source context (.expression expression :: rest) test post statements) :
    InitializerTyping source context rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head
    exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩

theorem assignment {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typed : InitializerTyping source context (.assignValue assignment operator rhs :: rest) test post statements) :
    SourceAssignmentHasType source context assignment operator rhs ∧
    InitializerTyping source context rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | assignValue actual => exact ⟨actual, control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩
theorem bitNot {assignment : AssignmentResolution}
    (typed : InitializerTyping source context (.assignBitNot assignment :: rest) test post statements) :
    SourceBitNotAssignmentValid source context assignment ∧
    InitializerTyping source context rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | assignBitNot actual => exact ⟨actual, control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩
end InitializerTyping

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

theorem represents_restore {mapping world expected type outcome value environment}
    (related : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world false expected type faults outcome value) :
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world false expected type faults (outcome.restore environment) value := by
  cases related with
  | fallthrough _ allowed => exact .fallthrough _ allowed
  | returned payload => exact .returned payload
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment
  | fault matched => exact .fault matched

theorem post_restore {context expected outcome environment index} {reached : callerProtocol.State index}
    (post : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post bridge context expected outcome reached) :
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post bridge context expected (outcome.restore environment) reached := by
  cases outcome <;> exact post

def Reflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowReflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode statements expected type code budget
  | .initializers items test post statements => CallableIndexedOwnedAdmittedStagedForHeadContracts.Reflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type code budget

def Preserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowPreserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode statements expected type code budget
  | .initializers items test post statements => CallableIndexedOwnedAdmittedStagedForHeadContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type code budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
/-! Scoped compiler statements include conditionals, finite while loops, bare plain assignment,
lexical allocation, discard and return. Strict child bounds run the original recursive
Source relation; writes target the actual heap reached by the RHS. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape PositionShape)
open CallableIndexedOwnedAdmittedStagedImperativePositions (PositionTyping InitializerTyping)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open GenericImperativeMatch (Tree)
open TypedLexicalControl (sequence_rename)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

theorem fault_post {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    {expected : TypeSystem.Ty} {failure : Staging.Recursive.Failure}
    (reached : callerProtocol.State index)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached)) :
    PostAdmission bridge context expected (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨stable, by intro value same; cases same⟩
  | stage origin call reason => exact stable

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge bindings definitions registered producer acquire transport extension functionTypes faithful observations in
/-- Native completion determines the actual ordered lexical Source trace,
including the distinct context after successful allocation and initializer
faults before allocation. The returned caller state retains the entire heap. -/
theorem reflects_position {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (graph : OccurrenceGraphWellFormed invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions callerProtocol invocation.source invalidProjection missingDefault receiving
      (fun reason token => faults (.semantic reason) token))
    (shape : PositionShape invocation.source position)
    (sourceTyped : PositionTyping invocation.source context position)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    CallableIndexedOwnedAdmittedStagedImperativePositions.Reflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope position expected type code budget := by
  revert shape sourceTyped projection
  induction catalogSites with
  | @body context scope mode statements expected type code syntaxTree body =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      exact CallableIndexedOwnedAdmittedStagedScopedLexicalFlow.reflects bridge bindings functions definitions registered producer.toOrdinary condition acquire children
        body shape projection within environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted completed
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.tail_of_let found form
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl graph.nodeOccurrencesUnique sourceTyped found form extended) projection (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .letUninitialized (lookupStatement?_sound found) form mono extended .append trace,
        represented, finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename] at completed
      obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := completed.bind_computation
      obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented,
          middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
        children context initialSize (Nat.lt_of_lt_of_le initialSmaller within) certified initialFound typed
          environments heaps locals agrees actualTyped initial admitted initialEval
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact ⟨Staging.Recursive.Size.stepSize [initialSourceSize], context, _, middle, middleMap, middleWorld,
            .letFault (lookupStatement?_sound found) form mono initialTrace, .fault matched,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
              nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl graph.nodeOccurrencesUnique sourceTyped found form extended) projection (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append trace,
            related, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard] at completed
      obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
          middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
        children context childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted childEvaluation
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
            .expressionFault (lookupStatement?_sound found) form childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.discard graph.nodeOccurrencesUnique sourceTyped found form) projection (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          have combined : Staging.Recursive.Size.StatementsIn program stages mode
              (Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize]) invocation context environment before
              (id :: rest) finalContext outcome after := by
            cases semi with
            | true => exact .discard (lookupStatement?_sound found) form childTrace tailTrace
            | false =>
                have falseMode : mode = false := continuing.resolve_left (by decide)
                cases falseMode
                exact .discardValue (lookupStatement?_sound found) form childTrace tailTrace
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
            combined, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, tailShape⟩ := shape.assignment_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      ·
        have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
          head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
          budget typedChildren (PreparedAssignmentReachedDiagnostics.operands headErrors semantic) completed within
        cases result with
        | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignBareFault (lookupStatement?_sound found) form snapshot trace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignBareOperands (lookupStatement?_sound found) form snapshot trace currentRead rootType initialized path invalid,
              .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected)
              (failure := .semantic (.invalidAssignmentOperands operator)) reached stable
        | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := ProtectedStateImperativeStatementSuffixTyping.assignment graph.nodeOccurrencesUnique sourceTyped found form
            obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih tailShape tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
              .assignBare (lookupStatement?_sound found) form snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
      ·
        have result := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
          head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
          budget typedChildren functionTypes
            (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial) completed within
        cases result with
        | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignProjectedKeysFault (lookupStatement?_sound found) form bare ready keyTrace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignProjectedGetterFault (lookupStatement?_sound found) form bare keyTrace failed, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
        | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
              .assignProjectedRhsFault (lookupStatement?_sound found) form bare keyTrace snapshot childTrace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
              .assignProjectedWriteFault (lookupStatement?_sound found) form bare keyTrace snapshot childTrace failed, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
        | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := ProtectedStateImperativeStatementSuffixTyping.assignment graph.nodeOccurrencesUnique sourceTyped found form
            obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih tailShape tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
              .assignProjected (lookupStatement?_sound found) form bare keyTrace snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨innerShape, restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner graph.nodeOccurrencesUnique sourceTyped found form
      have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.reflects bridge functions condition
        (innerIH innerShape innerTyped projection)
        found form (.inl (remainingIH restShape restTyped projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenIH elseIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.reflects bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form) projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.reflects bridge functions condition
        (ih innerShape innerTyped projection)
        found form (.inr ⟨exactUnique, stops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.reflects bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        found form (.inr ⟨exactUnique, thenStops, elseStops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @whileLoop context scope mode id node conditionId conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopBodyErrors remainingErrors loopIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨loopShape, restShape⟩ := shape.loop found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children graph.nodeOccurrencesUnique sourceTyped found form).2
      have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedWhileSequences.reflects bridge functions condition transport
        (children _) conditionFound conditionType typed certified nativeTyped
        (loopIH loopShape loopTyped projection)
        found form (remainingIH restShape restTyped projection) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren remaining catalog patternContext childErrors remainingErrors matchIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            ReflectsAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchReflects
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.reflects (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.reflects bridge functions condition
          selectedMeaning found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form) projection)) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren stops issued catalog patternContext childErrors matchIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            ReflectsAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchReflects
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.reflects (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.reflects bridge functions condition
          selectedMeaning found form (.inr ⟨exactUnique, stops⟩) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @breaking context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.breaking_evaluates _ actual store)
      exact ⟨_, _, .breaking environment, before, mapping, world,
        .breaking (lookupStatement?_sound found) form, .breaking environment, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted⟩
  | @continuing context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.continuing_evaluates _ actual store)
      exact ⟨_, _, .continuing environment, before, mapping, world,
        .continuing (lookupStatement?_sound found) form, .continuing environment, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted⟩
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, bare, tailShape⟩ := shape.bitNot_tail found form head.bare
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have result := CallableIndexedOwnedAdmittedStagedBareBitNotHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions transport
        head environments heaps locals agrees actualTyped initial admitted assignmentTyped headErrors completed
      cases result with
      | fault trace same matched finalHeaps maps worlds preservation reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [], context, _, _, _, _,
            .bitNotBareFault (lookupStatement?_sound found) form head.bare trace, .fault (semantic _ _ matched),
            finalHeaps, maps, worlds, preservation, .refl _, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := ProtectedStateImperativeStatementSuffixTyping.bitNot graph.nodeOccurrencesUnique sourceTyped found form
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .bitNotBare (lookupStatement?_sound found) form snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @bitNotProjected context scope mode id node assignment rest expected type body found form head remaining remainingErrors headSite ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, tailShape⟩ := shape.unary_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have projected : assignment.target.projections ≠ [] := by
        cases headSite with
        | projected _ _ nonempty _ => exact nonempty
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with
        | intro typed _ => exact typed
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.reflects_bounded
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
        head projected environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
        budget typedChildren functionTypes
        (PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment) headSite assignmentDiagnostics targetTyped initial)
        completed within
      cases result with
      | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
            .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keyTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge reached stable
      | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
            .bitNotProjectedGetterFault (lookupStatement?_sound found) form projected keyTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success keyTrace snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := ProtectedStateImperativeStatementSuffixTyping.bitNot graph.nodeOccurrencesUnique sourceTyped found form
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .bitNotProjected (lookupStatement?_sound found) form projected keyTrace snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @forLoop context scope mode id node items test post statements rest expected type initialCode body found form initialTree remaining initialErrors remainingErrors initialIH remainingIH =>
      intro shape sourceTyped projection
      obtain ⟨initialShape, postShape, loopShape, restShape⟩ := shape.for_children found form
      have initialTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.children graph.nodeOccurrencesUnique sourceTyped found form
      have tailTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      intro size
      exact CallableIndexedOwnedAdmittedStagedForSequences.reflects (size := size) bridge functions condition
        (initialIH ⟨initialShape, postShape, loopShape⟩ initialTyped projection) found form
        (remainingIH restShape tailTyped projection)
  | @initializersDone context scope test node post statements expected type testCode bodyCode postCode selfReason found nodeType certified bodyTree postTree nativeTyped bodyErrors postErrors bodyIH =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨control, _testTyped, bodyTyped, postTyped⟩ := InitializerTyping.nil sourceTyped
      obtain ⟨typedNode, typedFound, typed, generated⟩ := certified
      cases Option.some.inj (found.symm.trans typedFound)
      have postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Reflects
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope post expected type postCode budget :=
        CallableIndexedOwnedAdmittedStagedForHeaderReflection.reflects_at bridge bindings transport functions functionTypes faithful observations extension
          definitions registered producer condition acquire assignmentDiagnostics children graph.nodeOccurrencesUnique postTree postErrors semantic shape.2.1 postTyped
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, preserved, metadata, reached, related, resultPost⟩ :=
        CallableIndexedOwnedAdmittedStagedForHeads.reflects bridge functions condition transport
          (children _) found nodeType typed generated nativeTyped (bodyIH shape.2.2 bodyTyped projection) postCorrect
          within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [], sourceSize], outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps, worlds, preserved, metadata, reached, related, resultPost⟩
      simpa only [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore trace] using
        (CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop Staging.Recursive.Size.ForItems.empty trace)
  | @initializerUninitialized context nextContext scope binder rest body payload test post statements expected type mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.let_tail
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih ⟨tailShape, shape.2⟩ (InitializerTyping.absent sourceTyped extended) projection (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome.restore environment, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_absent mono extended .append trace,
        (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions represented), finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest test post statements expected type mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.let_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename] at completed
      obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := completed.bind_computation
      obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented,
          middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
        children context initialSize (Nat.lt_of_lt_of_le initialSmaller within) certified initialFound typed
          environments heaps locals agrees actualTyped initial admitted initialEval
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [initialSourceSize]], _, middle, middleMap, middleWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono initialTrace, .fault matched,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
              nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.initialized sourceTyped mono extended) projection (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], outcome.restore environment, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_initialized mono extended initialTrace .append trace,
            (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions related), finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @initializerDiscard context scope expression expressionNode rest lowered body test post statements expected type expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.discard_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard] at completed
      obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
          middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
        children context childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted childEvaluation
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [sourceSize]], _, middle, middleMap, middleWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.expression sourceTyped) projection (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], outcome, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_expression childTrace tailTrace, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @initializerAssign context scope assignment operator rhs rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, tailShape⟩ := shape.1.assignment_tail
      have assignmentTyped := (InitializerTyping.assignment sourceTyped).1
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      ·
        have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
          head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
          budget typedChildren (PreparedAssignmentReachedDiagnostics.operands headErrors semantic) completed within
        cases result with
        | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot trace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_operands snapshot trace currentRead rootType initialized path invalid,
              .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected)
              (failure := .semantic (.invalidAssignmentOperands operator)) reached stable
        | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := (InitializerTyping.assignment sourceTyped).2
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih ⟨tailShape, shape.2⟩ tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_assignment snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
      ·
        have result := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
          head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
          budget typedChildren functionTypes
            (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial) completed within
        cases result with
        | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault bare ready keyTrace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault bare keyTrace failed, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
        | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault bare keyTrace snapshot childTrace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault bare keyTrace snapshot childTrace failed, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
        | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := (InitializerTyping.assignment sourceTyped).2
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih ⟨tailShape, shape.2⟩ tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], outcome, after, finalMap, finalWorld,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment bare keyTrace snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @initializerBitNot context scope assignment rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, bare, tailShape⟩ := shape.1.bitNot_tail head.bare
      have assignmentTyped := (InitializerTyping.bitNot sourceTyped).1
      have result := CallableIndexedOwnedAdmittedStagedBareBitNotHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions transport
        head environments heaps locals agrees actualTyped initial admitted assignmentTyped headErrors completed
      cases result with
      | fault trace same matched finalHeaps maps worlds preservation reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []], _, _, _, _,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.bitNot_fault head.bare trace, .fault (semantic _ _ matched),
            finalHeaps, maps, worlds, preservation, .refl _, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (InitializerTyping.bitNot sourceTyped).2
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_bitNot snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @initializerBitNotProjected context scope assignment rest body test post statements expected type head remaining remainingErrors headSite ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨_, tailShape⟩ := shape.1.unary_tail
      have assignmentTyped := (InitializerTyping.bitNot sourceTyped).1
      have projected : assignment.target.projections ≠ [] := by
        cases headSite with
        | projected _ _ nonempty _ => exact nonempty
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with
        | intro typed _ => exact typed
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.reflects_bounded
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
        head projected environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
        budget typedChildren functionTypes
        (PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment) headSite assignmentDiagnostics targetTyped initial)
        completed within
      cases result with
      | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready keyTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge reached stable
      | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_getter_fault projected keyTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success keyTrace snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (InitializerTyping.bitNot sourceTyped).2
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_bitNot projected keyTrace snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩

include bridge bindings definitions registered producer acquire transport extension functionTypes faithful observations in
theorem reflects_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (graph : OccurrenceGraphWellFormed invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions callerProtocol invocation.source invalidProjection missingDefault receiving
      (fun reason token => faults (.semantic reason) token))
    {mode : Bool} {statements : List StatementId}
    (atStatements : position = .statements mode statements)
    (shape : Shape invocation.source mode statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases atStatements
  exact reflects_position bridge bindings transport functions functionTypes faithful observations extension definitions registered producer condition acquire
    children graph tree catalogSites semantic assignmentDiagnostics shape sourceTyped projection within
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation
/-! Scoped lexical statements retain their actual Source contexts, branch mode,
and marked native allocations. Child bounds are strict numeric hypotheses; the
compiler tree contains only typing, syntax and accepted allocator receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape)
open GenericLexicalStatements (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge bindings definitions registered producer acquire in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope mode statements expected type code)
    (shape : Shape invocation.source mode statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  induction tree generalizing size mapping world administrative actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @nil context scope mode expected type allowed =>
      cases trace
      exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates type actual store,
        .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @returnUnit context scope mode id node rest found form =>
      obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace
      refine ⟨_, store, mapping, world, LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store),
        .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
      exact ⟨admitted.rows, by intro source same; cases same; exact ⟨.unit, admitted.heap⟩⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
        .returning rest (lookupStatement?_sound found) form
      obtain ⟨childSize, childOutcome, sameSize, contextEq, outcomeEq, childTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
      subst finalContext
      subst outcome
      obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.preserves bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) childTrace
          (by simpa only [sameSize] using within)
      cases valueType
      cases represented with
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
        .tail (lookupStatement?_sound found) form
      obtain ⟨childSize, childOutcome, sameSize, contextEq, outcomeEq, childTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
      subst finalContext
      subst outcome
      obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.preserves bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) childTrace
          (by simpa only [sameSize] using within)
      cases valueType
      cases represented with
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent unique found form extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, represented, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with
        ⟨initialSize, failure, sameSize, contextEq, outcomeEq, initialTrace⟩ |
        ⟨initialSize, tailSize, sourceValue, location, middle, bound, sameSize, initialTrace, allocated, remainingTrace⟩
      · subst finalContext
        subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
            obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
                nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
              CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
                mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
                reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) initialPost.at_value.2
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
              ih tailShape projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), related, finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
      obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique
          (lookupStatement?_sound found) form continuing trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
            middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
                finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
              ih tailShape projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | block found form inner remaining innerIH remainingIH =>
      obtain ⟨innerShape, restShape⟩ := shape.block_children found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (fun {size} bounded => innerIH (size := size) (administrative := administrative) innerShape projection bounded)
        unique found form (.inl (fun {size} bounded => remainingIH (size := size) (administrative := administrative) restShape projection bounded)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
      obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.preserves bridge functions condition
        (children _) conditionFound conditionType typed certified
        (fun {size} bounded => thenIH (size := size) (administrative := administrative) leftShape projection bounded) (fun {size} bounded => elseIH (size := size) (administrative := administrative) rightShape projection bounded)
        unique found form (.inl (fun {size} bounded => remainingIH (size := size) (administrative := administrative) restShape projection bounded)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | terminalBlock exactUnique found form inner stops issued ih =>
      obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (fun {size} bounded => ih (size := size) (administrative := administrative) innerShape projection bounded)
        unique found form (.inr stops) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
      obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.preserves bridge functions condition
        (children _) conditionFound conditionType typed certified
        (fun {size} bounded => thenIH (size := size) (administrative := administrative) leftShape projection bounded) (fun {size} bounded => elseIH (size := size) (administrative := administrative) rightShape projection bounded)
        unique found form (.inr ⟨thenStops, elseStops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePreservation
/-! Straight-line compiler statements include bare plain assignment, lexical
allocation, discard and return. Strict child bounds run the original recursive
Source relation; writes target the actual heap reached by the RHS. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBareAssignmentTree (Shape)
open GenericImperativeMatch (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedLexicalFlow (result Represents restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge bindings definitions registered producer acquire transport extension in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {mode : Bool} {statements : List StatementId}
    (atStatements : position = .statements mode statements)
    (tailMode : mode = true) (shape : Shape invocation.source statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program stages size invocation context environment before
      statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context expected (result outcome) reached := by
  induction tree generalizing mode statements size mapping world actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @body context scope mode statements expected type code syntaxTree body =>
      cases atStatements
      exact CallableIndexedOwnedAdmittedStagedLexicalPreservation.preserves bridge bindings functions definitions registered producer condition acquire children unique
        body tailMode (shape.lexical_of_syntax syntaxTree tailMode) projection within environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted trace
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
      cases atStatements
      have tailShape := shape.tail_of_let found form
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalSourceInversion.absent unique found form extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih rfl tailMode tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, represented, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
      cases atStatements
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedLexicalSourceInversion.initialized unique found form mono extended trace with
        ⟨initialSize, failure, sameSize, contextEq, outcomeEq, initialTrace⟩ |
        ⟨initialSize, tailSize, sourceValue, location, middle, bound, sameSize, initialTrace, allocated, remainingTrace⟩
      · subst finalContext
        subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
            obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
                nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
              CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
                mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
                reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) initialPost.at_value.2
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
              ih rfl tailMode tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), related, finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
      cases atStatements
      cases tailMode
      obtain ⟨rfl, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail unique
          (lookupStatement?_sound found) form trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
            middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
                finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
              ih rfl rfl tailShape (ProtectedStateImperativeStatementSuffixTyping.discard unique sourceTyped found form) projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
      cases atStatements
      obtain ⟨rfl, bare, tailShape⟩ := shape.assign_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        functions extension head bare environments heaps locals agrees
      rcases CallableIndexedOwnedPreparedStagedBareAssignmentSourceInversion.child_and_tail unique found form snapshot trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, contextEq, outcomeEq, childTrace,
          currentRead, rootType, initialized, path, invalid⟩ |
        ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (typedChildren childSize childStrict) childTrace body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
          preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
      · exact (AssignmentOperandDiagnostics.invalid_not_equal invalid rfl).elim
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
            count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (typedChildren childSize childStrict) snapshot childTrace write
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih rfl tailMode tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form)
            projection tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted remainingTrace
        have native := (continuation body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using evaluated)
        exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
          maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
          last, callerProtocol.trans related lastRelated, post⟩
  | block found form inner remaining innerIH remainingIH => cases atStatements; exact False.elim (shape.not_block found form)
  | ifThen found form _ _ _ _ _ _ _ _ _ => cases atStatements; exact False.elim (shape.not_if found form)
  | terminalBlock _ found form _ _ _ _ => cases atStatements; exact False.elim (shape.not_block found form)
  | terminalIf _ found form _ _ _ _ _ _ _ _ _ _ => cases atStatements; exact False.elim (shape.not_if found form)
  | breaking found form | continuing found form | whileLoop found form _ _ _ _ _ _ _ _
  | bitNot found form _ _ _ | bitNotProjected found form _ _ _ | forLoop found form _ _ _ _
  | matchWith found form _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | terminalMatch _ found form _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      cases atStatements
      have impossible := shape.head_allowed found
      simp only [form, CallableIndexedOwnedPreparedStagedBareAssignmentTree.allowedForm, Bool.false_eq_true] at impossible
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot | initializerBitNotProjected =>
      cases atStatements

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePreservation
end
