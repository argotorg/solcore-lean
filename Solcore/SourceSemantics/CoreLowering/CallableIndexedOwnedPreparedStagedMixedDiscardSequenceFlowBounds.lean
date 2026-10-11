import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds

/-! Structural sequence composition over the actual accepted discard children.
Every tail runs at the reached Admission and the exact temporary binder. The
numeric Root family is an internal strict IH; the static tree stores no law.
Native reflection reconstructs independent Source grades and exact failures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt)

/-- Law-free original-source roots for each exact emitted child. The raw result
is the actual terminal root type; discard child types remain unrestricted. -/
inductive Tree (compiled : SourceCoreUnifiedCompilation.Compiled)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (semanticFaults : FunctionCalls.FaultRep)
    (result : Ty) (rawResult : TypeSystem.Ty) : List StatementId → Expr → Type where
  | terminal {expression statements child}
      (root : RootAt compiled context invocation scope expression child semanticFaults)
      (head : Head invocation expression statements)
      (sameType : child.type = result)
      (sameRaw : root.support.node.type = rawResult) :
      Tree compiled context invocation scope semanticFaults result rawResult statements
        (LocalLoop.returnValue result child.expression)
  | discard {id node expression rest first tailFlow}
      (root : RootAt compiled context invocation scope expression first semanticFaults)
      (contains : ContainsStatement invocation.source id node)
      (form : node.form = .expression expression true)
      (tail : Tree compiled context invocation scope semanticFaults result rawResult rest tailFlow) :
      Tree compiled context invocation scope semanticFaults result rawResult (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) first.expression tailFlow)

/-- The same receipt constructs the original statement tree. The supplied
factory issues actual original-source Roots for the literal used children;
raw typing, policy and original compiler authority remain fields of those Roots. -/
theorem Tree.of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow)
    (view : LambdaMetadataViews.MetadataView invocation.source source)
    (roots : ∀ expression child, receipt.Children expression child →
      RootAt compiled context invocation scope expression child semanticFaults) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal receipt generated =>
    intro roots
    have root := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head receipt view)
      receipt.sameType rfl⟩⟩
  | discard found form first firstGenerated tail generated ih =>
    intro roots
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used => roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard (roots _ _ (.inl ⟨rfl, rfl⟩))
      (lookupStatement?_sound (view.statement found)) form tailTree⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


section Flow
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {result : Ty} {rawResult : TypeSystem.Ty}
  {statements : List StatementId} {flow : Expr}

/-- Only genuine strict Root IHs are consumed. Structural tail recursion retains
its literal reached context, heap, Admission and native temporary binder. -/
theorem preserves_flow
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize) :
    ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
      {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
      {store : Store} {ξ : Renaming},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    Admission poolBridge context initial →
    ∀ {size : Nat}, size ≤ budget →
    ∀ {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
      {after : Dynamic.Heap},
    Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before statements finalContext bodyOutcome after →
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (flow.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld rawResult result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PostAdmission poolBridge context rawResult outcome reached := by
  induction tree with
  | terminal root head sameType sameRaw =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within finalContext bodyOutcome after trace
    cases sameType
    cases sameRaw
    have below := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
      profile root children within
    obtain ⟨childSize, outcome, sameSize, rfl, rfl, childTrace⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body root.support.unique head trace
    obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves poolBridge head
        ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed environments heaps locals agrees actualTyped
        initial admitted size below childTrace (by simpa only [sameSize] using Nat.le_refl size)
    exact ⟨rfl, outcome, rfl, value, finalStore, finalMap, finalWorld, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | discard root contains form tail ih =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within finalContext bodyOutcome after trace
    have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
      profile root children within
    rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail
        root.support.unique contains form trace with
      ⟨firstSize, failure, sameSize, rfl, rfl, firstTrace⟩ |
      ⟨firstSize, tailSize, sourceValue, middle, sameSize, firstTrace, tailTrace⟩
    · have firstStrict : firstSize < size := by
        rw [sameSize]
        exact Staging.Recursive.Size.child_lt_stepSize (by simp)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | fault matched =>
        refine ⟨rfl, .fault failure, rfl, _, finalStore, finalMap, finalWorld, ?_, .fault matched,
          finalHeaps, maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
        rw [LoopRenaming.discard]
        exact LocalSequence.discard_failure _ evaluated
    · have firstStrict : firstSize < size := by
        rw [sameSize]
        exact Staging.Recursive.Size.child_lt_stepSize (by simp)
      have tailWithin : tailSize ≤ budget := by
        apply Nat.le_trans _ within
        rw [sameSize]
        exact Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨rfl, outcome, sameOutcome, value, finalStore, finalMap, finalWorld, second,
            represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 tailWithin tailTrace
        refine ⟨rfl, outcome, sameOutcome, value, finalStore, finalMap, finalWorld, ?_, represented,
          finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
          firstMetadata.trans metadata, reached, firstRelated.trans related, post⟩
        rw [LoopRenaming.discard]
        rw [rename_prefix] at second
        exact LocalSequence.discard_success _ first second

/-- Each native bind inversion selects the actual executed children. Reflection
rebuilds every original discard, retaining independent Source grades and faults. -/
theorem reflects_flow
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize) :
    ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
      {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
      {store : Store} {ξ : Renaming},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    Admission poolBridge context initial →
    ∀ {size : Nat}, size ≤ budget → ∀ {value : Value} {finalStore : Store},
    EvaluationSize size actual store (flow.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld rawResult result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PostAdmission poolBridge context rawResult outcome reached := by
  induction tree with
  | terminal root head sameType sameRaw =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within value finalStore completed
    cases sameType
    cases sameRaw
    have below := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
      profile root children within
    exact CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects poolBridge head
      ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed environments heaps locals agrees actualTyped
      initial admitted size below completed (Nat.le_refl size)
  | @discard id node expression rest firstCode tailFlow root contains form tail ih =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within value finalStore completed
    have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
      profile root children within
    have original := completed
    rw [LoopRenaming.discard] at original
    change EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType result) (firstCode.expression.rename ξ)
        ((tailFlow.rename ξ).weakenAt 0)) value finalStore at original
    cases CallableIndirectCallBounds.bind_completed original (Nat.le_refl _) with
    | failed first strict =>
      obtain ⟨firstSize, outcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow _ strict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | fault matched =>
        exact ⟨_, .fault _, after, finalMap, finalWorld,
          .expressionFault contains form firstTrace, .fault matched, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
    | continued first remaining firstStrict remainingStrict =>
      have tailWithin := Nat.le_trans (Nat.le_of_lt remainingStrict) within
      obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow _ firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | @value sourceValue coreValue payload =>
        have shifted := remaining
        rw [← rename_prefix] at shifted
        obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees _)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 tailWithin shifted
        exact ⟨_, outcome, after, finalMap, finalWorld, .discard contains form firstTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans frame, firstMetadata.trans metadata, reached,
          firstRelated.trans related, post⟩
end Flow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
