import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeWhileComposition
import Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions

/-!
# Recursive named rows: imperative control

Bounds of imperative and lexical control, lexical trees and the catalog's body finish.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeControlBounds
/-! The existing control producers thread actual child post-witnesses through
five-way sequence and branch flow. Native continuations and Source grades are
unchanged; terminal paths retain the reached head witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (staticCondition : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include unique in
theorem block_preserves_at_with_state (_validity : SourceSemantics.Context → Prop)
    (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∀ child, child ≤ budget → ∀ {innerContext innerOutcome},
      ExecutesAt child false program context evidence source environment before statements innerContext innerOutcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (code.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type innerOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment innerContext after ∧
        Reached readiness context innerOutcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases trace with
  | control trace =>
    obtain ⟨rfl, child, innerContext, innerOutcome, rfl, executed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_value unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _, post⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (.control executed)
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      evaluated, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata, Reached.restore_control (protocol := protocol) (readiness := readiness) environment post⟩
  | fault failed =>
    obtain ⟨child, innerContext, failed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _, post⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (.fault failed)
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩


theorem block_reflects_at_with_state (_budget _size : Nat)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∃ sourceSize innerContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize false program context evidence source environment before statements innerContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment innerContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    ∃ sourceSize outcome after finalMap finalWorld,
      StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _, post⟩ := inner
  refine ⟨SourceExecutionSize.stepSize [sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
    ?_, restored environment outcome, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata, Reached.restore_control (protocol := protocol) (readiness := readiness) environment post⟩
  cases trace with
  | control trace => exact .control (.block (lookupStatement?_sound found) form trace)
  | fault failed => exact .fault (.block (lookupStatement?_sound found) form failed)


include unique in
theorem sequence_stopped_preserves_at_with_state (_validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (first : ∀ child, child ≤ budget → ∀ {outcome finalContext after},
      StatementOutcome program child context evidence source environment before id finalContext outcome after →
      finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (head.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (stops : ReachableStatementContinuations.StatementTerminates source id)
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context} {after : Dynamic.Heap}
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => cases stops headTrace.sound
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .breaking next, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .continuing next, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩



theorem sequence_stopped_reflects_at_with_state (_validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (first : ∀ child, child ≤ budget → ∀ {headValue middleStore},
      EvaluationSize child actual store (head.rename ξ) headValue middleStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
        Restored environment outcome ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome headValue ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after middleStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap middleStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, middleStore, canonical⟩)
    (stops : ReachableStatementContinuations.StatementTerminates source id)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before (id :: rest) finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata, post⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace.sound
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.breaking next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.continuing next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩



include unique in
include sites in
theorem block_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady trace
  exact block_preserves_at_with_state protocol functions program evidence unique validity budget size bounded found form initial (readiness := readiness)
    (fun child childBound {_ _} innerTrace => inner child childBound valid (sites.block sourceFacts found form) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady innerTrace) trace

include sites in
theorem block_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady evaluated
  exact block_reflects_at_with_state protocol functions program evidence budget size found form initial (readiness := readiness)
    (inner size bounded valid (sites.block sourceFacts found form) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady evaluated)

include unique in
include sites in
theorem sequence_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady trace
  have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (headTrace : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
      (tailTrace : ExecutesAt tailSize mode program middleContext evidence source next middle rest finalContext outcome after) (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment finalContext after ∧
        Reached readiness context outcome installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
    obtain ⟨rfl, restores, value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata, post⟩ :=
      first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.control headTrace)
    have same := restores next rfl
    subst next
    cases represented with
    | fallthrough _ =>
      obtain ⟨middleState, firstRelated, firstReady⟩ := post
      obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, lastPost⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid (sites.tail sourceFacts found (fun _ _ => notTail) headTrace.sound) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady tailTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical, ?_⟩
      · rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval
      · obtain ⟨final, lastRelated, finalReady⟩ := lastPost
        exact ⟨final, protocol.trans firstRelated lastRelated, finalReady⟩
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => exact go headTrace tailTrace headSmaller tailSmaller
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .breaking next, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .continuing next, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}


include sites in
theorem sequence_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady evaluated
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata, post⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts)
      environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady headEval
  cases represented with
  | fallthrough next =>
    obtain ⟨middleState, firstRelated, firstReady⟩ := post
    have same := restores next rfl
    subst next
    cases headTrace with | control headTrace =>
      obtain ⟨tailSize, tailSmaller, tailEval⟩ := evaluated.sequence_fallthrough headEval.sound
      obtain ⟨sourceTailSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, lastPost⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid (sites.tail sourceFacts found (fun _ _ => notTail) headTrace.sound)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
        (prepend (lookupStatement?_sound found) (fun _ _ => notTail) headTrace.sound tailTrace.sound)
      refine ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical, ?_⟩
      obtain ⟨final, lastRelated, finalReady⟩ := lastPost
      exact ⟨final, protocol.trans firstRelated lastRelated, finalReady⟩
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.breaking next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.continuing next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}


include sites in
theorem conditional_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionPreservesAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady trace
  have selected {conditionSize bodySize : Nat} {boolean : Bool} {middle : Dynamic.Heap} {innerContext : SourceSemantics.Context} {innerOutcome : Dynamic.ControlOutcome}
      (conditionTrace : SourceExecutionSize.ExpressionEvaluates program conditionSize context evidence source environment before condition (.bool boolean) middle)
      (branchTrace : ExecutesAt bodySize false program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext innerOutcome after) (conditionSmaller : conditionSize < size) (bodySmaller : bodySize < size) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.conditional type conditionCode thenCode elseCode).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type
          (Dynamic.restoreControl environment innerOutcome) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Reached readiness context (Dynamic.restoreControl environment innerOutcome) installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
    obtain ⟨_, middleStore, middleMap, middleWorld, conditionEval, represented, middleHeaps, maps, worlds, frame, metadata, post⟩ :=
      expressionPreserves conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨middleState, firstRelated, firstReady⟩ := post
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      have branchCorrect : PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
          bodySize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first | exact thenCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded)) | exact elseCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded))
      obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _, lastPost⟩ :=
        branchCorrect valid (sites.branch boolean sourceFacts found form) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady.1 branchTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, restore_rep represented environment, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, ?_⟩
      · rw [LoopRenaming.conditional]
        rw [GenericExpressionMeaning.rename_prefix] at branchEval
        cases boolean with
        | false => exact LocalControl.choose_false _ conditionEval branchEval
        | true => exact LocalControl.choose_true _ conditionEval branchEval
      · exact Reached.continue (protocol := protocol) (readiness := readiness) firstRelated
          (Reached.restore_control (protocol := protocol) (readiness := readiness) environment lastPost)
  obtain ⟨same, view⟩ := RecursiveNamedStatementSourceBounds.if_inv unique (lookupStatement?_sound found) form trace
  subst finalContext
  cases view with
  | conditionFault failed smaller =>
    obtain ⟨_, finalStore, finalMap, finalWorld, conditionEval, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.fault failed)
    cases represented with
    | fault matched =>
      refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, post⟩
      rw [LoopRenaming.conditional]
      exact LocalControl.choose_failure _ conditionEval
  | conditionType conditionTrace notBoolean runtimeType smaller =>
    obtain ⟨_, _, _, _, _, represented, _⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨_, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  | branch conditionTrace branchTrace conditionSmaller bodySmaller =>
    exact ⟨rfl, restored environment _, selected conditionTrace branchTrace conditionSmaller bodySmaller⟩


include sites in
theorem conditional_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionReflectsAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady evaluated
  rw [LoopRenaming.conditional] at evaluated
  obtain ⟨conditionSize, middleStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluated.bind_computation
  obtain ⟨sourceConditionSize, conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata, post⟩ :=
    expressionReflects conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
      environments heaps locals agrees actualTyped installed initialReady conditionEval
  cases represented with
  | fault matched =>
    cases conditionTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalControl.choose_failure _ conditionEval.sound)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (Dynamic.StatementExecutesOutcome.fault (Dynamic.StatementFaults.ifCondition (lookupStatement?_sound found) form failed.sound))
      exact ⟨sourceSize, _, middle, middleMap, middleWorld, trace,
        (by intro next impossible; cases impossible), .fault matched, middleHeaps, maps, worlds, frame, metadata, post⟩
  | value payload =>
    cases conditionTrace with
    | value conditionTrace =>
      obtain ⟨middleState, firstRelated, firstReady⟩ := post
      obtain ⟨boolean, sourceEq, coreEq⟩ := bool_fields payload
      subst sourceEq
      subst coreEq

      obtain ⟨branchSize, branchSmaller, branchEval⟩ :
          ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool boolean :: actual) middleStore
            ((if boolean then thenCode else elseCode).rename ξ |>.weakenAt 0) value finalStore := by
        cases boolean with
        | false => exact evaluated.choose_false conditionEval.sound
        | true => exact evaluated.choose_true conditionEval.sound
      have branchCorrect : ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
          branchSize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first
          | exact thenCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
          | exact elseCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
      obtain ⟨sourceBranchSize, innerContext, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _, lastPost⟩ :=
        branchCorrect valid (sites.branch boolean sourceFacts found form) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady.1
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (selected_intro program evidence found form conditionTrace.sound branchTrace.sound)
      refine ⟨sourceSize, Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        trace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata, ?_⟩
      exact Reached.continue (protocol := protocol) (readiness := readiness) firstRelated
        (Reached.restore_control (protocol := protocol) (readiness := readiness) environment lastPost)


include unique in
include sites in
theorem sequence_stopped_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    PreservesAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady trace
  exact sequence_stopped_preserves_at_with_state protocol functions program evidence unique validity budget size bounded found notTail environments locals initial (readiness := readiness)
    (fun child childBound {_ _ _} headTrace => first child childBound valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady headTrace) stops trace

include sites in
theorem sequence_stopped_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith protocol readiness staticCondition headFacts (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    ReflectsAtWith protocol readiness staticCondition facts (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady evaluated
  exact sequence_stopped_reflects_at_with_state protocol functions program evidence validity budget size bounded found notTail environments locals initial (readiness := readiness)
    (fun child childBound {_ _} headEval => first child childBound valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady headEval) stops evaluated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (staticCondition : Location → CallableIndexedHistory.NativeFrame → Prop)
abbrev PreservesAtWith := @ProtectedStateTransition.Lexical.Gated.PreservesAtFor
abbrev ReflectsAtWith := @ProtectedStateTransition.Lexical.Gated.ReflectsAtFor
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include unique in
theorem block_preserves_at_with_state (_validity : SourceSemantics.Context → Prop)
    (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∀ child, child ≤ budget → ∀ {innerContext innerOutcome},
      ExecutesAt child false program context evidence source environment before statements innerContext innerOutcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (code.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type innerOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment innerContext after ∧
        Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.block_preserves_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      _validity budget size bounded found form initial
      (fun child bound {_ _} trace => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := inner child bound trace
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩) trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem block_reflects_at_with_state (_budget _size : Nat)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∃ sourceSize innerContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize false program context evidence source environment before statements innerContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment innerContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    ∃ sourceSize outcome after finalMap finalWorld,
      StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := inner
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.block_reflects_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence)
      _budget _size found form initial
      ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

include unique in
theorem sequence_stopped_preserves_at_with_state (_validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (first : ∀ child, child ≤ budget → ∀ {outcome finalContext after},
      StatementOutcome program child context evidence source environment before id finalContext outcome after →
      finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (head.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (stops : ReachableStatementContinuations.StatementTerminates source id)
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context} {after : Dynamic.Heap}
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    WithReady.sequence_stopped_preserves_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      _validity budget size bounded found notTail environments locals initial
      (fun child bound {_ _ _} trace => by
        obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := first child bound trace
        exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩) stops trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

theorem sequence_stopped_reflects_at_with_state (_validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (first : ∀ child, child ≤ budget → ∀ {headValue middleStore},
      EvaluationSize child actual store (head.rename ξ) headValue middleStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
        Restored environment outcome ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome headValue ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after middleStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap middleStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Transition protocol initial ⟨scope, finalMap, finalWorld, after, middleStore, canonical⟩)
    (stops : ReachableStatementContinuations.StatementTerminates source id)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before (id :: rest) finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    WithReady.sequence_stopped_reflects_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence)
      _validity budget size bounded found notTail environments locals initial
      (fun child bound {_ _} evaluated => by
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := first child bound evaluated
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩) stops evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

include unique in
theorem block_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply WithReady.HeadPreservesAtWith.forget_true
  exact WithReady.block_preserves_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (unique := unique) (validity := validity) budget size bounded found form
    (fun child within => WithReady.PreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (inner child within))

theorem block_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply WithReady.HeadReflectsAtWith.forget_true
  exact WithReady.block_reflects_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (validity := validity) budget size bounded found form
    (fun child within => WithReady.ReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (inner child within))

include unique in
theorem sequence_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply WithReady.PreservesAtWith.forget_true
  exact WithReady.sequence_preserves_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (unique := unique) (validity := validity) budget size bounded found notTail
    (fun child within => WithReady.HeadPreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    (fun child within => WithReady.PreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (remaining child within))

theorem sequence_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply WithReady.ReflectsAtWith.forget_true
  exact WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (validity := validity) budget size bounded found notTail
    (fun child within => WithReady.HeadReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    (fun child within => WithReady.ReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (remaining child within))

theorem conditional_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply WithReady.HeadPreservesAtWith.forget_true
  exact WithReady.conditional_preserves_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (unique := unique) (validity := validity) budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true (protocol := protocol) (program := program) (evidence := evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context) (expressionPreserves child within context valid))
    found form conditionFound _conditionType conditionTree
    (fun child within => WithReady.PreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (thenCorrect child within))
    (fun child within => WithReady.PreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (elseCorrect child within))

theorem conditional_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply WithReady.HeadReflectsAtWith.forget_true
  exact WithReady.conditional_reflects_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (validity := validity) budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true (protocol := protocol) (program := program) (evidence := evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context) (expressionReflects child within context valid))
    found form conditionFound _conditionType conditionTree
    (fun child within => WithReady.ReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (thenCorrect child within))
    (fun child within => WithReady.ReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (elseCorrect child within))

include unique in
theorem sequence_stopped_preserves_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    PreservesAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply WithReady.PreservesAtWith.forget_true
  exact WithReady.sequence_stopped_preserves_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (unique := unique) (validity := validity) budget size bounded found notTail
    (fun child within => WithReady.HeadPreservesAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    stops

theorem sequence_stopped_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    ReflectsAtWith protocol staticCondition (validity := validity) (administrative := administrative) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply WithReady.ReflectsAtWith.forget_true
  exact WithReady.sequence_stopped_reflects_at_with (protocol := protocol) (staticCondition := staticCondition)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (validity := validity) budget size bounded found notTail
    (fun child within => WithReady.HeadReflectsAtWith.of_true (protocol := protocol) (condition := staticCondition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    stops
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Compatibility
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedStateTransition
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
theorem legacy_head_preserves {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : Control.HeadPreservesAtWith (administrative := administrative) (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    Stateful.HeadPreservesAtWith (administrative := administrative) (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial _condition trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_head_reflects {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : Control.HeadReflectsAtWith (administrative := administrative) (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    Stateful.HeadReflectsAtWith (administrative := administrative) (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial _condition evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

theorem legacy_expression_preserves {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults guarded) :
    ProtectedStateTransition.PreservesAt (ProtectedStateTransition.Lexical.legacyProtocol guarded)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_expression_reflects {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults guarded) :
    ProtectedStateTransition.ReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol guarded)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Only a legacy observer lifts through its proved administrative effects. -/
theorem legacy_preserves {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := guarded) (scope := scope) mode statements expected type code) :
    Lexical.Gated.PreservesAtFor (Lexical.legacyProtocol guarded) (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code :=
  Lexical.Gated.preserves_of_unguarded _ _ _ _ _
    (Lexical.legacy_preserves functions program evidence transport meaning)

/-- The original measured continuation remains the actual reflected grade. -/
theorem legacy_reflects {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := guarded) (scope := scope) mode statements expected type code) :
    Lexical.Gated.ReflectsAtFor (Lexical.legacyProtocol guarded) (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code :=
  Lexical.Gated.reflects_of_unguarded _ _ _ _ _
    (Lexical.legacy_reflects functions program evidence transport meaning)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Compatibility
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
/-! Lexical bodies embed into the five-way imperative contract without changing
an execution, heap, lexical context, caller entry or size. The only converted
field is the established three-way flow representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep)

variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {scope : Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {size : Nat}

theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.PreservesAtFor (validity := validity) functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
       (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

theorem preserves_at
    (correct : RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  exact preserves_at_for (functions := functions) (program := program) (evidence := evidence)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) correct

theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.ReflectsAtFor (validity := validity) functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
       (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

theorem reflects_at
    (correct : RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  exact reflects_at_for (functions := functions) (program := program) (evidence := evidence)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) correct

namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial gate trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped initial gate trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩

theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩

end Stateful

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds
/-! The existing block and sequence helpers consume only same-bound lexical
children. Original source cons witnesses and native bind/continuation inversion
select actual children; reflected source costs are constructed independently. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep prepend)
open TypedLexicalControl (Restored restored restore_rep LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLexicalContracts
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open RecursiveNamedCallBounds (ExpressionOutcome)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}


open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)

/- The shared block proof calls its child at this exact input. This avoids
requiring administrative transport in the legacy block API. -/
include unique in
theorem block_preserves_at_with_state_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (_validity : SourceSemantics.Context → Prop)
    (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∀ child, child ≤ budget → ∀ {innerContext innerOutcome},
      ExecutesAt child false program context evidence source environment before statements innerContext innerOutcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (code.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type innerOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment innerContext after ∧
        Reached readiness context innerOutcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before false statements type innerOutcome after value finalMap finalWorld finalStore)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.HeadOutcomePost headPost program context evidence source environment before id type outcome after value finalMap finalWorld finalStore := by
  cases trace with
  | control trace =>
    obtain ⟨rfl, child, innerContext, innerOutcome, rfl, executed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_value unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _, post, origin⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (.control executed)
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      evaluated, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata, Reached.restore_control (protocol := protocol) (readiness := readiness) environment post, NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin⟩
  | fault failed =>
    obtain ⟨child, innerContext, failed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _, post, origin⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (.fault failed)
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩

include unique in
theorem block_preserves_at_with_state (_validity : SourceSemantics.Context → Prop)
    (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∀ child, child ≤ budget → ∀ {innerContext innerOutcome},
      ExecutesAt child false program context evidence source environment before statements innerContext innerOutcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (code.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type innerOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment innerContext after ∧
        Reached readiness context innerOutcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    block_preserves_at_with_state_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source)
      protocol functions program evidence unique readiness _validity budget size bounded found form initial
      (fun child within {_ _} childTrace => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := inner child within childTrace
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, NamedLexicalFlowFaultPostContracts.FlowOutcomePost.of_trivial functions program evidence represented⟩) trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩


include unique sites in
theorem block_preserves_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady trace
  exact block_preserves_at_with_state_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) protocol functions program evidence unique validity budget size bounded found form initial (readiness := readiness)
    (fun child childBound {_ _} innerTrace => inner child childBound valid (sites.block sourceFacts found form) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady innerTrace) trace

include unique sites in
theorem block_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  exact NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (headFacts := headFacts) (meaning := block_preserves_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) (unique := unique) validity budget size bounded found form (fun child within => NamedLexicalFlowFaultPostContracts.PreservesAtFor.of_trivial (meaning := inner child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


/-- Reflection consumes the original native child once before restoring its
source control receipt; the concrete transition is relayed unchanged. -/
theorem block_reflects_at_with_state_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (_budget _size : Nat)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∃ sourceSize innerContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize false program context evidence source environment before statements innerContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment innerContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before false statements type outcome after value finalMap finalWorld finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.HeadOutcomePost headPost program context evidence source environment before id type outcome after value finalMap finalWorld finalStore := by
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _, post, origin⟩ := inner
  refine ⟨SourceExecutionSize.stepSize [sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
    ?_, restored environment outcome, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata, Reached.restore_control (protocol := protocol) (readiness := readiness) environment post, NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin⟩
  cases trace with
  | control trace => exact .control (.block (lookupStatement?_sound found) form trace)
  | fault failed => exact .fault (.block (lookupStatement?_sound found) form failed)

theorem block_reflects_at_with_state (_budget _size : Nat)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∃ sourceSize innerContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize false program context evidence source environment before statements innerContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment innerContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    ∃ sourceSize outcome after finalMap finalWorld,
      StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    block_reflects_at_with_state_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source)
      protocol functions program evidence readiness _budget _size found form initial (by
        obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := inner
        exact ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, NamedLexicalFlowFaultPostContracts.FlowOutcomePost.of_trivial functions program evidence represented⟩)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩


include sites in
theorem block_reflects_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady evaluated
  exact block_reflects_at_with_state_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) protocol functions program evidence budget size found form initial (readiness := readiness)
    (inner size bounded valid (sites.block sourceFacts found form) environments heaps locals agrees actualTyped reference read unmapped initial conditionProof initialReady evaluated)

include sites in
theorem block_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  exact NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (headFacts := headFacts) (meaning := block_reflects_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) validity budget size bounded found form (fun child within => NamedLexicalFlowFaultPostContracts.ReflectsAtFor.of_trivial (meaning := inner child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


include unique in
include sites in
theorem sequence_preserves_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady trace
  have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (headTrace : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
      (tailTrace : ExecutesAt tailSize mode program middleContext evidence source next middle rest finalContext outcome after) (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment finalContext after ∧
        Reached readiness context outcome installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type outcome after value finalMap finalWorld finalStore := by
    obtain ⟨rfl, restores, value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
      first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.control headTrace)
    have same := restores next rfl
    subst next
    cases represented with
    | fallthrough _ =>
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstPost
      obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, lastPost, lastOrigin⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid (sites.tail sourceFacts found (fun _ _ => notTail) headTrace.sound) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady tailTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical,
        Reached.continue (protocol := protocol) (readiness := readiness) firstRelated lastPost, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin⟩
      rw [LoopRenaming.sequence]
      simp only [GenericExpressionMeaning.rename_prefix] at tailEval
      exact LocalLoop.sequence_fallthrough _ headEval tailEval
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => exact go headTrace tailTrace headSmaller tailSmaller
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, firstPost, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, firstPost, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, firstPost, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩

include unique sites in
theorem sequence_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact NamedLexicalFlowFaultPostContracts.PreservesAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (facts := facts) (meaning := sequence_preserves_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) (unique := unique) validity budget size bounded found notTail (fun child within => NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor.of_trivial (meaning := first child within) (protocol := protocol) (readiness := readiness) (condition := condition) (headFacts := headFacts) (functions := functions) (program := program) (evidence := evidence)) (fun child within => NamedLexicalFlowFaultPostContracts.PreservesAtFor.of_trivial (meaning := remaining child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


include sites in
theorem sequence_reflects_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady evaluated
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts)
      environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady headEval
  cases represented with
  | fallthrough next =>
    have same := restores next rfl
    subst next
    cases headTrace with | control headTrace =>
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstPost
      obtain ⟨tailSize, tailSmaller, tailEval⟩ := evaluated.sequence_fallthrough headEval.sound
      obtain ⟨sourceTailSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, lastPost, lastOrigin⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid (sites.tail sourceFacts found (fun _ _ => notTail) headTrace.sound)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
        (prepend (lookupStatement?_sound found) (fun _ _ => notTail) headTrace.sound tailTrace.sound)
      exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical,
        Reached.continue (protocol := protocol) (readiness := readiness) firstRelated lastPost, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin⟩
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalControl.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, firstPost, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalControl.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, firstPost, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩

include sites in
theorem sequence_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact NamedLexicalFlowFaultPostContracts.ReflectsAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (facts := facts) (meaning := sequence_reflects_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) validity budget size bounded found notTail (fun child within => NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor.of_trivial (meaning := first child within) (protocol := protocol) (readiness := readiness) (condition := condition) (headFacts := headFacts) (functions := functions) (program := program) (evidence := evidence)) (fun child within => NamedLexicalFlowFaultPostContracts.ReflectsAtFor.of_trivial (meaning := remaining child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include sites in
theorem conditional_preserves_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := expressionPost) protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady trace
  have selected {conditionSize bodySize : Nat} {boolean : Bool} {middle : Dynamic.Heap} {innerContext : SourceSemantics.Context} {innerOutcome : Dynamic.ControlOutcome}
      (conditionTrace : SourceExecutionSize.ExpressionEvaluates program conditionSize context evidence source environment before conditionId (.bool boolean) middle)
      (branchTrace : ExecutesAt bodySize false program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext innerOutcome after) (conditionSmaller : conditionSize < size) (bodySmaller : bodySize < size) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.conditional type conditionCode thenCode elseCode).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type
          (Dynamic.restoreControl environment innerOutcome) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Reached readiness context (Dynamic.restoreControl environment innerOutcome) installed ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
        NamedLexicalFlowFaultPostContracts.HeadOutcomePost headPost program context evidence source environment before id type (Dynamic.restoreControl environment innerOutcome) after value finalMap finalWorld finalStore := by
    obtain ⟨_, middleStore, middleMap, middleWorld, conditionEval, represented, middleHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
      expressionPreserves conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstPost
      have branchCorrect : NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
          bodySize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first | exact thenCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded)) | exact elseCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded))
      obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _, lastPost, lastOrigin⟩ :=
        branchCorrect valid (sites.branch boolean sourceFacts found form) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady.1 branchTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, restore_rep represented environment, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata,
        Reached.continue (protocol := protocol) (readiness := readiness) firstRelated (Reached.restore_control (protocol := protocol) (readiness := readiness) environment lastPost), by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
      rw [LoopRenaming.conditional]
      rw [GenericExpressionMeaning.rename_prefix] at branchEval
      cases boolean with
      | false => exact LocalControl.choose_false _ conditionEval branchEval
      | true => exact LocalControl.choose_true _ conditionEval branchEval
  obtain ⟨same, view⟩ := RecursiveNamedStatementSourceBounds.if_inv unique (lookupStatement?_sound found) form trace
  subst finalContext
  cases view with
  | conditionFault failed smaller =>
    obtain ⟨_, finalStore, finalMap, finalWorld, conditionEval, represented, finalHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.fault failed)
    cases represented with
    | fault matched =>
      refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, firstPost, by exact NamedLexicalFlowFaultPostContracts.expression_to_head joins (.condition found form) failed.sound firstOrigin⟩
      rw [LoopRenaming.conditional]
      exact LocalControl.choose_failure _ conditionEval
  | conditionType conditionTrace notBoolean runtimeType smaller =>
    obtain ⟨_, _, _, _, _, represented, _⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
        environments heaps locals agrees actualTyped installed initialReady (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨_, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  | branch conditionTrace branchTrace conditionSmaller bodySmaller =>
    exact ⟨rfl, restored environment _, selected conditionTrace branchTrace conditionSmaller bodySmaller⟩

include sites in
theorem conditional_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionPreservesAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (headFacts := headFacts) (meaning := conditional_preserves_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) validity budget size bounded unique (fun child within context valid => NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt.of_trivial (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (protocol := protocol) (readiness := readiness) (program := program) (evidence := evidence) (exprFacts := exprFacts) (certificate := expressions context) (expressionPreserves child within context valid)) found form conditionFound _conditionType conditionTree (fun child within => NamedLexicalFlowFaultPostContracts.PreservesAtFor.of_trivial (meaning := thenCorrect child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)) (fun child within => NamedLexicalFlowFaultPostContracts.PreservesAtFor.of_trivial (meaning := elseCorrect child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


include sites in
theorem conditional_reflects_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := expressionPost) protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady evaluated
  rw [LoopRenaming.conditional] at evaluated
  obtain ⟨conditionSize, middleStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluated.bind_computation
  obtain ⟨sourceConditionSize, conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata, firstPost, firstOrigin⟩ :=
    expressionReflects conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound (sites.expression sourceFacts (.condition found form) conditionFound)
      environments heaps locals agrees actualTyped installed initialReady conditionEval
  cases represented with
  | fault matched =>
    cases conditionTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalControl.choose_failure _ conditionEval.sound)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (Dynamic.StatementExecutesOutcome.fault (Dynamic.StatementFaults.ifCondition (lookupStatement?_sound found) form failed.sound))
      exact ⟨sourceSize, _, middle, middleMap, middleWorld, trace,
        (by intro next impossible; cases impossible), .fault matched, middleHeaps, maps, worlds, frame, metadata, firstPost, by exact NamedLexicalFlowFaultPostContracts.expression_to_head joins (.condition found form) failed.sound firstOrigin⟩
  | value payload =>
    cases conditionTrace with
    | value conditionTrace =>
      obtain ⟨boolean, sourceEq, coreEq⟩ := bool_fields payload
      subst sourceEq
      subst coreEq

      obtain ⟨branchSize, branchSmaller, branchEval⟩ :
          ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool boolean :: actual) middleStore
            ((if boolean then thenCode else elseCode).rename ξ |>.weakenAt 0) value finalStore := by
        cases boolean with
        | false => exact evaluated.choose_false conditionEval.sound
        | true => exact evaluated.choose_true conditionEval.sound
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstPost
      have branchCorrect : NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
          branchSize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first
          | exact thenCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
          | exact elseCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
      obtain ⟨sourceBranchSize, innerContext, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _, lastPost, lastOrigin⟩ :=
        branchCorrect valid (sites.branch boolean sourceFacts found form) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditionProof firstReady.1
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (selected_intro program evidence found form conditionTrace.sound branchTrace.sound)
      exact ⟨sourceSize, Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        trace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata,
        Reached.continue (protocol := protocol) (readiness := readiness) firstRelated (Reached.restore_control (protocol := protocol) (readiness := readiness) environment lastPost), by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩

include sites in
theorem conditional_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionReflectsAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (headFacts := headFacts) (meaning := conditional_reflects_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) validity budget size bounded (fun child within context valid => NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt.of_trivial (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (protocol := protocol) (readiness := readiness) (program := program) (evidence := evidence) (exprFacts := exprFacts) (certificate := expressions context) (expressionReflects child within context valid)) found form conditionFound _conditionType conditionTree (fun child within => NamedLexicalFlowFaultPostContracts.ReflectsAtFor.of_trivial (meaning := thenCorrect child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)) (fun child within => NamedLexicalFlowFaultPostContracts.ReflectsAtFor.of_trivial (meaning := elseCorrect child within) (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := evidence)))


include unique in
include sites in
theorem sequence_stopped_preserves_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady trace
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => cases stops headTrace.sound
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post, origin⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata, post, origin⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts) environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩

include unique sites in
theorem sequence_stopped_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact NamedLexicalFlowFaultPostContracts.PreservesAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (facts := facts) (meaning := sequence_stopped_preserves_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) (unique := unique) validity budget size bounded found notTail (fun child within => NamedLexicalFlowFaultPostContracts.HeadPreservesAtFor.of_trivial (meaning := first child within) (protocol := protocol) (readiness := readiness) (condition := condition) (headFacts := headFacts) (functions := functions) (program := program) (evidence := evidence)) stops)


include sites in
theorem sequence_stopped_reflects_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor (post := headPost) protocol readiness condition headFacts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady evaluated
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata, post, origin⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid (sites.head sourceFacts)
      environments heaps locals agrees actualTyped reference read unmapped installed conditionProof initialReady headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace.sound
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalControl.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalControl.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, post, by first | trivial | exact NamedLexicalFlowFaultPostContracts.block_to_head joins found form origin | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins firstOrigin _ _ | exact NamedLexicalFlowFaultPostContracts.head_to_flow joins origin _ _ | exact NamedLexicalFlowFaultPostContracts.prefix_to_flow joins headTrace.sound lastOrigin | exact NamedLexicalFlowFaultPostContracts.selected_to_head joins found form conditionTrace.sound lastOrigin⟩


include sites in
theorem sequence_stopped_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact NamedLexicalFlowFaultPostContracts.ReflectsAtFor.forget (protocol := protocol) (readiness := readiness) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (facts := facts) (meaning := sequence_stopped_reflects_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source) (protocol := protocol) (condition := condition) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (functions := functions) (program := program) (evidence := evidence) validity budget size bounded found notTail (fun child within => NamedLexicalFlowFaultPostContracts.HeadReflectsAtFor.of_trivial (meaning := first child within) (protocol := protocol) (readiness := readiness) (condition := condition) (headFacts := headFacts) (functions := functions) (program := program) (evidence := evidence)) stops)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep prepend)
open TypedLexicalControl (Restored restored restore_rep LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLexicalContracts
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open RecursiveNamedCallBounds (ExpressionOutcome)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}


open ProtectedStateTransition

include unique in
theorem block_preserves_at_with_state (_validity : SourceSemantics.Context → Prop)
    (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∀ child, child ≤ budget → ∀ {innerContext innerOutcome},
      ExecutesAt child false program context evidence source environment before statements innerContext innerOutcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store (code.rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type innerOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment innerContext after ∧
        Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.block_preserves_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      _validity budget size bounded found form initial
      (fun child bound {_ _} trace => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := inner child bound trace
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
          RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩) trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

include unique in
theorem block_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor.forget_true
  exact WithReady.block_preserves_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (unique := unique) (validity := validity) budget size bounded found form
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (inner child within))

theorem block_reflects_at_with_state (_budget _size : Nat)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (inner : ∃ sourceSize innerContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize false program context evidence source environment before statements innerContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment innerContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    ∃ sourceSize outcome after finalMap finalWorld,
      StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := inner
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.block_reflects_at_with_state (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (functions := functions) (program := program) (evidence := evidence)
      _budget _size found form initial
      ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
        RecursiveNamedLexicalContracts.Stateful.WithReady.Reached.of_trivial post⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem block_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor.forget_true
  exact WithReady.block_reflects_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (validity := validity) budget size bounded found form
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (inner child within))

include unique in
theorem sequence_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.forget_true
  exact WithReady.sequence_preserves_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (unique := unique) (validity := validity) budget size bounded found notTail
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (remaining child within))

theorem sequence_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.forget_true
  exact WithReady.sequence_reflects_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (validity := validity) budget size bounded found notTail
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (remaining child within))

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

theorem conditional_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor.forget_true
  exact WithReady.conditional_preserves_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (unique := unique) (validity := validity) budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true (protocol := protocol) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context) (expressionPreserves child within context valid))
    found form conditionFound _conditionType conditionTree
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (thenCorrect child within))
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (elseCorrect child within))

theorem conditional_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {scope : Scope} {id : StatementId} {node : StatementNode}
    {conditionId : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen conditionId thenBody elseBody)
    (conditionFound : source.lookupExpression? conditionId = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope conditionId ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor.forget_true
  exact WithReady.conditional_reflects_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (validity := validity) budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true (protocol := protocol) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context) (expressionReflects child within context valid))
    found form conditionFound _conditionType conditionTree
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (thenCorrect child within))
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (elseCorrect child within))

include unique in
theorem sequence_stopped_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor.forget_true
  exact WithReady.sequence_stopped_preserves_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (unique := unique) (validity := validity) budget size bounded found notTail
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    stops

theorem sequence_stopped_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor.forget_true
  exact WithReady.sequence_stopped_reflects_at_for (protocol := protocol)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True)
    (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (functions := functions) (program := program) (evidence := evidence) (condition := condition)
    (validity := validity) budget size bounded found notTail
    (fun child within => RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor.of_true (protocol := protocol) (condition := condition) (functions := functions) (program := program) (evidence := evidence) (first child within))
    stops
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds.Stateful

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep prepend)
open TypedLexicalControl (Restored restored restore_rep LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLexicalContracts
open RecursiveNamedLexicalContracts.Stateful (legacy_PreservesAtFor legacy_ReflectsAtFor legacy_HeadPreservesAtFor legacy_HeadReflectsAtFor legacy_expression_preserves legacy_expression_reflects)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open RecursiveNamedCallBounds (ExpressionOutcome)
variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)


-- Keep the historical section binder even though the shared core discharges it.
set_option linter.unusedSectionVars false in
include unique in
theorem block_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAtFor (validity := validity) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨sameContext, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.block_preserves_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) validity budget size bounded found form ⟨trivial⟩
      (fun child childBound {_ _} innerTrace => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          inner child childBound valid environments heaps locals agrees actualTyped reference read unmapped installed innerTrace
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
          ⟨⟨trivial⟩, trivial⟩⟩) trace
  exact ⟨sameContext, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata⟩

include unique in
theorem block_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  exact block_preserves_at_for (functions := functions) (program := program) (evidence := evidence) (unique := unique)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded found form inner

theorem block_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAtFor (validity := validity) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, innerTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    inner size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.block_reflects_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) budget size found form ⟨trivial⟩
      ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, innerTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
        ⟨⟨trivial⟩, trivial⟩⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem block_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  exact block_reflects_at_for (functions := functions) (program := program) (evidence := evidence)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded found form inner

include unique transport in
theorem sequence_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_preserves_at_for (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      validity budget size bounded found notTail
      (fun child childBound => legacy_HeadPreservesAtFor functions program evidence transport (first child childBound)) (fun child childBound => legacy_PreservesAtFor functions program evidence transport (remaining child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

include unique transport in
theorem sequence_preserves_at (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact sequence_preserves_at_for (functions := functions) (program := program) (evidence := evidence) (unique := unique) (transport := transport)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded found notTail first remaining

include transport in
theorem sequence_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtFor (validity := validity) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAtFor (validity := validity) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_reflects_at_for (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      validity budget size bounded found notTail
      (fun child childBound => legacy_HeadReflectsAtFor functions program evidence transport (first child childBound)) (fun child childBound => legacy_ReflectsAtFor functions program evidence transport (remaining child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

include transport in
theorem sequence_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  exact sequence_reflects_at_for (functions := functions) (program := program) (evidence := evidence) (transport := transport)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded found notTail first remaining

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include transport in
theorem conditional_preserves_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨sameContext, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.conditional_preserves_at_for (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      validity budget size bounded (fun child childBound context valid => legacy_expression_preserves functions program evidence transport (expressionPreserves child childBound context valid)) found form conditionFound _conditionType conditionTree
      (fun child childBound => legacy_PreservesAtFor functions program evidence transport (thenCorrect child childBound)) (fun child childBound => legacy_PreservesAtFor functions program evidence transport (elseCorrect child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨sameContext, restores, value, finalStore, finalMap, finalWorld, evaluation, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport in
theorem conditional_preserves_at (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact conditional_preserves_at_for (functions := functions) (program := program) (evidence := evidence) (unique := unique) (transport := transport)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded expressionPreserves found form conditionFound _conditionType conditionTree thenCorrect elseCorrect

include transport in
theorem conditional_reflects_at_for (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.conditional_reflects_at_for (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      validity budget size bounded (fun child childBound context valid => legacy_expression_reflects functions program evidence transport (expressionReflects child childBound context valid)) found form conditionFound _conditionType conditionTree
      (fun child childBound => legacy_ReflectsAtFor functions program evidence transport (thenCorrect child childBound)) (fun child childBound => legacy_ReflectsAtFor functions program evidence transport (elseCorrect child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport in
theorem conditional_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact conditional_reflects_at_for (functions := functions) (program := program) (evidence := evidence) (transport := transport)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) budget size bounded expressionReflects found form conditionFound _conditionType conditionTree thenCorrect elseCorrect

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
/-! The existing two lexical Tree inductions carry the actual protected state
through expression children, marked allocation, and lexical tails. Each result
keeps three-way flow and stopping lexical evidence, with its state normalized
to the entry scope and canonical environment. A static physical-frame receipt
supplies allocation readiness from each reached state's real live read.
Legacy callers use the same proofs through guarded PLift witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes FlowRep not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized sequence_rename allocate_absent allocate_initialized valid_extend)
open GenericLexicalStatements (Tree Scope ValuesContext)
open RecursiveNamedLoopContracts (ExecutesAt)
open ProtectedLexicalStatements (return_unit_view nil_executes)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateBindings : Bindings protocol)
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer stateBindings acquire sites transfers in
theorem preserves_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := expressionPost) protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (sourceFacts : facts context mode statements expected)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (initialReady : readiness.Ready context state)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore := by
  induction tree generalizing size mapping world administrative environment canonical actual before after store ξ actualContext contextLocation native outcome resultContext with
  | @nil context scope mode expected type allowed =>
    cases source_view trace.sound with
    | control executed =>
      obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view mode executed
      exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
        heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨state, protocol.refl state, initialReady⟩, by trivial⟩
    | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault mode failed)
  | @returnUnit context scope mode id node rest found form =>
    obtain ⟨rfl, rfl, rfl⟩ := return_unit_view unique (lookupStatement?_sound found) form trace.sound
    exact ⟨_, store, mapping, world, LocalLoop.returned_evaluates .unit, .returned .unit,
      heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨state, protocol.refl state, initialReady⟩, by trivial⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, smaller⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition, origin⟩ :=
      expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.returning found form) expressionFound)
        environments heaps locals agrees actualTyped state initialReady childTrace
    cases represented with
    | value payload =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩, by trivial⟩
    | fault matched =>
      cases childTrace with | fault failed =>
       exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.returning found form) failed.sound origin _ _⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
    obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition, origin⟩ :=
      expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
        environments heaps locals agrees actualTyped state initialReady childTrace
    cases represented with
    | value payload =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩, by trivial⟩
    | fault matched =>
      cases childTrace with | fault failed =>
       exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.tail_to_flow joins found form failed.sound origin⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, tailSize, allocated, tailTrace, smaller⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.absent unique found form mono extended trace
    obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
      TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ conditioned) state read)
    obtain ⟨nextState, allocationRelated⟩ := allocationTransition
    have nextReady := transfers.absent state nextState initialReady extended allocated preservation
    have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
      (.letUninitialized (lookupStatement?_sound found) form mono extended allocated)
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, tailTransition, origin⟩ :=
      ih _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (extend contextValid extended) tailFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        nextState conditioned nextReady tailTrace
    obtain ⟨tailState, tailRelated, tailReady⟩ := tailTransition
    let finalState := stateBindings.restore
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)
    have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (binder := binder) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) transfers extended tailState tailReady
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated finalRelated, finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.letUninitialized (lookupStatement?_sound found) form mono extended allocated) origin⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename]
    rcases RecursiveNamedLexicalTreeSourceBounds.initialized unique found form mono extended trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata, transition, origin⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid initial initialFound (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound)
          environments heaps locals agrees actualTyped state initialReady (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.initialized found form mono) failed.sound origin _ _⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, transition, origin⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid initial initialFound (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound)
          environments heaps locals agrees actualTyped state initialReady (.value initialTrace)
      cases represented with
      | value payload =>
        obtain ⟨middleState, expressionRelated, expressionReady⟩ := transition
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        have nextReady := transfers.initialized middleState nextState expressionReady.1 extended
          (sourceType ▸ expressionReady.2) allocated allocationFrame
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
          (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended allocated)
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailTransition, origin⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) (extend contextValid extended) tailFacts
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState conditioned nextReady tailTrace
        obtain ⟨tailState, tailRelated, tailReady⟩ := tailTransition
        let finalState := stateBindings.restore
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState)
        have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (binder := binder) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) transfers extended tailState tailReady
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended,
          ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated finalRelated), finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended allocated) origin⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases RecursiveNamedLexicalTreeSourceBounds.discard unique found form guard trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, middle, childTrace, tail, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition, origin⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
          environments heaps locals agrees actualTyped state initialReady (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.expression found form) failed.sound origin _ _⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, transition, origin⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
          environments heaps locals agrees actualTyped state initialReady (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨middleState, expressionRelated, expressionReady⟩ := transition
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (not_tail form guard)
          (.expression (lookupStatement?_sound found) form childTrace.sound)
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical, tailTransition, origin⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid tailFacts (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned expressionReady.1 tail
        obtain ⟨finalState, tailRelated, finalReady⟩ := tailTransition
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical, ⟨finalState, protocol.trans expressionRelated tailRelated, finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.expression (lookupStatement?_sound found) form childTrace.sound) origin⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | block found form inner remaining innerIH remainingIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
      (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.block_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
        (globals := globals) (unique := unique) budget child within found form innerIH) remainingIH
      contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
      (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.conditional_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget child within unique expressionPreserves
        found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady trace

  | terminalBlock exactUnique found form inner stops issued innerIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_stopped_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
      (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := exactUnique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.block_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
        (globals := globals) (unique := exactUnique) budget child within found form innerIH)
      (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady trace
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_stopped_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
      (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := exactUnique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.conditional_preserves_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget child within exactUnique expressionPreserves
        found form conditionFound conditionType conditionTree thenIH elseIH)
      (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady trace


include definitions registered producer stateBindings acquire sites transfers in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionPreservesAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (sourceFacts : facts context mode statements expected)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (initialReady : readiness.Ready context state)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition, _⟩ :=
    preserves_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source)
      (protocol := protocol) (condition := condition) (producer := producer) (stateBindings := stateBindings) (acquire := acquire)
      (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (transfers := transfers)
      functions definitions registered program evidence validity extend budget size bounded
      (fun child within context valid => NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt.of_trivial (protocol := protocol) (readiness := readiness) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (exprFacts := exprFacts) (certificate := expressions context) (expressionPreserves child within context valid))
      tree contextValid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩

include definitions registered producer stateBindings acquire sites transfers in
set_option maxHeartbeats 1600000 in
theorem reflects_at_for_with_post (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : NamedLexicalFlowFaultPostContracts.HeadFaultPost) (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost)
    (joins : NamedLexicalFlowFaultPostContracts.Joins expressionPost headPost flowPost program evidence source) (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := expressionPost) protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (sourceFacts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (initialReady : readiness.Ready context state)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore := by
  suffices result : ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore by
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preservation, metadata, lexical, transition, origin⟩ := result
    obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
    exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, represented,
      finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩

  induction tree generalizing size mapping world administrative environment canonical actual before store ξ actualContext contextLocation native finalStore value with
  | @nil context scope mode expected type allowed =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨context, _, before, mapping, world, nil_executes mode program context evidence source environment before, .fallthrough environment, heaps,
      .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨state, protocol.refl state, initialReady⟩, by trivial⟩
  | @returnUnit context scope mode id node rest found form =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
    exact ⟨context, _, before, mapping, world,
      terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnUnit (lookupStatement?_sound found) form) (.returned _),
      .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨state, protocol.refl state, initialReady⟩, by trivial⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, transition, origin⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.returning found form) expressionFound)
        environments heaps locals agrees actualTyped state initialReady childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, head_fault mode rest (.returnValue (lookupStatement?_sound found) form failed.sound),
          .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.returning found form) failed.sound origin _ _⟩
    | value payload =>
      cases trace with | value childTrace =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace.sound) (.returned _),
          .returned (valueType ▸ payload), finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩, by trivial⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, transition, origin⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
        environments heaps locals agrees actualTyped state initialReady childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed.sound),
          .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.tail_to_flow joins found form failed.sound origin⟩
    | value payload =>
      cases trace with | value childTrace =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, .control (.tailExpression (lookupStatement?_sound found) form childTrace.sound),
          .returned (valueType ▸ payload), finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩, by trivial⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
      TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append state ((acquire _ _ conditioned) state read)
    obtain ⟨nextState, allocationRelated⟩ := allocationTransition
    have nextReady := transfers.absent state nextState initialReady extended Dynamic.Heap.Allocates.append preservation
    have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
      (.letUninitialized (lookupStatement?_sound found) form mono extended Dynamic.Heap.Allocates.append)
    obtain ⟨tailSize, smaller, continuation⟩ := evaluated.let_body allocationEval
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, transition, origin⟩ :=
      ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (extend contextValid extended) tailFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        nextState conditioned nextReady continuation
    obtain ⟨tailState, tailRelated, tailReady⟩ := transition
    let finalState := stateBindings.restore
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)
    have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
      (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (binder := binder) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) transfers extended tailState tailReady
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated finalRelated, finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.letUninitialized (lookupStatement?_sound found) form mono extended .append) origin⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename] at evaluated
    obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := evaluated.bind_computation
    obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata, transition, origin⟩ :=
      expressionReflects initialSize (Nat.le_of_lt (Nat.lt_of_lt_of_le initialSmaller bounded)) _ contextValid initial initialFound (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound)
        environments heaps locals agrees actualTyped state initialReady initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed.sound),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.initialized found form mono) failed.sound origin _ _⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        obtain ⟨middleState, expressionRelated, expressionReady⟩ := transition
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append middleState ((acquire _ _ conditioned) middleState frameRead)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        have nextReady := transfers.initialized middleState nextState expressionReady.1 extended
          (sourceType ▸ expressionReady.2) Dynamic.Heap.Allocates.append allocationFrame
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
          (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended Dynamic.Heap.Allocates.append)
        obtain ⟨branchSize, branchSmaller, branchEval⟩ := evaluated.bind_success initialEval.sound
        obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailTransition, origin⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_trans smaller branchSmaller) bounded)) (extend contextValid extended) tailFacts
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState conditioned nextReady tailEval
        obtain ⟨tailState, tailRelated, tailReady⟩ := tailTransition
        let finalState := stateBindings.restore
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        have finalRelated := protocol.trans tailRelated (stateBindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState)
        have finalReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (binder := binder) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) transfers extended tailState tailReady
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended,
          ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated finalRelated), finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append) origin⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rw [LoopRenaming.discard] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, transition, origin⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound)
        environments heaps locals agrees actualTyped state initialReady childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalSequence.discard_failure _ childEvaluation.sound)
        exact ⟨context, _, middle, middleMap, middleWorld,
          head_fault mode rest (.expression (lookupStatement?_sound found) form failed.sound),
          .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
          ⟨_, _, _, .here, environments.extend firstMaps firstWorlds, locals.mono firstMetadata⟩, transition, NamedLexicalFlowFaultPostContracts.expression_to_flow joins (.expression found form) failed.sound origin _ _⟩
    | @value _ coreValue payload =>
      cases trace with | value childTrace =>
        obtain ⟨middleState, expressionRelated, expressionReady⟩ := transition
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (not_tail form guard)
          (.expression (lookupStatement?_sound found) form childTrace.sound)
        obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := evaluated.bind_success childEvaluation.sound
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid tailFacts
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned expressionReady.1
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
        obtain ⟨finalState, tailRelated, finalReady⟩ := transition
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend (lookupStatement?_sound found) (not_tail form guard)
            (.expression (lookupStatement?_sound found) form childTrace.sound) tail,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans preservation, firstMetadata.trans metadata, lexical, ⟨finalState, protocol.trans expressionRelated tailRelated, finalReady⟩, NamedLexicalFlowFaultPostContracts.prefix_to_flow joins (.expression (lookupStatement?_sound found) form childTrace.sound) origin⟩
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    have innerBound : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) false statements expected type innerCode := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        innerIH child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    have tailBound : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) mode rest expected type body := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        remainingIH child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.block_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
          (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
          (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
          (globals := globals) budget child within found form innerBound) tailBound
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    have branchBound {statements : List StatementId} {branch : Expr}
        (meaning : ∀ child, child ≤ budget → ∀ (valid : validity context) (_facts : facts context false statements expected)
          {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
          {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
          {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value},
          DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions →
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
          Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
          RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
          canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) →
          store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) → contextLocation ∉ mapping →
          ∀ state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
          condition contextLocation native → readiness.Ready context state → EvaluationSize child actual store (branch.rename ξ) value finalStore →
          ∃ finalContext outcome after finalMap finalWorld,
            Executes false program context evidence source environment before statements finalContext outcome after ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ AdministrativePreserved mapping store finalMap finalStore ∧
            Dynamic.HeapMetadataExtend before after ∧ LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment finalContext after ∧
            Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before false statements type outcome after value finalMap finalWorld finalStore) :
        ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
          functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
          child (scope := scope) false statements expected type branch := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        meaning child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    have tailBound : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) mode rest expected type body := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        remainingIH child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.conditional_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
          (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
          (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) budget child within expressionReflects found form conditionFound conditionType conditionTree
          (branchBound thenIH) (branchBound elseIH)) tailBound
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerIH =>
    have innerBound : ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) false statements expected type innerCode := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        innerIH child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_stopped_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.block_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
          (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
          (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
          (globals := globals) budget child within found form innerBound)
        (GenericLexicalStatements.block_terminates exactUnique found form stops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩

  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    have branchBound {statements : List StatementId} {branch : Expr}
        (meaning : ∀ child, child ≤ budget → ∀ (valid : validity context) (_facts : facts context false statements expected)
          {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
          {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
          {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value},
          DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions →
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
          Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
          RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
          canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) →
          store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) → contextLocation ∉ mapping →
          ∀ state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
          condition contextLocation native → readiness.Ready context state → EvaluationSize child actual store (branch.rename ξ) value finalStore →
          ∃ finalContext outcome after finalMap finalWorld,
            Executes false program context evidence source environment before statements finalContext outcome after ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ AdministrativePreserved mapping store finalMap finalStore ∧
            Dynamic.HeapMetadataExtend before after ∧ LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment finalContext after ∧
            Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFlowFaultPostContracts.FlowOutcomePost flowPost program context evidence source environment before false statements type outcome after value finalMap finalWorld finalStore) :
        ∀ child, child ≤ budget → NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := flowPost) protocol readiness condition facts (validity := validity)
          functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
          child (scope := scope) false statements expected type branch := by
      intro child within valid childFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
        meaning child within valid childFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned childReady evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.WithReady.sequence_stopped_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
        (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.WithReady.conditional_reflects_at_for_with_post (expressionPost := expressionPost) (headPost := headPost) (flowPost := flowPost) (joins := joins) (validity := validity)
          (protocol := protocol) (condition := condition) (readiness := readiness)
      (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
          (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) budget child within expressionReflects found form conditionFound conditionType conditionTree
          (branchBound thenIH) (branchBound elseIH))
        (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition, origin⟩

include definitions registered producer stateBindings acquire sites transfers in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ExpressionReflectsAt protocol readiness program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (expressions context) (context := context) (source := source) (faults := faults) child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (sourceFacts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (initialReady : readiness.Ready context state)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Reached readiness context outcome state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition, _⟩ :=
    reflects_at_for_with_post (expressionPost := ExpressionFailurePostContracts.TrivialExpressionPost) (headPost := NamedLexicalFlowFaultPostContracts.TrivialHead) (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (joins := NamedLexicalFlowFaultPostContracts.trivial_joins program evidence source)
      (protocol := protocol) (condition := condition) (producer := producer) (stateBindings := stateBindings) (acquire := acquire)
      (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (transfers := transfers)
      functions definitions registered program evidence validity extend budget size bounded
      (fun child within context valid => NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt.of_trivial (protocol := protocol) (readiness := readiness) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (exprFacts := exprFacts) (certificate := expressions context) (expressionReflects child within context valid))
      tree contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped state conditioned initialReady evaluated
  exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩


end WithReady

include definitions registered producer stateBindings acquire in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := WithReady.preserves_at_for
    (protocol := protocol) (condition := condition) (producer := producer) (stateBindings := stateBindings) (acquire := acquire)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      (protocol := protocol) (program := program) (evidence := evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context)
      (expressionPreserves child within context valid))
    tree contextValid True.intro unique environments heaps locals agrees actualTyped reference read unmapped state conditioned True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

include definitions registered producer stateBindings acquire in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := WithReady.reflects_at_for
    (protocol := protocol) (condition := condition) (producer := producer) (stateBindings := stateBindings) (acquire := acquire)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
      (protocol := protocol) (program := program) (evidence := evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := expressions context)
      (expressionReflects child within context valid))
    tree contextValid True.intro environments heaps locals agrees actualTyped reference read unmapped state conditioned True.intro evaluated
  exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩
include definitions registered producer stateBindings acquire in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_at_for functions definitions registered program evidence protocol condition producer stateBindings acquire
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionPreserves tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped state conditioned trace

include definitions registered producer stateBindings acquire in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_at_for functions definitions registered program evidence protocol condition producer stateBindings acquire
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionReflects tree contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated

end Stateful

open ProtectedStateTransition

private def legacyBindings (bindings : ProtectedExpressionMeaning.Binds entry) :
    Bindings (ProtectedStateTransition.Lexical.legacyProtocol entry) where
  prepend state _id _type _value := ⟨bindings.prepend state.down⟩
  prepend_related _state _id _type _value := trivial
  prepend_records _state _id _type _value := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _state := trivial
  restore_records _state := rfl

private def legacyProducer (functions : FunctionModel values.checked.catalog ambient)
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    OrdinaryAllocation.Producer (ProtectedStateTransition.Lexical.legacyProtocol entry) layouts frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) :=
  OrdinaryAllocation.of_administrative _ (ProtectedStateTransition.Lexical.legacyTransport transport)
    (legacyBindings bindings) layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions)

include definitions registered transport bindings in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preservation, metadata, lexical, _⟩ :=
    Stateful.preserves_at_for functions definitions registered program evidence
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      (legacyProducer functions transport bindings) (legacyBindings bindings)
      (fun location native _ => OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      validity extend budget size bounded
      (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (expressionPreserves child within context valid))
      tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preservation, metadata, lexical⟩

include definitions registered transport bindings in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact preserves_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionPreserves tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered transport bindings in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, preservation, metadata, lexical, _⟩ :=
    Stateful.reflects_at_for functions definitions registered program evidence
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      (legacyProducer functions transport bindings) (legacyBindings bindings)
      (fun location native _ => OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      validity extend budget size bounded
      (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        functions program evidence transport (expressionReflects child within context valid))
      tree contextValid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, preservation, metadata, lexical⟩

include definitions registered transport bindings in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact reflects_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionReflects tree contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
/-! The actual catalog parameter entry supplies the source heap/environment,
renaming, typed native environment and protected frame observations to function
finish. Static profiles are indexed by that entry's real administrative context.
Flow meaning remains a separate pointwise input for later mutual induction;
these adapters do not close all catalog bodies or change static profile fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat} {expressionSyntax : ExpressionId → Prop}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (escapedFault : faults .controlEscapedFunction header.escaped)

include escapedFault

/-- The same source cost reaches the actual finish. Every administrative and
frame fact comes from the retained marked parameter entry. -/
theorem state_preserves_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor
      (entry := P) functions program header.function.evidence validity
      (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (entryP : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      P
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  have reference : entry.canonical[(header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping := by
    exact Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  exact RecursiveNamedFunctionFinishBounds.preserves_at_with functions program profile.accepted profile.generated profile.tree
    profile.projection header.unique escapedFault transport validity size meaning profile.initialValid
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped entryP trace

theorem state_preserves_at_with (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence validity
      (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical :=
  state_preserves_at_for functions escapedFault _ entry_transport validity profile size meaning entry ⟨entry.catalog⟩ trace

/-- Finish reflection selects its strict child from the original native
witness. The resulting source cost remains independent. -/
theorem state_reflects_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor
        (entry := P) functions program header.function.evidence validity
        (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (entryP : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      P
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  have reference : entry.canonical[(header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping := by
    exact Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  exact RecursiveNamedFunctionFinishBounds.reflects_at_with functions program profile.accepted profile.generated profile.tree
    profile.projection header.unique escapedFault transport validity budget size within meaning profile.initialValid
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped entryP completed

theorem state_reflects_at_with (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence validity
        (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical :=
  state_reflects_at_for functions escapedFault _ entry_transport validity profile budget size within meaning entry ⟨entry.catalog⟩ completed

/-- The same source cost reaches the actual finish. Every administrative and
frame fact comes from the retained marked parameter entry. -/
theorem state_preserves_at_match
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_preserves_at_with functions escapedFault
    (fun context => CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence)
    profile.toMatchProfileWith size meaning entry trace

/-- Finish reflection selects its strict child from the original native
witness. The resulting source cost remains independent. -/
theorem state_reflects_at_match
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_reflects_at_with functions escapedFault
    (fun context => CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence)
    profile.toMatchProfileWith budget size within meaning entry completed

theorem state_preserves_at
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_preserves_at_match functions escapedFault profile.to_match size meaning entry trace

theorem state_reflects_at
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_reflects_at_match functions escapedFault profile.to_match budget size within meaning entry completed

/-- Each real parameter entry chooses its own static administrative profile;
no fixed context is cast to an arbitrary typed capture. -/
theorem body_preserves_at
    (profiles : ∀ administrative, ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : ∀ administrative, RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output (profiles administrative).flow) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, completed, related, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    state_preserves_at functions escapedFault (profiles administrative) size (meaning administrative) entry trace
  exact ⟨value, finalStore, finalMap, finalWorld, completed, related, heaps, maps, worlds, frame, metadata⟩

/-- The same outer budget is retained for every captured administrative
context; only the actual finish subderivation selects a smaller obligation. -/
theorem body_reflects_at
    (profiles : ∀ administrative, ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ administrative, RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output (profiles administrative).flow)) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    state_reflects_at functions escapedFault (profiles administrative) budget size within (meaning administrative) entry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
end
