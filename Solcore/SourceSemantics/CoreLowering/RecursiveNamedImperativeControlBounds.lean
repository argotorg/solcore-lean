import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
import Solcore.SourceSemantics.CoreLowering.GenericImperativeWhileComposition

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
