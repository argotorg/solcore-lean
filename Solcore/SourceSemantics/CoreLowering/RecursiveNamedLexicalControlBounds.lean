import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts

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
