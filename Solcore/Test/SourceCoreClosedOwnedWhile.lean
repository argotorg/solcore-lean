import Solcore.Test.SourceCoreClosedOwnedLexicalBody
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning

/-! Closed finite while consumers derive their condition and body callbacks
from static literal and lexical Tree receipts. The actual owned allocator and
fixed frame read supply the body state; finite while folds keep its reached
pool through native recursion and restored source control. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedWhile
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition

/-- Only the compiler's ordinary builtin Boolean form is admitted. -/
def booleans (source : TypedSource) : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => ∃ node name boolean,
    source.lookupExpression? id = some node ∧
    node.form = .reference name (.builtinBoolean boolean) ∧
    CompatibleExpressionLiterals.Literal [] node lowered.type lowered.expression

private theorem boolean_literal_empty {solved : List SolvedRequirement} {node : ExpressionNode}
    {type : Ty} {code : Expr} {name : String} {boolean : Bool}
    (literal : CompatibleExpressionLiterals.Literal solved node type code)
    (form : node.form = .reference name (.builtinBoolean boolean)) :
    CompatibleExpressionLiterals.Literal [] node type code := by
  cases literal with
  | bool value actual type requirements coercions =>
    exact .bool value actual type requirements coercions
  | unit actual _ _ _ | word _ actual _ _ _ _ | resolvedWord actual _ | resolvedInteger actual _ =>
    rw [form] at actual
    cases actual

/-- Actual accepted lowering supplies the static Boolean receipt. -/
theorem boolean_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {name : String} {boolean : Bool}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    booleans source scope id lowered := by
  obtain ⟨other, otherFound, literal⟩ := CompatibleExpressionLiterals.of_functions
    found (by rw [form]; exact .bool name boolean)
    (by intro impossible; rw [form] at impossible; cases impossible)
    special readPolicy leafPolicy accepted
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  exact ⟨node, name, boolean, found, form, boolean_literal_empty literal form⟩

private theorem boolean_receipts {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (receipt : booleans source scope id lowered) :
    ∃ node, source.lookupExpression? id = some node ∧
      CompatibleExpressionLiterals.Literal [] node lowered.type lowered.expression ∧
      CompatibleExpressionLiterals.NumericEvidence context evidence node := by
  obtain ⟨node, name, boolean, found, form, literal⟩ := receipt
  refine ⟨node, found, literal, ?_⟩
  intro value resolution numeric
  rw [form] at numeric
  cases numeric

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

section Conditions
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

/-- Literal code has certified administrative effects and preserves records. -/
theorem boolean_preserves_at (size : Nat) (unique : NodeOccurrencesUnique source) :
    ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults size := by
  have plain : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults :=
    CompatibleExpressionLiterals.preserves_with_evidence (registry := registry) functions program context evidence
    (certificate := booleans source) boolean_receipts unique faults
  intro scope id lowered receipt node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees _typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    plain receipt found environments heaps locals agrees trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition (protocol headers keys) (administrativeTransport headers keys) initial maps worlds frame metadata⟩

/-- A literal's original native completion yields an independent source grade. -/
theorem boolean_reflects_at (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults size := by
  have plain : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults :=
    CompatibleExpressionLiterals.reflects_with_evidence (registry := registry) functions program context evidence source
    (certificate := booleans source) boolean_receipts faults
  intro scope id lowered receipt node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees _typed initial evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    plain receipt found environments heaps locals agrees evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition (protocol headers keys) (administrativeTransport headers keys) initial maps worlds frame metadata⟩
end Conditions

section While
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {bodyCode conditionCode : Expr} {reason : Word}
  {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionReceipt : booleans source scope condition ⟨.bool, conditionCode⟩)
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.whileLoop type conditionCode bodyCode reason) (LocalLoop.resultType type) ambient.definitions)
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values source Tests.SourceCoreClosedOwnedLexicalBody.noExpressions context scope false statements expected type bodyCode)
  (admission : GenericLexicalStatements.Syntax source Tests.SourceCoreClosedOwnedLexicalBody.noExpressionSyntax context false statements expected)
  (unique : NodeOccurrencesUnique source)

include definitions registered found form conditionFound conditionReceipt codeTyped tree unique in
/-- Source head execution consumes literal and closed Tree proofs internally. -/
theorem closed_while_preserves (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ TypedLexicalWhile.Restored environment outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have bodies : RecursiveNamedLoopContracts.Below size (fun child => ProtectedStateTransition.Lexical.Gated.PreservesAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.preserves_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_preserves_at functions evidence definitions registered tree child unique)
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    ProtectedWhile.Body.Stateful.while_preserves_bounded_for
      (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (administrativeTransport headers keys) (fun _ => True) size
      (fun child _ => boolean_preserves_at functions evidence child unique)
      found form conditionFound conditionReceipt codeTyped unique bodies
      size (Nat.le_refl _) trivial environments heaps locals agrees typed reference read unmapped initial seed trace
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native completion independently reconstructs source control and its pool. -/
theorem closed_while_reflects (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.reflects_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_reflects_at functions evidence definitions registered tree child)
  have bodyCannotFault : ∀ {actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason},
      Dynamic.StatementsExecute actualProgram actualContext actualEvidence source actualEnvironment before statements finalContext (.fault reason) after → False := by
    intro actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason trace
    exact GenericLexicalStatements.control_not_fault admission unique trace
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    ProtectedWhile.Body.Stateful.while_reflects_bounded_for
      (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
      (fun child _ => boolean_reflects_at functions evidence child)
      found form conditionFound conditionReceipt codeTyped bodies bodyCannotFault
      size within trivial environments heaps locals agrees typed reference read unmapped initial seed evaluated
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩
include codeTyped in
/-- The actual false loop installs its captured self closure, skips its body,
and keeps every row's exact record list. -/
theorem false_loop_keeps_records
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    let finalWorld := TypedLexicalWhile.installedWorld world type
    ∃ final : State headers keys ⟨scope, mapping, finalWorld, before, finalStore, canonical⟩,
      Evaluates actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      Relates initial final ∧ records final = records initial ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping finalWorld before finalStore ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type (conditionCode.rename ξ) (bodyCode.rename ξ)
          (LocalLoop.fallthrough type) reason store.length actual)) ∧
      store.length ∉ mapping ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native ∧
      (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame mapping finalStore record) := by
  obtain ⟨activation, progress, related, sameRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := protocol headers keys)
      functions (administrativeTransport headers keys) environments heaps locals agrees typed read unmapped codeTyped initial
  have conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type store.length actual)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) (.inRight .word (.bool false))
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) := by
    rw [falseCode]
    simp only [Core.LoopExecution.conditionCode, LanguageResult.success, Expr.weakenAt, Expr.rename]
    exact .inRight .bool
  have nativeTrace : Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (bodyCode.rename ξ) reason store.length actual
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (LocalLoop.fallthroughValue type)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) :=
    .done conditionEval
  refine ⟨activation.retained, ?_, related, sameRecords, progress.1, activation.live.selfRead,
    activation.live.selfUnmapped, (TypedLexicalWhile.retain unmapped read progress.2.2.2.1).2,
    ⟨selected, ghost, metadata, physicalOwner, stable⟩, ?_⟩
  · simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates
  · intro row record member
    exact record_snapshot activation.retained row member

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- A constructed false-loop completion reaches the shared reflection fold;
neither an evaluation nor a source execution is assumed. -/
theorem false_loop_reflection_exists
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ nativeSize sourceSize outcome after finalMap finalWorld,
      EvaluationSize nativeSize actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome (LocalLoop.fallthroughValue type) ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨_installed, evaluated, _observations⟩ := false_loop_keeps_records
    (headers := headers) (keys := keys) functions codeTyped falseCode initial selected physicalOwner stable
    environments heaps locals agrees typed read unmapped
  obtain ⟨nativeSize, completed⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, _heaps, _maps, _worlds, _frame, _metadata,
      final, related, prefixes, snapshots, _transition⟩ :=
    closed_while_reflects (headers := headers) (keys := keys) functions evidence definitions registered
      found form conditionFound conditionReceipt codeTyped tree admission unique nativeSize nativeSize (Nat.le_refl _)
      initial selected physicalOwner stable environments heaps locals agrees typed reference read unmapped completed
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, restored, represented,
    final, related, prefixes, snapshots⟩

end While
end Tests.SourceCoreClosedOwnedWhile
