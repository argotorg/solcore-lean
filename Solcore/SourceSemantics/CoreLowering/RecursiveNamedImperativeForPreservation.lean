import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBitNotStatementContracts

/-! The existing Match Tree closes lexical, assignment, loop and match children
at one fixed budget. The original For entry is a static inclusion wrapper. The reached header retains an inclusive loop continuation;
source and Core sizes are independent and no finite loop proof is duplicated. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
namespace Control
abbrev PreservesAt := @RecursiveNamedLoopContracts.PreservesAt
abbrev ReflectsAt := @RecursiveNamedLoopContracts.ReflectsAt
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

include unique in
theorem block_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  cases trace with
  | control trace =>
    obtain ⟨rfl, child, innerContext, innerOutcome, rfl, executed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_value unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed
        (.control executed)
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      evaluated, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failed =>
    obtain ⟨child, innerContext, failed, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.block_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      inner child (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed
        (.fault failed)
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

include unique transport in
theorem sequence_preserves_at (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
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
          context scope environment finalContext after := by
    obtain ⟨rfl, restores, value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
      first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
    have same := restores next rfl
    subst next
    cases represented with
    | fallthrough _ =>
      obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata) tailTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
      rw [LoopRenaming.sequence]
      simp only [GenericExpressionMeaning.rename_prefix] at tailEval
      exact LocalLoop.sequence_fallthrough _ headEval tailEval
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => exact go headTrace tailTrace headSmaller tailSmaller
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .breaking next, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .continuing next, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include unique in
private theorem sequence_stopped_preserves_at (budget size : Nat) (bounded : size ≤ budget) {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (fun _ _ => notTail) trace
  cases view with
  | next headTrace tailTrace headSmaller tailSmaller => cases stops headTrace.sound
  | terminal headTrace terminal headSmaller =>
    obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
    cases represented with
    | fallthrough _ => cases terminal
    | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
        .returned payload, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .breaking next, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
        .continuing next, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault headTrace headSmaller =>
    obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      first _ (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed (.fault headTrace)
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

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
    (thenCorrect : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
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
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    obtain ⟨_, middleStore, middleMap, middleWorld, conditionEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
      expressionPreserves conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound
        environments heaps locals agrees actualTyped installed (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      have branchCorrect : PreservesAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          bodySize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first | exact thenCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded)) | exact elseCorrect bodySize (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller bounded))
      obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _⟩ :=
        branchCorrect valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata) branchTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, restore_rep represented environment, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
      rw [LoopRenaming.conditional]
      rw [GenericExpressionMeaning.rename_prefix] at branchEval
      cases boolean with
      | false => exact LocalControl.choose_false _ conditionEval branchEval
      | true => exact LocalControl.choose_true _ conditionEval branchEval
  obtain ⟨same, view⟩ := RecursiveNamedStatementSourceBounds.if_inv unique (lookupStatement?_sound found) form trace
  subst finalContext
  cases view with
  | conditionFault failed smaller =>
    obtain ⟨_, finalStore, finalMap, finalWorld, conditionEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound
        environments heaps locals agrees actualTyped installed (.fault failed)
    cases represented with
    | fault matched =>
      refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
      rw [LoopRenaming.conditional]
      exact LocalControl.choose_failure _ conditionEval
  | conditionType conditionTrace notBoolean runtimeType smaller =>
    obtain ⟨_, _, _, _, _, represented, _⟩ :=
      expressionPreserves _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) context valid conditionTree conditionFound
        environments heaps locals agrees actualTyped installed (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨_, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  | branch conditionTrace branchTrace conditionSmaller bodySmaller =>
    exact ⟨rfl, restored environment _, selected conditionTrace branchTrace conditionSmaller bodySmaller⟩

end Control

namespace AssignmentSourceAt
private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) :
    ∀ other, ContainsStatement source id other → other.form = node.form := by
  intro other present
  exact congrArg StatementNode.form (Option.some.inj ((lookupStatement?_complete unique present).symm.trans found))

variable {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem value_success (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child updated,
      SourceExecutionSize.SourcePlaceAssignment program child context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧ child < size := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem unary_success (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child updated,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program child context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧ child < size := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem value_fault (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.SourcePlaceAssignmentFaults program child context evidence source
      environment before assignment.target operator rhs reason after ∧ child < size := by
  have shapes := shape unique found
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  clear found
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have same := shapes _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem unary_fault (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.SourcePlaceBitNotFaults program child context evidence source
      environment before assignment.target reason after ∧ child < size := by
  have shapes := shape unique found
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  clear found
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have same := shapes _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end AssignmentSourceAt

namespace ForSourceAt
private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem success_at
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome} {size : Nat}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (executed : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ initialSize loopSize loopContext loopFinalContext loopEnvironment initialized loopOutcome,
      outcome = Dynamic.restoreControl environment loopOutcome ∧
      SourceExecutionSize.ForItemsExecute program initialSize context evidence source environment before items loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopExecutes program loopSize loopContext evidence source loopEnvironment initialized condition post statements loopFinalContext loopOutcome after ∧ initialSize < size ∧ loopSize < size := by
  have formShape := shape unique contains form
  clear contains form
  cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, _, _, _, _, rfl, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

theorem fault_at
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault} {size : Nat}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    (∃ initialSize finalContext, SourceExecutionSize.ForItemsFault program initialSize context evidence source environment before items finalContext reason after ∧ initialSize < size) ∨
    (∃ initialSize loopSize loopContext loopEnvironment initialized,
      SourceExecutionSize.ForItemsExecute program initialSize context evidence source environment before items loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopFaults program loopSize loopContext evidence source loopEnvironment initialized condition post statements reason after ∧ initialSize < size ∧ loopSize < size) := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := formShape _ (by assumption); simp_all
  · exact Or.inl ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  · exact .inr ⟨_, _, _, _, _, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

end ForSourceAt

open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
private theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · exact ScalarStatementViews.breaking unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible

private theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · exact ScalarStatementViews.continuing unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.continuing_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible


open GenericImperativeFor (Tree Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (budget : Nat)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopPreservesAt functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => RecursiveNamedForContracts.LoopReflectsAt functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include definitions registered extension transport bindings meaning faithful observations in
theorem header_preserves_at (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨header, errors⟩ := headers
  cases trace with
  | control executed =>
    obtain ⟨rfl, initialSize, loopSize, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop, initialSmall, loopSmall⟩ :=
      ForSourceAt.success_at unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := by cases loop <;> rfl
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
      ProtectedForHeader.Tree.preserves_prefix_bounded functions definitions registered extension program evidence transport bindings faithful observations budget meaning header
        valid environments heaps locals agrees actualTyped reference read unmapped installed initialization (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
      tail.certificate _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.control loop)
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩
  | fault failed =>
    rcases ForSourceAt.fault_at unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, _, fault, smaller⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata⟩ :=
        ProtectedForHeader.Tree.preserves_fault_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations budget meaning header errors
          valid environments heaps locals agrees actualTyped reference read unmapped installed fault (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata⟩
    · obtain ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, initialization, loop, initialSmall, loopSmall⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
        ProtectedForHeader.Tree.preserves_prefix_bounded functions definitions registered extension program evidence transport bindings faithful observations budget meaning header
          valid environments heaps locals agrees actualTyped reference read unmapped installed initialization (Nat.le_trans (Nat.le_of_lt initialSmall) bounded)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
        tail.certificate _ (Nat.le_trans (Nat.le_of_lt loopSmall) bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.fault loop)
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
        frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩

include extension meaning transport bindings definitions registered faithful observations in
theorem loop_preserves_at (size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code)) :
    RecursiveNamedForContracts.LoopPreservesAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  have result := ProtectedFor.Body.loop_preserves_bounded functions program evidence transport budget (meaning _ valid)
    conditionFound conditionTree typed unique correct
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before after store finalContext finalEnvironment guarded continued execution
      exact ProtectedForHeader.post_preserves_bounded functions definitions registered extension program evidence transport bindings faithful observations budget meaning postTree
        actualValid actualAgrees actualReference guarded continued execution (Nat.le_of_lt small))
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before after store finalContext reason guarded continued execution
      exact ProtectedForHeader.post_fault_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations budget meaning postTree postErrors
        actualValid actualAgrees actualReference guarded continued execution (Nat.le_of_lt small))
  exact result size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

variable (meaningMost : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
  AtMost budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults entry))
include definitions registered extension transport bindings meaningMost faithful observations in
theorem preservesAt_match (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  have meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (certificates context) faults entry) :=
    fun context valid child smaller => meaningMost context valid child (Nat.le_of_lt smaller)
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      RecursiveNamedLexicalTreeBounds.preserves_at functions definitions registered program evidence transport bindings size size (Nat.le_refl size)
        (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
        body contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨location, middle, tailSize, allocated, tailTrace, smaller⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rw [sequence_rename]
    rcases RecursiveNamedLexicalTreeSourceBounds.initialized unique found form mono extended trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) initial initialFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) initial initialFound
          environments heaps locals agrees actualTyped installed (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rcases RecursiveNamedLexicalTreeSourceBounds.discard unique found form guard trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, middle, childTrace, tail, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ contextValid childSize (Nat.lt_of_lt_of_le smaller bounded) child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata) tail
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact Control.sequence_preserves_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.block_preserves_at (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size child within found form
        (fun child within => innerIH child (Nat.le_trans within bounded)))
      (fun child within => remainingIH child (Nat.le_trans within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact Control.sequence_preserves_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.conditional_preserves_at (functions := functions) (program := program) (evidence := evidence)
        (transport := transport) (frameLayout := frame) (globals := globals) size child within unique
        (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
        found form conditionFound conditionType conditionTree
        (fun child within => thenIH child (Nat.le_trans within bounded))
        (fun child within => elseIH child (Nat.le_trans within bounded)))
      (fun child within => remainingIH child (Nat.le_trans within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact Control.sequence_stopped_preserves_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.block_preserves_at (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) (unique := unique) size child within found form
        (fun child within => innerIH child (Nat.le_trans within bounded)))
      (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact Control.sequence_stopped_preserves_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.conditional_preserves_at (functions := functions) (program := program) (evidence := evidence)
        (transport := transport) (frameLayout := frame) (globals := globals) size child within unique
        (fun child within context valid => meaningMost context valid child (Nat.le_trans within bounded))
        found form conditionFound conditionType conditionTree
        (fun child within => thenIH child (Nat.le_trans within bounded))
        (fun child within => elseIH child (Nat.le_trans within bounded)))
      (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @breaking context scope mode id node rest expected type found form =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace.sound
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace.sound
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    apply Control.sequence_preserves_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (remaining := fun child within => restIH child (Nat.le_trans within bounded))
      (first := ?_) contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
    intro child within valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, _⟩ :=
      ProtectedWhile.Body.while_preserves_bounded functions program evidence transport budget (meaning _ valid)
        found form conditionFound conditionTree nativeTyped unique (fun child small => loopIH child (Nat.le_of_lt small)) child (Nat.le_trans within bounded)
        valid environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : ExecutesAt tailSize mode program middleContext evidence source next middle rest resultContext outcome after) (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, childSize, updated, assigned, childSmaller⟩ := AssignmentSourceAt.value_success unique found form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport
          faithful observations head
          environments heaps locals agrees actualTyped installed budget (meaning _ contextValid) assigned (Nat.le_of_lt (Nat.lt_trans childSmaller (Nat.lt_of_lt_of_le headSmaller bounded)))
      have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found) (by intro _ _; simp [form]) trace with
    | next first tail headSmaller tailSmaller => exact go first tail headSmaller tailSmaller
    | terminal first terminal _ =>
      obtain ⟨_, rfl, _⟩ := AssignmentSourceAt.value_success unique found form first
      cases terminal
    | fault first smaller =>
      obtain ⟨childSize, failed, childSmaller⟩ := AssignmentSourceAt.value_fault unique found form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ :=
        ProtectedAssignmentHeads.Head.preserves_fault_reachable_bounded functions extension program evidence transport
          faithful observations head environments heaps locals agrees actualTyped installed budget (meaning _ contextValid)
          headErrors.reachable failed (Nat.le_of_lt (Nat.lt_trans childSmaller (Nat.lt_of_lt_of_le smaller bounded))) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext environments heaps locals agrees actualTyped reference read unmapped installed trace
    have go {headSize tailSize : Nat} {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : ExecutesAt tailSize mode program middleContext evidence source next middle rest resultContext outcome after) (_headSmaller : headSize < size) (tailSmaller : tailSize < size) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, _childSize, updated, assigned, _childSmaller⟩ := AssignmentSourceAt.unary_success unique found form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
        head.preserves_prefix functions program evidence observations
          environments heaps locals agrees actualTyped assigned.sound
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata) tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found) (by intro _ _; simp [form]) trace with
    | next first tail headSmaller tailSmaller => exact go first tail headSmaller tailSmaller
    | terminal first terminal _ =>
      obtain ⟨_, rfl, _⟩ := AssignmentSourceAt.unary_success unique found form first
      cases terminal
    | fault first _ =>
      obtain ⟨_, failed, _⟩ := AssignmentSourceAt.unary_fault unique found form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        head.preserves_fault functions program evidence observations environments heaps locals agrees headErrors failed.sound body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact Control.sequence_preserves_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) (unique := unique) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => header_preserves_at functions definitions registered extension program evidence transport bindings budget meaning faithful observations
        child (Nat.le_trans within bounded) unique found form
        (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, errors.reachable⟩))
      (fun child within => restIH child (Nat.le_trans within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := fun size bounded => loop_preserves_at functions definitions registered extension program evidence transport bindings budget meaning faithful observations size bounded unique
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) (fun child small => loopIH child (Nat.le_of_lt small))
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩


  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalogValid patternContext childErrors remainingErrors childrenIH remainingIH =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded
    exact Control.sequence_preserves_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => GenericImperativeMatch.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped unique budget child within transport bindings (meaning context)
        (fun request member childContext valid child smaller => childrenIH request member childContext valid child (Nat.le_of_lt smaller)))
      remainingIH

  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalogValid patternContext childErrors childrenIH =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded
    exact Control.sequence_stopped_preserves_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => GenericImperativeMatch.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped unique budget child within transport bindings (meaning context)
        (fun request member childContext valid child smaller => childrenIH request member childContext valid child (Nat.le_of_lt smaller)))
      (ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops)

include definitions registered extension transport bindings meaningMost faithful observations in
theorem preservesAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact preservesAt_match functions definitions registered extension program evidence transport bindings budget faithful observations meaningMost
    diagnosticPolicy unique (GenericImperativeMatch.Tree.of_for tree) (GenericImperativeMatch.Tree.CatalogSites.of_for errors)

include definitions registered extension transport bindings meaning faithful observations in
/-- A caller with only strictly smaller expression laws can use the same main
induction at each actual statement size. The empty header remains inclusive
inside that invocation. -/
theorem preserves_below (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    Below budget (fun size => RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  intro size smaller
  exact preservesAt_for functions definitions registered extension program evidence transport bindings size faithful observations
    (fun context valid child within => meaning context valid child (Nat.lt_of_le_of_lt within smaller))
    diagnosticPolicy unique tree errors size (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
