import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation

/-! Original native children select the bounded reflected head and tail.
The same Match Tree supplies selected-child entry and catalog receipts.
Source costs are reconstructed independently, preserving the same lexical
exit context, typed hidden values and installed caller observations. -/
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
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
theorem block_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    inner size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  refine ⟨SourceExecutionSize.stepSize [sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
    ?_, restored environment outcome, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | control trace => exact .control (.block (lookupStatement?_sound found) form trace)
  | fault failed => exact .fault (.block (lookupStatement?_sound found) form failed)

include transport in
theorem sequence_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid
      environments heaps locals agrees actualTyped reference read unmapped installed headEval
  cases represented with
  | fallthrough next =>
    have same := restores next rfl
    subst next
    cases headTrace with | control headTrace =>
      obtain ⟨tailSize, tailSmaller, tailEval⟩ := evaluated.sequence_fallthrough headEval.sound
      obtain ⟨sourceTailSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        remaining tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) valid
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata)
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
        (prepend (lookupStatement?_sound found) (fun _ _ => notTail) headTrace.sound tailTrace.sound)
      exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.breaking next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.continuing next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem sequence_stopped_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rw [LoopRenaming.sequence] at evaluated
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := evaluated.bind_computation
  obtain ⟨sourceHeadSize, outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first headSize (Nat.le_of_lt (Nat.lt_of_lt_of_le headSmaller bounded)) valid
      environments heaps locals agrees actualTyped reference read unmapped installed headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace.sound
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_returned _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.returned _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.breaking next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_transfer _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.continuing next))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.sequence_failure _ headEval.sound)
    obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size
      (TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace.sound (.fault _))
    exact ⟨sourceSize, context, _, middle, middleMap, middleWorld, trace,
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

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
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rw [LoopRenaming.conditional] at evaluated
  obtain ⟨conditionSize, middleStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluated.bind_computation
  obtain ⟨sourceConditionSize, conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    expressionReflects conditionSize (Nat.le_of_lt (Nat.lt_of_lt_of_le conditionSmaller bounded)) context valid conditionTree conditionFound
      environments heaps locals agrees actualTyped installed conditionEval
  cases represented with
  | fault matched =>
    cases conditionTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalControl.choose_failure _ conditionEval.sound)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (Dynamic.StatementExecutesOutcome.fault (Dynamic.StatementFaults.ifCondition (lookupStatement?_sound found) form failed.sound))
      exact ⟨sourceSize, _, middle, middleMap, middleWorld, trace,
        (by intro next impossible; cases impossible), .fault matched, middleHeaps, maps, worlds, frame, metadata⟩
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
      have branchCorrect : ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          branchSize (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> first
          | exact thenCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
          | exact elseCorrect branchSize (Nat.le_of_lt (Nat.lt_of_lt_of_le branchSmaller bounded))
      obtain ⟨sourceBranchSize, innerContext, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _⟩ :=
        branchCorrect valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata)
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      obtain ⟨sourceSize, trace⟩ := StatementOutcome.has_size
        (selected_intro program evidence found form conditionTrace.sound branchTrace.sound)
      exact ⟨sourceSize, Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        trace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata⟩



end Control

open GenericImperativeFor (Tree Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
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

include definitions registered extension transport bindings reflection faithful observations in
theorem header_reflects_at (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨header, errors⟩ := headers
  have result := ProtectedForHeader.Tree.reflects_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations budget reflection functionTypes header errors
    valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated bounded
  cases result with
  | @continues initialSize remainingSize initialContext initialEnvironment initialized tail trace maps worlds frame metadata remaining smaller =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, loop, represented, progress⟩ :=
      tail.certificate _ (Nat.le_trans smaller bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed remaining
    refine ⟨SourceExecutionSize.stepSize [initialSize, sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩
    cases loop with
    | control loop => exact .control (.forLoop (lookupStatement?_sound found) form trace loop)
    | fault loop => exact .fault (.forIteration (lookupStatement?_sound found) form trace loop)
  | fault trace same matched heaps maps worlds frame metadata =>
    subst value
    exact ⟨_, _, _, _, _, .fault (.forInitializer (lookupStatement?_sound found) form trace),
      (by intro next impossible; cases impossible), .fault matched, heaps, maps, worlds, frame, metadata⟩

include extension reflection transport bindings definitions registered faithful observations in
theorem loop_reflects_at (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    RecursiveNamedForContracts.LoopReflectsAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  have result := ProtectedFor.Body.loop_reflects_bounded functions program evidence transport budget (reflection _ valid)
    conditionFound conditionTree typed correct bodyCannotFault
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before store finalStore value guarded continued execution
      exact ProtectedForHeader.post_reflects_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations budget reflection functionTypes postTree postErrors
        actualValid actualAgrees actualReference guarded continued execution (Nat.le_of_lt small))
  exact result size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated


private theorem measure_result {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap} {mode : Bool} {statements : List StatementId}
    {P : SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → LocationMap → StoreTyping → Prop}
    (result : ∃ finalContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements finalContext outcome after ∧
      P finalContext outcome after finalMap finalWorld) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      P finalContext outcome after finalMap finalWorld := by
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩ := result
  obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩

include definitions registered extension transport bindings reflection faithful observations in
theorem reflectsAt_match (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      RecursiveNamedLexicalTreeBounds.reflects_at functions definitions registered program evidence transport bindings size size (Nat.le_refl size)
        (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
        body contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    obtain ⟨tailSize, smaller, continuation⟩ := evaluated.let_body allocationEval
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih tailSize (Nat.lt_trans smaller bounded) (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace.sound,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    rw [sequence_rename] at evaluated
    obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := evaluated.bind_computation
    obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      reflection _ contextValid initialSize (Nat.lt_trans initialSmaller bounded) initial initialFound
        environments heaps locals agrees actualTyped installed initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed.sound),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        obtain ⟨branchSize, branchSmaller, branchEval⟩ := evaluated.bind_success initialEval.sound
        obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
        obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih tailSize (Nat.lt_trans (Nat.lt_trans smaller branchSmaller) bounded) (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append) trace.sound,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    rw [LoopRenaming.discard] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
      reflection _ contextValid childSize (Nat.lt_trans smaller bounded) child expressionFound
        environments heaps locals agrees actualTyped installed childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalSequence.discard_failure _ childEvaluation.sound)
        exact ⟨context, _, middle, middleMap, middleWorld,
          head_fault mode rest (.expression (lookupStatement?_sound found) form failed.sound),
          .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
          _, _, _, .here, environments.extend firstMaps firstWorlds, locals.mono firstMetadata⟩
    | @value _ coreValue payload =>
      cases trace with | value childTrace =>
        obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := evaluated.bind_success childEvaluation.sound
        obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, tail, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
          ih tailSize (Nat.lt_trans tailSmaller bounded) contextValid
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata)
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend (lookupStatement?_sound found) (not_tail form guard)
            (.expression (lookupStatement?_sound found) form childTrace.sound) tail.sound,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans preservation, firstMetadata.trans metadata, lexical⟩
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact Control.sequence_reflects_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.block_reflects_at (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size child within found form
        (fun child within => innerIH child (Nat.lt_of_le_of_lt within bounded)))
      (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact Control.sequence_reflects_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.conditional_reflects_at (functions := functions) (program := program) (evidence := evidence)
        (transport := transport) (frameLayout := frame) (globals := globals) size child within
        (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
        found form conditionFound conditionType conditionTree
        (fun child within => thenIH child (Nat.lt_of_le_of_lt within bounded))
        (fun child within => elseIH child (Nat.lt_of_le_of_lt within bounded)))
      (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact Control.sequence_stopped_reflects_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.block_reflects_at (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size child within found form
        (fun child within => innerIH child (Nat.lt_of_le_of_lt within bounded)))
      (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact Control.sequence_stopped_reflects_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => Control.conditional_reflects_at (functions := functions) (program := program) (evidence := evidence)
        (transport := transport) (frameLayout := frame) (globals := globals) size child within
        (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
        found form conditionFound conditionType conditionTree
        (fun child within => thenIH child (Nat.lt_of_le_of_lt within bounded))
        (fun child within => elseIH child (Nat.lt_of_le_of_lt within bounded)))
      (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @breaking context scope mode id node rest expected type found form =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
      simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
      simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply Control.sequence_reflects_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (remaining := fun child within => restIH child (Nat.lt_of_le_of_lt within bounded))
      (first := ?_) contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    intro child within valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, preservation, metadata, _⟩ :=
      ProtectedWhile.Body.while_reflects_bounded functions program evidence transport budget (reflection _ valid)
        found form conditionFound conditionTree nativeTyped loopIH (fun executed => loopTree.control_not_fault unique executed)
        child (Nat.le_trans within (Nat.le_of_lt bounded)) valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, preservation, metadata⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    have assigned := ProtectedAssignmentHeads.Head.reflects_reachable_bounded functions extension program evidence transport
      faithful observations head environments heaps locals agrees actualTyped installed budget (reflection _ contextValid)
      functionTypes headErrors.reachable evaluated (Nat.le_of_lt bounded)
    cases assigned with
    | @fault sourceSize reason token after finalMap finalWorld trace same matched finalHeaps maps worlds preservation metadata observed =>
      subst value
      exact ⟨context, .fault reason, after, finalMap, finalWorld,
          head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace.sound), .fault matched,
          finalHeaps, maps, worlds, preservation, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | @success sourceSize remainingSize updated middle written middleMap middleWorld slots trace middleHeaps maps worlds preservation metadata count typed observed smaller continuation =>
      have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨tailSourceSize, resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih remainingSize (Nat.lt_trans smaller bounded) contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace.sound) tail.sound,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩


  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    apply measure_result
    rcases head.reflects_sized functions program evidence observations
      environments heaps locals agrees actualTyped headErrors evaluated with
      ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨sourceSize, updated, middle, written, middleMap, middleWorld, slots, remainingSize, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, smaller, continuation⟩
    · exact ⟨context, .fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignBitNot (lookupStatement?_sound found) form trace.sound), .fault matched,
        finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨tailSourceSize, resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih remainingSize (Nat.lt_trans smaller bounded) contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata)
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignBitNot (lookupStatement?_sound found) form trace.sound) tailTrace.sound,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro size bounded contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact Control.sequence_reflects_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => header_reflects_at functions definitions registered extension program evidence transport bindings budget reflection faithful observations
        child (Nat.le_trans within (Nat.le_of_lt bounded)) functionTypes found form
        (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, errors.reachable⟩))
      (fun child within => restIH child (Nat.lt_of_le_of_lt within bounded))
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := fun size bounded => loop_reflects_at functions definitions registered extension program evidence transport bindings budget reflection faithful observations size bounded functionTypes
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH (fun executed => loopTree.control_not_fault unique executed)
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
    exact Control.sequence_reflects_at (functions := functions) (program := program) (evidence := evidence) (transport := transport)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => GenericImperativeMatch.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped budget child (Nat.le_trans within (Nat.le_of_lt bounded)) transport bindings (reflection context)
        childrenIH)
      (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))

  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalogValid patternContext childErrors childrenIH =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded
    exact Control.sequence_stopped_reflects_at (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
      (fun child within => GenericImperativeMatch.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped budget child (Nat.le_trans within (Nat.le_of_lt bounded)) transport bindings (reflection context)
        childrenIH)
      (ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops)

include definitions registered extension transport bindings reflection faithful observations in
theorem reflectsAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact reflectsAt_match functions definitions registered extension program evidence transport bindings budget reflection faithful observations
    diagnosticPolicy functionTypes unique (GenericImperativeMatch.Tree.of_for tree) (GenericImperativeMatch.Tree.CatalogSites.of_for errors)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
