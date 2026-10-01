import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileComposition

/-! Conditional composition for generic static expression certificates.
Transfer-aware child contracts are supplied by recursive statement induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Preserves Reflects HeadPreserves HeadReflects FlowRep restored restore_rep)
open CompatibleExpressionPrimitives (bool_fields)
variable {administrative : Core.Context} {readFuel : Nat} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults)
  (reflection : CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults)

include unique meaning in
theorem conditional_preserves {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped trace
  have selected {boolean : Bool} {middle : Dynamic.Heap} {innerContext : SourceSemantics.Context} {innerOutcome : Dynamic.ControlOutcome}
      (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle)
      (branchTrace : Executes false program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext innerOutcome after) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.conditional type conditionCode thenCode elseCode).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type
          (Dynamic.restoreControl environment innerOutcome) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    obtain ⟨_, middleStore, middleMap, middleWorld, conditionEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
      meaning valid conditionTree conditionFound
        environments heaps locals agrees actualTyped (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      have branchCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          (administrative := administrative) (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> assumption
      obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _⟩ :=
        branchCorrect valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 branchTrace
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, restore_rep represented environment, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
      rw [LoopRenaming.conditional]
      rw [GenericExpressionMeaning.rename_prefix] at branchEval
      cases boolean with
      | false => exact LocalControl.choose_false _ conditionEval branchEval
      | true => exact LocalControl.choose_true _ conditionEval branchEval
  cases trace with
  | control trace =>
    obtain ⟨rfl, boolean, middle, innerContext, innerOutcome, conditionTrace, rfl, branchTrace⟩ :=
      ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form trace
    exact ⟨rfl, restored environment innerOutcome, selected conditionTrace (.control branchTrace)⟩
  | fault failed =>
    rcases ScalarStatementViews.ifThen_fault unique (lookupStatement?_sound found) form failed with
      failed | ⟨value, actualType, conditionTrace, notBoolean, _, _⟩ | ⟨boolean, middle, innerContext, conditionTrace, failed⟩
    · obtain ⟨_, finalStore, finalMap, finalWorld, conditionEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning valid conditionTree conditionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [LoopRenaming.conditional]
        exact LocalControl.choose_failure _ conditionEval
    · obtain ⟨_, _, _, _, _, represented, _⟩ :=
        meaning valid conditionTree conditionFound
          environments heaps locals agrees actualTyped (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, rfl, _⟩ := bool_fields payload
        exact False.elim (notBoolean trivial)
    · exact ⟨rfl, (by intro next impossible; cases impossible), selected conditionTrace (.fault failed)⟩

theorem selected_intro {innerContext : SourceSemantics.Context} {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {boolean : Bool} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle)
    (branchTrace : Executes false program context evidence source environment middle
      (if boolean then thenBody else elseBody.getD []) innerContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context (Dynamic.restoreControl environment outcome) after := by
  cases boolean with
  | true => cases branchTrace with
    | control trace => exact .control (.ifTrue (lookupStatement?_sound found) form conditionTrace trace)
    | fault failed => exact .fault (.ifTrueBody (lookupStatement?_sound found) form conditionTrace failed)
  | false => cases elseBody with
    | none => cases branchTrace with
      | control trace => cases trace; exact .control (.ifFalseWithoutElse (lookupStatement?_sound found) form conditionTrace)
      | fault failed => cases failed
    | some statements => cases branchTrace with
      | control trace => exact .control (.ifFalseWithElse (lookupStatement?_sound found) form conditionTrace trace)
      | fault failed => exact .fault (.ifFalseBody (lookupStatement?_sound found) form conditionTrace failed)

include reflection in
theorem conditional_reflects {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (administrative := administrative) (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  rw [LoopRenaming.conditional] at evaluated
  have input : ∃ value middleStore, Evaluates actual store (conditionCode.rename ξ) value middleStore := by
    cases evaluated with
    | caseLeft child _ | caseRight child _ => exact ⟨_, _, child⟩
  obtain ⟨conditionValue, middleStore, conditionEval⟩ := input
  obtain ⟨conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    reflection valid conditionTree conditionFound
      environments heaps locals agrees actualTyped conditionEval
  cases represented with
  | fault matched =>
    cases conditionTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalControl.choose_failure _ conditionEval)
      exact ⟨_, middle, middleMap, middleWorld, .fault (.ifCondition (lookupStatement?_sound found) form failed),
        (by intro next impossible; cases impossible), .fault matched, middleHeaps, maps, worlds, frame, metadata⟩
  | value payload =>
    cases conditionTrace with
    | value conditionTrace =>
      obtain ⟨boolean, sourceEq, coreEq⟩ := bool_fields payload
      subst sourceEq
      subst coreEq

      have branchCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          (administrative := administrative) (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> assumption
      obtain ⟨_, sized⟩ := evaluation_has_size evaluated
      have branchEval : Evaluates (.bool boolean :: actual) middleStore ((if boolean then thenCode else elseCode).rename ξ |>.weakenAt 0) value finalStore := by
        cases boolean with
        | false => obtain ⟨_, _, branch⟩ := sized.choose_false conditionEval; exact branch.sound
        | true => obtain ⟨_, _, branch⟩ := sized.choose_true conditionEval; exact branch.sound
      obtain ⟨innerContext, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, _⟩ :=
        branchCorrect valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        selected_intro program evidence found form conditionTrace branchTrace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata⟩


end Solcore.SourceSemantics.CoreLowering.GenericImperativeWhile
