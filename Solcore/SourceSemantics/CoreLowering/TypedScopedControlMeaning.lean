import Solcore.SourceSemantics.CoreLowering.TypedScopedControlCertificates
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! Finite meaning of recursive typed blocks and conditionals. Every expression
and nested list is discharged by its static tree. Actual temporary payloads,
including the three sequence-envelope slots, are typed structurally. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedScopedControl
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open TypedScopedStatements (not_tail head_fault terminal_intro prepend SourceView source_view discard_view)

private def Restored (environment : Dynamic.Environment) (outcome : Dynamic.ControlOutcome) : Prop :=
  ∀ next, outcome = .fallthrough next → next = environment

private theorem restored (environment : Dynamic.Environment) (outcome : Dynamic.ControlOutcome) :
    Restored environment (Dynamic.restoreControl environment outcome) := by
  cases outcome <;> simp [Restored, Dynamic.restoreControl]

private theorem restore_rep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome} {value : Value}
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (environment : Dynamic.Environment) :
    FlowRep (registry := registry) functions mapping world faults expected type (Dynamic.restoreControl environment outcome) value := by
  cases represented with
  | fallthrough _ => exact .fallthrough environment
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

private def Preserves (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀     {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_trace : Executes mode program context evidence source environment before statements finalContext outcome after),
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private def Reflects (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀     {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private def HeadPreserves {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀     {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_trace : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private def HeadReflects {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀     {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem terminal_outcome {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after)
    (terminal : Dynamic.TerminalControl outcome) :
    Executes mode program context evidence source environment before (id :: rest) context outcome after := by
  cases head with
  | control trace => exact terminal_intro mode rest (lookupStatement?_sound found) notTail trace terminal
  | fault failed => exact head_fault mode rest failed

include unique in
private theorem block_preserves {scope : Scope} {id : StatementId} {node : StatementNode}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) false statements expected type code) :
    HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) id expected type code := by
  intro mapping world administrative actualContext environment canonical actual before after store ξ outcome finalContext
    environments heaps locals agrees actualTyped trace
  cases trace with
  | control trace =>
    obtain ⟨rfl, innerContext, innerOutcome, rfl, executed⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form trace
    obtain ⟨rfl, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      inner environments heaps locals agrees actualTyped (.control executed)
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      evaluated, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failed =>
    obtain ⟨innerContext, failed⟩ := ScalarStatementViews.block_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨rfl, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      inner environments heaps locals agrees actualTyped (.fault failed)
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

private theorem block_reflects {scope : Scope} {id : StatementId} {node : StatementNode}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) false statements expected type code) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) id expected type code := by
  intro mapping world administrative actualContext environment canonical actual before store finalStore ξ value
    environments heaps locals agrees actualTyped evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    inner environments heaps locals agrees actualTyped evaluated
  refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
    restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | control trace => exact .control (.block (lookupStatement?_sound found) form trace)
  | fault failed => exact .fault (.block (lookupStatement?_sound found) form failed)

include unique in
private theorem sequence_preserves {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) id expected type head)
    (remaining : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) mode rest expected type body) :
    Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro mapping world administrative actualContext environment canonical actual before after store ξ outcome finalContext
    environments heaps locals agrees actualTyped trace
  have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (headTrace : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
      (tailTrace : Executes mode program middleContext evidence source next middle rest finalContext outcome after) :
      finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    obtain ⟨rfl, restores, value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
      first environments heaps locals agrees actualTyped (.control headTrace)
    have same := restores next rfl
    subst next
    cases represented with
    | fallthrough _ =>
      obtain ⟨same, value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        remaining (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) tailTrace
      refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
      rw [LoopRenaming.sequence]
      simp only [GenericExpressionMeaning.rename_prefix] at tailEval
      exact LocalLoop.sequence_fallthrough _ headEval tailEval
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) executed with
      ⟨_, _, _, headTrace, tailTrace⟩ | ⟨headTrace, terminal⟩
    · exact go headTrace (by cases mode <;> exact .control tailTrace)
    · obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first environments heaps locals agrees actualTyped (.control headTrace)
      cases represented with
      | fallthrough _ => cases terminal
      | returned payload => exact ⟨rfl, _, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
          .returned payload, finalHeaps, maps, worlds, frame, metadata⟩
      | fault matched => exact ⟨rfl, _, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) failed with
      ⟨rfl, headTrace⟩ | ⟨_, _, _, headTrace, tailTrace⟩
    · obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first environments heaps locals agrees actualTyped (.fault headTrace)
      cases represented with
      | fault matched => exact ⟨rfl, _, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · exact go headTrace (by cases mode <;> exact .fault tailTrace)

private theorem sequence_reflects {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) id expected type head)
    (remaining : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) mode rest expected type body) :
    Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro mapping world administrative actualContext environment canonical actual before store finalStore ξ value
    environments heaps locals agrees actualTyped evaluated
  rw [LoopRenaming.sequence] at evaluated
  have input : ∃ value middleStore, Evaluates actual store (head.rename ξ) value middleStore := by
    cases evaluated with
    | caseLeft child _ | caseRight child _ => exact ⟨_, _, child⟩
  obtain ⟨headValue, middleStore, headEval⟩ := input
  obtain ⟨outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first environments heaps locals agrees actualTyped headEval
  cases represented with
  | fallthrough next =>
    have same := restores next rfl
    subst next
    cases headTrace with | control headTrace =>
      obtain ⟨_, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, tailEval⟩ := sized.sequence_fallthrough headEval
      obtain ⟨outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        remaining (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds))))
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval.sound)
      exact ⟨outcome, after, finalMap, finalWorld, prepend (lookupStatement?_sound found) (fun _ _ => notTail) headTrace tailTrace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_returned _ headEval)
    exact ⟨_, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨_, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata⟩

include extension contextValid unique uninitialized missing in
private theorem conditional_preserves {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world administrative actualContext environment canonical actual before after store ξ outcome finalContext
    environments heaps locals agrees actualTyped trace
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
      CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing conditionTree conditionFound
        environments heaps locals agrees actualTyped (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      have branchCorrect : Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
          (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> assumption
      obtain ⟨_, value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        branchCorrect (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds)) branchTrace
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
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing conditionTree conditionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [LoopRenaming.conditional]
        exact LocalControl.choose_failure _ conditionEval
    · obtain ⟨_, _, _, _, _, represented, _⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing conditionTree conditionFound
          environments heaps locals agrees actualTyped (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, rfl, _⟩ := bool_fields payload
        exact False.elim (notBoolean trivial)
    · exact ⟨rfl, (by intro next impossible; cases impossible), selected conditionTrace (.fault failed)⟩

private theorem selected_intro {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {boolean : Bool} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle)
    (branchTrace : Executes false program context evidence source environment middle
      (if boolean then thenBody else elseBody.getD []) context outcome after) :
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

include extension contextValid uninitialized missing in
private theorem conditional_reflects {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world administrative actualContext environment canonical actual before store finalStore ξ value
    environments heaps locals agrees actualTyped evaluated
  rw [LoopRenaming.conditional] at evaluated
  have input : ∃ value middleStore, Evaluates actual store (conditionCode.rename ξ) value middleStore := by
    cases evaluated with
    | caseLeft child _ | caseRight child _ => exact ⟨_, _, child⟩
  obtain ⟨conditionValue, middleStore, conditionEval⟩ := input
  obtain ⟨conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing conditionTree conditionFound
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

      have branchCorrect : Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)
          (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> assumption
      obtain ⟨_, sized⟩ := evaluation_has_size evaluated
      have branchEval : Evaluates (.bool boolean :: actual) middleStore ((if boolean then thenCode else elseCode).rename ξ |>.weakenAt 0) value finalStore := by
        cases boolean with
        | false => obtain ⟨_, _, branch⟩ := sized.choose_false conditionEval; exact branch.sound
        | true => obtain ⟨_, _, branch⟩ := sized.choose_true conditionEval; exact branch.sound
      obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        branchCorrect (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool boolean)) (.cons .bool (actualTyped.weaken worlds))
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        selected_intro program evidence found form conditionTrace branchTrace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata⟩

include extension contextValid unique uninitialized missing in
/-- The entire finite source sequence determines a native execution. No child
execution or universal child meaning is a certificate premise. -/
theorem Tree.preserves {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope mode statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world administrative environment canonical actual before after store ξ outcome finalContext actualContext with
  | fragment child =>
    exact TypedScopedStatements.Tree.preserves functions extension program evidence contextValid unique uninitialized missing child
      environments heaps locals agrees actualTyped trace
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨same, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) tail
        refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | block found form inner remaining innerIH remainingIH =>
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (unique := unique) found (by intro expression; simp [form])
      (block_preserves (functions := functions) (program := program) (evidence := evidence) (unique := unique) found form innerIH) remainingIH
      environments heaps locals agrees actualTyped trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (unique := unique) found (by intro expression; simp [form])
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (extension := extension) (contextValid := contextValid) (uninitialized := uninitialized) (missing := missing) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      environments heaps locals agrees actualTyped trace


include extension contextValid uninitialized missing in
/-- Every completed generated flow constructs its independent source trace.
The returned expression trace is derived from the actual native subtree. -/
theorem Tree.reflects {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope mode statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world administrative environment canonical actual before store finalStore ξ value actualContext with
  | fragment child =>
    exact TypedScopedStatements.Tree.reflects functions extension program evidence contextValid uninitialized missing child
      environments heaps locals agrees actualTyped evaluated
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩

  | block found form inner remaining innerIH remainingIH =>
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) found (by intro expression; simp [form])
      (block_reflects (functions := functions) (program := program) (evidence := evidence) found form innerIH) remainingIH
      environments heaps locals agrees actualTyped evaluated
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) found (by intro expression; simp [form])
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (extension := extension) (contextValid := contextValid) (uninitialized := uninitialized) (missing := missing) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      environments heaps locals agrees actualTyped evaluated

end Solcore.SourceSemantics.CoreLowering.TypedScopedControl
