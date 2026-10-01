import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning

/-! Guarded lexical composition keeps actual installed/global/frame authority
at every child entry. Scoped restoration changes source bindings only; shared
heap effects, exact captures and administrative snapshots remain protected. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes FlowRep not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalControl (Restored restored restore_rep LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context


section Source
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}

theorem nil_executes (mode : Bool) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Executes mode program context evidence source environment heap [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

theorem return_unit_view
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt none)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible
    · exact ScalarStatementViews.returnUnit unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.returnUnit_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible

theorem return_value_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible
    · obtain ⟨same, value, rfl, child⟩ := ScalarStatementViews.returnValue unique contains form head
      exact ⟨same, _, .value child, rfl⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, _⟩
    · exact ⟨same, _, .fault (ScalarStatementViews.returnValue_fault unique contains form head), rfl⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible

theorem tail_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before [id] finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have shape : ∀ other, ContainsStatement source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases trace with
  | control executed => cases executed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .value child, rfl⟩
    | singleton present notTail _ =>
      have eq := shape _ present; subst_vars
      exact False.elim (notTail expression form)
  | fault failed => cases failed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .fault child, rfl⟩
    | singleton head =>
      exact ⟨rfl, _, .fault (ScalarStatementViews.expression_fault unique contains form head), rfl⟩

end Source

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

def Preserves (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (_trace : Executes mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def Reflects (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ finalContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def HeadPreserves {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (_trace : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadReflects {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

include unique in
theorem block_preserves {scope : Scope} {id : StatementId} {node : StatementNode}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) false statements expected type code) :
    HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  cases trace with
  | control trace =>
    obtain ⟨rfl, innerContext, innerOutcome, rfl, executed⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      inner valid environments heaps locals agrees actualTyped reference read unmapped installed (.control executed)
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      evaluated, restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failed =>
    obtain ⟨innerContext, failed⟩ := ScalarStatementViews.block_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      inner valid environments heaps locals agrees actualTyped reference read unmapped installed (.fault failed)
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem block_reflects {scope : Scope} {id : StatementId} {node : StatementNode}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) false statements expected type code) :
    HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨innerContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    inner valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
    restore_rep represented environment, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | control trace => exact .control (.block (lookupStatement?_sound found) form trace)
  | fault failed => exact .fault (.block (lookupStatement?_sound found) form failed)

include unique transport in
theorem sequence_preserves {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (remaining : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode rest expected type body) :
    Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (headTrace : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
      (tailTrace : Executes mode program middleContext evidence source next middle rest finalContext outcome after) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type head body).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment finalContext after := by
    obtain ⟨rfl, restores, value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
      first valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
    have same := restores next rfl
    subst next
    cases represented with
    | fallthrough _ =>
      obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        remaining valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) executed with
      ⟨_, _, _, headTrace, tailTrace⟩ | ⟨headTrace, terminal⟩
    · exact go headTrace (by cases mode <;> exact .control tailTrace)
    · obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
      cases represented with
      | fallthrough _ => cases terminal
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
          .returned payload, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) failed with
      ⟨rfl, headTrace⟩ | ⟨_, _, _, headTrace, tailTrace⟩
    · obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped installed (.fault headTrace)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · exact go headTrace (by cases mode <;> exact .fault tailTrace)

include transport in
theorem sequence_reflects {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (remaining : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode rest expected type body) :
    Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rw [LoopRenaming.sequence] at evaluated
  have input : ∃ value middleStore, Evaluates actual store (head.rename ξ) value middleStore := by
    cases evaluated with
    | caseLeft child _ | caseRight child _ => exact ⟨_, _, child⟩
  obtain ⟨headValue, middleStore, headEval⟩ := input
  obtain ⟨outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first valid environments heaps locals agrees actualTyped reference read unmapped installed headEval
  cases represented with
  | fallthrough next =>
    have same := restores next rfl
    subst next
    cases headTrace with | control headTrace =>
      obtain ⟨_, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, tailEval⟩ := sized.sequence_fallthrough headEval
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        remaining valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (transport.extend installed maps worlds frame metadata)
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld, prepend (lookupStatement?_sound found) (fun _ _ => notTail) headTrace tailTrace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_returned _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalControl.terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalControl.terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include transport in
theorem conditional_preserves (unique : NodeOccurrencesUnique source)
    (expressionPreserves : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
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
      expressionPreserves context valid conditionTree conditionFound
        environments heaps locals agrees actualTyped installed (.value conditionTrace)
    cases represented with
    | value payload =>
      obtain ⟨actualBoolean, sourceEq, coreEq⟩ := bool_fields payload
      cases sourceEq
      subst coreEq
      have branchCorrect : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
        cases boolean <;> assumption
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
  cases trace with
  | control trace =>
    obtain ⟨rfl, boolean, middle, innerContext, innerOutcome, conditionTrace, rfl, branchTrace⟩ :=
      ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form trace
    exact ⟨rfl, restored environment innerOutcome, selected conditionTrace (.control branchTrace)⟩
  | fault failed =>
    rcases ScalarStatementViews.ifThen_fault unique (lookupStatement?_sound found) form failed with
      failed | ⟨value, actualType, conditionTrace, notBoolean, _, _⟩ | ⟨boolean, middle, innerContext, conditionTrace, failed⟩
    · obtain ⟨_, finalStore, finalMap, finalWorld, conditionEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        expressionPreserves context valid conditionTree conditionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld, ?_,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [LoopRenaming.conditional]
        exact LocalControl.choose_failure _ conditionEval
    · obtain ⟨_, _, _, _, _, represented, _⟩ :=
        expressionPreserves context valid conditionTree conditionFound
          environments heaps locals agrees actualTyped installed (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, rfl, _⟩ := bool_fields payload
        exact False.elim (notBoolean trivial)
    · exact ⟨rfl, (by intro next impossible; cases impossible), selected conditionTrace (.fault failed)⟩

include transport in
theorem conditional_reflects
    (expressionReflects : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rw [LoopRenaming.conditional] at evaluated
  have input : ∃ value middleStore, Evaluates actual store (conditionCode.rename ξ) value middleStore := by
    cases evaluated with
    | caseLeft child _ | caseRight child _ => exact ⟨_, _, child⟩
  obtain ⟨conditionValue, middleStore, conditionEval⟩ := input
  obtain ⟨conditionOutcome, middle, middleMap, middleWorld, conditionTrace, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    expressionReflects context valid conditionTree conditionFound
      environments heaps locals agrees actualTyped installed conditionEval
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

      have branchCorrect : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
          (scope := scope) false (if boolean then thenBody else elseBody.getD []) expected type (if boolean then thenCode else elseCode) := by
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
          (transport.extend installed maps worlds frame metadata)
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
        selected_intro program evidence found form conditionTrace branchTrace, restored environment outcome,
        restore_rep represented environment, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds,
        frame.trans lastFrame, metadata.trans lastMetadata⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatements
