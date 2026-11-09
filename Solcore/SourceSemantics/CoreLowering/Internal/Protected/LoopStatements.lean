import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedLexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedMatches
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations

/-!
# Protected contracts: loop statements

Loop statement trees, control and both directions, and structural elimination of imperative matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementTree
/-! One recursive guarded statement tree, with the same child family at every
loop depth. The old lexical fragment supplies return and tail leaves. Ordinary
bindings, assignments, block/if and loop transfers share the actual static
administrative context. Whole contextual extraction, for, match and unary
assignment are separate boundaries. No runtime execution is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
open GenericLexicalStatements (absentRequest initializedRequest sequence)

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (definitions : DataEnvironment)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | lexical {context scope mode statements expected type code}
      (fragment : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError
        values source expressions administrative definitions registry faults context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode statements expected type code
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : expressions context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : expressions context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | assignment {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (expressions context) scope administrative definitions assignment operator rhs)
      (errors : head.Errors registry faults)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type))

  | breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (LocalLoop.breaking type)
  | continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (LocalLoop.continuing type)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body reason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope false statements expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) definitions)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) body)

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControl
/-! Five-way guarded sequencing and scoped restoration. Actual heap progress
transports the installed entry; hidden typed values change only the runtime
environment and renaming. Loop induction stays in the common finite helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference
namespace Control
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalControl (LexicalResult selected_intro)
open TypedLexicalWhile (FlowRep Restored restored restore_rep)
open CompatibleExpressionPrimitives (bool_fields)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

abbrev Preserves := @ProtectedWhile.Body.Preserves
abbrev Reflects := @ProtectedWhile.Body.Reflects

def HeadPreserves {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    (inner : Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) false statements expected type code) :
    HeadPreserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
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
    (inner : Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) false statements expected type code) :
    HeadReflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
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
    (first : HeadPreserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (remaining : Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode rest expected type body) :
    Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
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
      | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .breaking next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .continuing next, finalHeaps, maps, worlds, frame, metadata,
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
    (first : HeadReflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (remaining : Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode rest expected type body) :
    Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
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
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.breaking _),
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.continuing _),
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
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
    (thenCorrect : Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadPreserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
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
      have branchCorrect : Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
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
    (thenCorrect : Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
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

      have branchCorrect : Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
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



/-- Use the real whole-loop head without weakening its protected input. -/
theorem of_retained_preserves {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (correct : ProtectedWhile.HeadPreserves functions program evidence (entry := entry) (administrative := administrative)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    HeadPreserves functions program evidence (entry := entry) (administrative := administrative)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ⟨same, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem of_retained_reflects {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (correct : ProtectedWhile.HeadReflects functions program evidence (entry := entry) (administrative := administrative)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    HeadReflects functions program evidence (entry := entry) (administrative := administrative)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Control
end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape
/-! Successful source control is structurally separate from source faults.
The same tree supplies this fact at every loop depth; it is not a runtime
body assumption of the final named consumer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference
open TypedScopedStatements (Executes)
open TypedLexicalWhile (ControlShape)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
  {definitions : DataEnvironment} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
theorem Tree.control_shape
    (tree : Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := by
  induction tree generalizing actualContext finalContext environment before after outcome with
  | lexical fragment => exact NamedWhileStatements.body_control_shape fragment unique executed
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique contains form first
      cases terminal

  | @breaking context scope mode id node rest expected type found form =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.breaking unique contains form head; exact .breaking environment
  | @continuing context scope mode id node rest expected type found form =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.continuing unique contains form head; exact .continuing environment
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body reason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.whileLoop unique contains form head
      rcases TypedLexicalWhile.while_control_shape innerTrace with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value

theorem Tree.control_not_fault
    (tree : Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases Tree.control_shape tree unique executed
theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
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

theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
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

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedImperativeMatchStructuralElimination
/-! Structural branch handlers bind every actual compiler field before their
payload. The motive depends only on the emitted Match indices. Header leaves
keep the actual post tree, and match leaves keep their compilation and context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch.Structural
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

abbrev AssignmentPayload := GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions
abbrev UnaryPayload := GenericForHeader.Structural.UnaryPayload
abbrev HeaderPayload := ∀ {context scope items type code},
  GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
    type (TypedForHeader.Fallthrough type) context scope items code → Prop
abbrev MatchPayload := SourceCoreCompatibleDataMatches.Context → SourceSemantics.Context → Prop
abbrev Motive := SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop

/-- This abbreviation reads only the indices of an already supplied tree. -/
abbrev GoalAt (M : Motive) {context scope position expected type code}
    (_tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) : Prop := M context scope position expected type code

structure BranchAlgebra (AP : AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := definitions)) (UP : UnaryPayload) (HP : HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative)) (MP : MatchPayload)
    (M : Motive) : Prop where
  body : ∀ {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code},
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.body syntaxTree body)

  uninitialized : ∀ {context nextContext scope mode id node binder rest expected type body payload}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder none}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)

  initialized : ∀ {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder (some initializer)}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)

  discard : ∀ {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.discard found form notTail expressionFound value remaining)

  block : ∀ {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_innerErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M inner)
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.block found form inner remaining)

  ifThen : ∀ {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_thenTreeErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M thenTree)
      (_elseTreeErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M elseTree)
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)

  breaking : ∀ {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt},
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)

  continuing : ∀ {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt},
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)

  whileLoop : ∀ {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .whileLoop condition statements}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_loopBodyErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M loopBody)
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)

  assign : ∀ {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining)
      (_headErrors : AP head),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.assign found form head remaining)


  bitNot : ∀ {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining)
      (_headErrors : UP head),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.bitNot found form head remaining)


  forLoop : ∀ {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_initialErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M initial) (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.forLoop found form initial remaining)

  initializersDone : ∀ {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (_loopErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M loopBody) (_postErrors : HP postTree),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)

  initializerUninitialized : ∀ {context nextContext scope binder rest body payload condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)

  initializerInitialized : ∀ {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)

  initializerDiscard : ∀ {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializerDiscard found value remaining)

  initializerAssign : ∀ {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining)
      (_headErrors : AP head),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializerAssign head remaining)

  initializerBitNot : ∀ {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining)
      (_headErrors : UP head),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.initializerBitNot head remaining)

  matchWith : ∀ {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_matchPayload : MP compilation context)
      (_childErrors : ∀ request member childContext valid, GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (children request member childContext valid))
      (_remainingErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M remaining),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining)


  terminalBlock : ∀ {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_innerErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M inner),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.terminalBlock unique found form inner stops issued)

  terminalIf : ∀ {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .ifThen condition thenBody (some elseBody)}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false elseBody) expected type elseCode}
      {thenStops : GenericLexicalStatements.Stopped source thenBody}
      {elseStops : GenericLexicalStatements.Stopped source elseBody}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_thenErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M thenTree)
      (_elseErrors : GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M elseTree),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M
        (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)


  terminalMatch : ∀ {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {stops : ReachableMatchContinuations.DefaultStopped source id resolution}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_matchPayload : MP compilation context)
      (_childErrors : ∀ request member childContext valid, GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (children request member childContext valid)),
      GoalAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) M (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children stops issued)

def Eliminates (AP : AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := definitions)) (UP : UnaryPayload) (HP : HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative)) (MP : MatchPayload)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∀ M : Motive, BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame)
    (globals := globals) (onError := onError) (values := values) (source := source)
    (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions)
    (administrative := administrative) AP UP HP MP M → M context scope position expected type code

/-- The original catalog recursor retains its own exact diagnostic payloads. -/
theorem of_catalog_sites {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : Tree.CatalogSites diagnosticPolicy registry faults tree) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (definitions := definitions) (administrative := administrative)
      (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
      (fun postTree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
      context scope position expected type code := by
  intro M algebra
  refine Tree.CatalogSites.rec (motive := fun {context scope position expected type code} _ _ =>
    M context scope position expected type code)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body
    exact algebra.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH
    exact algebra.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH
    exact algebra.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (_innerErrors := innerErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH
    exact algebra.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (_thenTreeErrors := thenTreeErrorsIH) (_elseTreeErrors := elseTreeErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node rest expected type found form
    exact algebra.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node rest expected type found form
    exact algebra.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH
    exact algebra.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (_loopBodyErrors := loopBodyErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH
    exact algebra.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (_initialErrors := initialErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH
    exact algebra.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (_loopErrors := loopErrorsIH) (_postErrors := postErrors)
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH
    exact algebra.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH
    exact algebra.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) (_matchPayload := ⟨catalog, patternContext⟩) (_childErrors := childErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH
    exact algebra.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (_innerErrors := innerErrorsIH)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH
    exact algebra.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (_thenErrors := thenErrorsIH) (_elseErrors := elseErrorsIH)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH
    exact algebra.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) (_matchPayload := ⟨catalog, patternContext⟩) (_childErrors := childErrorsIH)

variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- A post-header payload retains the identical tree and its own plan tokens. -/
def PreparedHeader {context scope items type code}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code) : Prop :=
  ∃ plan : EmittedDiagnosticPlan.Plan factory,
    GenericForHeader.Coupled factory invalidProjection missingDefault tree plan ∧
      EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan

/-- This static supplier sees the real Source occurrence and selected compiler
receipt. Catalog and context fields do not follow from the joint receipt. -/
def MatchSupplier (MP : MatchPayload) : Prop :=
  ∀ {context scope id node resolution scrutineeNode type matched selfReason control caseFacts}
    (_found : source.lookupStatement? id = some node)
    (_form : node.form = .matchWith resolution)
    (_scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    (_scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
    (_casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (_defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    (compilation : SourceCoreCompatibleDataMatches.Context)
    (_sameValues : compilation.values = values)
    (_sameDefinitions : compilation.definitions = definitions)
    (_allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
    (requests : List GenericMatchChildren.Request)
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
    (_ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt), MP compilation context

/-- Existing joint recursion supplies payloads from the same retained plan. -/
theorem of_coupled (MP : MatchPayload)
    (matchSupplier : MatchSupplier (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (certificates := certificates) (definitions := definitions) MP)
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (definitions := definitions) (administrative := administrative)
      (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
      (fun postTree => PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) postTree) MP
      context scope position expected type code := by
  intro M algebra
  have result : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope position expected type code := by
    refine Coupled.rec (motive := fun {context scope position expected type code} _ plan _ =>
      EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope position expected type code)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ coupled
    · intro context scope mode statements expected type code syntaxTree body  tokens
      exact algebra.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
    · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerPlan innerCoupled remainingPlan remainingCoupled innerCoupledIH remainingCoupledIH tokens
      cases tokens with
      | pair innerTokens remainingTokens =>
        exact algebra.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (_innerErrors := innerCoupledIH innerTokens) (_remainingErrors := remainingCoupledIH remainingTokens)
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreePlan thenTreeCoupled elseTreePlan elseTreeCoupled remainingPlan remainingCoupled thenTreeCoupledIH elseTreeCoupledIH remainingCoupledIH tokens
      cases tokens with
      | pair thenTokens restTokens => cases restTokens with
        | pair elseTokens remainingTokens =>
          exact algebra.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (_thenTreeErrors := thenTreeCoupledIH thenTokens) (_elseTreeErrors := elseTreeCoupledIH elseTokens) (_remainingErrors := remainingCoupledIH remainingTokens)
    · intro context scope mode id node rest expected type found form  tokens
      exact algebra.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    · intro context scope mode id node rest expected type found form  tokens
      exact algebra.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyPlan loopBodyCoupled remainingPlan remainingCoupled loopBodyCoupledIH remainingCoupledIH tokens
      cases tokens with
      | pair loopTokens remainingTokens =>
        exact algebra.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (_loopBodyErrors := loopBodyCoupledIH loopTokens) (_remainingErrors := remainingCoupledIH remainingTokens)
    · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingPlan remainingCoupled site origin sameToken sourceTyped rightTyped profile fuel prepared remainingCoupledIH tokens
      cases tokens with
      | pair remainingTokens _ =>
        exact algebra.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingCoupledIH remainingTokens) (_headErrors := .intro site origin sameToken sourceTyped rightTyped profile fuel prepared)
    · intro context scope mode id node assignment rest expected type body found form head remaining remainingPlan remainingCoupled writable bare profile remainingCoupledIH tokens
      cases tokens with
      | pair remainingTokens unaryTokens => cases unaryTokens with
        | unary _ _ _ _ site origin same =>
          exact algebra.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingCoupledIH remainingTokens) (_headErrors := .intro writable bare profile site origin same)
    · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialPlan initialCoupled remainingPlan remainingCoupled initialCoupledIH remainingCoupledIH tokens
      cases tokens with
      | pair initialTokens remainingTokens =>
        exact algebra.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (_initialErrors := initialCoupledIH initialTokens) (_remainingErrors := remainingCoupledIH remainingTokens)
    · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopBodyPlan loopCoupled postTreePlan postCoupled loopCoupledIH tokens
      cases tokens with
      | pair loopTokens postTokens =>
        exact algebra.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (_loopErrors := loopCoupledIH loopTokens) (_postErrors := ⟨postTreePlan, postCoupled, postTokens⟩)
    · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingPlan remainingCoupled remainingCoupledIH tokens
      exact algebra.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (_remainingErrors := remainingCoupledIH tokens)
    · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingPlan remainingCoupled site origin sameToken sourceTyped rightTyped profile fuel prepared remainingCoupledIH tokens
      cases tokens with
      | pair remainingTokens _ =>
        exact algebra.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingCoupledIH remainingTokens) (_headErrors := .intro site origin sameToken sourceTyped rightTyped profile fuel prepared)
    · intro context scope assignment rest body condition post statements expected type head remaining remainingPlan remainingCoupled writable bare profile remainingCoupledIH tokens
      cases tokens with
      | pair remainingTokens unaryTokens => cases unaryTokens with
        | unary _ _ _ _ site origin same =>
          exact algebra.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingCoupledIH remainingTokens) (_headErrors := .intro writable bare profile site origin same)
    · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childPlans childCoupled remainingPlan remainingCoupled childCoupledIH remainingCoupledIH tokens
      cases tokens with
      | pair selectedTokens remainingTokens => cases selectedTokens with
        | selected childTokens =>
          exact algebra.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) (_childErrors := fun request member childContext valid => childCoupledIH request member childContext valid (childTokens request member childContext valid)) (_remainingErrors := remainingCoupledIH remainingTokens) (_matchPayload := matchSupplier found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary)
    · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerPlan innerCoupled innerCoupledIH tokens
      exact algebra.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (_innerErrors := innerCoupledIH tokens)
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenTreePlan thenCoupled elseTreePlan elseCoupled thenCoupledIH elseCoupledIH tokens
      cases tokens with
      | pair thenTokens elseTokens =>
        exact algebra.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (_thenErrors := thenCoupledIH thenTokens) (_elseErrors := elseCoupledIH elseTokens)
    · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childPlans childCoupled childCoupledIH tokens
      cases tokens with
      | selected childTokens =>
        exact algebra.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) (_childErrors := fun request member childContext valid => childCoupledIH request member childContext valid (childTokens request member childContext valid)) (_matchPayload := matchSupplier found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary)
  exact result tokens

end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch.Structural
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementPreservation
/-! Actual lexical tree induction transports the guarded entry through source
allocations and hidden native slots. No canonical heap/environment typing is
used to manufacture installed code, captures or history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedLexicalStatements
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized sequence_rename allocate_absent allocate_initialized valid_extend)

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
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves [FunctionCalls.FaultTokens faults]
    (expressionPreserves : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree layouts owner active frame globals onError values source expressions administrative ambient.definitions registry faults
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
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
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction tree generalizing mapping world environment canonical actual before after store ξ actualContext contextLocation native outcome resultContext with
  | lexical fragment =>
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
      ProtectedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations program evidence transport bindings
        expressionPreserves fragment contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨value, finalStore, finalMap, finalWorld, completed, FlowRep.of_lexical represented,
      finalHeaps, maps, worlds, frame, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        expressionPreserves _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        expressionPreserves _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
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
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        expressionPreserves _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionPreserves _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
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

  | block found form inner remaining innerIH remainingIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.conditional_preserves transport unique expressionPreserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace


  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head headErrors remaining ih =>
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence transport
          (expressionPreserves _ contextValid) faithful observations head
          environments heaps locals agrees actualTyped installed assigned
      have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ :=
          ProtectedAssignmentHeads.Head.preserves_fault functions extension program evidence transport
            (expressionPreserves _ contextValid) faithful observations head
            environments heaps locals agrees actualTyped installed headErrors
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

  | @breaking context scope mode id node rest expected type found form =>
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.of_retained_preserves functions program evidence (ProtectedWhile.Body.while_preserves functions program evidence transport
        (expressionPreserves _ contextValid) found form conditionFound conditionTree nativeTyped unique loopIH)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementReflection
/-! Actual lexical tree induction transports the guarded entry through source
allocations and hidden native slots. No canonical heap/environment typing is
used to manufacture installed code, captures or history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedLexicalStatements
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized sequence_rename allocate_absent allocate_initialized valid_extend)

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
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations transport bindings runtimeViews in
theorem Tree.reflects [FunctionCalls.FaultTokens faults]
    (expressionPreserves : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry)
    (expressionReflects : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree layouts owner active frame globals onError values source expressions administrative ambient.definitions registry faults
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
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
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction tree generalizing mapping world environment canonical actual before store ξ actualContext contextLocation native finalStore value with
  | lexical fragment =>
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
      ProtectedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews program evidence transport bindings
        expressionPreserves expressionReflects fragment contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, sourceTrace, FlowRep.of_lexical represented,
      finalHeaps, maps, worlds, frame, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      expressionReflects _ contextValid initial initialFound
        environments heaps locals agrees actualTyped installed initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        expressionReflects _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨context, _, after, finalMap, finalWorld, TypedScopedStatements.head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionReflects _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
            ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata)
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            TypedScopedStatements.prepend (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩

  | block found form inner remaining innerIH remainingIH =>
    exact Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (Control.block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (Control.conditional_reflects transport expressionReflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head headErrors remaining ih =>
    rcases ProtectedAssignmentHeads.Head.reflects functions extension program evidence transport
      (expressionPreserves _ contextValid) (expressionReflects _ contextValid) faithful observations
      head environments heaps locals agrees actualTyped installed runtimeViews headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩
    · exact ⟨context, .fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
        finalHeaps, maps, worlds, preservation, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tail,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩

  | @breaking context scope mode id node rest expected type found form =>
    have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
      simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
      simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH =>
    exact Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals)  found (by intro expression; simp [form])
      (Control.of_retained_reflects functions program evidence (ProtectedWhile.Body.while_reflects functions program evidence transport
        (expressionReflects _ contextValid) found form conditionFound conditionTree nativeTyped loopIH
          (fun executed => loopBody.control_not_fault unique executed))) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
end
