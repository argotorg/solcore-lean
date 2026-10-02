import Solcore.SourceSemantics.CoreLowering.GenericImperativeForPost
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.ProtectedBitNotStatements
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementReflection

/-! The existing statements/initializers grammar supplies one recursive induction.
Every ordinary child consumes its actual protected entry; for and while delegate
to their shared finite helpers. Static source/native/error receipts remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep restored restore_rep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)
open GenericImperativeFor (Tree Position)
open ProtectedWhile.Body (Preserves Reflects)
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
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)

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
    type (fun context scope code => ProtectedFor.Body.LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

abbrev ReflectingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

include definitions registered extension transport bindings meaning faithful observations in
theorem header_preserves_reachable (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨header, errors⟩ := headers
  cases trace with
  | control executed =>
    obtain ⟨rfl, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop⟩ :=
      ForSourceViews.success unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := by cases loop <;> rfl
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
      ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence transport bindings meaning faithful observations header
        valid environments heaps locals agrees actualTyped reference read unmapped installed initialization
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.control loop)
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩
  | fault failed =>
    rcases ForSourceViews.fault unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, fault⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata⟩ :=
        ProtectedForHeader.Tree.preserves_fault_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations header errors
          valid environments heaps locals agrees actualTyped reference read unmapped installed fault
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata⟩
    · obtain ⟨loopContext, loopEnvironment, initialized, initialization, loop⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
        ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence transport bindings meaning faithful observations header
          valid environments heaps locals agrees actualTyped reference read unmapped installed initialization
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
        tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.fault loop)
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
        frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩

include definitions registered extension transport bindings meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem header_preserves (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeader (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  apply header_preserves_reachable (functions := functions) (headers := by rcases headers with ⟨header, errors⟩; exact ⟨header, errors.reachable⟩)
  all_goals assumption

include extension meaning transport bindings definitions registered faithful observations in
theorem loop_preserves_reachable (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    ProtectedFor.Body.LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  have result := ProtectedFor.Body.loop_preserves functions program evidence transport (meaning _ valid)
    conditionFound conditionTree typed unique correct
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        mapping world before after store finalContext finalEnvironment guarded continued execution
      exact ProtectedForHeader.post_preserves functions definitions registered extension program evidence transport bindings meaning faithful observations postTree
        actualValid actualAgrees actualReference guarded continued execution)
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        mapping world before after store finalContext reason guarded continued execution
      exact ProtectedForHeader.post_fault_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations postTree postErrors
        actualValid actualAgrees actualReference guarded continued execution)
  exact result valid environments heaps locals agrees actualTyped reference read unmapped installed trace

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev PreservesAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeader (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeader (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include extension meaning transport bindings definitions registered faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem loop_preserves (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (correct : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    ProtectedFor.Body.LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_preserves_reachable (functions := functions) (postErrors := postErrors.reachable)
  all_goals assumption

include definitions registered extension transport bindings meaning faithful observations in
theorem preservesAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      ProtectedLexicalStatements.Tree.preserves functions definitions registered program evidence transport bindings meaning body contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
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
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
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
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ contextValid child expressionFound
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

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.conditional_preserves transport unique meaning (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace


  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.of_retained_preserves functions program evidence (ProtectedWhile.Body.while_preserves functions program evidence transport
        (meaning _ contextValid) found form conditionFound conditionTree nativeTyped unique loopIH)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
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
          (meaning _ contextValid) faithful observations head
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
          ProtectedAssignmentHeads.Head.preserves_fault_reachable functions extension program evidence transport
            (meaning _ contextValid) faithful observations head
            environments heaps locals agrees actualTyped installed (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors)
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedBitNotStatements.assignment_preserves functions program evidence observations transport
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (header_preserves_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_preserves_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations unique
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH
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

include definitions registered extension transport bindings meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem preservesAt (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    PreservesAt (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply preservesAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
