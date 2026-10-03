import Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts

/-! Measured match views and pointwise child contracts keep original source
and Core sizes separate. Only actual child derivations supply a budget bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open TypedLexicalWhile (FlowRep Restored restored ValuesContext)
open TypedLexicalControl (LexicalResult)
inductive TraceBelow (budget : Nat) (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (resolution : MatchResolution) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | scrutineeFault {reason after exprSize}
      (fault : SourceExecutionSize.ExpressionFaults program exprSize context evidence source environment before resolution.scrutinee reason after) (smaller : exprSize < budget) :
      TraceBelow budget program context evidence source environment before resolution (.fault reason) after
  | patternFault {node value middle hidden location exprSize}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : SourceExecutionSize.ExpressionEvaluates program exprSize context evidence source environment before resolution.scrutinee value middle) (exprSmaller : exprSize < budget)
      (allocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (fault : Dynamic.MatchCasesPatternFault context value resolution.cases) :
      TraceBelow budget program context evidence source environment before resolution (.fault .invalidPattern) hidden
  | arm {node value middle hidden location statements bindings armContext armEnvironment bound finalContext outcome after exprSize bodySize}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : SourceExecutionSize.ExpressionEvaluates program exprSize context evidence source environment before resolution.scrutinee value middle) (exprSmaller : exprSize < budget)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
      (extended : BindersExtend source.owner context (bindings.map Prod.fst) armContext)
      (allocated : Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
      (body : RecursiveNamedCallBounds.StatementsOutcome program bodySize armContext evidence source armEnvironment bound statements finalContext outcome after) (bodySmaller : bodySize < budget) :
      TraceBelow budget program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | default {node value middle hidden location statements finalContext outcome after exprSize bodySize}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : SourceExecutionSize.ExpressionEvaluates program exprSize context evidence source environment before resolution.scrutinee value middle) (exprSmaller : exprSize < budget)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
      (body : RecursiveNamedCallBounds.StatementsOutcome program bodySize context evidence source environment hidden statements finalContext outcome after) (bodySmaller : bodySize < budget) :
      TraceBelow budget program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | noBranch {node value middle hidden location exprSize}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : SourceExecutionSize.ExpressionEvaluates program exprSize context evidence source environment before resolution.scrutinee value middle) (exprSmaller : exprSize < budget)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
      TraceBelow budget program context evidence source environment before resolution (.fallthrough environment) hidden

theorem TraceBelow.sound {budget : Nat} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (trace : TraceBelow budget program context evidence source environment before resolution outcome after) :
    DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after := by
  cases trace with
  | scrutineeFault fault _ => exact .scrutineeFault fault.sound
  | patternFault found evaluated _ allocated fault => exact .patternFault found evaluated.sound allocated fault
  | arm found evaluated _ hidden selected extended allocated body _ =>
    exact .arm found evaluated.sound hidden selected extended allocated body.sound
  | default found evaluated _ hidden selected body _ => exact .default found evaluated.sound hidden selected body.sound
  | noBranch found evaluated _ hidden selected => exact .noBranch found evaluated.sound hidden selected

private theorem original_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) :
    ∀ other, ContainsStatement source id other → other.form = node.form := by
  intro other present
  exact congrArg StatementNode.form (Option.some.inj ((lookupStatement?_complete unique present).symm.trans found))

theorem of_outcome {program : Program} {size budget : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {resolution : MatchResolution}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) (within : size ≤ budget)
    (executed : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ TraceBelow budget program context evidence source environment before resolution outcome after := by
  have shapes := original_shape unique found
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  clear found
  cases executed with
  | control executed =>
    cases executed <;> have actualForm := shapes _ (by assumption) <;> simp_all
    · exact .arm (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
    · exact .default (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption) (.control (by assumption))
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
    · exact .noBranch (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption)
  | fault failed =>
    refine ⟨rfl, ?_⟩
    cases failed
    all_goals first
      | exact False.elim (present (by assumption))
      | have actualForm := shapes _ (by assumption); simp_all
    · exact .scrutineeFault (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
    · exact .patternFault (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption)
    · exact .arm (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
    · exact .default (by assumption) (by assumption)
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        (by assumption) (by assumption) (.fault (by assumption))
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry} (budget : Nat)

def ArmPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program evidence validity (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ArmPreservesBelowFor (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def ArmReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program evidence validity (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ArmReflectsBelowFor (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program evidence validity (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  DefaultPreservesBelowFor (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program evidence validity (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  DefaultReflectsBelowFor (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)


namespace Head
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  HeadPreservesAtFor (entry := entry) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code
    (values := values) (source := source) (context := context) (registry := registry) (administrative := administrative)
    (frameLayout := frameLayout) (globals := globals) (faults := faults)

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  HeadReflectsAtFor (entry := entry) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code
    (values := values) (source := source) (context := context) (registry := registry) (administrative := administrative)
    (frameLayout := frameLayout) (globals := globals) (faults := faults)

end Head


/-- The scrutinee bound comes from the actual outer case evaluation. -/
theorem initial_evaluation_sized {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {references : Renaming} {binder : TypedBinder}
    {outputType payloadType : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized allocator source scope references binder
      outputType payloadType initializer body = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value} {size : Nat}
    (completed : EvaluationSize size environment before (code.rename ξ) result after) :
    ∃ child value middle, child < size ∧
      EvaluationSize child environment before (initializer.rename ξ) value middle := by
  cases allocator with
  | none =>
    cases accepted
    rw [LoopRenaming.letInitialized] at completed
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, _, by omega, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, _, by omega, evaluated⟩
  | some allocate =>
    unfold SourceCoreSourceCells.letInitialized at accepted
    obtain ⟨allocation, generated, same⟩ := CompatibleEncoding.bind_ok accepted
    cases same
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, _, by omega, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, _, by omega, evaluated⟩

theorem Certificate.initial_evaluation_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : SourceCoreSourceCells.Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value} {size : Nat}
    (completed : EvaluationSize size environment before (code.rename ξ) result after) :
    ∃ node lowered child value middle, source.lookupExpression? resolution.scrutinee = some node ∧
      expressionCertificate scope resolution.scrutinee lowered ∧ child < size ∧
      EvaluationSize child environment before (lowered.expression.rename ξ) value middle := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    obtain ⟨child, value, middle, smaller, evaluated⟩ := RecursiveNamedMatchSourceBounds.initial_evaluation_sized hiddenCompiled completed
    exact ⟨_, _, child, value, middle, found, expression, smaller, evaluated⟩


/-- Erasure is used only when adapting a previously proved unrestricted law. -/
theorem trace_has_budget {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (trace : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after) :
    ∃ budget, TraceBelow budget program context evidence source environment before resolution outcome after := by
  cases trace with
  | scrutineeFault fault =>
    obtain ⟨n, measured⟩ := SourceExecutionSize.ExpressionFaults.has_size fault
    exact ⟨n + 1, .scrutineeFault measured (by omega)⟩
  | patternFault found evaluated allocated fault =>
    obtain ⟨n, measured⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluated
    exact ⟨n + 1, .patternFault found measured (by omega) allocated fault⟩
  | arm found evaluated hidden selected extended allocated body =>
    obtain ⟨n, measured⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluated
    obtain ⟨m, bodyMeasured⟩ := RecursiveNamedCallBounds.StatementsOutcome.has_size body
    exact ⟨n + m + 1, .arm found measured (by omega) hidden selected extended allocated bodyMeasured (by omega)⟩
  | default found evaluated hidden selected body =>
    obtain ⟨n, measured⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluated
    obtain ⟨m, bodyMeasured⟩ := RecursiveNamedCallBounds.StatementsOutcome.has_size body
    exact ⟨n + m + 1, .default found measured (by omega) hidden selected bodyMeasured (by omega)⟩
  | noBranch found evaluated hidden selected =>
    obtain ⟨n, measured⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluated
    exact ⟨n + 1, .noBranch found measured (by omega) hidden selected⟩

section UnboundedAdapters
variable {functions program parent control evidence resolution bodyCertificate expected type}

theorem ArmPreservesBelow.of_unbounded {outerScope : Scope}
    (meaning : CompatibleMatchMeaning.ArmPreservesScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    ArmPreservesBelow (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected selectedBody armContext staticFinal facts extended typed child smaller
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact meaning sameScope selected selectedBody extended typed valid environments heaps locals agrees actualTyped reference read unmapped trace.sound

theorem ArmReflectsBelow.of_unbounded {outerScope : Scope}
    (meaning : CompatibleMatchMeaning.ArmReflectsScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    ArmReflectsBelow (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected selectedBody armContext staticFinal facts extended typed child smaller
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed completed
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning sameScope selected selectedBody extended typed valid environments heaps locals agrees actualTyped reference read unmapped completed.sound
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size (mode := false) trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, measured, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

theorem DefaultPreservesBelow.of_unbounded {outerScope : Scope}
    (meaning : CompatibleMatchMeaning.DefaultPreservesScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    DefaultPreservesBelow (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected selectedBody staticFinal facts typed child smaller
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact meaning sameScope selected selectedBody typed valid environments heaps locals agrees actualTyped reference read unmapped trace.sound

theorem DefaultReflectsBelow.of_unbounded {outerScope : Scope}
    (meaning : CompatibleMatchMeaning.DefaultReflectsScoped functions program parent control evidence resolution bodyCertificate expected type outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    DefaultReflectsBelow (entry := entry) functions program parent control evidence resolution bodyCertificate expected type budget outerScope (source := source) (solved := solved) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected selectedBody staticFinal facts typed child smaller
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed completed
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning sameScope selected selectedBody typed valid environments heaps locals agrees actualTyped reference read unmapped completed.sound
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size (mode := false) trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, measured, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

end UnboundedAdapters

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds
