import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyEdges

/-! Pointwise five-way statement and while contracts retain independent source
sizes and original Core sizes. The strict outer budget restricts callback
obligations; it does not equate source and native costs or grant body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

abbrev Below := RecursiveNamedBoundedContracts.Below

def ExecutesAt (size : Nat) (mode : Bool) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : SourceSemantics.Context)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  match mode with
  | false => RecursiveNamedCallBounds.StatementsOutcome program size context evidence source environment before statements finalContext outcome after
  | true => RecursiveNamedCallBounds.FunctionOutcome program size context evidence source environment before statements finalContext outcome after

theorem ExecutesAt.sound {size : Nat} {mode : Bool} {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after) :
    TypedScopedStatements.Executes mode program context evidence source environment before statements finalContext outcome after := by
  cases mode with
  | false => exact RecursiveNamedCallBounds.StatementsOutcome.sound trace
  | true => exact RecursiveNamedCallBounds.FunctionOutcome.sound trace

theorem ExecutesAt.has_size {mode : Bool} {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : TypedScopedStatements.Executes mode program context evidence source environment before statements finalContext outcome after) :
    ∃ size, ExecutesAt size mode program context evidence source environment before statements finalContext outcome after := by
  cases mode with
  | false => exact RecursiveNamedCallBounds.StatementsOutcome.has_size trace
  | true => exact RecursiveNamedCallBounds.FunctionOutcome.has_size trace

inductive StatementOutcome (program : Program) (size : Nat) :
    SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      StatementId → SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {context finalContext evidence source environment before after id outcome}
      (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
      StatementOutcome program size context evidence source environment before id finalContext outcome after
  | fault {context evidence source environment before after id reason}
      (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
      StatementOutcome program size context evidence source environment before id context (.fault reason) after

theorem StatementOutcome.sound {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after := by
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

theorem StatementOutcome.has_size {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    ∃ size, StatementOutcome program size context evidence source environment before id finalContext outcome after := by
  cases trace with
  | control trace => obtain ⟨size, sized⟩ := SourceExecutionSize.StatementExecutes.has_size trace; exact ⟨size, .control sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.StatementFaults.has_size trace; exact ⟨size, .fault sized⟩

inductive WhileOutcome (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements context outcome after) :
      WhileOutcome program size context evidence source environment before condition statements outcome after
  | fault {reason after} (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
      WhileOutcome program size context evidence source environment before condition statements (.fault reason) after

/-- The selected source statement is fixed by complete occurrence lookup. -/
private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

/-- Inversion retains the original measured while child and its strict bound. -/
theorem statement_while_control {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .whileLoop condition statements)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ child innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.WhileExecutes program child context evidence source environment before condition statements innerContext innerOutcome after ∧
      child < size := by
  have shape := statement_shape unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, rfl, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- The failure child is taken from the original statement derivation. -/
theorem statement_while_fault {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId} {reason}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .whileLoop condition statements)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.WhileFaults program child context evidence source environment before condition statements reason after ∧ child < size := by
  have shape := statement_shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id :=
    fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalControl (LexicalResult)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

/-- The ordinary contract is the same validity specialization. -/
def PreservesAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  PreservesAtFor functions program evidence (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope)
      size mode statements expected type code

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after


/-- The ordinary contract is the same validity specialization. -/
def ReflectsAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ReflectsAtFor functions program evidence (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope)
      size mode statements expected type code
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
