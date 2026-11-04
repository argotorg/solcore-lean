import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForFinite
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericMatches
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl

/-!
# Recursive named rows: statement contracts

Contracts of loops, lexical statements, `for` and match prefixes, with their Source bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
/-! Statement-list inversion retains the original head and tail source
witnesses. A function singleton has no tail premise; only its empty nil
continuation is constructed, with size one bounded by the positive head.
These source sizes say nothing about native execution sizes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
open Frontend SourceInference
open RecursiveNamedLoopContracts RecursiveNamedCallBounds

inductive Cons (program : Program) (mode : Bool) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (rest : List StatementId) (size : Nat) :
    SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | next {headSize tailSize middleContext nextEnvironment middle finalContext outcome after}
      (head : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id
        middleContext (.fallthrough nextEnvironment) middle)
      (tail : ExecutesAt tailSize mode program middleContext evidence source nextEnvironment middle rest finalContext outcome after)
      (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
      Cons program mode context evidence source environment before id rest size finalContext outcome after
  | terminal {headSize finalContext outcome after}
      (head : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id finalContext outcome after)
      (control : Dynamic.TerminalControl outcome) (headSmaller : headSize < size) :
      Cons program mode context evidence source environment before id rest size finalContext outcome after
  | fault {headSize reason after}
      (head : SourceExecutionSize.StatementFaults program headSize context evidence source environment before id reason after)
      (headSmaller : headSize < size) :
      Cons program mode context evidence source environment before id rest size context (.fault reason) after

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) :
    ∀ other, ContainsStatement source id other → other = node := by
  intro other present
  exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))

/-- Every ordinary cons form uses its original measured children. The tail
expression singleton is handled separately by the lexical grammar. -/
theorem cons_inv {program : Program} {mode : Bool} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    Cons program mode context evidence source environment before id rest size finalContext outcome after := by
  cases mode with
  | false =>
    cases trace with
    | control trace => cases trace with
      | cons head tail =>
        exact Cons.next (mode := false) head (.control tail)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
      | terminal head control => exact .terminal head control (SourceExecutionSize.child_lt_stepSize (by simp))
    | fault trace => cases trace with
      | head failed => exact .fault failed (SourceExecutionSize.child_lt_stepSize (by simp))
      | tail head failed =>
        exact Cons.next (mode := false) head (.fault failed)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | true =>
    cases trace with
    | control trace => cases trace with
      | tailExpression present form child =>
        have same := statement_shape unique contains _ present
        exact False.elim (notTail rfl rfl _ (same ▸ form))
      | singleton present notTailHead head =>
        cases outcome with
        | fallthrough nextEnvironment =>
          exact Cons.next (mode := true) head (.control .nil)
            (SourceExecutionSize.child_lt_stepSize (by simp)) (by
            have positive := head.positive
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
            omega)
        | returned value => exact .terminal head (.returned value) (SourceExecutionSize.child_lt_stepSize (by simp))
        | breaking nextEnvironment => exact .terminal head (.breaking nextEnvironment) (SourceExecutionSize.child_lt_stepSize (by simp))
        | continuing nextEnvironment => exact .terminal head (.continuing nextEnvironment) (SourceExecutionSize.child_lt_stepSize (by simp))
        | fault reason => exact .terminal head (.fault reason) (SourceExecutionSize.child_lt_stepSize (by simp))
      | cons head tail =>
        exact Cons.next (mode := true) head (.control tail)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
      | terminal head control => exact .terminal head control (SourceExecutionSize.child_lt_stepSize (by simp))
    | fault trace => cases trace with
      | singleton failed | head failed => exact .fault failed (SourceExecutionSize.child_lt_stepSize (by simp))
      | tailExpression present form child =>
        have same := statement_shape unique contains _ present
        exact False.elim (notTail rfl rfl _ (same ▸ form))
      | tail head failed =>
        exact Cons.next (mode := true) head (.fault failed)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

private theorem shape_form {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) : ∀ other, ContainsStatement source id other → other.form = form := by
  intro other present
  exact (statement_shape unique contains other present) ▸ same

section StatementChildren
variable {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)

include unique contains in
theorem return_value {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ child value, outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem expression_value {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child value,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem initialized_value {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ child value middle location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem block_value {statements : List StatementId} (form : node.form = .block statements)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ child innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.StatementsExecute program child context evidence source environment before statements innerContext innerOutcome after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, rfl, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

variable {reason : Dynamic.SemanticFault}

private theorem not_missing (found : ContainsStatement source id node) : ¬ Dynamic.StatementMissing source id :=
  fun absent => Dynamic.StatementAbsentIn.excludes_contains absent found

include unique contains in
theorem return_fault {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem expression_fault {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem initialized_fault {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before initializer reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem block_fault {statements : List StatementId} (form : node.form = .block statements)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child innerContext,
      SourceExecutionSize.StatementsFault program child context evidence source environment before statements innerContext reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end StatementChildren

/-- A real tail expression keeps its original expression child. An ordinary
singleton fault passes through the original measured statement fault first. -/
theorem tail_inv {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (trace : FunctionOutcome program size context evidence source environment before [id] finalContext outcome after) :
    finalContext = context ∧ ∃ child expressionOutcome,
      ExpressionOutcome program child context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) ∧ child < size := by
  cases trace with
  | control trace => cases trace with
    | tailExpression present same evaluated =>
      rw [statement_shape unique contains _ present, form] at same
      cases same
      exact ⟨rfl, _, _, .value evaluated, rfl, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | singleton present notTail executed =>
      have same := statement_shape unique contains _ present
      exact False.elim (notTail _ (same ▸ form))
  | fault trace => cases trace with
    | tailExpression present same failed =>
      rw [statement_shape unique contains _ present, form] at same
      cases same
      exact ⟨rfl, _, _, .fault failed, rfl, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | singleton failed =>
      obtain ⟨child, evaluated, smaller⟩ := expression_fault unique contains form failed
      exact ⟨rfl, child, .fault _, .fault evaluated, rfl,
        Nat.lt_trans smaller (SourceExecutionSize.child_lt_stepSize (by simp))⟩

inductive IfTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (thenBody : List StatementId)
    (elseBody : Option (List StatementId)) (size : Nat) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | conditionFault {child reason after}
      (failed : SourceExecutionSize.ExpressionFaults program child context evidence source environment before condition reason after)
      (smaller : child < size) : IfTrace program context evidence source environment before condition thenBody elseBody size (.fault reason) after
  | conditionType {child value actual after}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before condition value after)
      (notBoolean : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual)
      (smaller : child < size) : IfTrace program context evidence source environment before condition thenBody elseBody size (.fault (.typeMismatch .bool actual)) after
  | branch {conditionSize bodySize boolean middle finalContext outcome after}
      (conditionEvaluated : SourceExecutionSize.ExpressionEvaluates program conditionSize context evidence source environment before condition (.bool boolean) middle)
      (body : StatementsOutcome program bodySize context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) finalContext outcome after)
      (conditionSmaller : conditionSize < size) (bodySmaller : bodySize < size) :
      IfTrace program context evidence source environment before condition thenBody elseBody size (Dynamic.restoreControl environment outcome) after

/-- Conditional inversion retains the real condition and selected branch.
The missing else branch has only a size-one nil continuation. -/
theorem if_inv {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ IfTrace program context evidence source environment before condition thenBody elseBody size outcome after := by
  have shape := shape_form unique contains form
  have present : ¬ Dynamic.StatementMissing source id := not_missing contains
  clear contains form
  cases trace with
  | control trace =>
    cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
    · exact .branch (boolean := true) (by assumption) (.control (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
    · apply IfTrace.branch (boolean := false) (elseBody := none)
        (environment := environment) (outcome := .fallthrough environment) (finalContext := context)
        (by assumption) (.control .nil)
      · exact SourceExecutionSize.child_lt_stepSize (by simp)
      · have positive := (show SourceExecutionSize.ExpressionEvaluates _ _ _ _ _ _ _ _ _ _ from by assumption).positive
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
        omega
    · exact .branch (boolean := false) (by assumption) (.control (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault trace =>
    cases trace
    all_goals first
      | exact False.elim (present (by assumption))
      | have actualForm := shape _ (by assumption); simp_all
    · exact .conditionFault (by assumption) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .conditionType (by assumption) (by assumption) (by assumption) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .branch (boolean := true) (by assumption) (.fault (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .branch (boolean := false) (by assumption) (.fault (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
/-! Pointwise contracts keep the existing three-way lexical FlowRep, exact
installed authority and lexical extension. Source and Core sizes are separate;
these contracts do not turn bounded hypotheses into unbounded meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedScopedStatements (FlowRep)
open TypedLexicalControl (Restored LexicalResult)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Below := RecursiveNamedBoundedContracts.Below

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def PreservesAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  PreservesAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def ReflectsAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ReflectsAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadPreservesAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadReflectsAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
/-! Pointwise for contracts retain independent measured source loop/post
outcomes and original Core post/loop witnesses. A fixed outer budget selects
strictly smaller callbacks. The actual six post slots remain observed values;
no continuation agreement supplies a size or unrestricted body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (LoopState Progress SourceLoop postValues)
abbrev Below := RecursiveNamedBoundedContracts.Below

inductive ForOutcome (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements context outcome after) :
      ForOutcome program size context evidence source environment before condition post statements outcome after
  | fault {reason after} (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
      ForOutcome program size context evidence source environment before condition post statements (.fault reason) after

theorem ForOutcome.sound {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : ForOutcome program size context evidence source environment before condition post statements outcome after) :
    SourceLoop program context evidence source environment before condition post statements outcome after := by
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

theorem ForOutcome.has_size {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : SourceLoop program context evidence source environment before condition post statements outcome after) :
    ∃ size, ForOutcome program size context evidence source environment before condition post statements outcome after := by
  cases trace with
  | control trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopExecutes.has_size trace; exact ⟨size, .control sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopFaults.has_size trace; exact ⟨size, .fault sized⟩

abbrev State (entry : ProtectedExpressionMeaning.Entry) (values : ValuesContext)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop :=
  LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body post reason mapping world heap store ∧
  entry scope mapping world heap store canonical

def PostPreservesAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostFaultsAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostReflectsAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)

variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

def LoopPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
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
    (_trace : ForOutcome program size context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopPreservesAt (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopPreservesAtFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    size (scope := scope) condition post statements expected type code

def LoopReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
      ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopReflectsAt (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopReflectsAtFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    size (scope := scope) condition post statements expected type code

theorem post_computation_size {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postSize postStore postValue, postSize < size ∧
      EvaluationSize postSize (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore :=
  ForHeaderNativeBounds.post_computation_sized continued evaluation bodyEval

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts
/-! The actual match prefix retains the ordered canonical additions and an
original strict native continuation. Installed catalog observations travel
through real source allocations and protected native effects. These are
runtime prefix lemmas, not additional static body execution assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix

/-- Canonical binders are prepended in their actual order; hidden evaluation
slots occur only in the separate actual environment and renaming. -/
theorem installed {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    {scope nextScope : Scope} {canonical nextCanonical : Environment}
    {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store}
    (initial : entry scope mapping world before store canonical)
    (spine : CanonicalPrefix scope canonical nextScope nextCanonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    entry nextScope finalMap finalWorld after finalStore nextCanonical := by
  obtain ⟨addedScope, addedValues, same, rfl, rfl⟩ := spine
  have original := transport.extend initial maps worlds frame metadata
  induction addedScope generalizing addedValues with
  | nil => cases addedValues <;> simp_all
  | cons binding rest ih =>
    cases addedValues with
    | nil => simp at same
    | cons value values =>
      have previous := ih (addedValues := values) (by simpa using same)
      exact bindings.prepend previous

/-- Exiting a selected arm restores the original canonical environment while
retaining every real heap/store effect. No final body's size is inferred. -/
theorem restored {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry)
    {scope : Scope} {canonical : Environment} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store}
    (initial : entry scope mapping world before store canonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    entry scope finalMap finalWorld after finalStore canonical :=
  transport.extend initial maps worlds frame metadata

theorem selected_prefix_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, agreement⟩ :=
    CompatibleMatchTypedSelectionPrefix.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
      catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped
      reference read unmapped evaluated selectedSource
  have metadata : Dynamic.HeapMetadataExtend heap finalHeap := by
    have hidden := Dynamic.HeapMetadataExtend.of_allocation allocated
    cases selectedBody with
    | arm _ allocated _ => exact hidden.trans (GenericLexicalContext.binders_metadata allocated)
    | default _ => exact hidden
    | noBranch => exact hidden
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine,
    installed transport bindings initial spine maps worlds frame metadata, agreement⟩


theorem selected_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact selected_prefix_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource transport bindings initial

theorem success_prefix_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩ :=
    selected_prefix_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated selected transport bindings initial
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩


theorem success_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact success_prefix_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
/-! Views for the unchanged lexical Tree retain original source children and
their strict costs. Pure allocation stays an ordinary source receipt. Reflected
source costs are independent of the native costs used to select child laws. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
open Frontend SourceInference
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (ExpressionOutcome)

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) :
    ∀ other, ContainsStatement source id other → other.form = node.form := by
  intro other present
  have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  exact congrArg StatementNode.form same

private theorem extension_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem absent_statement {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all

/-- An absent binding retains the original tail witness, including a fault
after the successful allocation. -/
theorem absent {mode : Bool} {program : Program} {size : Nat} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ location middle tailSize, Dynamic.Heap.Allocates before binder.scheme.body none location middle ∧
      ExecutesAt tailSize mode program nextContext evidence source ((binder.id, location) :: environment)
        middle rest finalContext outcome after ∧ tailSize < size := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head tail _ tailSmaller =>
    obtain ⟨extension, location, same, allocated⟩ := absent_statement unique found form head
    cases extension_eq extended extension
    cases same
    exact ⟨location, _, _, allocated, tail, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, _, same, _⟩ := absent_statement unique found form head
    cases same; cases terminal
  | fault failed _ =>
    exact False.elim (ScalarStatementViews.letUninitialized_cannot_fault unique (lookupStatement?_sound found) form mono failed.sound)

/-- An initialized binding retains both original initializer and tail costs.
Initializer failure precedes the allocation and context extension. -/
theorem initialized {mode : Bool} {program : Program} {size : Nat} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ child reason, finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before initializer reason after ∧ child < size) ∨
    (∃ child tailSize value location middle allocatedHeap,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      ExecutesAt tailSize mode program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after ∧ child < size ∧ tailSize < size) := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head tail headSmaller tailSmaller =>
    obtain ⟨extension, child, value, middle, location, same, initial, allocated, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_value unique (lookupStatement?_sound found) form mono head
    cases extension_eq extended extension
    cases same
    exact .inr ⟨child, _, value, location, middle, _, initial, allocated, tail, Nat.lt_trans smaller headSmaller, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, _, _, _, _, same, _, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_value unique (lookupStatement?_sound found) form mono head
    cases same; cases terminal
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_fault unique (lookupStatement?_sound found) form mono failed
    exact .inl ⟨child, _, rfl, rfl, initial, Nat.lt_trans childSmaller smaller⟩

/-- Discard evaluates its expression before the original tail. -/
theorem discard {mode : Bool} {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {semicolon : Bool} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon) (guard : (!semicolon && mode && rest.isEmpty) = false)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ child reason, finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size) ∨
    (∃ child tailSize value middle,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value middle ∧
      ExecutesAt tailSize mode program context evidence source environment middle rest finalContext outcome after ∧
      child < size ∧ tailSize < size) := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (TypedScopedStatements.not_tail form guard) trace
  cases view with
  | next head tail headSmaller tailSmaller =>
    obtain ⟨rfl, same, child, value, initial, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.expression_value unique (lookupStatement?_sound found) form head
    cases Dynamic.ControlOutcome.fallthrough.inj same
    exact .inr ⟨child, _, value, _, initial, tail, Nat.lt_trans smaller headSmaller, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, same, _, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.expression_value unique (lookupStatement?_sound found) form head
    cases same; cases terminal
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.expression_fault unique (lookupStatement?_sound found) form failed
    exact .inl ⟨child, _, rfl, rfl, initial, Nat.lt_trans childSmaller smaller⟩

/-- A returning statement retains the original expression outcome and cost. -/
theorem returning {mode : Bool} {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ child expressionOutcome,
      ExpressionOutcome program child context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) ∧ child < size := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head _ _ _ =>
    obtain ⟨_, _, _, same, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique (lookupStatement?_sound found) form head
    cases same
  | terminal head _ smaller =>
    obtain ⟨rfl, child, value, rfl, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique (lookupStatement?_sound found) form head
    exact ⟨rfl, child, .value value, .value initial, rfl, Nat.lt_trans childSmaller smaller⟩
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.return_fault unique (lookupStatement?_sound found) form failed
    exact ⟨rfl, child, .fault _, .fault initial, rfl, Nat.lt_trans childSmaller smaller⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
end
