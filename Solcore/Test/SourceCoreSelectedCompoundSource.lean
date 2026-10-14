import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Test.SourceCoreNamedBranchSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

inductive Operation where
  | add
  | divide
  deriving DecidableEq, Repr

def Operation.operator : Operation → Syntax.ValueAssignOp
  | .add => .add
  | .divide => .divide

def Operation.apply : Operation → Word → Word → Word
  | .add, left, right => left.add right
  | .divide, left, right => left.udiv right

theorem Operation.applies (operation : Operation) (left right : Word) :
    Dynamic.AssignmentValueApplies operation.operator (some (.word left)) (.word right)
      (.word (operation.apply left right)) := by
  cases operation with
  | add => exact .add (.wordAdd left right)
  | divide => exact .divide (.wordDivide left right)

def appendWord (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := value}]⟩
def location (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩
def inputHeap (before : Dynamic.Heap) (left right : Word) : Dynamic.Heap :=
  appendWord (appendWord before (some (.word left))) (some (.word right))
def resultHeap (before : Dynamic.Heap) (right result : Word) : Dynamic.Heap :=
  inputHeap before result right

def missingHeap (before : Dynamic.Heap) (right : Word) : Dynamic.Heap :=
  appendWord (appendWord before (some (.word right))) none

structure CompoundShape (source : TypedSource) (operation : Operation) where
  left : TypedBinder
  right : TypedBinder
  resolution : AssignmentResolution
  assignment : StatementNode
  returned : StatementNode
  rhs : Tests.SourceCoreNamedBranch.WordRead source right
  result : Tests.SourceCoreNamedBranch.WordRead source left
  inputs : source.inputs = [left, right]
  leftScheme : left.scheme = .mono .word
  rightScheme : right.scheme = .mono .word
  distinct : right.id ≠ left.id
  roots : source.roots = [.statement assignment.id, .statement returned.id]
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution operation.operator rhs.node.id
  targetRoot : resolution.target.root = left.id
  targetBare : resolution.target.projections = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

structure MissingShape (source : TypedSource) where
  right : TypedBinder
  binder : TypedBinder
  resolution : AssignmentResolution
  declared : StatementNode
  assignment : StatementNode
  returned : StatementNode
  rhs : Tests.SourceCoreNamedBranch.WordRead source right
  inputs : source.inputs = [right]
  rightScheme : right.scheme = .mono .word
  localScheme : binder.scheme = .mono .word
  distinct : binder.id ≠ right.id
  roots : source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl binder none
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .divide rhs.node.id
  targetRoot : resolution.target.root = binder.id
  targetBare : resolution.target.projections = []

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

private theorem write_append (previousCells : List Dynamic.Cell) (old next : Dynamic.Cell)
    (suffix : List Dynamic.Cell) :
    Dynamic.Heap.CellsWrite (previousCells ++ old :: suffix) previousCells.length next (previousCells ++ next :: suffix) := by
  induction previousCells with
  | nil => exact .head
  | cons head rest ih => exact .tail ih

private theorem read_word {program : SourceSemantics.Program} {source : TypedSource} {binder : TypedBinder}
    (node : Tests.SourceCoreNamedBranch.WordRead source binder)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (loc : Dynamic.Location) (value : Word)
    (lookup : Dynamic.Environment.LooksUp environment binder.id loc)
    (reads : Dynamic.Heap.Reads heap loc ⟨.word, some (.word value), none⟩) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id (.word value) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
  · rw [node.coercions]; exact .nil

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem compound_input_types {operation : Operation} (shape : CompoundShape header.function.source operation) :
    header.types = [.word, .word] := by
  have params : header.function.parameters = [shape.left, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.leftScheme, shape.rightScheme,
    TypeSystem.Scheme.mono] using types.symm

/-- The target snapshot precedes the RHS; the actual current root is written
before the final read. Earlier calls' cells are retained exactly. -/
theorem compound_call {operation : Operation} (shape : CompoundShape header.function.source operation)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (left right : Word) :
    PlainValue anchor header invocation before [.word left, .word right]
      (.word (operation.apply left right)) (resultHeap before right (operation.apply left right)) := by
  let first := appendWord before (some (.word left))
  let environment : Dynamic.Environment := [(shape.right.id, location first), (shape.left.id, location before)]
  have leftAllocation : Dynamic.Heap.Allocates before .word (some (.word left)) (location before) first := .append
  have rightAllocation : Dynamic.Heap.Allocates first .word (some (.word right))
      (location first) (inputHeap before left right) := .append
  have leftRead : Dynamic.Heap.Reads (inputHeap before left right) (location before)
      ⟨.word, some (.word left), none⟩ := rightAllocation.preserves_read leftAllocation.reads_new
  have params : header.function.parameters = [shape.left, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word left, .word right]
      environment (inputHeap before left right) := by
    rw [params]
    exact .cons (by rw [shape.leftScheme]; exact leftAllocation)
      (.cons (by rw [shape.rightScheme]; exact rightAllocation) (.nil _ _))
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before left right)
      shape.resolution.target
      {location := location before, rootType := .word, valueType := shape.resolution.target.type,
        projections := [], selected := some (.word left)} (inputHeap before left right) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := ⟨.word, some (.word left), none⟩)
      (currentCell := ⟨.word, some (.word left), none⟩)
    · rw [shape.targetRoot]; exact .tail shape.distinct .head
    · exact leftRead
    · rw [shape.targetBare]; exact .nil
    · exact leftRead
    · exact .initialized
    · exact .nil
  have write : Dynamic.Heap.Writes (inputHeap before left right) (location before)
      (some (.word (operation.apply left right))) (resultHeap before right (operation.apply left right)) := by
    apply Dynamic.Heap.Writes.intro leftRead
    simpa only [inputHeap, resultHeap, appendWord, location, List.append_assoc, List.singleton_append] using
      write_append before.cells ⟨.word, some (.word left), none⟩
        ⟨.word, some (.word (operation.apply left right)), none⟩ [⟨.word, some (.word right), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before left right)
      shape.assignment.id header.context (.fallthrough environment)
      (resultHeap before right (operation.apply left right)) := by
    apply Dynamic.StatementExecutes.assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
    apply Dynamic.SourcePlaceAssignment.intro resolve
    · exact read_word shape.rhs header.context header.function.evidence environment (inputHeap before left right)
        (location first) right .head rightAllocation.reads_new
    · exact .intro leftRead rfl .initialized (.leaf (operation.applies left right)) write
  have finalRead : Dynamic.Heap.Reads (resultHeap before right (operation.apply left right))
      (location before) ⟨.word, some (.word (operation.apply left right)), none⟩ := by
    exact .intro ((Dynamic.Heap.CellAt.append_last before.cells _).append_left)
  have roots : header.function.body = [shape.assignment.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before left right)
      header.function.body header.context (.returned (.word (operation.apply left right)))
      (resultHeap before right (operation.apply left right)) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_word shape.result header.context header.function.evidence environment _ (location before)
          (operation.apply left right) (.tail shape.distinct .head) finalRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


theorem missing_input_types (shape : MissingShape header.function.source) : header.types = [.word] := by
  have params : header.function.parameters = [shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.rightScheme,
    TypeSystem.Scheme.mono] using types.symm

private theorem missing_extension (shape : MissingShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ localContext, BinderExtends header.function.source.owner header.context shape.binder localContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.declared.id, shape.assignment.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at typed
  cases typed with
  | cons head tail =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.declaredFound)
    rw [shape.declaredForm] at formTyped
    cases formTyped with
    | letUninitialized mono extension => exact ⟨_, extension⟩

/-- An absent compound target fails after the RHS has been evaluated. The
parameter and absent local remain in the exact reached Source heap. -/
theorem missing_call (shape : MissingShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (right : Word) :
    PlainFault anchor header invocation before [.word right] (.invalidAssignmentOperands .divide)
      (missingHeap before right) := by
  let input := appendWord before (some (.word right))
  let environment : Dynamic.Environment := [(shape.right.id, location before)]
  let localEnvironment : Dynamic.Environment := (shape.binder.id, location input) :: environment
  have inputAllocation : Dynamic.Heap.Allocates before .word (some (.word right)) (location before) input := .append
  have localAllocation : Dynamic.Heap.Allocates input .word none (location input) (missingHeap before right) := .append
  have params : header.function.parameters = [shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word right] environment input := by
    rw [params]
    exact .cons (by rw [shape.rightScheme]; exact inputAllocation) (.nil _ _)
  obtain ⟨localContext, extension⟩ := missing_extension header shape certified
  have absent : Dynamic.RootInitialValue (⟨.word, none, none⟩ : Dynamic.Cell) none :=
    .uninitialized (by intro ⟨key, value, impossible⟩; cases impossible)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment (missingHeap before right)
      shape.resolution.target
      {location := location input, rootType := .word, valueType := shape.resolution.target.type,
        projections := [], selected := none} (missingHeap before right) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := ⟨.word, none, none⟩)
      (currentCell := ⟨.word, none, none⟩)
    · rw [shape.targetRoot]; exact .head
    · exact localAllocation.reads_new
    · rw [shape.targetBare]; exact .nil
    · exact localAllocation.reads_new
    · exact absent
    · exact .nil
  have failed : Dynamic.StatementFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment (missingHeap before right)
      shape.assignment.id (.invalidAssignmentOperands .divide) (missingHeap before right) := by
    apply Dynamic.StatementFaults.assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
    apply Dynamic.SourcePlaceAssignmentFaults.operands resolve
    · exact read_word shape.rhs localContext header.function.evidence localEnvironment _ (location before)
        right (.tail shape.distinct .head) (localAllocation.preserves_read inputAllocation.reads_new)
    · exact localAllocation.reads_new
    · rfl
    · exact absent
    · exact .nil
    · exact .uninitialized (by intro impossible; cases impossible)
  have roots : header.function.body = [shape.declared.id, shape.assignment.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsFault (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment input header.function.body
      localContext (.invalidAssignmentOperands .divide) (missingHeap before right) := by
    rw [roots]
    exact .tail (.letUninitialized (lookupStatement?_sound shape.declaredFound) shape.declaredForm
      (by rw [shape.localScheme]; rfl) extension (by rw [shape.localScheme]; exact localAllocation))
      (.head failed)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.fault body)
  cases invoked with
  | fault invoked => exact ⟨rawD, global, sourceAt, .globalBody sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedCompound
