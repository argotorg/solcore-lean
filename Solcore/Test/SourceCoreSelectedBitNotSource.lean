import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Test.SourceCoreNamedBranchSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

def appendWord (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := value}]⟩
def location (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩
def inputHeap (before : Dynamic.Heap) (value : Word) : Dynamic.Heap := appendWord before (some (.word value))
def resultHeap (before : Dynamic.Heap) (value : Word) : Dynamic.Heap := appendWord before (some (.word value.bitNot))
def missingHeap (before : Dynamic.Heap) : Dynamic.Heap := appendWord before none

structure UnaryShape (source : TypedSource) where
  binder : TypedBinder
  resolution : AssignmentResolution
  assignment : StatementNode
  returned : StatementNode
  result : Tests.SourceCoreNamedBranch.WordRead source binder
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono .word
  roots : source.roots = [.statement assignment.id, .statement returned.id]
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignBitNot resolution
  targetRoot : resolution.target.root = binder.id
  targetBare : resolution.target.projections = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

structure MissingShape (source : TypedSource) where
  binder : TypedBinder
  resolution : AssignmentResolution
  declared : StatementNode
  assignment : StatementNode
  returned : StatementNode
  inputs : source.inputs = []
  localScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl binder none
  assignmentFound : source.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignBitNot resolution
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

theorem unary_input_types (shape : UnaryShape header.function.source) : header.types = [.word] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using types.symm

/-- The actual cell is read once and complemented in place. Prior calls' cells
are retained exactly, and the final read observes the new word. -/
theorem unary_call (shape : UnaryShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Word) :
    PlainValue anchor header invocation before [.word value] (.word value.bitNot) (resultHeap before value) := by
  let environment : Dynamic.Environment := [(shape.binder.id, location before)]
  have allocation : Dynamic.Heap.Allocates before .word (some (.word value))
      (location before) (inputHeap before value) := .append
  have read := allocation.reads_new
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word value]
      environment (inputHeap before value) := by
    rw [params]
    exact .cons (by rw [shape.scheme]; exact allocation) (.nil _ _)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before value)
      shape.resolution.target
      {location := location before, rootType := .word, valueType := shape.resolution.target.type,
        projections := [], selected := some (.word value)} (inputHeap before value) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := ⟨.word, some (.word value), none⟩)
      (currentCell := ⟨.word, some (.word value), none⟩)
    · rw [shape.targetRoot]; exact .head
    · exact read
    · rw [shape.targetBare]; exact .nil
    · exact read
    · exact .initialized
    · exact .nil
  have write : Dynamic.Heap.Writes (inputHeap before value) (location before)
      (some (.word value.bitNot)) (resultHeap before value) := by
    apply Dynamic.Heap.Writes.intro read
    simpa only [inputHeap, resultHeap, appendWord, location, List.append_nil] using
      write_append before.cells ⟨.word, some (.word value), none⟩ ⟨.word, some (.word value.bitNot), none⟩ []
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before value)
      shape.assignment.id header.context (.fallthrough environment) (resultHeap before value) :=
    .assignBitNot (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
      (.intro resolve (.intro read rfl .initialized (.leaf (.word value)) write))
  have finalRead : Dynamic.Heap.Reads (resultHeap before value)
      (location before) ⟨.word, some (.word value.bitNot), none⟩ :=
    .intro (Dynamic.Heap.CellAt.append_last before.cells _)
  have roots : header.function.body = [shape.assignment.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap before value)
      header.function.body header.context (.returned (.word value.bitNot)) (resultHeap before value) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_word shape.result header.context header.function.evidence environment _ (location before)
          value.bitNot .head finalRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

theorem missing_input_types (shape : MissingShape header.function.source) : header.types = [] := by
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_nil] using types.symm

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

/-- An uninitialized unary target faults without an expression or write. The
new local and all earlier cells remain in the exact reached Source heap. -/
theorem missing_call (shape : MissingShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    PlainFault anchor header invocation before [] (.invalidUnaryOperand .bitNot) (missingHeap before) := by
  let localEnvironment : Dynamic.Environment := [(shape.binder.id, location before)]
  have localAllocation : Dynamic.Heap.Allocates before .word none (location before) (missingHeap before) := .append
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [] [] before := by
    rw [params]; exact .nil _ _
  obtain ⟨localContext, extension⟩ := missing_extension header shape certified
  have absent : Dynamic.RootInitialValue (⟨.word, none, none⟩ : Dynamic.Cell) none :=
    .uninitialized (by intro ⟨key, value, impossible⟩; cases impossible)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment (missingHeap before)
      shape.resolution.target
      {location := location before, rootType := .word, valueType := shape.resolution.target.type,
        projections := [], selected := none} (missingHeap before) := by
    apply Dynamic.SourcePlaceResolves.intro (initialCell := ⟨.word, none, none⟩)
      (currentCell := ⟨.word, none, none⟩)
    · rw [shape.targetRoot]; exact .head
    · exact localAllocation.reads_new
    · rw [shape.targetBare]; exact .nil
    · exact localAllocation.reads_new
    · exact absent
    · exact .nil
  have failed : Dynamic.StatementFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment (missingHeap before)
      shape.assignment.id (.invalidUnaryOperand .bitNot) (missingHeap before) :=
    .assignBitNot (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm (.uninitialized resolve rfl)
  have roots : header.function.body = [shape.declared.id, shape.assignment.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsFault (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [] before header.function.body
      localContext (.invalidUnaryOperand .bitNot) (missingHeap before) := by
    rw [roots]
    exact .tail (.letUninitialized (lookupStatement?_sound shape.declaredFound) shape.declaredForm
      (by rw [shape.localScheme]; rfl) extension (by rw [shape.localScheme]; exact localAllocation))
      (.head failed)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.fault body)
  cases invoked with
  | fault invoked => exact ⟨rawD, global, sourceAt, .globalBody sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedBitNot
