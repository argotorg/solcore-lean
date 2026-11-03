import Solcore.Test.SourceCoreSelectedProjectedBitNotSource
import Solcore.Core.UnaryPrimitives

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot.Captured
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

/-- Facts read from the unchanged `make` declaration, without an execution premise. -/
structure Shape (source : TypedSource) where
  table : TypedBinder
  key : TypedBinder
  resolution : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  outer : StatementNode
  lambda : ExpressionNode
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  tableRead : Tests.SourceCoreNamedBranch.Read source table mappingType
  resultKey : Tests.SourceCoreNamedBranch.WordRead source key
  result : IndexRead source tableRead.node.id resultKey.node.id
  inputs : source.inputs = [table]
  tableScheme : table.scheme = .mono mappingType
  tableCopied : CaptureBinders.copiedBinder? source table.id = some table
  keyScheme : key.scheme = .mono .word
  keyTable : key.id ≠ table.id
  roots : source.roots = [.statement outer.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignBitNot resolution
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]
  targetType : resolution.target.type = .word
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [key] .word [assigned.id, returned.id]
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  outerFound : source.lookupStatement? outer.id = some outer
  outerForm : outer.form = .returnStmt (some lambda.id)

def mappingCell (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Cell :=
  {type := mappingType, value := some (mappingValue entries)}

/-- The factory's input cell and the closure's snapshot of it. Later calls
append their own copies and arguments in `suffix`; nothing writes the snapshot. -/
def heap (before : Dynamic.Heap) (entries : List (Dynamic.Value × Dynamic.Value))
    (suffix : List Dynamic.Cell := []) : Dynamic.Heap :=
  ⟨before.cells ++ mappingCell entries :: mappingCell entries :: suffix⟩

/-- The closure's snapshot, right after the input cell. -/
def snapshotLocation (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length + 1⟩

def function {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (shape : Shape header.function.source) (before : Dynamic.Heap) : Dynamic.Closure := {
  parameters := [shape.key], resultType := .word, body := [shape.assigned.id, shape.returned.id]
  source := header.function.source, captured := [(shape.table.id, snapshotLocation before)]
  context := header.context, evidence := header.function.evidence }

def keyCell (key : Word) : Dynamic.Cell := {type := .word, value := some (.word key)}

/-- The cells one call appends: its copy of the snapshot, written by the update,
and its key. -/
def callCells (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value)) : List Dynamic.Cell :=
  [mappingCell ((.word key, .word previous.bitNot) :: tail), keyCell key]

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

private theorem cell_at (previousCells : List Dynamic.Cell) (cell : Dynamic.Cell) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.CellAt (previousCells ++ cell :: suffix) previousCells.length cell := by
  induction previousCells with
  | nil => exact .head
  | cons first rest ih => exact .tail ih

private theorem write_at (previousCells : List Dynamic.Cell) (old next : Dynamic.Cell) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.CellsWrite (previousCells ++ old :: suffix) previousCells.length next (previousCells ++ next :: suffix) := by
  induction previousCells with
  | nil => exact .head
  | cons first rest ih => exact .tail ih

private theorem read_value {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source binder type)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (current : Dynamic.Heap) (loc : Dynamic.Location)
    (value : Dynamic.Value)
    (lookup : Dynamic.Environment.LooksUp environment binder.id loc)
    (reads : Dynamic.Heap.Reads current loc ⟨type, some value, none⟩) :
    Dynamic.ExpressionEvaluates program context evidence source environment current node.node.id value current := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
  · rw [node.coercions]; exact .nil

private theorem lambda_parameters {source : TypedSource} {context : SourceSemantics.Context}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {type : TypeSystem.Ty} {stage : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType source context (.lambda parameters result body) type stage) :
    ∃ types next, MonoBindersExtend source.owner context parameters types next := by
  cases typed with
  | lambda _ extension _ _ => exact ⟨_, _, extension⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [mappingType] := by
  have params : header.function.parameters = [shape.table] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, TypeSystem.Scheme.mono] using types.symm

/-- Allocate the actual mapping parameter; the lambda copies that exact cell
into the closure's snapshot. -/
theorem factory_plain {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (entries : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before [mappingValue entries]
      (.closure (function header shape before)) (heap before entries) := by
  have params : header.function.parameters = [shape.table] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates before shape.table.scheme.body
      (some (mappingValue entries)) (location before) (appendCell before mappingType (some (mappingValue entries))) := by
    rw [shape.tableScheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [mappingValue entries]
      [(shape.table.id, location before)] (appendCell before mappingType (some (mappingValue entries))) := by
    rw [params]; exact .cons allocated (.nil _ _)
  have stored : Dynamic.Heap.Allocates before mappingType (some (mappingValue entries)) (location before)
      (appendCell before mappingType (some (mappingValue entries))) := .append
  have copied : Dynamic.Heap.AllocatesCopy (appendCell before mappingType (some (mappingValue entries)))
      (mappingCell entries) (snapshotLocation before) (heap before entries) := by
    have appended := Dynamic.Heap.AllocatesCopy.append
      (heap := appendCell before mappingType (some (mappingValue entries))) (cell := mappingCell entries)
    simpa only [appendCell, heap, snapshotLocation, mappingCell, List.length_append, List.length_singleton,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using appended
  have snapshot : Dynamic.EnvironmentCopies header.function.source [(shape.table.id, location before)]
      (appendCell before mappingType (some (mappingValue entries)))
      [(shape.table.id, snapshotLocation before)] (heap before entries) :=
    .copied shape.tableCopied stored.reads_new copied (.nil _)
  have roots : header.function.body = [shape.outer.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.table.id, location before)]
      (appendCell before mappingType (some (mappingValue entries))) shape.lambda.id
      (.closure (function header shape before)) (heap before entries) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lambdaFound)
    · rw [shape.lambdaForm]
      exact .lambda (by rw [shape.lambdaRequirements, shape.lambdaCoercions]; rfl) snapshot
    · rw [shape.lambdaCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.table.id, location before)]
      (appendCell before mappingType (some (mappingValue entries))) header.function.body header.context
      (.returned (.closure (function header shape before))) (heap before entries) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.outerFound)
      (by rw [shape.outerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.outerFound) shape.outerForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

/-- Execute the captured update from original syntax. The call copies the
closure's snapshot, binds the key after the copy and writes only the copy, so
every call starts from the mapping the factory received. Earlier call
allocations remain in `suffix`. There is no RHS. -/
theorem closure_plain (before : Dynamic.Heap) (key previous : Word)
    (tail : List (Dynamic.Value × Dynamic.Value)) (suffix : List Dynamic.Cell)
    {context : SourceSemantics.Context} (invocation : Staging.Recursive.Scope)
    (signatures : context.signatures = (Program.ofChecked compiled.sourceProgram).signatures)
    (typed : Dynamic.ValueHasType context (heap before ((.word key, .word previous) :: tail) suffix)
      (.closure (function header shape before)) (.function .word .word)) :
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      (function header shape before).evidence (heap before ((.word key, .word previous) :: tail) suffix)
      (.closure (function header shape before)) [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail)) := by
  obtain ⟨_parameters, _result, sameSignatures, code, covers, _captures⟩ := typed.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) (function header shape before) :=
    ⟨sameSignatures.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  obtain ⟨id, node, _contains, form, _rawType, formTyped⟩ := code.occurrence
  rw [form] at formTyped
  obtain ⟨parameterTypes, callContext, parameters⟩ := lambda_parameters formTyped
  let original := mappingValue ((.word key, .word previous) :: tail)
  let replacement := mappingValue ((.word key, .word previous.bitNot) :: tail)
  let initial := heap before ((.word key, .word previous) :: tail) suffix
  let copied := appendCell initial mappingType (some original)
  let current := appendCell copied .word (some (.word key))
  let after := heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail)
  let entry : Dynamic.Environment := [(shape.table.id, location initial)]
  let environment : Dynamic.Environment :=
    [(shape.key.id, location copied), (shape.table.id, location initial)]
  have snapshotRead : Dynamic.Heap.Reads initial (snapshotLocation before) ⟨mappingType, some original, none⟩ := by
    have selected := cell_at (before.cells ++ [⟨mappingType, some original, none⟩])
      ⟨mappingType, some original, none⟩ suffix
    apply Dynamic.Heap.Reads.intro
    simpa only [initial, original, heap, snapshotLocation, mappingCell, List.append_assoc, List.cons_append,
      List.nil_append, List.singleton_append, List.length_append, List.length_singleton] using selected
  have copyAllocated : Dynamic.Heap.AllocatesCopy initial ⟨mappingType, some original, none⟩
      (location initial) copied := .append
  have copy : Dynamic.EnvironmentCopies header.function.source (function header shape before).captured
      initial entry copied :=
    .copied shape.tableCopied snapshotRead copyAllocated (.nil _)
  have allocation : Dynamic.Heap.Allocates copied .word (some (.word key)) (location copied) current := .append
  have rootRead := allocation.preserves_read copyAllocated.reads_new
  have keyRead := allocation.reads_new
  have allocated : Dynamic.BindersAllocate entry copied
      (function header shape before).parameters [.word key] environment current := by
    exact .cons (by rw [shape.keyScheme]; exact allocation) (.nil _ _)
  have equalKey : Dynamic.ValueEquivalent (.word key) (.word key) := .refl (.word key)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      callContext header.function.evidence header.function.source environment current shape.resolution.target
      {location := location initial, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩) (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.keyTable .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ .head keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head equalKey) .nil
  have write : Dynamic.Heap.Writes current (location initial) (some replacement) after := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, copied, initial, after, original, replacement, appendCell, heap, location, keyCell,
      callCells, mappingCell, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using
      write_at (before.cells ++ mappingCell ((.word key, .word previous) :: tail) ::
          mappingCell ((.word key, .word previous) :: tail) :: suffix)
        ⟨mappingType, some original, none⟩ ⟨mappingType, some replacement, none⟩ [keyCell key]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      callContext header.function.evidence header.function.source environment current shape.assigned.id
      callContext (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.assignBitNot (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    exact .intro resolve (.intro rootRead rfl .initialized
      (.indexFound (.head equalKey) (.leaf (.word previous)) (.update (.head equalKey))) write)
  have finalRoot : Dynamic.Heap.Reads after (location initial) ⟨mappingType, some replacement, none⟩ := by
    have selected := cell_at (before.cells ++ mappingCell ((.word key, .word previous) :: tail) ::
      mappingCell ((.word key, .word previous) :: tail) :: suffix) ⟨mappingType, some replacement, none⟩ [keyCell key]
    apply Dynamic.Heap.Reads.intro
    simpa only [after, initial, replacement, heap, location, callCells, mappingCell, List.append_assoc,
      List.cons_append, List.nil_append] using selected
  have finalKey : Dynamic.Heap.Reads after (location copied) ⟨.word, some (.word key), none⟩ := by
    have selected := cell_at (before.cells ++ mappingCell ((.word key, .word previous) :: tail) ::
      mappingCell ((.word key, .word previous) :: tail) :: suffix ++ [⟨mappingType, some replacement, none⟩])
      (keyCell key) []
    apply Dynamic.Heap.Reads.intro
    simpa only [after, copied, initial, original, replacement, appendCell, heap, location, callCells, mappingCell,
      keyCell, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
      List.length_append, List.length_cons, List.length_nil] using selected
  have result : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      callContext header.function.evidence header.function.source environment after shape.result.node.id
      (.word previous.bitNot) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.result.found)
    · rw [shape.result.form]
      exact .indexFound (by rw [shape.result.requirements, shape.result.coercions]; rfl)
        (read_value shape.tableRead _ _ _ _ _ _ (.tail shape.keyTable .head) finalRoot)
        (read_value shape.resultKey _ _ _ _ _ _ .head finalKey) (.head equalKey)
    · rw [shape.result.coercions]; exact .nil
  exact .closure rfl frame parameters copy allocated
    (.cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro expression impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm result))) rfl

end Tests.SourceCoreSelectedProjectedBitNot.Captured
