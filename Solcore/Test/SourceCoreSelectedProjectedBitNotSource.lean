import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Test.SourceCoreNamedBranchSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

def mappingType : TypeSystem.Ty := .mapping .word .word
def appendCell (before : Dynamic.Heap) (type : TypeSystem.Ty)
    (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := type, value := value}]⟩
def location (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩
def mappingValue (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Value :=
  .mapping .word .word entries
def parameterHeap (before : Dynamic.Heap) (entries : List (Dynamic.Value × Dynamic.Value))
    (key : Word) : Dynamic.Heap :=
  appendCell (appendCell before mappingType (some (mappingValue entries)))
    .word (some (.word key))

structure UnaryShape (source : TypedSource) where
  table : TypedBinder
  key : TypedBinder
  resolution : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  result : Tests.SourceCoreNamedBranch.Read source table mappingType
  inputs : source.inputs = [table, key]
  tableScheme : table.scheme = .mono mappingType
  keyScheme : key.scheme = .mono .word
  keyTable : key.id ≠ table.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignBitNot resolution
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]
  targetType : resolution.target.type = .word
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

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
    Dynamic.Heap.CellsWrite (previousCells ++ old :: suffix) previousCells.length next
      (previousCells ++ next :: suffix) := by
  induction previousCells with
  | nil => exact .head
  | cons head rest ih => exact .tail ih

private theorem read_value {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source binder type)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (loc : Dynamic.Location)
    (value : Dynamic.Value)
    (lookup : Dynamic.Environment.LooksUp environment binder.id loc)
    (reads : Dynamic.Heap.Reads heap loc ⟨type, some value, none⟩) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
  · rw [node.coercions]; exact .nil

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem unary_input_types (shape : UnaryShape header.function.source) :
    header.types = [mappingType, .word] := by
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.keyScheme, TypeSystem.Scheme.mono] using types.symm

theorem unary_call (shape : UnaryShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key]
      (mappingValue ((.word key, .word previous.bitNot) :: tail))
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
  let original := mappingValue ((.word key, .word previous) :: tail)
  let replacement := mappingValue ((.word key, .word previous.bitNot) :: tail)
  let first := appendCell before mappingType (some original)
  let current := appendCell first .word (some (.word key))
  let environment : Dynamic.Environment :=
    [(shape.key.id, location first), (shape.table.id, location before)]
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) current := .append
  have rootRead := keyAllocation.preserves_read rootAllocation.reads_new
  have keyRead := keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word key] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation) (.nil _ _))
  have equalKey : Dynamic.ValueEquivalent (.word key) (.word key) := .refl (.word key)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.keyTable .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head equalKey) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, first, appendCell, original, replacement,
      parameterHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨mappingType, some original, none⟩
        ⟨mappingType, some replacement, none⟩ [⟨.word, some (.word key), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.assigned.id header.context (.fallthrough environment)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    apply Dynamic.StatementExecutes.assignBitNot (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head equalKey) (.leaf (.word previous)) (.update (.head equalKey))) write
  have finalRootRead : Dynamic.Heap.Reads
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key)
      (location before) ⟨mappingType, some replacement, none⟩ := by
    obtain ⟨cell, readBefore, readAfter⟩ := write.reads_updated
    have same := readBefore.functional rootRead
    cases same
    exact readAfter
  have roots : header.function.body = [shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned replacement)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_value shape.result _ _ _ _ _ _ (.tail shape.keyTable .head) finalRootRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


structure CopyShape (source : TypedSource) where
  argument : TypedBinder
  copy : TypedBinder
  initialized : StatementNode
  returned : StatementNode
  initializer : Tests.SourceCoreNamedBranch.WordRead source argument
  result : Tests.SourceCoreNamedBranch.WordRead source copy
  inputs : source.inputs = [argument]
  argumentScheme : argument.scheme = .mono .word
  copyScheme : copy.scheme = .mono .word
  roots : source.roots = [.statement initialized.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl copy (some initializer.node.id)
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

def copyHeap (before : Dynamic.Heap) (value : Word) : Dynamic.Heap :=
  appendCell (appendCell before .word (some (.word value))) .word (some (.word value))

theorem copy_input_types (shape : CopyShape header.function.source) : header.types = [.word] := by
  have params : header.function.parameters = [shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.argumentScheme, TypeSystem.Scheme.mono] using types.symm

private theorem copy_extension (shape : CopyShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ localContext, BinderExtends header.function.source.owner header.context shape.copy localContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.initialized.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at typed
  cases typed with
  | cons head tail =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.initializedFound)
    rw [shape.initializedForm] at formTyped
    cases formTyped with
    | letInitialized value mono extension => exact ⟨_, extension⟩
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly (by rw [shape.copyScheme]; rfl))

/-- The unchanged scalar helper establishes an independent initial Source
call in the complete program before mapping inputs are sent to later calls. -/
theorem copy_call (shape : CopyShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Word) :
    PlainValue anchor header invocation before [.word value] (.word value) (copyHeap before value) := by
  let middle := appendCell before .word (some (.word value))
  let after := copyHeap before value
  let environment : Dynamic.Environment := [(shape.argument.id, location before)]
  let localEnvironment := (shape.copy.id, location middle) :: environment
  have inputAllocation : Dynamic.Heap.Allocates before .word (some (.word value)) (location before) middle := .append
  have copyAllocation : Dynamic.Heap.Allocates middle .word (some (.word value)) (location middle) after := .append
  have params : header.function.parameters = [shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word value] environment middle := by
    rw [params]; exact .cons (by rw [shape.argumentScheme]; exact inputAllocation) (.nil _ _)
  obtain ⟨localContext, extension⟩ := copy_extension header shape certified
  have roots : header.function.body = [shape.initialized.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment middle header.function.body
      localContext (.returned (.word value)) after := by
    rw [roots]
    apply Dynamic.FunctionStatementsExecute.cons
    · exact .letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
        (read_value shape.initializer _ _ _ _ _ _ .head inputAllocation.reads_new)
        (by rw [shape.copyScheme]; rfl) extension (by rw [shape.copyScheme]; exact copyAllocation)
    · exact .singleton (lookupStatement?_sound shape.returnedFound)
        (by rw [shape.returnedForm]; intro id impossible; cases impossible)
        (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
          (read_value shape.result _ _ localEnvironment after _ _ .head copyAllocation.reads_new))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


def missingHeap (before : Dynamic.Heap) (entries : List (Dynamic.Value × Dynamic.Value))
    (key : Word) : Dynamic.Heap :=
  appendCell (appendCell (appendCell before mappingType (some (mappingValue entries)))
    .word (some (.word key))) .word none

def missingLocation (before : Dynamic.Heap) (entries : List (Dynamic.Value × Dynamic.Value))
    (key : Word) : Dynamic.Location :=
  location (appendCell (appendCell before mappingType (some (mappingValue entries)))
    .word (some (.word key)))

structure MissingShape (source : TypedSource) where
  table : TypedBinder
  key : TypedBinder
  absent : TypedBinder
  resolution : AssignmentResolution
  declared : StatementNode
  assigned : StatementNode
  returned : StatementNode
  absentRead : Tests.SourceCoreNamedBranch.WordRead source absent
  inputs : source.inputs = [table, key]
  tableScheme : table.scheme = .mono mappingType
  keyScheme : key.scheme = .mono .word
  absentScheme : absent.scheme = .mono .word
  keyTable : key.id ≠ table.id
  absentTable : absent.id ≠ table.id
  absentKey : absent.id ≠ key.id
  roots : source.roots = [.statement declared.id, .statement assigned.id, .statement returned.id]
  declaredFound : source.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl absent none
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignBitNot resolution
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index absentRead.node.id]

theorem missing_input_types (shape : MissingShape header.function.source) :
    header.types = [mappingType, .word] := by
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.keyScheme,
    TypeSystem.Scheme.mono] using types.symm

private theorem missing_extension (shape : MissingShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ localContext, BinderExtends header.function.source.owner header.context shape.absent localContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.declared.id, shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at typed
  cases typed with
  | cons head tail =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.declaredFound)
    rw [shape.declaredForm] at formTyped
    cases formTyped with
    | letUninitialized mono extension => exact ⟨_, extension⟩

/-- A genuine uninitialized key faults before snapshot selection. The root
mapping and all allocated cells remain at the reached heap. -/
theorem missing_call (shape : MissingShape header.function.source)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainFault anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key]
      (.uninitializedLocation (missingLocation before ((.word key, .word previous) :: tail) key))
      (missingHeap before ((.word key, .word previous) :: tail) key) := by
  let original := mappingValue ((.word key, .word previous) :: tail)
  let first := appendCell before mappingType (some original)
  let second := appendCell first .word (some (.word key))
  let current := appendCell second .word none
  let environment : Dynamic.Environment := [(shape.key.id, location first), (shape.table.id, location before)]
  let localEnvironment := (shape.absent.id, location second) :: environment
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) second := .append
  have absentAllocation : Dynamic.Heap.Allocates second .word none (location second) current := .append
  have rootRead := absentAllocation.preserves_read (keyAllocation.preserves_read rootAllocation.reads_new)
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [original, .word key]
      environment second := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation) (.nil _ _))
  obtain ⟨localContext, extension⟩ := missing_extension header shape certified
  have keyFault : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment current
      shape.absentRead.node.id (.uninitializedLocation (location second)) current := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.absentRead.found)
    rw [shape.absentRead.form]
    exact Dynamic.ExpressionFormFaults.localUninitialized
      (requirements := shape.absentRead.node.requirements)
      (coercions := shape.absentRead.node.coercions) (owned := [])
      (by rw [shape.absentRead.requirements, shape.absentRead.coercions]; rfl)
      .head absentAllocation.reads_new rfl rfl (by rintro ⟨keyType, valueType, impossible⟩; cases impossible)
  have failed : Dynamic.StatementFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment current
      shape.assigned.id (.uninitializedLocation (location second)) current :=
by
      apply Dynamic.StatementFaults.assignBitNot (lookupStatement?_sound shape.assignedFound) shape.assignedForm
      apply Dynamic.SourcePlaceBitNotFaults.target
      apply Dynamic.SourcePlaceFaults.projectionExpression
      · rw [shape.targetRoot]; exact .tail shape.absentTable (.tail shape.keyTable .head)
      · exact rootRead
      · rw [shape.targetProjections]; exact .indexHead keyFault
  have roots : header.function.body = [shape.declared.id, shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsFault (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment second header.function.body
      localContext (.uninitializedLocation (location second)) current := by
    rw [roots]
    exact .tail (.letUninitialized (lookupStatement?_sound shape.declaredFound) shape.declaredForm
      (by rw [shape.absentScheme]; rfl) extension (by rw [shape.absentScheme]; exact absentAllocation))
      (.head failed)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.fault body)
  cases invoked with
  | fault invoked => exact ⟨rawD, global, sourceAt, .globalBody sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ invoked)⟩



/-- An absent Word entry supplies zero and is appended with its complement. -/
theorem default_call (shape : UnaryShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key : Word) :
    PlainValue anchor header invocation before
      [mappingValue [], .word key]
      (mappingValue [(.word key, .word (Word.zero).bitNot)])
      (parameterHeap before [(.word key, .word (Word.zero).bitNot)] key) := by
  let original := mappingValue []
  let replacement := mappingValue [(.word key, .word (Word.zero).bitNot)]
  let first := appendCell before mappingType (some original)
  let current := appendCell first .word (some (.word key))
  let environment : Dynamic.Environment :=
    [(shape.key.id, location first), (shape.table.id, location before)]
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) current := .append
  have rootRead := keyAllocation.preserves_read rootAllocation.reads_new
  have keyRead := keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word key] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation) (.nil _ _))
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word Word.zero)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.keyTable .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexDefault .nil .word .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (parameterHeap before [(.word key, .word (Word.zero).bitNot)] key) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, first, appendCell, original, replacement,
      parameterHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨mappingType, some original, none⟩
        ⟨mappingType, some replacement, none⟩ [⟨.word, some (.word key), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.assigned.id header.context (.fallthrough environment)
      (parameterHeap before [(.word key, .word (Word.zero).bitNot)] key) := by
    apply Dynamic.StatementExecutes.assignBitNot (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve ?_
    exact .intro rootRead rfl .initialized
      (.indexDefault .nil .word (.leaf (.word Word.zero)) (.append .nil)) write
  have finalRootRead : Dynamic.Heap.Reads
      (parameterHeap before [(.word key, .word (Word.zero).bitNot)] key)
      (location before) ⟨mappingType, some replacement, none⟩ := by
    obtain ⟨cell, readBefore, readAfter⟩ := write.reads_updated
    have same := readBefore.functional rootRead
    cases same
    exact readAfter
  have roots : header.function.body = [shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned replacement)
      (parameterHeap before [(.word key, .word (Word.zero).bitNot)] key) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_value shape.result _ _ _ _ _ _ (.tail shape.keyTable .head) finalRootRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩



structure InitializerShape (source : TypedSource) where
  table : TypedBinder
  key : TypedBinder
  resolution : AssignmentResolution
  condition : ExpressionNode
  post : List ForItemForm
  assigned : StatementNode
  returned : StatementNode
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  result : Tests.SourceCoreNamedBranch.Read source table mappingType
  inputs : source.inputs = [table, key]
  tableScheme : table.scheme = .mono mappingType
  keyScheme : key.scheme = .mono .word
  keyTable : key.id ≠ table.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .forLoop [.assignBitNot resolution] condition.id post []
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]
  targetType : resolution.target.type = .word
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

  conditionFound : source.lookupExpression? condition.id = some condition
  conditionForm : condition.form = .reference "false" (.builtinBoolean false)
  conditionRequirements : condition.requirements = []
  conditionCoercions : condition.coercions = []

theorem initializer_input_types (shape : InitializerShape header.function.source) :
    header.types = [mappingType, .word] := by
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.keyScheme, TypeSystem.Scheme.mono] using types.symm

/-- Execute the actual projected initializer before the false condition; the post is skipped. -/
theorem initializer_call (shape : InitializerShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value))
 :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key]
      (mappingValue ((.word key, .word previous.bitNot) :: tail))
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
  let original := mappingValue ((.word key, .word previous) :: tail)
  let replacement := mappingValue ((.word key, .word previous.bitNot) :: tail)
  let first := appendCell before mappingType (some original)
  let current := appendCell first .word (some (.word key))
  let environment : Dynamic.Environment :=
    [(shape.key.id, location first), (shape.table.id, location before)]
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) current := .append
  have rootRead := keyAllocation.preserves_read rootAllocation.reads_new
  have keyRead := keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word key] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation) (.nil _ _))
  have equalKey : Dynamic.ValueEquivalent (.word key) (.word key) := .refl (.word key)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.keyTable .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head equalKey) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, first, appendCell, original, replacement,
      parameterHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨mappingType, some original, none⟩
        ⟨mappingType, some replacement, none⟩ [⟨.word, some (.word key), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.assigned.id header.context (.fallthrough environment)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    have initial : Dynamic.ForItemsExecute (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source environment current
        [.assignBitNot shape.resolution]
        header.context environment (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
      apply Dynamic.ForItemsExecute.cons (nextEnvironment := environment)
        (middle := parameterHeap before ((.word key, .word previous.bitNot) :: tail) key)
      · apply Dynamic.ForItemExecutes.assignBitNot (updatedRoot := replacement)
        refine .intro resolve ?_
        exact .intro rootRead rfl .initialized
          (.indexFound (.head equalKey) (.leaf (.word previous)) (.update (.head equalKey))) write
      · exact .nil
    have condition : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source environment
        (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) shape.condition.id (.bool false)
        (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionFound)
      · rw [shape.conditionForm]
        exact .builtinBoolean (by rw [shape.conditionRequirements, shape.conditionCoercions]; rfl)
      · rw [shape.conditionCoercions]; exact .nil
    exact Dynamic.StatementExecutes.forLoop (lookupStatement?_sound shape.assignedFound) shape.assignedForm initial (.done condition)
  have finalRootRead : Dynamic.Heap.Reads
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key)
      (location before) ⟨mappingType, some replacement, none⟩ := by
    obtain ⟨cell, readBefore, readAfter⟩ := write.reads_updated
    have same := readBefore.functional rootRead
    cases same
    exact readAfter
  have roots : header.function.body = [shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned replacement)
      (parameterHeap before ((.word key, .word previous.bitNot) :: tail) key) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_value shape.result _ _ _ _ _ _ (.tail shape.keyTable .head) finalRootRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


def nestedType : TypeSystem.Ty := .mapping .word mappingType
def nestedValue (first second value : Word) : Dynamic.Value :=
  .mapping .word mappingType [(.word first, mappingValue [(.word second, .word value)])]
def nestedHeap (before : Dynamic.Heap) (first second value : Word) : Dynamic.Heap :=
  appendCell (appendCell (appendCell before nestedType (some (nestedValue first second value)))
    .word (some (.word first))) .word (some (.word second))

structure IndexRead (source : TypedSource) (base key : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .index base key
  requirements : node.requirements = []
  coercions : node.coercions = []

private theorem index_read {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {base key : ExpressionId} {keyType valueType : TypeSystem.Ty}
    {entries : List (Dynamic.Value × Dynamic.Value)} {index value : Dynamic.Value}
    (node : IndexRead source base key)
    (baseValue : Dynamic.ExpressionEvaluates program context evidence source environment heap base
      (.mapping keyType valueType entries) heap)
    (keyValue : Dynamic.ExpressionEvaluates program context evidence source environment heap key index heap)
    (lookup : Dynamic.MappingLookup index entries value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .indexFound (by rw [node.requirements, node.coercions]; rfl) baseValue keyValue lookup
  · rw [node.coercions]; exact .nil

structure NestedShape (source : TypedSource) where
  table : TypedBinder
  first : TypedBinder
  second : TypedBinder
  resolution : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  firstRead : Tests.SourceCoreNamedBranch.WordRead source first
  secondRead : Tests.SourceCoreNamedBranch.WordRead source second
  baseRead : Tests.SourceCoreNamedBranch.Read source table nestedType
  returnFirst : Tests.SourceCoreNamedBranch.WordRead source first
  returnSecond : Tests.SourceCoreNamedBranch.WordRead source second
  inner : IndexRead source baseRead.node.id returnFirst.node.id
  outer : IndexRead source inner.node.id returnSecond.node.id
  inputs : source.inputs = [table, first, second]
  tableScheme : table.scheme = .mono nestedType
  firstScheme : first.scheme = .mono .word
  secondScheme : second.scheme = .mono .word
  firstTable : first.id ≠ table.id
  secondTable : second.id ≠ table.id
  secondFirst : second.id ≠ first.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignBitNot resolution
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index firstRead.node.id, .index secondRead.node.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some outer.node.id)

theorem nested_input_types (shape : NestedShape header.function.source) :
    header.types = [nestedType, .word, .word] := by
  have params : header.function.parameters = [shape.table, shape.first, shape.second] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.firstScheme,
    shape.secondScheme, TypeSystem.Scheme.mono] using types.symm

/-- Both original keys are evaluated in source order; the latest root is
updated through both existing entries and read again by the original return. -/
theorem nested_call (shape : NestedShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (first second previous : Word) :
    PlainValue anchor header invocation before
      [nestedValue first second previous, .word first, .word second]
      (.word previous.bitNot) (nestedHeap before first second previous.bitNot) := by
  let original := nestedValue first second previous
  let replacement := nestedValue first second previous.bitNot
  let tableHeap := appendCell before nestedType (some original)
  let firstHeap := appendCell tableHeap .word (some (.word first))
  let current := appendCell firstHeap .word (some (.word second))
  let environment : Dynamic.Environment := [(shape.second.id, location firstHeap), (shape.first.id, location tableHeap), (shape.table.id, location before)]
  have tableAllocation : Dynamic.Heap.Allocates before nestedType (some original) (location before) tableHeap := .append
  have firstAllocation : Dynamic.Heap.Allocates tableHeap .word (some (.word first)) (location tableHeap) firstHeap := .append
  have secondAllocation : Dynamic.Heap.Allocates firstHeap .word (some (.word second)) (location firstHeap) current := .append
  have rootRead := secondAllocation.preserves_read (firstAllocation.preserves_read tableAllocation.reads_new)
  have firstRead := secondAllocation.preserves_read firstAllocation.reads_new
  have secondRead := secondAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.first, shape.second] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word first, .word second] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact tableAllocation)
      (.cons (by rw [shape.firstScheme]; exact firstAllocation)
        (.cons (by rw [shape.secondScheme]; exact secondAllocation) (.nil _ _)))
  have rootLookup : Dynamic.Environment.LooksUp environment shape.table.id (location before) :=
    .tail shape.secondTable (.tail shape.firstTable .head)
  have firstLookup : Dynamic.Environment.LooksUp environment shape.first.id (location tableHeap) :=
    .tail shape.secondFirst .head
  have secondLookup : Dynamic.Environment.LooksUp environment shape.second.id (location firstHeap) :=
    .head
  have firstEqual : Dynamic.ValueEquivalent (.word first) (.word first) := .refl (.word first)
  have secondEqual : Dynamic.ValueEquivalent (.word second) (.word second) := .refl (.word second)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.resolution.target
      { location := location before, rootType := nestedType, valueType := shape.resolution.target.type,
        projections := [.index (.word first), .index (.word second)], selected := some (.word previous) } current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨nestedType, some original, none⟩) (currentCell := ⟨nestedType, some original, none⟩)
    · rw [shape.targetRoot]; exact rootLookup
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.firstRead _ _ _ _ _ _ firstLookup firstRead)
        (.index (read_value shape.secondRead _ _ _ _ _ _ secondLookup secondRead) .nil)
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head firstEqual) (.indexFound (.head secondEqual) .nil)
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (nestedHeap before first second previous.bitNot) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, firstHeap, tableHeap, appendCell, original, replacement,
      nestedHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨nestedType, some original, none⟩ ⟨nestedType, some replacement, none⟩
        [⟨.word, some (.word first), none⟩, ⟨.word, some (.word second), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assigned.id
      header.context (.fallthrough environment) (nestedHeap before first second previous.bitNot) := by
    apply Dynamic.StatementExecutes.assignBitNot (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head firstEqual)
        (.indexFound (.head secondEqual) (.leaf (.word previous)) (.update (.head secondEqual)))
        (.update (.head firstEqual))) write
  let finalTable := appendCell before nestedType (some replacement)
  let finalFirst := appendCell finalTable .word (some (.word first))
  let finalSecond := appendCell finalFirst .word (some (.word second))
  have finalTableAllocation : Dynamic.Heap.Allocates before nestedType (some replacement) (location before) finalTable := .append
  have finalFirstAllocation : Dynamic.Heap.Allocates finalTable .word (some (.word first)) (location tableHeap) finalFirst := by
    have same : location tableHeap = location finalTable := by simp [location, tableHeap, finalTable, appendCell]
    rw [same]; exact .append
  have finalSecondAllocation : Dynamic.Heap.Allocates finalFirst .word (some (.word second)) (location firstHeap) finalSecond := by
    have same : location firstHeap = location finalFirst := by simp [location, firstHeap, finalFirst, tableHeap, finalTable, appendCell]
    rw [same]; exact .append
  have finalRootRead := finalSecondAllocation.preserves_read (finalFirstAllocation.preserves_read finalTableAllocation.reads_new)
  have finalFirstRead := finalSecondAllocation.preserves_read finalFirstAllocation.reads_new
  have finalSecondRead := finalSecondAllocation.reads_new
  have returned : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment
      (nestedHeap before first second previous.bitNot) shape.outer.node.id
      (.word previous.bitNot) (nestedHeap before first second previous.bitNot) := index_read shape.outer
    (index_read shape.inner (read_value shape.baseRead _ _ _ _ _ _ rootLookup finalRootRead)
      (read_value shape.returnFirst _ _ _ _ _ _ firstLookup finalFirstRead) (.head firstEqual))
    (read_value shape.returnSecond _ _ _ _ _ _ secondLookup finalSecondRead) (.head secondEqual)
  have roots : header.function.body = [shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned (.word previous.bitNot)) (nestedHeap before first second previous.bitNot) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm returned))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


end Tests.SourceCoreSelectedProjectedBitNot
