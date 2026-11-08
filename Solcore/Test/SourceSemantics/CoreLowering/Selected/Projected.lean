import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.PublicOutputs
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Core.Internal.PrimitiveLaws

/-!
# Selected projected tests

Projected assignments, projected bit-not and proxies.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedAssignmentProgram
set_option autoImplicit false
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Frontend

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function replace(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] = right; return table; }",
    "function add(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] += right; return table; }",
    "function divide(table: mapping(Word => Word), key: Word, right: Word) returns (mapping(Word => Word)) { table[key] /= right; return table; }",
    "function ordered(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] = 80; table[9] = 90; return table; }",
    "function nested(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word, right: Word) returns (Word) { table[first][second] += right; return table[first][second]; }",
    "function key(value: Word) returns (Word) { let copy: Word = value; return copy; }",
    "function failedKey(value: Word) returns (Word) { let copy: Word = value; let absent: Word; return absent; }",
    "function effects(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[key(index)] += key(right); return table; }",
    "function keyFailure(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[failedKey(index)] += key(right); return table; }",
    "function rhsFailure(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { table[key(index)] += failedKey(right); return table; }",
    "function missing(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { let absent: Word; table[index] += absent; return table; }",
    "function initialize(table: mapping(Word => Word), index: Word, right: Word) returns (mapping(Word => Word)) { for (table[index] = right; false; table[index] += 1) { } return table; }",
    "function post(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; i < 1; table[i] += 2, i += 1) { continue; } return table; }",
    "function stop(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; true; table[i] += 2) { break; } return table; }",
    "function make(table: mapping(Word => Word)) returns (function(Word) returns (Word)) { return lam(index: Word) -> Word { table[index] += 1; return table[index]; }; }"
  ]}] }

def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

end Tests.SourceCoreSelectedProjectedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedAssignmentSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedAssignment
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
    (key right : Word) : Dynamic.Heap :=
  appendCell (appendCell (appendCell before mappingType (some (mappingValue entries)))
    .word (some (.word key))) .word (some (.word right))

structure UpdateShape (source : TypedSource) (operator : Syntax.ValueAssignOp) where
  table : TypedBinder
  key : TypedBinder
  right : TypedBinder
  resolution : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  rightRead : Tests.SourceCoreNamedBranch.WordRead source right
  result : Tests.SourceCoreNamedBranch.Read source table mappingType
  inputs : source.inputs = [table, key, right]
  tableScheme : table.scheme = .mono mappingType
  keyScheme : key.scheme = .mono .word
  rightScheme : right.scheme = .mono .word
  keyTable : key.id ≠ table.id
  rightTable : right.id ≠ table.id
  rightKey : right.id ≠ key.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignValue resolution operator rightRead.node.id
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

theorem update_input_types {operator} (shape : UpdateShape header.function.source operator) :
    header.types = [mappingType, .word, .word] := by
  have params : header.function.parameters = [shape.table, shape.key, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.keyScheme,
    shape.rightScheme, TypeSystem.Scheme.mono] using types.symm

theorem update_call {operator} (shape : UpdateShape header.function.source operator)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous right updated : Word) (tail : List (Dynamic.Value × Dynamic.Value))
    (operation : Dynamic.AssignmentValueApplies operator (some (.word previous))
      (.word right) (.word updated)) :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key, .word right]
      (mappingValue ((.word key, .word updated) :: tail))
      (parameterHeap before ((.word key, .word updated) :: tail) key right) := by
  let original := mappingValue ((.word key, .word previous) :: tail)
  let replacement := mappingValue ((.word key, .word updated) :: tail)
  let first := appendCell before mappingType (some original)
  let second := appendCell first .word (some (.word key))
  let current := appendCell second .word (some (.word right))
  let environment : Dynamic.Environment :=
    [(shape.right.id, location second), (shape.key.id, location first), (shape.table.id, location before)]
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) second := .append
  have rightAllocation : Dynamic.Heap.Allocates second .word (some (.word right)) (location second) current := .append
  have rootRead := rightAllocation.preserves_read (keyAllocation.preserves_read rootAllocation.reads_new)
  have keyRead := rightAllocation.preserves_read keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word key, .word right] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation)
        (.cons (by rw [shape.rightScheme]; exact rightAllocation) (.nil _ _)))
  have equalKey : Dynamic.ValueEquivalent (.word key) (.word key) := .refl (.word key)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.rightTable (.tail shape.keyTable .head)
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.tail shape.rightKey .head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head equalKey) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (parameterHeap before ((.word key, .word updated) :: tail) key right) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, second, first, appendCell, original, replacement,
      parameterHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨mappingType, some original, none⟩
        ⟨mappingType, some replacement, none⟩ [⟨.word, some (.word key), none⟩, ⟨.word, some (.word right), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.assigned.id header.context (.fallthrough environment)
      (parameterHeap before ((.word key, .word updated) :: tail) key right) := by
    apply Dynamic.StatementExecutes.assignValue (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve (read_value shape.rightRead _ _ _ _ _ _ .head rightAllocation.reads_new) ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head equalKey) (.leaf operation) (.update (.head equalKey))) write
  have finalRootRead : Dynamic.Heap.Reads
      (parameterHeap before ((.word key, .word updated) :: tail) key right)
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
      (parameterHeap before ((.word key, .word updated) :: tail) key right) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_value shape.result _ _ _ _ _ _ (.tail shape.rightTable (.tail shape.keyTable .head)) finalRootRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

theorem equal_call (shape : UpdateShape header.function.source .equal)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous right : Word) (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key, .word right]
      (mappingValue ((.word key, .word right) :: tail))
      (parameterHeap before ((.word key, .word right) :: tail) key right) :=
  update_call header shape sourceAt anchor invocation before key previous right right tail (.equal _ _)

theorem add_call (shape : UpdateShape header.function.source .add)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous right : Word) (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key, .word right]
      (mappingValue ((.word key, .word (previous + right)) :: tail))
      (parameterHeap before ((.word key, .word (previous + right)) :: tail) key right) :=
  update_call header shape sourceAt anchor invocation before key previous right (previous + right) tail
    (.add (.wordAdd previous right))

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
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  rightRead : Tests.SourceCoreNamedBranch.WordRead source absent
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
  assignedForm : assigned.form = .assignValue resolution .add rightRead.node.id
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index keyRead.node.id]

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

/-- The index is read before the genuine RHS fault. No reconstructed mapping
is written; all parameter and absent-local cells remain at the reached heap. -/
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
  have keyRead := absentAllocation.preserves_read keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [original, .word key]
      environment second := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation) (.nil _ _))
  obtain ⟨localContext, extension⟩ := missing_extension header shape certified
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment current shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.absentTable (.tail shape.keyTable .head)
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.tail shape.absentKey .head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head (.refl (.word key))) .nil
  have rightFault : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment current
      shape.rightRead.node.id (.uninitializedLocation (location second)) current := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.rightRead.found)
    rw [shape.rightRead.form]
    exact Dynamic.ExpressionFormFaults.localUninitialized
      (requirements := shape.rightRead.node.requirements)
      (coercions := shape.rightRead.node.coercions) (owned := [])
      (by rw [shape.rightRead.requirements, shape.rightRead.coercions]; rfl)
      .head absentAllocation.reads_new rfl rfl (by rintro ⟨keyType, valueType, impossible⟩; cases impossible)
  have failed : Dynamic.StatementFaults (Program.ofChecked compiled.sourceProgram)
      localContext header.function.evidence header.function.source localEnvironment current
      shape.assigned.id (.uninitializedLocation (location second)) current :=
    .assignValue (lookupStatement?_sound shape.assignedFound) shape.assignedForm (.rhs resolve rightFault)
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

structure InitializerShape (source : TypedSource) where
  table : TypedBinder
  key : TypedBinder
  right : TypedBinder
  resolution : AssignmentResolution
  condition : ExpressionNode
  post : List ForItemForm
  assigned : StatementNode
  returned : StatementNode
  keyRead : Tests.SourceCoreNamedBranch.WordRead source key
  rightRead : Tests.SourceCoreNamedBranch.WordRead source right
  result : Tests.SourceCoreNamedBranch.Read source table mappingType
  inputs : source.inputs = [table, key, right]
  tableScheme : table.scheme = .mono mappingType
  keyScheme : key.scheme = .mono .word
  rightScheme : right.scheme = .mono .word
  keyTable : key.id ≠ table.id
  rightTable : right.id ≠ table.id
  rightKey : right.id ≠ key.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .forLoop [.assignValue resolution .equal rightRead.node.id] condition.id post []
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
    header.types = [mappingType, .word, .word] := by
  have params : header.function.parameters = [shape.table, shape.key, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.keyScheme,
    shape.rightScheme, TypeSystem.Scheme.mono] using types.symm

/-- Execute the actual projected initializer before the false condition; the post is skipped. -/
theorem initializer_call (shape : InitializerShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (key previous right : Word) (tail : List (Dynamic.Value × Dynamic.Value))
 :
    PlainValue anchor header invocation before
      [mappingValue ((.word key, .word previous) :: tail), .word key, .word right]
      (mappingValue ((.word key, .word right) :: tail))
      (parameterHeap before ((.word key, .word right) :: tail) key right) := by
  let original := mappingValue ((.word key, .word previous) :: tail)
  let replacement := mappingValue ((.word key, .word right) :: tail)
  let first := appendCell before mappingType (some original)
  let second := appendCell first .word (some (.word key))
  let current := appendCell second .word (some (.word right))
  let environment : Dynamic.Environment :=
    [(shape.right.id, location second), (shape.key.id, location first), (shape.table.id, location before)]
  have rootAllocation : Dynamic.Heap.Allocates before mappingType (some original) (location before) first := .append
  have keyAllocation : Dynamic.Heap.Allocates first .word (some (.word key)) (location first) second := .append
  have rightAllocation : Dynamic.Heap.Allocates second .word (some (.word right)) (location second) current := .append
  have rootRead := rightAllocation.preserves_read (keyAllocation.preserves_read rootAllocation.reads_new)
  have keyRead := rightAllocation.preserves_read keyAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.key, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word key, .word right] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact rootAllocation)
      (.cons (by rw [shape.keyScheme]; exact keyAllocation)
        (.cons (by rw [shape.rightScheme]; exact rightAllocation) (.nil _ _)))
  have equalKey : Dynamic.ValueEquivalent (.word key) (.word key) := .refl (.word key)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.resolution.target
      {location := location before, rootType := mappingType, valueType := shape.resolution.target.type,
        projections := [.index (.word key)], selected := some (.word previous)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType, some original, none⟩)
      (currentCell := ⟨mappingType, some original, none⟩)
    · rw [shape.targetRoot]; exact .tail shape.rightTable (.tail shape.keyTable .head)
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (read_value shape.keyRead _ _ _ _ _ _ (.tail shape.rightKey .head) keyRead) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head equalKey) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement)
      (parameterHeap before ((.word key, .word right) :: tail) key right) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, second, first, appendCell, original, replacement,
      parameterHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨mappingType, some original, none⟩
        ⟨mappingType, some replacement, none⟩ [⟨.word, some (.word key), none⟩, ⟨.word, some (.word right), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current
      shape.assigned.id header.context (.fallthrough environment)
      (parameterHeap before ((.word key, .word right) :: tail) key right) := by
    have initial : Dynamic.ForItemsExecute (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source environment current
        [.assignValue shape.resolution .equal shape.rightRead.node.id]
        header.context environment (parameterHeap before ((.word key, .word right) :: tail) key right) := by
      apply Dynamic.ForItemsExecute.cons (nextEnvironment := environment)
        (middle := parameterHeap before ((.word key, .word right) :: tail) key right)
      · apply Dynamic.ForItemExecutes.assignValue (updatedRoot := replacement)
        refine .intro resolve (read_value shape.rightRead _ _ _ _ _ _ .head rightAllocation.reads_new) ?_
        exact .intro rootRead rfl .initialized
          (.indexFound (.head equalKey) (.leaf (.equal _ _)) (.update (.head equalKey))) write
      · exact .nil
    have condition : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source environment
        (parameterHeap before ((.word key, .word right) :: tail) key right) shape.condition.id (.bool false)
        (parameterHeap before ((.word key, .word right) :: tail) key right) := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionFound)
      · rw [shape.conditionForm]
        exact .builtinBoolean (by rw [shape.conditionRequirements, shape.conditionCoercions]; rfl)
      · rw [shape.conditionCoercions]; exact .nil
    exact Dynamic.StatementExecutes.forLoop (lookupStatement?_sound shape.assignedFound) shape.assignedForm initial (.done condition)
  have finalRootRead : Dynamic.Heap.Reads
      (parameterHeap before ((.word key, .word right) :: tail) key right)
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
      (parameterHeap before ((.word key, .word right) :: tail) key right) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
        (read_value shape.result _ _ _ _ _ _ (.tail shape.rightTable (.tail shape.keyTable .head)) finalRootRead)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

def nestedType : TypeSystem.Ty := .mapping .word mappingType
def nestedValue (first second value : Word) : Dynamic.Value :=
  .mapping .word mappingType [(.word first, mappingValue [(.word second, .word value)])]
def nestedHeap (before : Dynamic.Heap) (first second right value : Word) : Dynamic.Heap :=
  appendCell (appendCell (appendCell (appendCell before nestedType (some (nestedValue first second value)))
    .word (some (.word first))) .word (some (.word second))) .word (some (.word right))

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
  right : TypedBinder
  resolution : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  firstRead : Tests.SourceCoreNamedBranch.WordRead source first
  secondRead : Tests.SourceCoreNamedBranch.WordRead source second
  rightRead : Tests.SourceCoreNamedBranch.WordRead source right
  baseRead : Tests.SourceCoreNamedBranch.Read source table nestedType
  returnFirst : Tests.SourceCoreNamedBranch.WordRead source first
  returnSecond : Tests.SourceCoreNamedBranch.WordRead source second
  inner : IndexRead source baseRead.node.id returnFirst.node.id
  outer : IndexRead source inner.node.id returnSecond.node.id
  inputs : source.inputs = [table, first, second, right]
  tableScheme : table.scheme = .mono nestedType
  firstScheme : first.scheme = .mono .word
  secondScheme : second.scheme = .mono .word
  rightScheme : right.scheme = .mono .word
  firstTable : first.id ≠ table.id
  secondTable : second.id ≠ table.id
  secondFirst : second.id ≠ first.id
  rightTable : right.id ≠ table.id
  rightFirst : right.id ≠ first.id
  rightSecond : right.id ≠ second.id
  roots : source.roots = [.statement assigned.id, .statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignValue resolution .add rightRead.node.id
  targetRoot : resolution.target.root = table.id
  targetProjections : resolution.target.projections = [.index firstRead.node.id, .index secondRead.node.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some outer.node.id)

theorem nested_input_types (shape : NestedShape header.function.source) :
    header.types = [nestedType, .word, .word, .word] := by
  have params : header.function.parameters = [shape.table, shape.first, shape.second, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.tableScheme, shape.firstScheme,
    shape.secondScheme, shape.rightScheme, TypeSystem.Scheme.mono] using types.symm

/-- Both original keys are evaluated in source order; the latest root is
updated through both existing entries and read again by the original return. -/
theorem nested_call (shape : NestedShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (first second previous right : Word) :
    PlainValue anchor header invocation before
      [nestedValue first second previous, .word first, .word second, .word right]
      (.word (previous + right)) (nestedHeap before first second right (previous + right)) := by
  let original := nestedValue first second previous
  let replacement := nestedValue first second (previous + right)
  let tableHeap := appendCell before nestedType (some original)
  let firstHeap := appendCell tableHeap .word (some (.word first))
  let secondHeap := appendCell firstHeap .word (some (.word second))
  let current := appendCell secondHeap .word (some (.word right))
  let environment : Dynamic.Environment := [(shape.right.id, location secondHeap),
    (shape.second.id, location firstHeap), (shape.first.id, location tableHeap), (shape.table.id, location before)]
  have tableAllocation : Dynamic.Heap.Allocates before nestedType (some original) (location before) tableHeap := .append
  have firstAllocation : Dynamic.Heap.Allocates tableHeap .word (some (.word first)) (location tableHeap) firstHeap := .append
  have secondAllocation : Dynamic.Heap.Allocates firstHeap .word (some (.word second)) (location firstHeap) secondHeap := .append
  have rightAllocation : Dynamic.Heap.Allocates secondHeap .word (some (.word right)) (location secondHeap) current := .append
  have rootRead := rightAllocation.preserves_read (secondAllocation.preserves_read (firstAllocation.preserves_read tableAllocation.reads_new))
  have firstRead := rightAllocation.preserves_read (secondAllocation.preserves_read firstAllocation.reads_new)
  have secondRead := rightAllocation.preserves_read secondAllocation.reads_new
  have params : header.function.parameters = [shape.table, shape.first, shape.second, shape.right] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters
      [original, .word first, .word second, .word right] environment current := by
    rw [params]
    exact .cons (by rw [shape.tableScheme]; exact tableAllocation)
      (.cons (by rw [shape.firstScheme]; exact firstAllocation)
        (.cons (by rw [shape.secondScheme]; exact secondAllocation)
          (.cons (by rw [shape.rightScheme]; exact rightAllocation) (.nil _ _))))
  have rootLookup : Dynamic.Environment.LooksUp environment shape.table.id (location before) :=
    .tail shape.rightTable (.tail shape.secondTable (.tail shape.firstTable .head))
  have firstLookup : Dynamic.Environment.LooksUp environment shape.first.id (location tableHeap) :=
    .tail shape.rightFirst (.tail shape.secondFirst .head)
  have secondLookup : Dynamic.Environment.LooksUp environment shape.second.id (location firstHeap) :=
    .tail shape.rightSecond .head
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
      (nestedHeap before first second right (previous + right)) := by
    apply Dynamic.Heap.Writes.intro rootRead
    simpa only [current, secondHeap, firstHeap, tableHeap, appendCell, original, replacement,
      nestedHeap, location, List.append_assoc, List.cons_append, List.nil_append] using
      write_append before.cells ⟨nestedType, some original, none⟩ ⟨nestedType, some replacement, none⟩
        [⟨.word, some (.word first), none⟩, ⟨.word, some (.word second), none⟩, ⟨.word, some (.word right), none⟩]
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assigned.id
      header.context (.fallthrough environment) (nestedHeap before first second right (previous + right)) := by
    apply Dynamic.StatementExecutes.assignValue (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve (read_value shape.rightRead _ _ _ _ _ _ .head rightAllocation.reads_new) ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head firstEqual)
        (.indexFound (.head secondEqual) (.leaf (.add (.wordAdd previous right))) (.update (.head secondEqual)))
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
  have finalRightAllocation : Dynamic.Heap.Allocates finalSecond .word (some (.word right)) (location secondHeap)
      (nestedHeap before first second right (previous + right)) := by
    have same : location secondHeap = location finalSecond := by simp [location, secondHeap, finalSecond, firstHeap, finalFirst, tableHeap, finalTable, appendCell]
    rw [same]; exact .append
  have finalRootRead := finalRightAllocation.preserves_read
    (finalSecondAllocation.preserves_read (finalFirstAllocation.preserves_read finalTableAllocation.reads_new))
  have finalFirstRead := finalRightAllocation.preserves_read (finalSecondAllocation.preserves_read finalFirstAllocation.reads_new)
  have finalSecondRead := finalRightAllocation.preserves_read finalSecondAllocation.reads_new
  have returned : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment
      (nestedHeap before first second right (previous + right)) shape.outer.node.id
      (.word (previous + right)) (nestedHeap before first second right (previous + right)) := index_read shape.outer
    (index_read shape.inner (read_value shape.baseRead _ _ _ _ _ _ rootLookup finalRootRead)
      (read_value shape.returnFirst _ _ _ _ _ _ firstLookup finalFirstRead) (.head firstEqual))
    (read_value shape.returnSecond _ _ _ _ _ _ secondLookup finalSecondRead) (.head secondEqual)
  have roots : header.function.body = [shape.assigned.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned (.word (previous + right))) (nestedHeap before first second right (previous + right)) := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm returned))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedProjectedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedAssignmentFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "projected artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "projected original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "projected original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "projected global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "projected substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "projected ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "projected ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "projected unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

private def statement (source : TypedSource) (id : NodeId) : IO StatementNode := do
  let .statement sid := id | throw (IO.userError "projected statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "projected statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "projected read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeUpdate (source : TypedSource) (operator : Syntax.ValueAssignOp) : IO (UpdateShape source operator) := do
  let [table, key, right] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .assignValue resolution _ rhsId := assigned.form | throw (IO.userError "projected assignment form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let rightRead ← wordRead source right rhsId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key, right]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "projected right scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨rightTable⟩ ← observed (right.id ≠ table.id) "projected distinct right/table"
  let ⟨rightKey⟩ ← observed (right.id ≠ key.id) "projected distinct right/key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue resolution operator rightRead.node.id) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  return ⟨table, key, right, resolution, assigned, returned, keyRead, rightRead, result, inputs,
    tableScheme, keyScheme, rightScheme, keyTable, rightTable, rightKey, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm⟩

def observeInitializer (source : TypedSource) : IO (InitializerShape source) := do
  let [table, key, right] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .forLoop [.assignValue resolution .equal rhsId] conditionId post [] := assigned.form | throw (IO.userError "projected initializer form")
  let some condition := source.lookupExpression? conditionId | throw (IO.userError "projected initializer condition")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let rightRead ← wordRead source right rhsId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key, right]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "projected right scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨rightTable⟩ ← observed (right.id ≠ table.id) "projected distinct right/table"
  let ⟨rightKey⟩ ← observed (right.id ≠ key.id) "projected distinct right/key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .forLoop [.assignValue resolution .equal rightRead.node.id] condition.id post []) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "initializer condition identity"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference "false" (.builtinBoolean false)) "initializer false condition"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "initializer condition requirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "initializer condition coercions"
  return ⟨table, key, right, resolution, condition, post, assigned, returned, keyRead, rightRead, result, inputs,
    tableScheme, keyScheme, rightScheme, keyTable, rightTable, rightKey, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm, conditionFound, conditionForm, conditionRequirements, conditionCoercions⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "missing inputs")
  let [first, second, third] := source.roots | throw (IO.userError "missing roots")
  let declared ← statement source first
  let assigned ← statement source second
  let returned ← statement source third
  let .letDecl absent none := declared.form | throw (IO.userError "missing declaration")
  let .assignValue resolution .add rhsId := assigned.form | throw (IO.userError "missing assignment")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "missing index")
  let keyRead ← wordRead source key keyId
  let rightRead ← wordRead source absent rhsId
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "missing original inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "missing table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "missing key scheme"
  let ⟨absentScheme⟩ ← observed (absent.scheme = .mono .word) "missing absent scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "missing distinct key"
  let ⟨absentTable⟩ ← observed (absent.id ≠ table.id) "missing distinct absent/table"
  let ⟨absentKey⟩ ← observed (absent.id ≠ key.id) "missing distinct absent/key"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assigned.id, .statement returned.id]) "missing original roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl absent none) "missing declaration form"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "missing assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue resolution .add rightRead.node.id) "missing assignment form"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "missing target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "missing key identity"
  return ⟨table, key, absent, resolution, declared, assigned, returned, keyRead, rightRead, inputs,
    tableScheme, keyScheme, absentScheme, keyTable, absentTable, absentKey, roots,
    declaredFound, declaredForm, assignedFound, assignedForm, targetRoot, targetProjections⟩

def observeCopy (source : TypedSource) : IO (CopyShape source) := do
  let [argument] := source.inputs | throw (IO.userError "copy inputs")
  let [first, second] := source.roots | throw (IO.userError "copy roots")
  let initialized ← statement source first
  let returned ← statement source second
  let .letDecl copy (some initializerId) := initialized.form | throw (IO.userError "copy initialized local")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "copy return")
  let initializer ← wordRead source argument initializerId
  let result ← wordRead source copy resultId
  let ⟨inputs⟩ ← observed (source.inputs = [argument]) "copy original inputs"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "copy argument scheme"
  let ⟨copyScheme⟩ ← observed (copy.scheme = .mono .word) "copy local scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement returned.id]) "copy original roots"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "copy initialized identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl copy (some initializer.node.id)) "copy initialized form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "copy returned identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "copy returned form"
  return ⟨argument, copy, initialized, returned, initializer, result, inputs, argumentScheme,
    copyScheme, roots, initializedFound, initializedForm, returnedFound, returnedForm⟩

private def expression (source : TypedSource) (id : ExpressionId) : IO ExpressionNode := do
  let some node := source.lookupExpression? id | throw (IO.userError "nested expression lookup")
  return node

private def observeIndex (source : TypedSource) (node : ExpressionNode) (base key : ExpressionId) :
    IO (IndexRead source base key) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "nested index identity"
  let ⟨form⟩ ← observed (node.form = .index base key) "nested index form"
  let ⟨requirements⟩ ← observed (node.requirements = []) "nested index requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "nested index coercions"
  return ⟨node, found, form, requirements, coercions⟩

def observeNested (source : TypedSource) : IO (NestedShape source) := do
  let [table, first, second, right] := source.inputs | throw (IO.userError "nested original inputs")
  let [a, b] := source.roots | throw (IO.userError "nested original roots")
  let assigned ← statement source a
  let returned ← statement source b
  let .assignValue resolution .add rhsId := assigned.form | throw (IO.userError "nested assignment")
  let [.index firstId, .index secondId] := resolution.target.projections | throw (IO.userError "nested target indices")
  let firstRead ← wordRead source first firstId
  let secondRead ← wordRead source second secondId
  let rightRead ← wordRead source right rhsId
  let .returnStmt (some returnedId) := returned.form | throw (IO.userError "nested return")
  let outerNode ← expression source returnedId
  let .index innerId secondReturnId := outerNode.form | throw (IO.userError "nested outer return index")
  let innerNode ← expression source innerId
  let .index baseId firstReturnId := innerNode.form | throw (IO.userError "nested inner return index")
  let baseNode ← expression source baseId
  let baseRead ← Tests.SourceCoreNamedBranch.observeRead source table baseNode nestedType
  let returnFirst ← wordRead source first firstReturnId
  let returnSecond ← wordRead source second secondReturnId
  let inner ← observeIndex source innerNode baseRead.node.id returnFirst.node.id
  let outer ← observeIndex source outerNode inner.node.id returnSecond.node.id
  let ⟨inputs⟩ ← observed (source.inputs = [table, first, second, right]) "nested inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono nestedType) "nested tableScheme"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono .word) "nested firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono .word) "nested secondScheme"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "nested rightScheme"
  let ⟨firstTable⟩ ← observed (first.id ≠ table.id) "nested firstTable"
  let ⟨secondTable⟩ ← observed (second.id ≠ table.id) "nested secondTable"
  let ⟨secondFirst⟩ ← observed (second.id ≠ first.id) "nested secondFirst"
  let ⟨rightTable⟩ ← observed (right.id ≠ table.id) "nested rightTable"
  let ⟨rightFirst⟩ ← observed (right.id ≠ first.id) "nested rightFirst"
  let ⟨rightSecond⟩ ← observed (right.id ≠ second.id) "nested rightSecond"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "nested roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "nested assignedFound"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue resolution .add rightRead.node.id) "nested assignedForm"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "nested targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index firstRead.node.id, .index secondRead.node.id]) "nested targetProjections"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "nested returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some outer.node.id)) "nested returnedForm"
  return ⟨table, first, second, right, resolution, assigned, returned, firstRead, secondRead, rightRead,
    baseRead, returnFirst, returnSecond, inner, outer, inputs, tableScheme, firstScheme, secondScheme, rightScheme, firstTable, secondTable, secondFirst, rightTable, rightFirst, rightSecond, roots, assignedFound, assignedForm, targetRoot, targetProjections, returnedFound, returnedForm⟩

structure ObservedProgram (fixture : CompiledFixture) where
  nestedRow : Row fixture
  initializerRow : Row fixture
  keyRow : Row fixture
  replaceRow : Row fixture
  addRow : Row fixture
  divideRow : Row fixture
  missingRow : Row fixture
  nestedShape : NestedShape nestedRow.original.function.typedBody
  initializerShape : InitializerShape initializerRow.original.function.typedBody
  keyShape : CopyShape keyRow.original.function.typedBody
  replaceShape : UpdateShape replaceRow.original.function.typedBody .equal
  addShape : UpdateShape addRow.original.function.typedBody .add
  divideShape : UpdateShape divideRow.original.function.typedBody .divide
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 15
  originals : fixture.recipe.compiled.sourceProgram.signatures.functions.length = 15

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let nestedRow ← observeRow fixture "nested"
  let nestedShape ← observeNested nestedRow.original.function.typedBody
  let initializerRow ← observeRow fixture "initialize"
  let initializerShape ← observeInitializer initializerRow.original.function.typedBody
  let keyRow ← observeRow fixture "key"
  let keyShape ← observeCopy keyRow.original.function.typedBody
  let replaceRow ← observeRow fixture "replace"
  let addRow ← observeRow fixture "add"
  let divideRow ← observeRow fixture "divide"
  let missingRow ← observeRow fixture "missing"
  let replaceShape ← observeUpdate replaceRow.original.function.typedBody .equal
  let addShape ← observeUpdate addRow.original.function.typedBody .add
  let divideShape ← observeUpdate divideRow.original.function.typedBody .divide
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 15) "projected complete cache"
  let ⟨originals⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.functions.length = 15) "projected complete original program"
  return ⟨nestedRow, initializerRow, keyRow, replaceRow, addRow, divideRow, missingRow, nestedShape, initializerShape, keyShape, replaceShape, addShape, divideShape, missingShape, cacheSize, originals⟩

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "projected bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedProjectedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedAssignmentSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

def publicEntries (entries : List (Word × Word)) :
    List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def sourceEntries (entries : List (Word × Word)) : List (Dynamic.Value × Dynamic.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def dataEntries (entries : List (Word × Word)) :
    List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def publicMap (entries : List (Word × Word)) : SourceCorePublicValues.Value :=
  .mapping .word .word (publicEntries entries)

private theorem map_carrier (entries : List (Word × Word)) :
    publicMap entries = SourceCoreIndexedSession.DataInput.publicValue (.mapping .word .word (dataEntries entries)) := by
  simp only [publicMap, SourceCoreIndexedSession.DataInput.publicValue]
  congr 1
  induction entries with
  | nil => simp only [publicEntries, dataEntries, List.map_nil, SourceCoreIndexedSession.DataInput.publicEntries]
  | cons pair tail ih =>
    simpa only [publicEntries, dataEntries, List.map_cons,
      SourceCoreIndexedSession.DataInput.publicEntries, SourceCoreIndexedSession.DataInput.publicValue] using
        congrArg (List.cons (.word pair.1, .word pair.2)) ih

private theorem map_types (context : SourceSemantics.Context) (entries : List (Word × Word)) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicMap entries) mappingType := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty _ _
  | cons pair tail ih => exact .entry (.word pair.1) (.word pair.2) ih

private theorem map_meaning (entries : List (Word × Word)) :
    RecursiveNamedPublicDataInputs.Means (publicMap entries) (mappingValue (sourceEntries entries)) := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty
  | cons pair tail ih => exact .prepend (.word pair.1) (.word pair.2) ih

private theorem word_types (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (.word value) .word :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
private theorem word_meaning (value : Word) : RecursiveNamedPublicDataInputs.Means (.word value) (.word value) :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.keyRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7))
    (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 7)] (.value (.word (Word.ofNatModulo 7)))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7)) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe []
        initial.header.function.resultType started.call.checkpoint (.word (Word.ofNatModulo 7))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 7)]

/-- A genuine scalar helper initializes the same complete fifteen-row program.
Its ordinary Source trace is built before public completion; later calls use
that issued state's mapping-aware input path. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, _signatureSame⟩ := observed.keyRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have shape : CopyShape initial.header.function.source := by rw [sourceEq]; exact observed.keyShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping initial.header
  have plain := fun invocation => copy_call initial.header shape certified sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 7)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 7)], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl; exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 7)] initial.header.types := by
    rw [copy_input_types initial.header shape]
    exact .cons (word_types _ _) .nil
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple types
      (.cons (word_meaning _) .nil) (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure UpdateMeaning (row : Row fixture) (key previous right updated : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key, .word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key, .word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key, .word right]
    (mappingValue (sourceEntries ((key, updated) :: tail)))
    (parameterHeap state.heap (sourceEntries ((key, updated) :: tail)) key right)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key, .word right]
        (.value (mappingValue (sourceEntries ((key, updated) :: tail))))
        (parameterHeap state.heap (sourceEntries ((key, updated) :: tail)) key right) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (mappingValue (sourceEntries ((key, updated) :: tail)))
        (parameterHeap state.heap (sourceEntries ((key, updated) :: tail)) key right)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key, .word right]

/-- Exact original assignment syntax and a primitive Word operation determine
the whole ordered mapping output. The theorem requires no execution callback. -/
theorem update_from_source (row : Row fixture) {operator : Syntax.ValueAssignOp}
    (shape : UpdateShape row.original.function.typedBody operator)
    (key previous right updated : Word) (tail : List (Word × Word))
    (operation : Dynamic.AssignmentValueApplies operator (some (.word previous)) (.word right) (.word updated))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key, .word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (UpdateMeaning issued state row key previous right updated tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : UpdateShape request.header.function.source operator := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => update_call request.header actualShape sourceAt anchor invocation state.heap
    key previous right updated (sourceEntries tail) operation
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key, .word right]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key, .word right] := by
    rw [body_types, update_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _))
        (.cons (.data (word_types _ _) (word_meaning _)) .nil))
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture) (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
    (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
    (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.fault (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))))
        (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe
        (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key)))
        call (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]

/-- The original projected update resolves its key before the genuine absent
right-hand-side read. The fault retains its exact input and local allocations. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : MissingShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping request.header
  have plain := fun invocation => missing_call request.header actualShape certified sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
      (plain invocation)⟩⟩

/-- A genuine failure returns a state for the same complete issued catalog.
The next original addition starts at that exact reached heap. -/
theorem missing_then_reuse (missingRow addRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (addShape : UpdateShape addRow.original.function.typedBody .add)
    (key previous right : Word) (tail : List (Word × Word))
    (call : StartedCall session missingRow.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))) token ∧
            ∀ nextCall : StartedCall returned addRow.original.key
                [publicMap ((key, previous) :: tail), .word key, .word right] runOptions,
              Nonempty (UpdateMeaning issued next addRow key previous right (previous + right) tail nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow key previous tail call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape key previous tail call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact update_from_source issued next addRow addShape key previous right (previous + right) tail
      (.add (.wordAdd previous right)) nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

/-- The same public catalog executes the authentic for initializer and then
skips its post after the original false condition. -/
theorem initializer_from_source (row : Row fixture)
    (shape : InitializerShape row.original.function.typedBody)
    (key previous right : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key, .word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (UpdateMeaning issued state row key previous right right tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : InitializerShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => initializer_call request.header actualShape sourceAt anchor invocation state.heap
    key previous right (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key, .word right]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key, .word right] := by
    rw [body_types, initializer_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _))
        (.cons (.data (word_types _ _) (word_meaning _)) .nil))
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

def publicNested (first second previous : Word) : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(.word first, publicMap [(second, previous)])]

private theorem nested_types (context : SourceSemantics.Context) (first second previous : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicNested first second previous) nestedType := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.entry (.word first) (.mapping (.entry (.word second) (.word previous) (.empty _ _))) (.empty _ _))

private theorem nested_meaning (first second previous : Word) :
    RecursiveNamedPublicDataInputs.Means (publicNested first second previous) (nestedValue first second previous) := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.prepend (.word first) (.mapping (.prepend (.word second) (.word previous) .empty)) .empty)

structure NestedMeaning (row : Row fixture) (first second previous right : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second, .word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key
    [publicNested first second previous, .word first, .word second, .word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [nestedValue first second previous, .word first, .word second, .word right]
    (.word (previous + right)) (nestedHeap state.heap first second right (previous + right))
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [nestedValue first second previous, .word first, .word second, .word right]
        (.value (.word (previous + right))) (nestedHeap state.heap first second right (previous + right)) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (.word (previous + right))
        (nestedHeap state.heap first second right (previous + right))) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [nestedValue first second previous, .word first, .word second, .word right]

/-- The original two-key source trace connects to the same whole public
issuer; both key evaluations and the exact four parameter cells are retained. -/
theorem nested_from_source (row : Row fixture) (shape : NestedShape row.original.function.typedBody)
    (first second previous right : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second, .word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (NestedMeaning issued state row first second previous right call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : NestedShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => nested_call request.header actualShape sourceAt anchor invocation state.heap first second previous right
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicNested first second previous, .word first, .word second, .word right]
      [nestedValue first second previous, .word first, .word second, .word right] := by
    rw [body_types, nested_input_types request.header actualShape]
    exact .cons (.data (nested_types _ _ _ _) (nested_meaning _ _ _))
      (.cons (.data (word_types _ _) (word_meaning _))
        (.cons (.data (word_types _ _) (word_meaning _))
          (.cons (.data (word_types _ _) (word_meaning _)) .nil)))
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

/-- The independent bootstrap trace supplies the actual state for the first
mapping addition in the same issued session. No completed call is assumed. -/
theorem initial_then_add (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)])
    (key previous right : Word) (tail : List (Word × Word)) :
    ∃ meaning : InitialMeaning fixture observed started, ∀ invocation,
      (∃ requiredExecution requiredOutput,
        ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome started.artifact),
          requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
          started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
          ∃ completion : SourceCoreExecution.Completion started.artifact,
            outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
            ∃ next : meaning.issued.toIssued.State meaning.initial.header completion.session [],
              next.heap = copyHeap ⟨[]⟩ (Word.ofNatModulo 7) ∧
              ∀ nextCall : StartedCall completion.session observed.addRow.original.key
                  [publicMap ((key, previous) :: tail), .word key, .word right] runOptions,
                Nonempty (UpdateMeaning meaning.issued next observed.addRow key previous right
                  (previous + right) tail nextCall)) ∨
      SelectedCompilationStageClosedInitialForward.StageStopped meaning.issued started.call
        meaning.initial invocation [.word (Word.ofNatModulo 7)] := by
  obtain ⟨meaning⟩ := initial_from_source fixture observed profile started
  refine ⟨meaning, ?_⟩
  intro invocation
  rcases meaning.forward invocation with finished | stopped
  · obtain ⟨requiredExecution, requiredOutput, forward⟩ := finished.2
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨completion, outcomeEq, ready, next, heapEq, _value, _handles⟩ :=
      forward executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    refine ⟨completion, outcomeEq, ready, next, heapEq, ?_⟩
    intro nextCall
    exact update_from_source meaning.issued next observed.addRow observed.addShape key previous right
      (previous + right) tail (.add (.wordAdd previous right)) nextCall ready
  · exact .inr stopped

end Tests.SourceCoreSelectedProjectedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedAssignmentProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def table (entries : List (Nat × Nat)) : SourceCorePublicValues.Value :=
  .mapping .word .word (entries.map fun pair => (word pair.1, word pair.2))
private def nested : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(word 7, table [(2, 4)])]

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected startup" (session.start key arguments)
  let .outOfFuel suspended ← pending.resume 0 0
    | throw (IO.userError "projected zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "projected success missing")
  require (completed.value == expected) "projected result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected fault startup" (session.start key arguments)
  let .failed reason after ← pending.resume 100000 1000
    | throw (IO.userError "projected original read did not fail")
  let some diagnostic ← get "projected diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "projected diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "projected original read diagnostic changed"
  pure after

/-- All configured rows come from the unchanged complete original program.
The bootstrap-to-mapping theorem is constructed before execution. Ordered key
calls, fault prefixes, header controls and repeated calls of a retained closure,
each starting from its creation-time capture, are runtime companions. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "projected original selected profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 15 &&
      fixture.recipe.compiled.indexed.base.functions.length == 15 && profile.table.rows.length == 15)
    "projected original declarations/cache/table changed"
  let started ← observeStarted fixture observed.keyRow.original.key [word 7]
  have _sourceFirst := initial_then_add fixture observed profile started
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) (Word.ofNatModulo 3)
    [(Word.ofNatModulo 7, Word.ofNatModulo 99), (Word.ofNatModulo 2, Word.ofNatModulo 6)]
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "projected initial zero fuel did not suspend")
  let .succeeded initial ← suspended.resume 100000 1000
    | throw (IO.userError "projected initial helper failed")
  require (initial.value == word 7) "projected initial helper changed"
  let mut session := initial.session
  let mut heaps := [started.session.heapSize, initial.session.heapSize]
  for (name, arguments, expected) in [
      ("replace", [table [(7,4),(7,99),(2,6)], word 7, word 8], table [(7,8),(7,99),(2,6)]),
      ("add", [table [(7,4),(7,99),(2,6)], word 7, word 3], table [(7,7),(7,99),(2,6)]),
      ("divide", [table [(7,4)], word 7, word 0], table [(7,0)]),
      ("ordered", [table [(7,4),(7,99),(2,6)]], table [(7,80),(7,99),(2,6),(9,90)]),
      ("nested", [nested, word 7, word 2, word 3], word 7),
      ("effects", [table [(7,4)], word 7, word 3], table [(7,7)]),
      ("initialize", [table [], word 7, word 8], table [(7,8)]),
      ("post", [table []], table [(0,2)]),
      ("stop", [table []], table [])] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram name
    session ← success session key arguments expected
    heaps := heaps ++ [session.heapSize]
  for name in ["keyFailure", "rhsFailure", "missing"] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram name
    let arguments := if name == "missing" then [table [(7,4)], word 7]
      else [table [(7,4)], word 7, word 3]
    session ← failure session key arguments
    heaps := heaps ++ [session.heapSize]
  session ← success session observed.addRow.original.key [table [(7,4)], word 7, word 3] (table [(7,7)])
  heaps := heaps ++ [session.heapSize]
  let make ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram "make"
  let pending ← get "projected captured factory" (session.start make [table [(7,4)]])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "projected captured factory failed")
  let .function handle := made.value | throw (IO.userError "projected captured handle missing")
  let pending ← get "projected captured first" (made.session.startHandlePacked handle (word 7))
  let .succeeded first ← pending.resume 100000 1000
    | throw (IO.userError "projected captured first failed")
  let pending ← get "projected captured reuse" (first.session.startHandlePacked handle (word 7))
  let .succeeded last ← pending.resume 100000 1000
    | throw (IO.userError "projected captured reuse failed")
  require (first.value == word 5 && last.value == word 5) "projected captured result changed"
  heaps := heaps ++ [made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [16, 22, 40, 58, 76, 97, 133, 163, 182, 198, 205, 223, 250, 262, 280, 286, 304, 322])
    "projected exact native heaps changed"
  IO.println s!"PROJECTED_CACHE: cache{fixture.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  IO.println s!"PROJECTED_NATIVE_HEAPS: {heaps}"
  IO.println "PROJECTED_ASSIGNMENT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProjectedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotProgram
set_option autoImplicit false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Frontend

/-- One unchanged original program for two explicit compilation scopes. The
complete runtime companion configures every declaration as a seed. -/
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function key(value: Word) returns (Word) { let copy: Word = value; return copy; }",
    "function failedKey(value: Word) returns (Word) { let copy: Word = value; let absent: Word; return absent; }",
    "function invert(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[index] ~=; return table; }",
    "function nested(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word) returns (Word) { table[first][second] ~=; return table[first][second]; }",
    "function effects(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[key(index)] ~=; return table; }",
    "function keyFailure(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { let absent: Word; table[absent] ~=; return table; }",
    "function calledKeyFailure(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { table[failedKey(index)] ~=; return table; }",
    "function nestedFailure(table: mapping(Word => mapping(Word => Word)), first: Word, second: Word) returns (Word) { table[key(first)][failedKey(second)] ~=; return 0; }",
    "function initialize(table: mapping(Word => Word), index: Word) returns (mapping(Word => Word)) { for (table[index] ~=; false; table[index] ~=) { } return table; }",
    "function post(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; i < 1; table[i] ~=, i += 1) { continue; } return table; }",
    "function stop(table: mapping(Word => Word)) returns (mapping(Word => Word)) { for (let i: Word = 0; true; table[i] ~=) { break; } return table; }",
    "function make(table: mapping(Word => Word)) returns (function(Word) returns (Word)) { return lam(index: Word) -> Word { table[index] ~=; return table[index]; }; }",
    "function defaultLocal() returns (Word) { let table: mapping(Word => Word); table[1] ~=; return table[1]; }"
  ]}] }

def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

end Tests.SourceCoreSelectedProjectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

/-- Named/header proof entries are configured before compilation. The original
checked program still contains the captured factory, whose proof profile is a
separate recorded boundary. -/
def namedHeaderEntries : List String := [
  "key", "failedKey", "invert", "nested", "effects", "keyFailure",
  "calledKeyFailure", "nestedFailure", "initialize", "post", "stop", "defaultLocal"]

private def compileEntries (entries : Option (List String)) : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let selected := match entries with
      | none => program.signatures.functions
      | some names => program.signatures.functions.filter (fun signature => names.contains signature.name)
    let seeds := selected.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "projected artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


/-- Complete compiler/runtime companion: every original declaration is a seed. -/
def compileFixture : IO CompiledFixture := compileEntries none

/-- Actual selected compiler receipt for all twelve named/header entries. -/
def compileNamedHeaderFixture : IO CompiledFixture := compileEntries (some namedHeaderEntries)

structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "projected original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "projected original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "projected global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "projected substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "projected ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "projected ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "projected unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

private def statement (source : TypedSource) (id : NodeId) : IO StatementNode := do
  let .statement sid := id | throw (IO.userError "projected statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "projected statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "projected read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeUnary (source : TypedSource) : IO (UnaryShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .assignBitNot resolution := assigned.form | throw (IO.userError "projected assignment form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  return ⟨table, key, resolution, assigned, returned, keyRead, result, inputs,
    tableScheme, keyScheme, keyTable, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "missing inputs")
  let [first, second, third] := source.roots | throw (IO.userError "missing roots")
  let declared ← statement source first
  let assigned ← statement source second
  let returned ← statement source third
  let .letDecl absent none := declared.form | throw (IO.userError "missing declaration")
  let .assignBitNot resolution := assigned.form | throw (IO.userError "missing assignment")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "missing index")
  let absentRead ← wordRead source absent keyId
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "missing original inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "missing table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "missing key scheme"
  let ⟨absentScheme⟩ ← observed (absent.scheme = .mono .word) "missing absent scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "missing distinct key"
  let ⟨absentTable⟩ ← observed (absent.id ≠ table.id) "missing distinct absent/table"
  let ⟨absentKey⟩ ← observed (absent.id ≠ key.id) "missing distinct absent/key"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assigned.id, .statement returned.id]) "missing original roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl absent none) "missing declaration form"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "missing assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "missing assignment form"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "missing target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index absentRead.node.id]) "missing key identity"
  return ⟨table, key, absent, resolution, declared, assigned, returned, absentRead, inputs,
    tableScheme, keyScheme, absentScheme, keyTable, absentTable, absentKey, roots,
    declaredFound, declaredForm, assignedFound, assignedForm, targetRoot, targetProjections⟩

def observeCopy (source : TypedSource) : IO (CopyShape source) := do
  let [argument] := source.inputs | throw (IO.userError "copy inputs")
  let [first, second] := source.roots | throw (IO.userError "copy roots")
  let initialized ← statement source first
  let returned ← statement source second
  let .letDecl copy (some initializerId) := initialized.form | throw (IO.userError "copy initialized local")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "copy return")
  let initializer ← wordRead source argument initializerId
  let result ← wordRead source copy resultId
  let ⟨inputs⟩ ← observed (source.inputs = [argument]) "copy original inputs"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "copy argument scheme"
  let ⟨copyScheme⟩ ← observed (copy.scheme = .mono .word) "copy local scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id, .statement returned.id]) "copy original roots"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "copy initialized identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl copy (some initializer.node.id)) "copy initialized form"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "copy returned identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "copy returned form"
  return ⟨argument, copy, initialized, returned, initializer, result, inputs, argumentScheme,
    copyScheme, roots, initializedFound, initializedForm, returnedFound, returnedForm⟩

def observeInitializer (source : TypedSource) : IO (InitializerShape source) := do
  let [table, key] := source.inputs | throw (IO.userError "projected input count")
  let [first, second] := source.roots | throw (IO.userError "projected statement count")
  let assigned ← statement source first
  let returned ← statement source second
  let .forLoop [.assignBitNot resolution] conditionId post [] := assigned.form | throw (IO.userError "projected initializer form")
  let some condition := source.lookupExpression? conditionId | throw (IO.userError "projected initializer condition")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "projected key count")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "projected return form")
  let keyRead ← wordRead source key keyId
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "projected result lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source table resultNode mappingType
  let ⟨inputs⟩ ← observed (source.inputs = [table, key]) "projected inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "projected table scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "projected key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "projected distinct key"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "projected roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "projected assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .forLoop [.assignBitNot resolution] condition.id post []) "projected original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "projected target root"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "projected original key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "projected raw leaf"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "projected return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "projected return read"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "initializer condition identity"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference "false" (.builtinBoolean false)) "initializer false condition"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "initializer condition requirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "initializer condition coercions"
  return ⟨table, key, resolution, condition, post, assigned, returned, keyRead, result, inputs,
    tableScheme, keyScheme, keyTable, roots,
    assignedFound, assignedForm, targetRoot, targetProjections, targetType, returnedFound, returnedForm, conditionFound, conditionForm, conditionRequirements, conditionCoercions⟩

private def expression (source : TypedSource) (id : ExpressionId) : IO ExpressionNode := do
  let some node := source.lookupExpression? id | throw (IO.userError "nested expression lookup")
  return node

private def observeIndex (source : TypedSource) (node : ExpressionNode) (base key : ExpressionId) :
    IO (IndexRead source base key) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "nested index identity"
  let ⟨form⟩ ← observed (node.form = .index base key) "nested index form"
  let ⟨requirements⟩ ← observed (node.requirements = []) "nested index requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "nested index coercions"
  return ⟨node, found, form, requirements, coercions⟩

def observeNested (source : TypedSource) : IO (NestedShape source) := do
  let [table, first, second] := source.inputs | throw (IO.userError "nested original inputs")
  let [a, b] := source.roots | throw (IO.userError "nested original roots")
  let assigned ← statement source a
  let returned ← statement source b
  let .assignBitNot resolution := assigned.form | throw (IO.userError "nested assignment")
  let [.index firstId, .index secondId] := resolution.target.projections | throw (IO.userError "nested target indices")
  let firstRead ← wordRead source first firstId
  let secondRead ← wordRead source second secondId
  let .returnStmt (some returnedId) := returned.form | throw (IO.userError "nested return")
  let outerNode ← expression source returnedId
  let .index innerId secondReturnId := outerNode.form | throw (IO.userError "nested outer return index")
  let innerNode ← expression source innerId
  let .index baseId firstReturnId := innerNode.form | throw (IO.userError "nested inner return index")
  let baseNode ← expression source baseId
  let baseRead ← Tests.SourceCoreNamedBranch.observeRead source table baseNode nestedType
  let returnFirst ← wordRead source first firstReturnId
  let returnSecond ← wordRead source second secondReturnId
  let inner ← observeIndex source innerNode baseRead.node.id returnFirst.node.id
  let outer ← observeIndex source outerNode inner.node.id returnSecond.node.id
  let ⟨inputs⟩ ← observed (source.inputs = [table, first, second]) "nested inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono nestedType) "nested tableScheme"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono .word) "nested firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono .word) "nested secondScheme"
  let ⟨firstTable⟩ ← observed (first.id ≠ table.id) "nested firstTable"
  let ⟨secondTable⟩ ← observed (second.id ≠ table.id) "nested secondTable"
  let ⟨secondFirst⟩ ← observed (second.id ≠ first.id) "nested secondFirst"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id, .statement returned.id]) "nested roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "nested assignedFound"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "nested assignedForm"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "nested targetRoot"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index firstRead.node.id, .index secondRead.node.id]) "nested targetProjections"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "nested returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some outer.node.id)) "nested returnedForm"
  return ⟨table, first, second, resolution, assigned, returned, firstRead, secondRead,
    baseRead, returnFirst, returnSecond, inner, outer, inputs, tableScheme, firstScheme, secondScheme, firstTable, secondTable, secondFirst, roots, assignedFound, assignedForm, targetRoot, targetProjections, returnedFound, returnedForm⟩

structure ObservedProgram (fixture : CompiledFixture) where
  nestedRow : Row fixture
  initializerRow : Row fixture
  nestedShape : NestedShape nestedRow.original.function.typedBody
  initializerShape : InitializerShape initializerRow.original.function.typedBody
  keyRow : Row fixture
  invertRow : Row fixture
  missingRow : Row fixture
  keyShape : CopyShape keyRow.original.function.typedBody
  invertShape : UnaryShape invertRow.original.function.typedBody
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 12
  originals : fixture.recipe.compiled.sourceProgram.signatures.functions.length = 13

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let nestedRow ← observeRow fixture "nested"
  let initializerRow ← observeRow fixture "initialize"
  let nestedShape ← observeNested nestedRow.original.function.typedBody
  let initializerShape ← observeInitializer initializerRow.original.function.typedBody
  let keyRow ← observeRow fixture "key"
  let invertRow ← observeRow fixture "invert"
  let missingRow ← observeRow fixture "keyFailure"
  let keyShape ← observeCopy keyRow.original.function.typedBody
  let invertShape ← observeUnary invertRow.original.function.typedBody
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 12) "projected unary named/header selected cache"
  let ⟨originals⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.functions.length = 13) "projected unary complete original program"
  return ⟨nestedRow, initializerRow, nestedShape, initializerShape, keyRow, invertRow, missingRow, keyShape, invertShape, missingShape, cacheSize, originals⟩

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "projected bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedProjectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot.Captured
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

/-- Observe original compiler nodes and binders; no completed execution is read. -/
def observeShape (source : TypedSource) : IO (Shape source) := do
  let [table] := source.inputs | throw (IO.userError "captured mapping input")
  let [.statement outerId] := source.roots | throw (IO.userError "captured mapping root")
  let some outer := source.lookupStatement? outerId | throw (IO.userError "captured outer lookup")
  let .returnStmt (some lambdaId) := outer.form | throw (IO.userError "captured outer return")
  let some lambda := source.lookupExpression? lambdaId | throw (IO.userError "captured lambda lookup")
  let .lambda [key] .word [assignedId, returnedId] := lambda.form | throw (IO.userError "captured lambda body")
  let some assigned := source.lookupStatement? assignedId | throw (IO.userError "captured assignment lookup")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "captured inner return lookup")
  let .assignBitNot resolution := assigned.form | throw (IO.userError "captured unary form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "captured unary key")
  let some keyNode := source.lookupExpression? keyId | throw (IO.userError "captured key lookup")
  let keyRead ← Tests.SourceCoreNamedBranch.observeRead source key keyNode .word
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "captured result return")
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "captured result lookup")
  let .index tableId resultKeyId := resultNode.form | throw (IO.userError "captured result index")
  let some tableNode := source.lookupExpression? tableId | throw (IO.userError "captured table lookup")
  let some resultKeyNode := source.lookupExpression? resultKeyId | throw (IO.userError "captured result key lookup")
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead source table tableNode mappingType
  let resultKey ← Tests.SourceCoreNamedBranch.observeRead source key resultKeyNode .word
  let ⟨resultFound⟩ ← observed (source.lookupExpression? resultNode.id = some resultNode) "captured result identity"
  let ⟨resultForm⟩ ← observed (resultNode.form = .index tableRead.node.id resultKey.node.id) "captured result children"
  let ⟨resultRequirements⟩ ← observed (resultNode.requirements = []) "captured result requirements"
  let ⟨resultCoercions⟩ ← observed (resultNode.coercions = []) "captured result coercions"
  let result : IndexRead source tableRead.node.id resultKey.node.id :=
    ⟨resultNode, resultFound, resultForm, resultRequirements, resultCoercions⟩
  let ⟨inputs⟩ ← observed (source.inputs = [table]) "captured inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "captured mapping scheme"
  let ⟨tableCopied⟩ ← observed (CaptureBinders.copiedBinder? source table.id = some table) "captured mapping copied"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "captured key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "captured distinct binders"
  let ⟨roots⟩ ← observed (source.roots = [.statement outer.id]) "captured roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "captured assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "captured assignment operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "captured target binder"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "captured target key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "captured original leaf type"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "captured return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "captured return form"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "captured lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [key] .word [assigned.id, returned.id]) "captured lambda children"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "captured lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "captured lambda coercions"
  let ⟨outerFound⟩ ← observed (source.lookupStatement? outer.id = some outer) "captured outer identity"
  let ⟨outerForm⟩ ← observed (outer.form = .returnStmt (some lambda.id)) "captured outer child"
  return ⟨table, key, resolution, assigned, returned, outer, lambda, keyRead, tableRead, resultKey, result,
    inputs, tableScheme, tableCopied, keyScheme, keyTable, roots, assignedFound, assignedForm, targetRoot,
    targetProjections, targetType, returnedFound, returnedForm, lambdaFound, lambdaForm,
    lambdaRequirements, lambdaCoercions, outerFound, outerForm⟩

structure ObservedFactory (fixture : CompiledFixture) where
  row : Row fixture
  shape : Shape row.original.function.typedBody
  resultType : row.original.function.inferredBodyType = .function .word .word

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  let row ← observeRow fixture "make"
  let shape ← observeShape row.original.function.typedBody
  let ⟨resultType⟩ ← observed (row.original.function.inferredBodyType = .function .word .word)
    "captured factory result type"
  return ⟨row, shape, resultType⟩

end Tests.SourceCoreSelectedProjectedBitNot.Captured
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

def publicEntries (entries : List (Word × Word)) :
    List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def sourceEntries (entries : List (Word × Word)) : List (Dynamic.Value × Dynamic.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def dataEntries (entries : List (Word × Word)) :
    List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) :=
  entries.map (fun pair => (.word pair.1, .word pair.2))
def publicMap (entries : List (Word × Word)) : SourceCorePublicValues.Value :=
  .mapping .word .word (publicEntries entries)

private theorem map_carrier (entries : List (Word × Word)) :
    publicMap entries = SourceCoreIndexedSession.DataInput.publicValue (.mapping .word .word (dataEntries entries)) := by
  simp only [publicMap, SourceCoreIndexedSession.DataInput.publicValue]
  congr 1
  induction entries with
  | nil => simp only [publicEntries, dataEntries, List.map_nil, SourceCoreIndexedSession.DataInput.publicEntries]
  | cons pair tail ih =>
    simpa only [publicEntries, dataEntries, List.map_cons,
      SourceCoreIndexedSession.DataInput.publicEntries, SourceCoreIndexedSession.DataInput.publicValue] using
        congrArg (List.cons (.word pair.1, .word pair.2)) ih

private theorem map_types (context : SourceSemantics.Context) (entries : List (Word × Word)) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicMap entries) mappingType := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty _ _
  | cons pair tail ih => exact .entry (.word pair.1) (.word pair.2) ih

private theorem map_meaning (entries : List (Word × Word)) :
    RecursiveNamedPublicDataInputs.Means (publicMap entries) (mappingValue (sourceEntries entries)) := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty
  | cons pair tail ih => exact .prepend (.word pair.1) (.word pair.2) ih

private theorem word_types (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (.word value) .word :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
private theorem word_meaning (value : Word) : RecursiveNamedPublicDataInputs.Means (.word value) (.word value) :=
  ⟨.word value, by simp only [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.keyRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7))
    (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 7)] (.value (.word (Word.ofNatModulo 7)))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7)) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe []
        initial.header.function.resultType started.call.checkpoint (.word (Word.ofNatModulo 7))
        (copyHeap ⟨[]⟩ (Word.ofNatModulo 7))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 7)]

/-- A genuine scalar helper initializes the selected named/header compilation
of the unchanged thirteen-declaration program.
Its ordinary Source trace is built before public completion; later calls use
that issued state's mapping-aware input path. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, _signatureSame⟩ := observed.keyRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have shape : CopyShape initial.header.function.source := by rw [sourceEq]; exact observed.keyShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping initial.header
  have plain := fun invocation => copy_call initial.header shape certified sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 7)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 7)], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl; exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 7)] initial.header.types := by
    rw [copy_input_types initial.header shape]
    exact .cons (word_types _ _) .nil
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple types
      (.cons (word_meaning _) .nil) (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure UnaryMeaning (row : Row fixture) (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
    (mappingValue (sourceEntries ((key, previous.bitNot) :: tail)))
    (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.value (mappingValue (sourceEntries ((key, previous.bitNot) :: tail))))
        (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (mappingValue (sourceEntries ((key, previous.bitNot) :: tail)))
        (parameterHeap state.heap (sourceEntries ((key, previous.bitNot) :: tail)) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]

/-- Exact original unary syntax determines the whole ordered mapping output. The theorem requires no execution callback. -/
theorem unary_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (UnaryMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => unary_call request.header actualShape sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

structure DefaultMeaning (row : Row fixture) (key : Word)
    (call : StartedCall session row.original.key [publicMap [], .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap [], .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [mappingValue (sourceEntries []), .word key]
    (mappingValue (sourceEntries [(key, (Word.zero).bitNot)]))
    (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries []), .word key]
        (.value (mappingValue (sourceEntries [(key, (Word.zero).bitNot)])))
        (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (mappingValue (sourceEntries [(key, (Word.zero).bitNot)]))
        (parameterHeap state.heap (sourceEntries [(key, (Word.zero).bitNot)]) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries []), .word key]

/-- The original unary update inserts the complement of the genuine Word default into an empty mapping. -/
theorem default_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody)
    (key : Word)
    (call : StartedCall session row.original.key [publicMap [], .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (DefaultMeaning issued state row key call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => default_call request.header actualShape sourceAt anchor invocation state.heap
    key
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap [], .word key]
      [mappingValue (sourceEntries []), .word key] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture) (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [publicMap ((key, previous) :: tail), .word key]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap
    [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
    (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
    (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.fault (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))))
        (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe
        (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key)))
        call (missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]

/-- The original projected unary update reads an uninitialized key local.
The fault precedes snapshot selection and retains its exact allocations. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : MissingShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping request.header
  have plain := fun invocation => missing_call request.header actualShape certified sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))
      (plain invocation)⟩⟩

/-- A genuine failure returns a state for the same selected issued catalog.
The next original complement starts at that exact reached heap. -/
theorem missing_then_reuse (missingRow invertRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (invertShape : UnaryShape invertRow.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session missingRow.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap (sourceEntries ((key, previous) :: tail)) key ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.uninitializedLocation (missingLocation state.heap (sourceEntries ((key, previous) :: tail)) key))) token ∧
            ∀ nextCall : StartedCall returned invertRow.original.key
                [publicMap ((key, previous) :: tail), .word key] runOptions,
              Nonempty (UnaryMeaning issued next invertRow key previous tail nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow key previous tail call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape key previous tail call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact unary_from_source issued next invertRow invertShape key previous tail
      nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

/-- The same public catalog executes the authentic for initializer and then
skips its post after the original false condition. -/
theorem initializer_from_source (row : Row fixture)
    (shape : InitializerShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (call : StartedCall session row.original.key [publicMap ((key, previous) :: tail), .word key] runOptions)
    (ready : session.ExportsReady) : Nonempty (UnaryMeaning issued state row key previous tail call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : InitializerShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => initializer_call request.header actualShape sourceAt anchor invocation state.heap
    key previous (sourceEntries tail)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicMap ((key, previous) :: tail), .word key]
      [mappingValue (sourceEntries ((key, previous) :: tail)), .word key] := by
    rw [body_types, initializer_input_types request.header actualShape]
    exact .cons (.data (map_types _ _) (map_meaning _))
      (.cons (.data (word_types _ _) (word_meaning _)) .nil)
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

def publicNested (first second previous : Word) : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(.word first, publicMap [(second, previous)])]

private theorem nested_types (context : SourceSemantics.Context) (first second previous : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicNested first second previous) nestedType := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.entry (.word first) (.mapping (.entry (.word second) (.word previous) (.empty _ _))) (.empty _ _))

private theorem nested_meaning (first second previous : Word) :
    RecursiveNamedPublicDataInputs.Means (publicNested first second previous) (nestedValue first second previous) := by
  refine ⟨.mapping .word mappingType [(.word first, .mapping .word .word [(.word second, .word previous)])], ?_, ?_⟩
  · simp [publicNested, publicMap, publicEntries, SourceCoreIndexedSession.DataInput.publicValue,
      SourceCoreIndexedSession.DataInput.publicEntries]
  · exact .mapping (.prepend (.word first) (.mapping (.prepend (.word second) (.word previous) .empty)) .empty)

structure NestedMeaning (row : Row fixture) (first second previous : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key
    [publicNested first second previous, .word first, .word second]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap
    [nestedValue first second previous, .word first, .word second]
    (.word previous.bitNot) (nestedHeap state.heap first second previous.bitNot)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap
        [nestedValue first second previous, .word first, .word second]
        (.value (.word previous.bitNot)) (nestedHeap state.heap first second previous.bitNot) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe entries
        request.header.function.resultType call.checkpoint (.word previous.bitNot)
        (nestedHeap state.heap first second previous.bitNot)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation
      [nestedValue first second previous, .word first, .word second]

/-- The original two-key source trace connects to the same whole public
issuer; both key evaluations and the exact three parameter cells are retained. -/
theorem nested_from_source (row : Row fixture) (shape : NestedShape row.original.function.typedBody)
    (first second previous : Word)
    (call : StartedCall session row.original.key
      [publicNested first second previous, .word first, .word second] runOptions)
    (ready : session.ExportsReady) : Nonempty (NestedMeaning issued state row first second previous call) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have actualShape : NestedShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => nested_call request.header actualShape sourceAt anchor invocation state.heap first second previous
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [publicNested first second previous, .word first, .word second]
      [nestedValue first second previous, .word first, .word second] := by
    rw [body_types, nested_input_types request.header actualShape]
    exact .cons (.data (nested_types _ _ _ _) (nested_meaning _ _ _))
      (.cons (.data (word_types _ _) (word_meaning _))
        (.cons (.data (word_types _ _) (word_meaning _)) .nil))
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.later issued state call request inputs ready (plain invocation)⟩⟩

/-- The independent bootstrap trace supplies the actual state for the first
mapping complement in the same issued session. No completed call is assumed. -/
theorem initial_then_invert (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.keyRow.original.key [.word (Word.ofNatModulo 7)])
    (key previous : Word) (tail : List (Word × Word)) :
    ∃ meaning : InitialMeaning fixture observed started, ∀ invocation,
      (∃ requiredExecution requiredOutput,
        ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome started.artifact),
          requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
          started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
          ∃ completion : SourceCoreExecution.Completion started.artifact,
            outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
            ∃ next : meaning.issued.toIssued.State meaning.initial.header completion.session [],
              next.heap = copyHeap ⟨[]⟩ (Word.ofNatModulo 7) ∧
              ∀ nextCall : StartedCall completion.session observed.invertRow.original.key
                  [publicMap ((key, previous) :: tail), .word key] runOptions,
                Nonempty (UnaryMeaning meaning.issued next observed.invertRow key previous tail nextCall)) ∨
      SelectedCompilationStageClosedInitialForward.StageStopped meaning.issued started.call
        meaning.initial invocation [.word (Word.ofNatModulo 7)] := by
  obtain ⟨meaning⟩ := initial_from_source fixture observed profile started
  refine ⟨meaning, ?_⟩
  intro invocation
  rcases meaning.forward invocation with finished | stopped
  · obtain ⟨requiredExecution, requiredOutput, forward⟩ := finished.2
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨completion, outcomeEq, ready, next, heapEq, _value, _handles⟩ :=
      forward executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    refine ⟨completion, outcomeEq, ready, next, heapEq, ?_⟩
    intro nextCall
    exact unary_from_source meaning.issued next observed.invertRow observed.invertShape key previous
      tail nextCall ready
  · exact .inr stopped

structure InitialDataSelection {fixture : CompiledFixture} (row : Row fixture)
    {publicArguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.original.key publicArguments) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = row.original.function.typedBody

/-- The first selected call retains its actual data encoder and original row. -/
theorem initial_data_selection {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {publicArguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.original.key publicArguments) :
    Nonempty (InitialDataSelection row started) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) eligible
  exact ⟨⟨issued, initial, initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))⟩⟩

def InitialDataForward {fixture : CompiledFixture} {row : Row fixture}
    {publicArguments : List SourceCorePublicValues.Value}
    {started : Started fixture row.original.key publicArguments}
    (selected : InitialDataSelection row started) (arguments : List Dynamic.Value)
    (value : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∀ invocation,
    PlainValue selected.initial.header selected.initial.header invocation ⟨[]⟩ arguments value after ∧
    ((SourceCall selected.initial.header selected.initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt selected.issued.catalog.rows
        selected.initial.header selected.issued.initial selected.issued.support.profile fixture.recipe []
        selected.initial.header.function.resultType started.call.checkpoint value after) ∨
      SelectedCompilationStageClosedInitialForward.StageStopped selected.issued started.call selected.initial invocation arguments)

/-- A mapping can be the first input. Duplicate keys retain their original
order, and the exact Source heap contains only this call's two parameter cells. -/
theorem initial_unary_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (shape : UnaryShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture row.original.key [publicMap ((key, previous) :: tail), .word key]) :
    ∃ selected : InitialDataSelection row started,
      InitialDataForward selected [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (mappingValue (sourceEntries ((key, previous.bitNot) :: tail)))
        (parameterHeap ⟨[]⟩ (sourceEntries ((key, previous.bitNot) :: tail)) key) := by
  obtain ⟨selected⟩ := initial_data_selection row profile started
  have actualShape : UnaryShape selected.initial.header.function.source := by rw [selected.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.issued.catalog.rows).receipts
      selected.initial.header selected.initial.start.selected.member
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes selected.initial.header.function.context
      [publicMap ((key, previous) :: tail), .word key] selected.initial.header.types := by
    rw [unary_input_types selected.initial.header actualShape]
    exact .cons (map_types _ _) (.cons (word_types _ _) .nil)
  refine ⟨selected, ?_⟩
  intro invocation
  have plain := unary_call selected.initial.header actualShape sourceAt selected.initial.header invocation ⟨[]⟩
    key previous (sourceEntries tail)
  exact ⟨plain, selected.initial.forward_data_output_plain types
    (.cons (map_meaning _) (.cons (word_meaning _) .nil)) plain⟩

/-- An empty mapping at startup uses the actual Word default before complement. -/
theorem initial_default_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (shape : UnaryShape row.original.function.typedBody) (key : Word)
    (started : Started fixture row.original.key [publicMap [], .word key]) :
    ∃ selected : InitialDataSelection row started,
      InitialDataForward selected [mappingValue [], .word key]
        (mappingValue (sourceEntries [(key, Word.zero.bitNot)]))
        (parameterHeap ⟨[]⟩ (sourceEntries [(key, Word.zero.bitNot)]) key) := by
  obtain ⟨selected⟩ := initial_data_selection row profile started
  have actualShape : UnaryShape selected.initial.header.function.source := by rw [selected.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.issued.catalog.rows).receipts
      selected.initial.header selected.initial.start.selected.member
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes selected.initial.header.function.context
      [publicMap [], .word key] selected.initial.header.types := by
    rw [unary_input_types selected.initial.header actualShape]
    exact .cons (map_types _ _) (.cons (word_types _ _) .nil)
  refine ⟨selected, ?_⟩
  intro invocation
  have plain := default_call selected.initial.header actualShape sourceAt selected.initial.header invocation ⟨[]⟩ key
  exact ⟨plain, selected.initial.forward_data_output_plain types
    (.cons (map_meaning _) (.cons (word_meaning _) .nil)) plain⟩

/-- A failed key read on the first data call preserves its reached heap and
returns a session continuation with the encoder's actual metadata registry. -/
theorem initial_missing_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (shape : MissingShape row.original.function.typedBody)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture row.original.key [publicMap ((key, previous) :: tail), .word key]) :
    ∃ selected : InitialDataSelection row started, ∀ invocation,
      PlainFault selected.initial.header selected.initial.header invocation ⟨[]⟩
        [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
        (.uninitializedLocation (missingLocation ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key))
        (missingHeap ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key) ∧
      ((SourceCall selected.initial.header selected.initial.header invocation ⟨[]⟩
          [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]
          (.fault (.semantic (.uninitializedLocation (missingLocation ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key))))
          (missingHeap ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key) ∧
        SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) selected.issued.catalog.rows
          selected.initial.header selected.issued.initial selected.issued.support.profile fixture.recipe
          (.semantic (.uninitializedLocation (missingLocation ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key)))
          started.call (missingHeap ⟨[]⟩ (sourceEntries ((key, previous) :: tail)) key)) ∨
        SelectedCompilationStageClosedInitialForward.StageStopped selected.issued started.call selected.initial invocation
          [mappingValue (sourceEntries ((key, previous) :: tail)), .word key]) := by
  obtain ⟨selected⟩ := initial_data_selection row profile started
  have actualShape : MissingShape selected.initial.header.function.source := by rw [selected.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.issued.catalog.rows).receipts
      selected.initial.header selected.initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified selected.issued.support.bodyTyping selected.initial.header
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes selected.initial.header.function.context
      [publicMap ((key, previous) :: tail), .word key] selected.initial.header.types := by
    rw [missing_input_types selected.initial.header actualShape]
    exact .cons (map_types _ _) (.cons (word_types _ _) .nil)
  refine ⟨selected, ?_⟩
  intro invocation
  have plain := missing_call selected.initial.header actualShape certified sourceAt selected.initial.header invocation ⟨[]⟩
    key previous (sourceEntries tail)
  exact ⟨plain, selected.initial.forward_data_fault_plain types
    (.cons (map_meaning _) (.cons (word_meaning _) .nil)) plain⟩

end Tests.SourceCoreSelectedProjectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedProjectedBitNot.Captured
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  (shape : Shape header.function.source) (before : Dynamic.Heap)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (entry : Entry)
  (state : issued.toIssued.State anchor session entries)

/-- A current ordinary call is constructed before its public completion. The
only closure typing used here comes from the genuine retained session history. -/
theorem direct_from_captured (member : entry ∈ entries)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value)) (suffix : List Dynamic.Cell)
    (sameHeap : state.heap = heap before ((.word key, .word previous) :: tail) suffix)
    (source : entry.source = .closure (function header shape before))
    (entryType : entry.sourceType = .function .word .word)
    (handleType : entry.handle.sourceType = .function .word .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle (.word key) fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail)) ∧
    ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        anchor.function.context state.heap entry.source [.word key] (.value (.word previous.bitNot))
        (heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail)) ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
        issued.support.profile recipe entries (.word previous.bitNot) checkpoint
        (heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail))) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [.word key]) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry member).2.2
  rw [entryType, source, sameHeap] at typed
  have plain := closure_plain header shape before key previous tail suffix invocation
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping anchor).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous) :: tail) (suffix ++ callCells key previous tail)) := by
    simpa only [source, sameHeap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      .word (.word key) (.word key) :=
    .data ⟨.word key, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word key⟩
      ⟨.word key, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word key⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry member
    entryType input started ready (.singleton _) (.word previous.bitNot) rfl handleType ordinary⟩

/-- Every sufficiently fueled first completion retains the same handle and
snapshot. The second ordinary call starts again from the snapshot, returns the
same complement and appends its own copy and key, before the second public call
executes. -/
def RepeatAfterFirst (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value))
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word previous.bitNot ∧
        ∃ next : issued.toIssued.State anchor completion.session entries,
          next.heap = heap before ((.word key, .word previous) :: tail) (callCells key previous tail) ∧
          ∀ nextFuel (second : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle (.word key) nextFuel = .ok second →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              next.heap entry.source [.word key] (.word previous.bitNot)
              (heap before ((.word key, .word previous) :: tail) (callCells key previous tail ++ callCells key previous tail)) ∧
            ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
                anchor.function.context next.heap entry.source [.word key] (.value (.word previous.bitNot))
                (heap before ((.word key, .word previous) :: tail) (callCells key previous tail ++ callCells key previous tail)) ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
                issued.support.profile recipe entries (.word previous.bitNot) second
                (heap before ((.word key, .word previous) :: tail) (callCells key previous tail ++ callCells key previous tail))) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued next entry second invocation [.word key])

/-- The Source-first two-call law: both calls return the complement of the
factory's entry. It retains actual stage rejection alternatives and never
assumes either current public call has already completed. -/
theorem twice_from_captured (member : entry ∈ entries)
    (key previous : Word) (tail : List (Dynamic.Value × Dynamic.Value))
    (sameHeap : state.heap = heap before ((.word key, .word previous) :: tail))
    (source : entry.source = .closure (function header shape before))
    (entryType : entry.sourceType = .function .word .word)
    (handleType : entry.handle.sourceType = .function .word .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle (.word key) fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [.word key] (.word previous.bitNot)
      (heap before ((.word key, .word previous) :: tail) (callCells key previous tail)) ∧
    (RepeatAfterFirst (anchor := anchor) (entries := entries) issued before entry key previous tail checkpoint invocation ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [.word key]) := by
  obtain ⟨ordinary, forward⟩ := direct_from_captured issued shape before entry state member key previous tail []
    sameHeap source entryType handleType ready started invocation
  refine ⟨ordinary, ?_⟩
  rcases forward with ⟨_staged, execution, output, complete⟩ | stopped
  · left
    refine ⟨execution, output, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, value, exports, next, nextHeap⟩ :=
      complete executionFuel outputFuel outcome executionBound outputBound resumed
    refine ⟨completion, actual, value, next, nextHeap, ?_⟩
    intro nextFuel second accepted
    exact direct_from_captured issued shape before entry next member key previous tail (callCells key previous tail)
      nextHeap source entryType handleType exports accepted invocation
  · exact .inr stopped


private theorem map_carrier (entries : List (Word × Word)) :
    publicMap entries = SourceCoreIndexedSession.DataInput.publicValue (.mapping .word .word (dataEntries entries)) := by
  simp only [publicMap, SourceCoreIndexedSession.DataInput.publicValue]
  congr 1
  induction entries with
  | nil => simp only [publicEntries, dataEntries, List.map_nil, SourceCoreIndexedSession.DataInput.publicEntries]
  | cons pair tail ih =>
    simpa only [publicEntries, dataEntries, List.map_cons,
      SourceCoreIndexedSession.DataInput.publicEntries, SourceCoreIndexedSession.DataInput.publicValue] using
        congrArg (List.cons (.word pair.1, .word pair.2)) ih

private theorem map_types (context : SourceSemantics.Context) (entries : List (Word × Word)) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context (publicMap entries) mappingType := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty _ _
  | cons pair tail ih => exact .entry (.word pair.1) (.word pair.2) ih

private theorem map_meaning (entries : List (Word × Word)) :
    RecursiveNamedPublicDataInputs.Means (publicMap entries) (mappingValue (sourceEntries entries)) := by
  refine ⟨.mapping .word .word (dataEntries entries), map_carrier entries, .mapping ?_⟩
  induction entries with
  | nil => exact .empty
  | cons pair tail ih => exact .prepend (.word pair.1) (.word pair.2) ih

section Initial
variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (keyValue previous : Word) (tail : List (Word × Word))
  (call : SelectedCompilationPublicSessionState.StartedCall session key
    [publicMap ((keyValue, previous) :: tail)] options)
  (initial : Initial issued.toIssued call)

/-- A fresh mapping input reaches the returned handle and both subsequent
calls in one session. Each execution budget is obtained before that call runs. -/
def FactoryChain (shape : Shape initial.header.function.source) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (next : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧
          next.heap = heap ⟨[]⟩ (sourceEntries ((keyValue, previous) :: tail)) ∧
          entry.source = .closure (function initial.header shape ⟨[]⟩) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle (.word keyValue) fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              next.heap entry.source [.word keyValue] (.word previous.bitNot)
              (heap ⟨[]⟩ (sourceEntries ((keyValue, previous) :: tail)) (callCells keyValue previous (sourceEntries tail))) ∧
            (RepeatAfterFirst (anchor := initial.header) (entries := [entry]) issued ⟨[]⟩ entry keyValue previous (sourceEntries tail) checkpoint invocation ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued next entry checkpoint invocation [.word keyValue])

/-- The original factory call is independent of Core. Initial mapping metadata
comes from actual startup, not a scalar helper or a completed public call. -/
theorem initial_factory_chain (shape : Shape initial.header.function.source)
    (resultType : initial.header.function.resultType = .function .word .word)
    (invocation : Staging.Recursive.Scope) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue initial.header initial.header invocation ⟨[]⟩
      [mappingValue (sourceEntries ((keyValue, previous) :: tail))]
      (.closure (function initial.header shape ⟨[]⟩))
      (heap ⟨[]⟩ (sourceEntries ((keyValue, previous) :: tail))) ∧
    (FactoryChain issued keyValue previous tail call initial shape invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation
        [mappingValue (sourceEntries ((keyValue, previous) :: tail))]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt initial.header invocation ⟨[]⟩
    (sourceEntries ((keyValue, previous) :: tail))
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [publicMap ((keyValue, previous) :: tail)] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons (map_types _ _) .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings
      [publicMap ((keyValue, previous) :: tail)] [mappingValue (sourceEntries ((keyValue, previous) :: tail))] :=
    .cons (map_meaning _) .nil
  have forward := initial.forward_data_function_plain types meanings (by rw [resultType]; rfl) plain
  refine ⟨plain, ?_⟩
  rcases forward with ⟨_staged, execution, output, complete⟩ | stopped
  · left
    refine ⟨execution, output, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, ready, entry, entryType, source, returned, handleType, next, sameHeap⟩ :=
      complete executionFuel outputFuel outcome executionBound outputBound resumed
    rw [resultType] at entryType handleType
    refine ⟨completion, actual, entry, next, returned, sameHeap, source, ?_⟩
    intro fuel checkpoint accepted
    exact twice_from_captured issued shape ⟨[]⟩ entry next (List.mem_singleton_self _) keyValue previous
      (sourceEntries tail) sameHeap source entryType handleType ready accepted invocation
  · exact .inr stopped
end Initial

/-- Concrete checked compilation and authentic first startup provide every
semantic premise for the factory and its two retained calls. -/
structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture observed.row.original.key [publicMap ((key, previous) :: tail)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  sourceEq : initial.header.function.source = observed.row.original.function.typedBody
  plain : ∀ invocation, RecursiveNamedPublicPhysicalSessionState.PlainValue
    initial.header initial.header invocation ⟨[]⟩ [mappingValue (sourceEntries ((key, previous) :: tail))]
    (.closure (function initial.header shape ⟨[]⟩)) (heap ⟨[]⟩ (sourceEntries ((key, previous) :: tail)))
  forward : ∀ invocation,
    FactoryChain issued key previous tail started.call initial shape invocation ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [mappingValue (sourceEntries ((key, previous) :: tail))]

theorem from_checked_initial (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (key previous : Word) (tail : List (Word × Word))
    (started : Started fixture observed.row.original.key [publicMap ((key, previous) :: tail)]) :
    Nonempty (InitialMeaning fixture observed key previous tail started) := by
  obtain ⟨row, rowSame, _signatureSame⟩ := observed.row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.resultType))
  have shape : Shape initial.header.function.source := by rw [sourceEq]; exact observed.shape
  have chain := fun invocation => initial_factory_chain issued key previous tail started.call initial shape resultEq invocation
  exact ⟨⟨issued, initial, shape, sourceEq, fun invocation => (chain invocation).1,
    fun invocation => (chain invocation).2⟩⟩

end Tests.SourceCoreSelectedProjectedBitNot.Captured
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProjectedBitNotProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def findKey (program : CheckedProgram) (name : String) : IO SourceCoreExecution.Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError "missing function")
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def table (entries : List (Nat × Nat)) : SourceCorePublicValues.Value :=
  .mapping .word .word (entries.map fun pair => (word pair.1, word pair.2))
private def complement (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n).bitNot
private def complemented (entries : List (Nat × Nat)) (key : Nat) (value : Nat) : SourceCorePublicValues.Value :=
  .mapping .word .word ((word key, complement value) :: entries.map (fun pair => (word pair.1, word pair.2)))
private def nested : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(word 7, table [(2, 4)])]

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected startup" (session.start key arguments)
  let .outOfFuel suspended ← pending.resume 0 0
    | throw (IO.userError "projected zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "projected success missing")
  require (completed.value == expected) "projected result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected fault startup" (session.start key arguments)
  let .failed reason after ← pending.resume 100000 1000
    | throw (IO.userError "projected original read did not fail")
  let some diagnostic ← get "projected diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "projected diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "projected original read diagnostic changed"
  pure after

/-- The unchanged thirteen-declaration program has a complete checked profile.
Independent Source proofs cover fresh mapping inputs, the returned captured
handle, and two retained calls. The twelve-entry named/header regression remains. -/
def run : IO Unit := do
  let proofFixture ← compileNamedHeaderFixture
  let observed ← observeProgram proofFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      proofFixture.recipe.compiled proofFixture.checked
    | throw (IO.userError "projected bit-not named/header selected profile rejected")
  require (proofFixture.recipe.compiled.sourceProgram.functions.length == 13 &&
      proofFixture.recipe.compiled.indexed.base.functions.length == 12 && profile.table.rows.length == 12)
    "projected bit-not selected originals/cache/table changed"
  let initialMap ← observeStarted proofFixture observed.invertRow.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4), (Word.ofNatModulo 7, Word.ofNatModulo 99)], word 7]
  have _initialMapProof := initial_unary_from_source observed.invertRow profile observed.invertShape
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [(Word.ofNatModulo 7, Word.ofNatModulo 99)] initialMap
  let .succeeded mapped ← initialMap.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial mapping call failed")
  require (mapped.value == complemented [(7,99)] 7 4) "initial mapping first-match output changed"
  let initialDefault ← observeStarted proofFixture observed.invertRow.original.key [publicMap [], word 9]
  have _initialDefaultProof := initial_default_from_source observed.invertRow profile observed.invertShape
    (Word.ofNatModulo 9) initialDefault
  let .succeeded defaulted ← initialDefault.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial empty mapping call failed")
  require (defaulted.value == complemented [] 9 0) "initial mapping default changed"
  let initialMissing ← observeStarted proofFixture observed.missingRow.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4)], word 7]
  have _initialMissingProof := initial_missing_from_source observed.missingRow profile observed.missingShape
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [] initialMissing
  let .failed reason failed ← initialMissing.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial mapping key did not fail")
  let some diagnostic ← get "initial mapping diagnostic" (failed.diagnostic observed.missingRow.original.key reason)
    | throw (IO.userError "initial mapping diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "initial mapping fault changed"
  let reused ← success failed observed.invertRow.original.key [table [(7,4)], word 7] (complemented [] 7 4)
  let initialDataHeaps := [initialMap.session.heapSize, mapped.session.heapSize,
    initialDefault.session.heapSize, defaulted.session.heapSize,
    initialMissing.session.heapSize, failed.heapSize, reused.heapSize]
  require (initialDataHeaps == [13,28,13,28,13,22,37]) "initial mapping exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_INITIAL_DATA_HEAPS: {initialDataHeaps}"
  let proofStarted ← observeStarted proofFixture observed.keyRow.original.key [word 7]
  have _sourceFirst := initial_then_invert proofFixture observed profile proofStarted
    (Word.ofNatModulo 7) (Word.ofNatModulo 4)
    [(Word.ofNatModulo 7, Word.ofNatModulo 99), (Word.ofNatModulo 2, Word.ofNatModulo 6)]
  let .outOfFuel proofSuspended ← proofStarted.call.checkpoint.resume 0 0
    | throw (IO.userError "projected bit-not selected initial suspension")
  let .succeeded proofInitial ← proofSuspended.resume 100000 1000
    | throw (IO.userError "projected bit-not selected initial helper")
  require (proofInitial.value == word 7) "projected selected initial helper changed"
  let proofAfter ← success proofInitial.session observed.invertRow.original.key
    [table [(7,4),(7,99),(2,6)], word 7] (complemented [(7,99),(2,6)] 7 4)
  let proofMissing ← findKey proofFixture.recipe.compiled.sourceProgram "keyFailure"
  let proofFailed ← failure proofAfter proofMissing [table [(7,4)], word 7]
  let proofReused ← success proofFailed observed.invertRow.original.key
    [table [(7,4)], word 7] (complemented [] 7 4)
  let proofHeaps := [proofStarted.session.heapSize, proofInitial.session.heapSize,
    proofAfter.heapSize, proofFailed.heapSize, proofReused.heapSize]
  require (proofHeaps == [13,19,34,43,58]) "projected selected exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_SELECTED_CACHE: originals13/cache12/table{profile.table.rows.length}; genuine key failure and same-session reuse passed"
  IO.println s!"PROJECTED_BITNOT_SELECTED_NATIVE_HEAPS: {proofHeaps}"

  let fixture ← compileFixture
  have _sameOriginal : fixture.recipe.compiled.sourceProgram = proofFixture.recipe.compiled.sourceProgram :=
    Except.ok.inj (fixture.checked.symm.trans proofFixture.checked)
  require (fixture.recipe.compiled.sourceProgram.functions.length == 13 &&
      fixture.recipe.compiled.indexed.base.functions.length == 13)
    "projected bit-not complete original cache changed"
  let some fullProfile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "captured projected unary complete profile rejected")
  require (fullProfile.table.rows.length == 13) "captured complete profile table changed"
  let factory ← Captured.observeFactory fixture
  let capturedStarted ← observeStarted fixture factory.row.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4)]]
  have _capturedSourceChain := Captured.from_checked_initial fixture factory fullProfile
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [] capturedStarted
  let .outOfFuel capturedSuspended ← capturedStarted.call.checkpoint.resume 0 0
    | throw (IO.userError "captured mapping initial suspension")
  let .succeeded capturedMade ← capturedSuspended.resume 100000 1000
    | throw (IO.userError "captured mapping initial factory failed")
  let .function capturedHandle := capturedMade.value
    | throw (IO.userError "captured mapping initial handle missing")
  let capturedPending ← get "captured mapping retained first"
    (capturedMade.session.startHandlePacked capturedHandle (word 7))
  let .outOfFuel capturedFirstSuspended ← capturedPending.resume 0 0
    | throw (IO.userError "captured mapping retained first suspension")
  let .succeeded capturedFirst ← capturedFirstSuspended.resume 100000 1000
    | throw (IO.userError "captured mapping retained first failed")
  let capturedAgain ← get "captured mapping retained second"
    (capturedFirst.session.startHandlePacked capturedHandle (word 7))
  let .succeeded capturedRepeated ← capturedAgain.resume 100000 1000
    | throw (IO.userError "captured mapping retained repeat failed")
  require (capturedFirst.value == complement 4 && capturedRepeated.value == complement 4)
    "captured mapping same-handle complement changed"
  let capturedHeaps := [capturedStarted.session.heapSize, capturedMade.session.heapSize,
    capturedFirst.session.heapSize, capturedRepeated.session.heapSize]
  require (capturedHeaps == [14,20,38,56]) "captured mapping exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_CAPTURED_SOURCE_CHAIN_HEAPS: {capturedHeaps}"
  let keyRow ← observeRow fixture "key"
  let started ← observeStarted fixture keyRow.original.key [word 7]
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "projected bit-not initial suspension")
  let .succeeded initial ← suspended.resume 100000 1000
    | throw (IO.userError "projected bit-not initial helper")
  require (initial.value == word 7) "projected initial helper changed"
  let program := fixture.recipe.compiled.sourceProgram
  let recipe := fixture.recipe
  let mut session := initial.session
  let mut heaps := [started.session.heapSize, initial.session.heapSize]
  for (name, arguments, expected) in [
      ("invert", [table [(7,4),(7,99),(2,6)], word 7], complemented [(7,99),(2,6)] 7 4),
      ("invert", [table [], word 9], complemented [] 9 0),
      ("nested", [nested, word 7, word 2], complement 4),
      ("effects", [table [(7,4)], word 7], complemented [] 7 4),
      ("initialize", [table [], word 7], complemented [] 7 0),
      ("post", [table []], complemented [] 0 0),
      ("stop", [table []], table []),
      ("defaultLocal", [], complement 0)] do
    let key ← findKey recipe.compiled.sourceProgram name
    session ← success session key arguments expected
    heaps := heaps ++ [session.heapSize]
  for (name, arguments) in [
      ("keyFailure", [table [(7,4)], word 7]),
      ("calledKeyFailure", [table [(7,4)], word 7]),
      ("nestedFailure", [nested, word 7, word 2])] do
    let key ← findKey recipe.compiled.sourceProgram name
    session ← failure session key arguments
    heaps := heaps ++ [session.heapSize]
  let invert ← findKey program "invert"
  session ← success session invert [table [(7,4)], word 7] (complemented [] 7 4)
  heaps := heaps ++ [session.heapSize]
  let make ← findKey recipe.compiled.sourceProgram "make"
  let pending ← get "projected captured factory" (session.start make [table [(7,4)]])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "projected captured factory failed")
  let .function handle := made.value | throw (IO.userError "projected captured handle missing")
  let pending ← get "projected captured first" (made.session.startHandlePacked handle (word 7))
  let .succeeded first ← pending.resume 100000 1000
    | throw (IO.userError "projected captured first failed")
  let pending ← get "projected captured reuse" (first.session.startHandlePacked handle (word 7))
  let .succeeded last ← pending.resume 100000 1000
    | throw (IO.userError "projected captured reuse failed")
  require (first.value == complement 4 && last.value == complement 4) "projected captured result changed"
  heaps := heaps ++ [made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [14,20,35,50,83,104,120,136,143,158,167,182,206,221,227,245,263])
    "projected bit-not exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_COMPLETE_PROFILE: originals13/cache{recipe.compiled.indexed.base.functions.length}/table{fullProfile.table.rows.length}; captured Source/public complement on both calls"
  IO.println s!"PROJECTED_BITNOT_NATIVE_HEAPS: {heaps}"
  IO.println "PROJECTED_BITNOT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProjectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProxySource
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

/-- All declarations are configured before compilation; raw proxy identity is
kept distinct even though every proxy has the same native unit payload. -/
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function proxyWord() returns (@Word) { return @Word; }",
    "function proxyBool() returns (@Bool) { return @Bool; }",
    "function echoWord(value: @Word) returns (@Word) { return value; }"
  ]}] }
def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

structure LiteralShape (source : TypedSource) (inner : TypeSystem.Ty) where
  returned : StatementNode
  node : ExpressionNode
  inputs : source.inputs = []
  roots : source.roots = [.statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some node.id)
  found : source.lookupExpression? node.id = some node
  form : node.form = .proxy inner
  requirements : node.requirements = []
  coercions : node.coercions = []

structure EchoShape (source : TypedSource) (inner : TypeSystem.Ty) where
  binder : TypedBinder
  returned : StatementNode
  read : Tests.SourceCoreNamedBranch.Read source binder (.proxy inner)
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono (.proxy inner)
  roots : source.roots = [.statement returned.id]
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some read.node.id)

def echoHeap (before : Dynamic.Heap) (inner : TypeSystem.Ty) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .proxy inner, value := some (.proxy inner)}]⟩

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

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem literal_types {inner : TypeSystem.Ty} (shape : LiteralShape header.function.source inner) :
    header.types = [] := by
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_nil] using types.symm

theorem echo_types {inner : TypeSystem.Ty} (shape : EchoShape header.function.source inner) :
    header.types = [.proxy inner] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using types.symm

/-- Original proxy evaluation uses its raw inner type and leaves the heap intact. -/
theorem literal_plain {inner : TypeSystem.Ty} (shape : LiteralShape header.function.source inner)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    PlainValue anchor header invocation before [] (.proxy inner) before := by
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [] [] before := by
    rw [params]; exact .nil _ _
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [] before shape.node.id (.proxy inner) before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.found)
    · rw [shape.form]; exact .proxy (by rw [shape.requirements, shape.coercions]; rfl)
    · rw [shape.coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [] before header.function.body
      header.context (.returned (.proxy inner)) before := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

/-- A fresh proxy input allocates one original parameter cell; returning it
retains the raw proxy identity, independently of a public execution result. -/
theorem echo_plain {inner : TypeSystem.Ty} (shape : EchoShape header.function.source inner)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    PlainValue anchor header invocation before [.proxy inner] (.proxy inner) (echoHeap before inner) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates before (.proxy inner) (some (.proxy inner))
      ⟨before.cells.length⟩ (echoHeap before inner) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.proxy inner]
      [(shape.binder.id, ⟨before.cells.length⟩)] (echoHeap before inner) := by
    rw [params]; exact .cons (by rw [shape.scheme]; exact allocated) (.nil _ _)
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨before.cells.length⟩)]
      (echoHeap before inner) shape.read.node.id (.proxy inner) (echoHeap before inner) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.read.found)
    · rw [shape.read.form]
      exact .local (by rw [shape.read.requirements, shape.read.coercions]; rfl) .head allocated.reads_new rfl rfl
    · rw [shape.read.coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨before.cells.length⟩)]
      (echoHeap before inner) header.function.body header.context (.returned (.proxy inner)) (echoHeap before inner) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedProxy
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProxyFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "proxy artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "proxy original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "proxy original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "proxy global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "proxy substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "proxy ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "proxy ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "proxy unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

def observeLiteral (source : TypedSource) (inner : TypeSystem.Ty) : IO (LiteralShape source inner) := do
  let [.statement id] := source.roots | throw (IO.userError "proxy roots")
  let some returned := source.lookupStatement? id | throw (IO.userError "proxy return lookup")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "proxy return form")
  let some node := source.lookupExpression? expression | throw (IO.userError "proxy expression lookup")
  let ⟨inputs⟩ ← observed (source.inputs = []) "proxy input count"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "proxy root identity"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "proxy return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some node.id)) "proxy child identity"
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "proxy node identity"
  let ⟨form⟩ ← observed (node.form = .proxy inner) "proxy original raw inner type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "proxy requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "proxy coercions"
  return ⟨returned, node, inputs, roots, returnedFound, returnedForm, found, form, requirements, coercions⟩

def observeEcho (source : TypedSource) (inner : TypeSystem.Ty) : IO (EchoShape source inner) := do
  let [binder] := source.inputs | throw (IO.userError "proxy echo input")
  let [.statement id] := source.roots | throw (IO.userError "proxy echo root")
  let some returned := source.lookupStatement? id | throw (IO.userError "proxy echo return")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "proxy echo child")
  let some node := source.lookupExpression? expression | throw (IO.userError "proxy echo read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder node (.proxy inner)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "proxy echo inputs"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (.proxy inner)) "proxy echo raw input"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "proxy echo root identity"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "proxy echo return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "proxy echo child identity"
  return ⟨binder, returned, read, inputs, scheme, roots, returnedFound, returnedForm⟩

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "proxy bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedProxy
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProxySourceFirst
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

/-- Actual compiler selection and fresh bootstrap determine the public issuer
and original source. No body execution or completed public call is assumed. -/
structure Selection {fixture : CompiledFixture} (row : Row fixture)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = row.original.function.typedBody

theorem selection {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) :
    Nonempty (Selection row started) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) eligible
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  exact ⟨⟨issued, initial, sourceEq⟩⟩

/-- The final public conclusion retains the whole Source value, authentic
encoding and retained history, or an actual earlier stage rejection. -/
structure InitialOutput {fixture : CompiledFixture} (row : Row fixture)
    {publicArguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.original.key publicArguments)
    (arguments : List Dynamic.Value) (value : Dynamic.Value) (after : Dynamic.Heap) extends Selection row started where
  plain : ∀ invocation, RecursiveNamedPublicPhysicalSessionState.PlainValue
    initial.header initial.header invocation ⟨[]⟩ arguments value after
  forward : ∀ invocation,
    (SelectedCompilationPublicSessionState.SourceCall initial.header initial.header invocation
        ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header issued.initial
        issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation arguments

/-- The original @T expression produces a proxy with exactly its raw inner
identity, before any native execution is observed. -/
theorem literal_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (inner : TypeSystem.Ty) (shape : LiteralShape row.original.function.typedBody inner)
    (started : Started fixture row.original.key []) :
    Nonempty (InitialOutput row started [] (.proxy inner) ⟨[]⟩) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : LiteralShape chosen.initial.header.function.source inner := by
    rw [chosen.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => literal_plain chosen.initial.header actual sourceAt
    chosen.initial.header invocation ⟨[]⟩
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [] chosen.initial.header.types := by
    rw [literal_types chosen.initial.header actual]; exact .nil
  exact ⟨{
    toSelection := chosen
    plain := plain
    forward := fun invocation => chosen.initial.forward_data_output_plain types .nil (plain invocation) }⟩

/-- A fresh proxy public input has an independent raw-typing/meaning receipt;
the actual initial metadata encoder and whole-output theorem preserve it. -/
theorem echo_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (inner : TypeSystem.Ty) (shape : EchoShape row.original.function.typedBody inner)
    (started : Started fixture row.original.key [.proxy inner]) :
    Nonempty (InitialOutput row started [.proxy inner] (.proxy inner) (echoHeap ⟨[]⟩ inner)) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : EchoShape chosen.initial.header.function.source inner := by
    rw [chosen.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => echo_plain chosen.initial.header actual sourceAt
    chosen.initial.header invocation ⟨[]⟩
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [.proxy inner] chosen.initial.header.types := by
    rw [echo_types chosen.initial.header actual]
    exact .cons ⟨.proxy inner, by simp [SourceCoreIndexedSession.DataInput.publicValue], .proxy inner⟩ .nil
  have means : RecursiveNamedPublicDataInputs.Meanings [.proxy inner] [.proxy inner] :=
    .cons ⟨.proxy inner, by simp [SourceCoreIndexedSession.DataInput.publicValue], .proxy inner⟩ .nil
  exact ⟨{
    toSelection := chosen
    plain := plain
    forward := fun invocation => chosen.initial.forward_data_output_plain types means (plain invocation) }⟩

end Tests.SourceCoreSelectedProxy
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedProxyProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- One complete checked cache supplies both proxy literals and a genuine
metadata-bearing initial proxy input. Source traces precede each public result. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "proxy complete checked profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 3 &&
      fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.table.rows.length == 3)
    "proxy original/cache/profile rows changed"
  let echo ← observeRow fixture "echoWord"
  let echoShape ← observeEcho echo.original.function.typedBody .word
  let mut literalHeaps := []
  for (name, inner) in [("proxyWord", TypeSystem.Ty.word), ("proxyBool", .bool)] do
    let row ← observeRow fixture name
    let shape ← observeLiteral row.original.function.typedBody inner
    let started ← observeStarted fixture row.original.key []
    have _sourceFirst := literal_from_source row profile inner shape started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "proxy literal zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError "proxy literal failed")
    require (completed.value == .proxy inner) "proxy original raw inner identity changed"
    literalHeaps := literalHeaps ++ [started.session.heapSize, completed.session.heapSize]
    if inner == .word then
      let pending ← get "proxy same-session exported input"
        (completed.session.start echo.original.key [completed.value])
      let .succeeded echoed ← pending.resume 100000 1000
        | throw (IO.userError "proxy same-session exported input failed")
      require (echoed.value == .proxy .word && echoed.session.heapSize == 7)
        "proxy same-session raw identity/heap changed"
  require (literalHeaps == [4,4,4,4]) "proxy literal exact heaps changed"
  let started ← observeStarted fixture echo.original.key [.proxy .word]
  have _sourceInput := echo_from_source echo profile .word echoShape started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "proxy input zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "proxy initial data input failed")
  require (completed.value == .proxy .word) "proxy initial output identity changed"
  match completed.session.start echo.original.key [.proxy .bool] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "proxy mismatched raw inner type accepted")
  let again ← get "proxy valid reuse after input rejection"
    (completed.session.start echo.original.key [completed.value])
  let .succeeded reused ← again.resume 100000 1000
    | throw (IO.userError "proxy reuse after input rejection failed")
  require (reused.value == .proxy .word) "proxy reused raw identity changed"
  let inputHeaps := [started.session.heapSize, completed.session.heapSize, reused.session.heapSize]
  require (inputHeaps == [4,7,10]) "proxy initial/reuse exact heaps changed"
  IO.println s!"PROXY_COMPLETE_CACHE: originals3/cache3/table{profile.table.rows.length}"
  IO.println s!"PROXY_LITERAL_NATIVE_HEAPS: {literalHeaps}"
  IO.println s!"PROXY_INPUT_REUSE_NATIVE_HEAPS: {inputHeaps}"
  IO.println "PROXY_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProxy
end
