import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.Execution
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion

/-!
# Selected profile tests

Selected profiles of bit-not, body control, box outputs, completions, composites and compounds.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBitNotSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBitNotFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function invert(value: Word) returns (Word) { value ~=; return value; }",
    "function initialize(value: Word) returns (Word) { for (value ~=; false; value ~=) { } return value; }",
    "function post(value: Word) returns (Word) { for (let i: Word = 0; i < 1; value ~=, i += 1) { continue; } return value; }",
    "function stop(value: Word) returns (Word) { for (let i: Word = 0; true; value ~=) { break; } return value; }",
    "function missing() returns (Word) { let absent: Word; absent ~=; return 0; }",
    "function postMissing() returns (Word) { let absent: Word; for (let i: Word = 0; true; absent ~=) { continue; } return 0; }",
    "function initialMissing() returns (Word) { let absent: Word; for (absent ~=; false; ) { } return 0; }",
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(ignored: Word) -> Word { value ~=; return value; }; }"
  ]}] }
def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  nativeResult : global.resultType = .word
  resultType : original.function.inferredBodyType = .word
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "bitnot artifact absent")
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

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "bitnot original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "bitnot original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "bitnot global key"
      let ⟨nativeResult⟩ ← observed (global.resultType = .word) "bitnot native result"
      let ⟨resultType⟩ ← observed (original.function.inferredBodyType = .word) "bitnot raw result"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "bitnot substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "bitnot ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "bitnot ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        nativeResult := nativeResult
        resultType := resultType
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "bitnot unique physical slot")

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
  let .statement sid := id | throw (IO.userError "bitnot statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "bitnot statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "bitnot read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeUnary (source : TypedSource) : IO (UnaryShape source) := do
  let [binder] := source.inputs | throw (IO.userError "bitnot parameter count")
  let [first, second] := source.roots | throw (IO.userError "bitnot statement count")
  let assignment ← statement source first
  let returned ← statement source second
  let .assignBitNot resolution := assignment.form | throw (IO.userError "bitnot assignment form")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "bitnot return form")
  let result ← wordRead source binder resultId
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "bitnot original inputs"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono .word) "bitnot input scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement assignment.id, .statement returned.id]) "bitnot original roots"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "bitnot assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignBitNot resolution) "bitnot original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "bitnot target identity"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "bitnot bare target"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "bitnot return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "bitnot return read"
  return ⟨binder, resolution, assignment, returned, result, inputs, scheme, roots,
    assignmentFound, assignmentForm, targetRoot, targetBare, returnedFound, returnedForm⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [first, second, third] := source.roots | throw (IO.userError "missing statement count")
  let declared ← statement source first
  let assignment ← statement source second
  let returned ← statement source third
  let .letDecl binder none := declared.form | throw (IO.userError "missing local declaration")
  let .assignBitNot resolution := assignment.form | throw (IO.userError "missing unary assignment")
  let ⟨inputs⟩ ← observed (source.inputs = []) "missing inputs"
  let ⟨localScheme⟩ ← observed (binder.scheme = .mono .word) "missing local scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]) "missing roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl binder none) "missing absent declaration"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "missing assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignBitNot resolution) "missing operator identity"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "missing target root"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "missing target projections"
  return ⟨binder, resolution, declared, assignment, returned, inputs, localScheme, roots,
    declaredFound, declaredForm, assignmentFound, assignmentForm, targetRoot, targetBare⟩

structure ObservedProgram (fixture : CompiledFixture) where
  invertRow : Row fixture
  missingRow : Row fixture
  invertShape : UnaryShape invertRow.original.function.typedBody
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 8

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let invertRow ← observeRow fixture "invert"
  let missingRow ← observeRow fixture "missing"
  let invertShape ← observeUnary invertRow.original.function.typedBody
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 8) "bitnot cache size"
  return ⟨invertRow, missingRow, invertShape, missingShape, cacheSize⟩

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
  | .outOfFuel _ => throw (IO.userError "bitnot bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBitNotSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

private theorem word_types (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context [.word value] [.word] :=
  .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil

private theorem word_meanings (value : Word) :
    RecursiveNamedPublicDataInputs.Meanings [.word value] [.word value] :=
  .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil

private theorem word_inputs (entries : List RecursiveNamedPublicFunctionHistory.Entry)
    (context : SourceSemantics.Context) (value : Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word] [.word value] [.word value] :=
  .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.invertRow.original.key [.word (Word.ofNatModulo 7)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.invertRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7).bitNot)
    (resultHeap ⟨[]⟩ (Word.ofNatModulo 7))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 7)] (.value (.word (Word.ofNatModulo 7).bitNot))
        (resultHeap ⟨[]⟩ (Word.ofNatModulo 7)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word (Word.ofNatModulo 7).bitNot)
        started.call (resultHeap ⟨[]⟩ (Word.ofNatModulo 7))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 7)]

/-- Source execution is derived from the observed original body before the
initial public checkpoint completes. The compiler profile remains explicit. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.invertRow.original.key [.word (Word.ofNatModulo 7)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, signatureSame⟩ := observed.invertRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.invertRow.resultType))
  have nativeEq : initial.header.output = .word := initial.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans observed.invertRow.nativeResult))
  have shape : UnaryShape initial.header.function.source := by rw [sourceEq]; exact observed.invertShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
      [.word (Word.ofNatModulo 7)] (.word (Word.ofNatModulo 7).bitNot)
      (resultHeap ⟨[]⟩ (Word.ofNatModulo 7)) := by
    intro invocation
    exact unary_call initial.header shape sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 7)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 7)],
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl; exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 7)] initial.header.types := by
    rw [unary_input_types initial.header shape]
    exact word_types _ _
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple types
      (word_meanings _) (.word (Word.ofNatModulo 7).bitNot) resultEq nativeEq (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure LaterMeaning (row : Row fixture) (value : Word)
    (call : StartedCall session row.original.key [.word value] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word value]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap [.word value]
    (.word value.bitNot) (resultHeap state.heap value)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word value]
        (.value (.word value.bitNot)) (resultHeap state.heap value) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.word value.bitNot)
        call (resultHeap state.heap value)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word value]

/-- Subsequent unary execution uses the same issued catalog and exact returned
Source heap; the ordinary trace is independent of public completion. -/
theorem later_from_source (row : Row fixture)
    (shape : UnaryShape row.original.function.typedBody) (value : Word)
    (call : StartedCall session row.original.key [.word value] runOptions)
    (ready : session.ExportsReady) : Nonempty (LaterMeaning issued state row value call) := by
  obtain ⟨eligible, rowSame, signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := request.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans row.resultType))
  have nativeEq : request.header.output = .word := request.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans row.nativeResult))
  have actualShape : UnaryShape request.header.function.source := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => unary_call request.header actualShape sourceAt anchor invocation state.heap value
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [body_types, unary_input_types request.header actualShape]
    exact word_inputs _ _ _
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.scalar issued state call request inputs ready
      (.word value.bitNot) resultEq nativeEq (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture)
    (call : StartedCall session row.original.key [] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key []
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap []
    (.invalidUnaryOperand .bitNot) (missingHeap state.heap)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap []
        (.fault (.semantic (.invalidUnaryOperand .bitNot))) (missingHeap state.heap) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.semantic (.invalidUnaryOperand .bitNot))
        call (missingHeap state.heap)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation []

/-- The absent target produces the genuine unary fault without evaluating
an expression. The public failure uses the exact original body and heap. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
     (call : StartedCall session row.original.key [] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row call) := by
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
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .nil
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.invalidUnaryOperand .bitNot) (plain invocation)⟩⟩

/-- Every sufficiently fueled genuine operand failure returns a state for
this same issued catalog, and an independent complement trace starts from that
exact reached heap. No completed call is an input to this continuation. -/
theorem missing_then_reuse (missingRow invertRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (invertShape : UnaryShape invertRow.original.function.typedBody)
    (call : StartedCall session missingRow.original.key [] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.invalidUnaryOperand .bitNot)) token ∧
            ∀ nextCall : StartedCall returned invertRow.original.key
                [.word (Word.ofNatModulo 7)] runOptions,
              Nonempty (LaterMeaning issued next invertRow (Word.ofNatModulo 7) nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact later_from_source issued next invertRow invertShape (Word.ofNatModulo 7) nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

end Tests.SourceCoreSelectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBitNotProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def flipped (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n).bitNot

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "bitnot startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "bitnot zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "bitnot success missing")
  require (completed.value == expected) "bitnot result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "bitnot fault startup" (session.start key [])
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "bitnot absent target did not fail")
  let some diagnostic ← get "bitnot diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "bitnot diagnostic missing")
  require (match diagnostic.error with | .invalidUnaryOperand .bitNot none => true | _ => false)
    "bitnot unary diagnostic changed"
  pure after

/-- The first call consumes the independent Source proof before completion.
Header controls and a retained closure whose every call starts from its
creation-time capture are runtime companions in the same original
eight-function program and the same public session. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "bitnot original selected profile rejected")
  require (fixture.recipe.compiled.indexed.base.functions.length == 8 && profile.table.rows.length == 8)
    "bitnot original cache/table changed"
  let started ← observeStarted fixture observed.invertRow.original.key [word 7]
  have _sourceFirst := initial_from_source fixture observed profile started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "bitnot initial zero fuel did not suspend")
  let .succeeded one ← suspended.resume 100000 1000
    | throw (IO.userError "bitnot initial complement failed")
  require (one.value == flipped 7) "bitnot initial complement changed"
  let keys ← ["initialize", "post", "stop", "postMissing", "initialMissing", "make"].mapM
    (SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram)
  let [initializer, post, stop, postMissing, initialMissing, make] := keys
    | throw (IO.userError "bitnot original keys changed")
  let two ← success one.session initializer [word 7] (flipped 7)
  let three ← success two post [word 7] (flipped 7)
  let four ← success three stop [word 7] (word 7)
  let five ← failure four observed.missingRow.original.key
  let six ← failure five postMissing
  let seven ← failure six initialMissing
  let eight ← success seven observed.invertRow.original.key [word 7] (flipped 7)
  let pending ← get "bitnot factory startup" (eight.start make [word 7])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "bitnot factory failed")
  let .function handle := made.value | throw (IO.userError "bitnot captured handle missing")
  let pendingFirst ← get "bitnot captured first" (made.session.startHandlePacked handle (word 0))
  let .succeeded first ← pendingFirst.resume 100000 1000
    | throw (IO.userError "bitnot captured first failed")
  require (first.value == flipped 7) "bitnot captured first result changed"
  let pendingLast ← get "bitnot captured repeated" (first.session.startHandlePacked handle (word 0))
  let .succeeded last ← pendingLast.resume 100000 1000
    | throw (IO.userError "bitnot captured reuse failed")
  require (last.value == flipped 7) "bitnot captured reused result changed"
  let heaps := [started.session.heapSize, one.session.heapSize, two.heapSize, three.heapSize,
    four.heapSize, five.heapSize, six.heapSize, seven.heapSize, eight.heapSize,
    made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [9, 12, 16, 23, 30, 33, 40, 43, 46, 52, 58, 64])
    "bitnot original native stores changed"
  IO.println s!"BITNOT_CACHE: cache{fixture.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  IO.println s!"BITNOT_NATIVE_HEAPS: {heaps}"
  IO.println "BITNOT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBodyControlSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  first : ExpressionNode
  discard : StatementNode
  second : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  roots : source.roots = [.statement discard.id, .statement returned.id]
  firstFound : source.lookupExpression? first.id = some first
  firstForm : first.form = .reference binder.name (.local binder.id)
  firstRequirements : first.requirements = []
  firstCoercions : first.coercions = []
  discardFound : source.lookupStatement? discard.id = some discard
  discardForm : discard.form = .expression first.id true
  secondFound : source.lookupExpression? second.id = some second
  secondForm : second.form = .reference binder.name (.local binder.id)
  secondRequirements : second.requirements = []
  secondCoercions : second.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some second.id)

def sourceHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩

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
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [.word] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

include shape in
/-- Allocate the parameter, evaluate the discarded read, then evaluate the return.
The proof uses original Source occurrences before the public checkpoint runs. -/
theorem ordinary_call {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.word word) (sourceHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (sourceHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (sourceHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.discard.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have read (node : ExpressionNode) (found : header.function.source.lookupExpression? node.id = some node)
      (form : node.form = .reference shape.binder.name (.local shape.binder.id))
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
        (sourceHeap word) node.id (.word word) (sourceHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .local (by rw [requirements, coercions]; rfl) .head
        (Dynamic.Heap.Allocates.reads_new (Dynamic.Heap.Allocates.append (heap := ⟨[]⟩)
          (type := .word) (value := some (.word word)))) rfl rfl
    · rw [coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (sourceHeap word)
      header.function.body header.context (.returned (.word word)) (sourceHeap word) := by
    rw [roots]
    exact .cons (.expression (lookupStatement?_sound shape.discardFound) shape.discardForm
      (read shape.first shape.firstFound shape.firstForm shape.firstRequirements shape.firstCoercions))
      (.singleton (lookupStatement?_sound shape.returnedFound)
        (by rw [shape.returnedForm]; intro id impossible; cases impossible)
        (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
          (read shape.second shape.secondFound shape.secondForm shape.secondRequirements shape.secondCoercions)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedBodyControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBodyControlFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function discard(value: Word) returns (Word) { value; return value; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "body control source input shape")
  let [.expression first, .statement discard, .expression second, .statement returned] := source.nodes
    | throw (IO.userError "body control source occurrence shape")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "body control inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "body control binderType"
  let ⟨roots⟩ ← observed (source.roots = [.statement discard.id, .statement returned.id]) "body control roots"
  let ⟨firstFound⟩ ← observed (source.lookupExpression? first.id = some first) "body control firstFound"
  let ⟨firstForm⟩ ← observed (first.form = .reference binder.name (.local binder.id)) "body control firstForm"
  let ⟨firstRequirements⟩ ← observed (first.requirements = []) "body control firstRequirements"
  let ⟨firstCoercions⟩ ← observed (first.coercions = []) "body control firstCoercions"
  let ⟨discardFound⟩ ← observed (source.lookupStatement? discard.id = some discard) "body control discardFound"
  let ⟨discardForm⟩ ← observed (discard.form = .expression first.id true) "body control discardForm"
  let ⟨secondFound⟩ ← observed (source.lookupExpression? second.id = some second) "body control secondFound"
  let ⟨secondForm⟩ ← observed (second.form = .reference binder.name (.local binder.id)) "body control secondForm"
  let ⟨secondRequirements⟩ ← observed (second.requirements = []) "body control secondRequirements"
  let ⟨secondCoercions⟩ ← observed (second.coercions = []) "body control secondCoercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "body control returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some second.id)) "body control returnedForm"
  return {
    binder := binder
    first := first
    discard := discard
    second := second
    returned := returned
    inputs := inputs
    binderType := binderType
    roots := roots
    firstFound := firstFound
    firstForm := firstForm
    firstRequirements := firstRequirements
    firstCoercions := firstCoercions
    discardFound := discardFound
    discardForm := discardForm
    secondFound := secondFound
    secondForm := secondForm
    secondRequirements := secondRequirements
    secondCoercions := secondCoercions
    returnedFound := returnedFound
    returnedForm := returnedForm }

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  shape : Shape named.specialized.function.typedBody
  resultType : named.specialized.function.inferredBodyType = .word
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "body control artifact absent")
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
            have original : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "body control selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "body control original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .word) "body control factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "body control substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "body control factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "body control parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "body control physical slot"
                return {
                  recipe := recipe
                  checked := original
                  seeds := seeds
                  facade := publicCompiled
                  accepted := accepted
                  selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade
                  profile := profile
                  original := originalRow
                  originalMember := by
                    rw [originals]
                    exact List.mem_cons_self
                  named := named
                  functions := functions
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "body control cache shape")

theorem Fixture.eligible (fixture : Fixture) :
    Nonempty (SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted
    fixture.selected fixture.originalMember
  have member := List.mem_of_getElem? prepared.selected
  rw [fixture.functions] at member
  have same := List.mem_singleton.mp member
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram fixture.named.specialized := by
    rw [← same, prepared.same]
    exact prepared.origin
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      fixture.named.specialized.parameterSubstitution := by
    rw [fixture.substitution]
    intro parameter replacement impossible
    cases impossible
  exact ⟨⟨fixture.named, 0, fixture.named.signature,
    by rw [fixture.functions]; rfl, fixture.slot, rfl,
    ⟨origin, range, fixture.ordinary, fixture.ordinaryInputs⟩⟩⟩

structure Started (fixture : Fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key [.word seed] runOptions

def observeStarted (fixture : Fixture) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "body control bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedBodyControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBodyControlSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

/-- Only actual compilation, profile, bootstrap and start receipts precede this
ordinary Source proof. No completed public result is an input. -/
structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
    (.word seed) (sourceHeap seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
      (.value (.word seed)) (sourceHeap seed) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint (.word seed) (sourceHeap seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

theorem from_source (fixture : Fixture) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) (namedEq.trans rowSame))
  let shape : Shape initial.header.function.source := sourceEq.symm ▸ fixture.shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := fun invocation => ordinary_call initial.header shape sourceAt invocation seed
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact ⟨⟨issued, initial, shape, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedBodyControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBoxOutputSource
/-! The constructor result is built from the actual Source nodes and one
fresh parameter cell. The checked selected header supplies constructor typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  read : ExpressionNode
  construct : ExpressionNode
  statement : StatementNode
  instantiation : DataConstructorInstantiation
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  readFound : source.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  constructFound : source.lookupExpression? construct.id = some construct
  constructForm : construct.form = .constructor instantiation [read.id]
  constructRequirements : construct.requirements = []
  constructCoercions : construct.coercions = []
  substitution : instantiation.parameterSubstitution = []
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some construct.id)

def appendWord (before : Dynamic.Heap) (word : Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := some (.word word)}]⟩

def result (instantiation : DataConstructorInstantiation) (word : Word) : Dynamic.Value :=
  .constructed instantiation [.word word]

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
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [.word] := by
  have parameters : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [parameters, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

include shape in
theorem roots : header.function.body = [shape.statement.id] :=
  roots_injective (header.agreement.roots.symm.trans shape.roots)

private theorem constructor_admissible {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation arguments)
    (typing : ExpressionHasType source context id type) :
    DataConstructorInstantiation.Admissible context instantiation := by
  cases typing with
  | intro contains raw _rawEq _rawType _type _plan =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at raw
    cases raw with
    | constructor valid _arguments => exact valid

include shape in
theorem constructor_valid
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    DataConstructorInstantiation.Valid header.context shape.instantiation := by
  obtain ⟨final, facts, statements, _complete⟩ := certified.statements
  rw [roots header shape] at statements
  cases statements with
  | singleton statement =>
    cases statement with
    | returnValue contains form expression _type =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.statementFound)
      cases same
      rw [shape.statementForm] at form
      cases Option.some.inj (StatementForm.returnStmt.inj form)
      have valid := constructor_admissible header.unique shape.constructFound shape.constructForm expression
      cases valid with
      | intro dataType signature dataMember signatureMember owner constructorEq exact range payload result =>
        exact .intro dataType signature dataMember signatureMember owner constructorEq exact
          (by rw [shape.substitution]; intro parameter replacement impossible; cases impossible) payload result
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique (by assumption)).symm.trans shape.statementFound)
      cases same
      simp_all [shape.statementForm]

include shape in
theorem ordinary_call
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue anchor header invocation before [.word word]
      (result shape.instantiation word) (appendWord before word) := by
  have parameters : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates before shape.binder.scheme.body
      (some (.word word)) ⟨before.cells.length⟩ (appendWord before word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word word]
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before word) := by
    rw [parameters]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before word)
      shape.read.id (.word word) (appendWord before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.readFound)
    · rw [shape.readForm]
      exact .local (by rw [shape.readRequirements, shape.readCoercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [shape.readCoercions]; exact .nil
  have constructed : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before word)
      shape.construct.id (result shape.instantiation word) (appendWord before word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.constructFound)
    · rw [shape.constructForm]
      exact .constructor (by rw [shape.constructRequirements, shape.constructCoercions]; rfl)
        (constructor_valid header shape certified) (.cons read .nil)
    · rw [shape.constructCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before word)
      header.function.body header.context (.returned (result shape.instantiation word)) (appendWord before word) := by
    rw [roots header shape]
    exact .singleton (lookupStatement?_sound shape.statementFound)
      (by rw [shape.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm constructed)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedBoxOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBoxOutputFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "enum Box { Wrap(Word) } function box(value: Word) returns (Box) { return .Wrap(value); }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "box source input shape")
  let [.expression read, .expression construct, .statement statement] := source.nodes
    | throw (IO.userError "box source occurrence shape")
  let .constructor instantiation _arguments := construct.form
    | throw (IO.userError "box constructor form")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "box inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "box parameter type"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "box roots"
  let ⟨readFound⟩ ← observed (source.lookupExpression? read.id = some read) "box read occurrence"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "box read form"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "box read requirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "box read coercions"
  let ⟨constructFound⟩ ← observed (source.lookupExpression? construct.id = some construct) "box constructor occurrence"
  let ⟨constructForm⟩ ← observed (construct.form = .constructor instantiation [read.id]) "box constructor arguments"
  let ⟨constructRequirements⟩ ← observed (construct.requirements = []) "box constructor requirements"
  let ⟨constructCoercions⟩ ← observed (construct.coercions = []) "box constructor coercions"
  let ⟨substitution⟩ ← observed (instantiation.parameterSubstitution = []) "box constructor substitution"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement) "box return occurrence"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some construct.id)) "box return form"
  return {
    binder := binder, read := read, construct := construct, statement := statement,
    instantiation := instantiation, inputs := inputs, binderType := binderType, roots := roots,
    readFound := readFound, readForm := readForm, readRequirements := readRequirements,
    readCoercions := readCoercions, constructFound := constructFound, constructForm := constructForm,
    constructRequirements := constructRequirements, constructCoercions := constructCoercions,
    substitution := substitution, statementFound := statementFound, statementForm := statementForm }

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  shape : Shape named.specialized.function.typedBody
  resultType : named.specialized.function.inferredBodyType = shape.instantiation.resultType
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "box artifact absent")
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
            have original : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "box selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "box original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = shape.instantiation.resultType) "box factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "box substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "box factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "box parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "box physical slot"
                return {
                  recipe := recipe
                  checked := original
                  seeds := seeds
                  facade := publicCompiled
                  accepted := accepted
                  selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade
                  profile := profile
                  original := originalRow
                  originalMember := by
                    rw [originals]
                    exact List.mem_cons_self
                  named := named
                  functions := functions
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "box cache shape")

theorem Fixture.eligible (fixture : Fixture) :
    Nonempty (SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted
    fixture.selected fixture.originalMember
  have member := List.mem_of_getElem? prepared.selected
  rw [fixture.functions] at member
  have same := List.mem_singleton.mp member
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram fixture.named.specialized := by
    rw [← same, prepared.same]
    exact prepared.origin
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      fixture.named.specialized.parameterSubstitution := by
    rw [fixture.substitution]
    intro parameter replacement impossible
    cases impossible
  exact ⟨⟨fixture.named, 0, fixture.named.signature,
    by rw [fixture.functions]; rfl, fixture.slot, rfl,
    ⟨origin, range, fixture.ordinary, fixture.ordinaryInputs⟩⟩⟩

structure Started (fixture : Fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key [.word seed] runOptions

def observeStarted (fixture : Fixture) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "box bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedBoxOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBoxOutputSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt ReturnedValue)

variable {fixture : Fixture}

private theorem selected_shape (fixture : Fixture)
    {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (same : header.named = fixture.named) : Nonempty (Shape header.function.source) := by
  have sourceEq := header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) same)
  exact ⟨sourceEq.symm ▸ fixture.shape⟩

private theorem selected_eq (fixture : Fixture)
    (row : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) :
    row.named = fixture.named := by
  have member := List.mem_of_getElem? row.cached
  rw [fixture.functions] at member
  exact List.mem_singleton.mp member

structure LaterMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : issued.toIssued.State anchor session []) (word : Word)
    (call : StartedCall session fixture.named.signature.key [.word word] runOptions)
    (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session fixture.named.signature.key [.word word] runOptions.inputValidationFuel
    before.world before.store
  shape : Shape request.header.function.source
  plain : PlainValue anchor request.header invocation before.heap [.word word]
    (result shape.instantiation word) (appendWord before.heap word)
  forward :
    (SourceCall anchor request.header invocation before.heap [.word word]
      (.value (result shape.instantiation word)) (appendWord before.heap word) ∧
      ForwardAt issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe []
        request.header.function.resultType call.checkpoint (result shape.instantiation word)
        (appendWord before.heap word)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued before call request.header invocation [.word word]

theorem later_from_source (fixture : Fixture) (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : issued.toIssued.State anchor session []) (word : Word)
    (call : StartedCall session fixture.named.signature.key [.word word] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    Nonempty (LaterMeaning issued before word call invocation) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call row
  obtain ⟨shape⟩ := selected_shape fixture (namedEq.trans (selected_eq fixture row))
  have certified := issued.support.certificates request.header request.selected.member
  have plain := ordinary_call request.header shape certified request.sourceAt anchor invocation before.heap word
  have bindingTypes : request.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
    have types := Dynamic.MonoBindersExtend.bodyTypes_eq request.header.extended
    rw [request.header.parameters] at types
    simpa only [input_types request.header shape, List.map_map, Function.comp_def] using types
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [bindingTypes]
    exact .cons (.data ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  exact ⟨⟨request, shape, plain,
    SelectedCompilationStageClosedOutputForward.later issued before call request inputs ready plain⟩⟩

structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
    (result shape.instantiation seed) (appendWord ⟨[]⟩ seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
      (.value (result shape.instantiation seed)) (appendWord ⟨[]⟩ seed) ∧
      ForwardAt issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe []
        initial.header.function.resultType started.call.checkpoint (result shape.instantiation seed)
        (appendWord ⟨[]⟩ seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

theorem initial_from_source (fixture : Fixture) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  obtain ⟨shape⟩ := selected_shape fixture (namedEq.trans (selected_eq fixture row))
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := issued.support.certificates initial.header initial.start.selected.member
  have plain := fun invocation => ordinary_call initial.header shape certified sourceAt
    initial.header invocation ⟨[]⟩ seed
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact ⟨⟨issued, initial, shape, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

/-- Every sufficiently funded first completion carries its entire constructor
representation. A subsequent actual named start obtains a fresh independent
ordinary constructor trace and the same full-output guarantee. -/
def InitialMeaning.Followed
    {started : Started fixture} (meaning : InitialMeaning fixture started)
    (invocation : Staging.Recursive.Scope) : Prop :=
    (∃ executionBound outputBound,
      ∀ executionFuel outputFuel outcome, executionBound ≤ executionFuel → outputBound ≤ outputFuel →
      started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion, outcome = .succeeded completion ∧
      ∃ after : meaning.issued.toIssued.State meaning.initial.header completion.session [],
        after.heap = appendWord ⟨[]⟩ seed ∧
        ReturnedValue completion after meaning.initial.header.function.resultType
          (result meaning.shape.instantiation seed) outputFuel ∧
        ∀ word (call : StartedCall completion.session fixture.named.signature.key [.word word] runOptions),
          Nonempty (LaterMeaning meaning.issued after word call invocation)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped meaning.issued started.call
      meaning.initial invocation [.word seed]

theorem InitialMeaning.followed
    {started : Started fixture} (meaning : InitialMeaning fixture started)
    (invocation : Staging.Recursive.Scope) : meaning.Followed invocation := by
  rcases meaning.forward invocation with ⟨_source, bound, outBound, forward⟩ | stopped
  · refine .inl ⟨bound, outBound, ?_⟩
    intro fuel outFuel outcome enough outputEnough resumed
    obtain ⟨completion, succeeded, ready, after, heap, represented, _selection⟩ :=
      forward fuel outFuel outcome enough outputEnough resumed
    exact ⟨completion, succeeded, after, heap, represented,
      fun word call => later_from_source fixture meaning.issued after word call ready invocation⟩
  · exact .inr stopped

/-- The initial ordinary proof and the subsequent ordinary proof share the
actual returned history and full constructor representation. -/
theorem from_source (fixture : Fixture) (started : Started fixture) :
    ∃ meaning : InitialMeaning fixture started, ∀ invocation, meaning.Followed invocation := by
  obtain ⟨meaning⟩ := initial_from_source fixture started
  exact ⟨meaning, meaning.followed⟩

end Tests.SourceCoreSelectedBoxOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBoxOutputRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "box initial call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "box initial call did not complete")
  require (first.value == .constructed fixture.shape.instantiation [.word seed])
    "initial full constructor output changed"
  let secondWord := Word.ofNatModulo 52
  let .ok checkpoint := first.session.start fixture.named.signature.key [.word secondWord] runOptions.inputValidationFuel
    | throw (IO.userError "later box call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "later box call did not suspend at zero fuel")
  let .succeeded second ← suspended.resume 100000 1000
    | throw (IO.userError "later box call did not complete")
  require (second.value == .constructed fixture.shape.instantiation [.word secondWord])
    "later full constructor output changed"
  require ([started.session.heapSize, first.session.heapSize, second.session.heapSize] == [2, 5, 8])
    "box physical heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 1) "box cache changed"
  IO.println s!"SOURCE_FIRST_CONSTRUCTOR_OUTPUT_PASS: actual check/compile/profile; independent original read/constructor traces; closed initial then later full ReturnedValue and exact Source heap; no manual well-formedness; zero-fuel resume both calls; Wrap(37), Wrap(52); heaps{[started.session.heapSize, first.session.heapSize, second.session.heapSize]}"

end Tests.SourceCoreSelectedBoxOutput
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompilationProfile
/-! The actual compiler profile accepts the selected identity cache even when
an unrelated checked conversion has no executable coercion method. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompilationProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreCompilationScope (workspace options)

def run : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"scope profile checking: {reprStr errors}")
  | .ok program =>
    let some identity := program.signatures.functions.find? (·.name == "identity")
      | throw (IO.userError "scope profile identity missing")
    match generated : SourceCoreCompiler.compileChecked program [.declaration identity.id] options with
    | .error error => throw (IO.userError s!"scope profile compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "scope profile cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans
            (SourceCoreCompiler.compileChecked_program generated)
        have accepted : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]
          exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached accepted
          | throw (IO.userError "scope profile rejected the selected identity")
        have _selectedBodies : SelectedCompilationBodyTyping.Bodies cached :=
          SelectedCompilationCheckedBodyTyping.of_checked accepted profile
        unless cached.sourceProgram.functions.length == 2 &&
            cached.indexed.base.functions.length == 1 && profile.table.rows.length == 1 do
          throw (IO.userError "scope profile changed original declarations or selected cache")
        IO.println "SELECTED_COMPILATION_PROFILE_PASS: checker-derived signatures and selected body typing; original functions2; selected cache1/table1; unrelated missing coercion method retained"

end Tests.SourceCoreSelectedCompilationProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompletionSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

def inputHeap (flag : Bool) (word : Word) : Dynamic.Heap :=
  ⟨[{type := .bool, value := some (.bool flag)}, {type := .word, value := some (.word word)}]⟩
def thenHeap (word : Word) : Dynamic.Heap :=
  ⟨(inputHeap true word).cells ++ [{type := .word, value := some (.word word)}]⟩
def branchHeap (flag : Bool) (word : Word) : Dynamic.Heap :=
  if flag then thenHeap word else inputHeap false word

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
  {function : CheckedFunction} {signature : ProgramFunctionSignature}
  (shape : Tests.SourceCoreNamedBranch.FactoryShape function signature)
  (sourceEq : header.function.source = function.typedBody)

include shape sourceEq in
theorem branch_input_types : header.types = [.bool, .word] := by
  have params : header.function.parameters = [shape.flag, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.flagScheme,
    shape.argumentScheme, TypeSystem.Scheme.mono] using types.symm

include shape sourceEq in
private theorem branch_extension (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ localContext, BinderExtends function.typedBody.owner header.context shape.copyBinder localContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.branch.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  rw [roots, sourceEq] at typed
  cases typed with
  | singleton head =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete (sourceEq ▸ header.unique) contains).symm.trans shape.branchFound)
    rw [shape.branchForm] at formTyped
    cases formTyped with
    | ifWithElse condition first second =>
      cases first with
      | cons head tail =>
        obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
        cases Option.some.inj ((lookupStatement?_complete (sourceEq ▸ header.unique) contains).symm.trans shape.initializedFound)
        rw [shape.initializedForm] at formTyped
        cases formTyped with
        | letInitialized value mono extension => exact ⟨_, extension⟩
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly (by rw [shape.localScheme]; rfl))

include shape sourceEq in
/-- Both original branches are evaluated from independent Source rules. The true
branch allocates its original copy; the false branch preserves the parameter heap. -/
theorem branch_call (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope)
    (flag : Bool) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [.bool flag, .word word] (.word word) (branchHeap flag word) := by
  let environment : Dynamic.Environment := [(shape.argument.id, ⟨1⟩), (shape.flag.id, ⟨0⟩)]
  let localEnvironment : Dynamic.Environment := (shape.copyBinder.id, ⟨2⟩) :: environment
  have params : header.function.parameters = [shape.flag, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.bool flag, .word word]
      environment (inputHeap flag word) := by
    rw [params]
    exact .cons (by rw [shape.flagScheme]; exact .append)
      (.cons (by rw [shape.argumentScheme]; exact .append) (.nil _ _))
  have roots : header.function.body = [shape.branch.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  have read {binder : TypedBinder} {type : TypeSystem.Ty} (value : Dynamic.Value)
      (node : Tests.SourceCoreNamedBranch.Read function.typedBody binder type)
      (context : SourceSemantics.Context) (env : Dynamic.Environment) (heap : Dynamic.Heap)
      (location : Dynamic.Location)
      (lookup : Dynamic.Environment.LooksUp env binder.id location)
      (reads : Dynamic.Heap.Reads heap location ⟨type, some value, none⟩) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        context header.function.evidence function.typedBody env heap node.node.id value heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [node.form]
      exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
    · rw [node.coercions]; exact .nil
  obtain ⟨localContext, extension⟩ := branch_extension header shape sourceEq certified
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap flag word)
      header.function.body header.context (.returned (.word word)) (branchHeap flag word) := by
    rw [roots, sourceEq]
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.branchFound)
      (by rw [shape.branchForm]; intro id impossible; cases impossible)
    cases flag with
    | false =>
      apply Dynamic.StatementExecutes.ifFalseWithElse (outcome := .returned (.word word))
        (lookupStatement?_sound shape.branchFound) shape.branchForm
      · exact read (.bool false) shape.conditionRead header.context environment (inputHeap false word) ⟨0⟩
          (.tail shape.argumentFlag .head) (.intro .head)
      · exact .terminal (.returnValue (lookupStatement?_sound shape.elseReturnFound) shape.elseReturnForm
          (read (.word word) shape.elseRead header.context environment (inputHeap false word) ⟨1⟩ .head (.intro (.tail .head)))) (.returned _)
    | true =>
      apply Dynamic.StatementExecutes.ifTrue (outcome := .returned (.word word))
        (lookupStatement?_sound shape.branchFound) shape.branchForm
      · exact read (.bool true) shape.conditionRead header.context environment (inputHeap true word) ⟨0⟩
          (.tail shape.argumentFlag .head) (.intro .head)
      · apply Dynamic.StatementsExecute.cons
        · exact .letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
            (read (.word word) shape.initialRead header.context environment (inputHeap true word) ⟨1⟩ .head (.intro (.tail .head)))
            (by rw [shape.localScheme]; rfl) extension (by rw [shape.localScheme]; exact .append)
        · exact .terminal (.returnValue (lookupStatement?_sound shape.thenReturnFound) shape.thenReturnForm
            (read (.word word) shape.localRead localContext localEnvironment (thenHeap word) ⟨2⟩ .head (.intro (.tail (.tail .head))))) (.returned _)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


structure TailShape (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.WordRead source binder
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  found : source.lookupStatement? statement.id = some statement
  form : statement.form = .expression read.node.id false

def tailHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩

theorem tail_input_types (shape : TailShape header.function.source) : header.types = [.word] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderScheme,
    TypeSystem.Scheme.mono] using types.symm

/-- A final expression returns its ordinary Source value in true function mode. -/
theorem tail_call (shape : TailShape header.function.source)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [.word word] (.word word) (tailHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (tailHeap word) := by
    rw [params]
    exact .cons (by rw [shape.binderScheme]; exact .append) (.nil _ _)
  have roots : header.function.body = [shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (tailHeap word)
      header.function.body header.context (.returned (.word word)) (tailHeap word) := by
    rw [roots]
    apply Dynamic.FunctionStatementsExecute.tailExpression (lookupStatement?_sound shape.found) shape.form
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.read.found)
    · rw [shape.read.form]
      exact .local (by rw [shape.read.requirements, shape.read.coercions]; rfl) .head (.intro .head) rfl rfl
    · rw [shape.read.coercions]; exact .nil
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

structure UnitShape (source : TypedSource) where
  inputs : source.inputs = []
  roots : source.roots = []

theorem unit_input_types (shape : UnitShape header.function.source) : header.types = [] := by
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_nil] using types.symm

/-- Actual Unit fallthrough is a Source call result without an explicit return. -/
theorem unit_call (shape : UnitShape header.function.source)
    (unitResult : header.function.resultType = .unit)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [] .unit ⟨[]⟩ := by
  have params : header.function.parameters = [] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [] [] ⟨[]⟩ := by
    rw [params]; exact .nil _ _
  have roots : header.function.body = [] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [] ⟨[]⟩
      header.function.body header.context (.fallthrough []) ⟨[]⟩ := by
    rw [roots]; exact .nil
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.unit unitResult body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩


structure LetUnitShape (source : TypedSource) where
  argument : TypedBinder
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.WordRead source argument
  statement : StatementNode
  inputs : source.inputs = [argument]
  argumentScheme : argument.scheme = .mono .word
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  found : source.lookupStatement? statement.id = some statement
  form : statement.form = .letDecl binder (some read.node.id)

def letUnitHeap (word : Word) : Dynamic.Heap :=
  ⟨[{type := .word, value := some (.word word)}, {type := .word, value := some (.word word)}]⟩

theorem let_unit_input_types (shape : LetUnitShape header.function.source) : header.types = [.word] := by
  have params : header.function.parameters = [shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.argumentScheme,
    TypeSystem.Scheme.mono] using types.symm

/-- Unit completion retains the actual initialized local cell and lexical fallthrough. -/
theorem let_unit_call (shape : LetUnitShape header.function.source)
    (unitResult : header.function.resultType = .unit)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [.word word] .unit (letUnitHeap word) := by
  have roots : header.function.body = [shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have localExtension : ∃ localContext, BinderExtends header.function.source.owner header.context shape.binder localContext := by
    obtain ⟨final, facts, typed, completes⟩ := certified.statements
    rw [roots] at typed
    cases typed with
    | singleton head =>
      obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.found)
      rw [shape.form] at formTyped
      cases formTyped with
      | letInitialized value mono extension => exact ⟨_, extension⟩
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly (by rw [shape.binderScheme]; rfl))
  obtain ⟨localContext, extension⟩ := localExtension
  have params : header.function.parameters = [shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.argument.id, ⟨0⟩)] (tailHeap word) := by
    rw [params]
    exact .cons (by rw [shape.argumentScheme]; exact .append) (.nil _ _)
  have value : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.argument.id, ⟨0⟩)]
      (tailHeap word) shape.read.node.id (.word word) (tailHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.read.found)
    · rw [shape.read.form]
      exact .local (by rw [shape.read.requirements, shape.read.coercions]; rfl) .head (.intro .head) rfl rfl
    · rw [shape.read.coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.argument.id, ⟨0⟩)] (tailHeap word)
      header.function.body localContext (.fallthrough [(shape.binder.id, ⟨1⟩), (shape.argument.id, ⟨0⟩)])
      (letUnitHeap word) := by
    rw [roots]
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.found)
      (by rw [shape.form]; intro id impossible; cases impossible)
    exact .letInitialized (lookupStatement?_sound shape.found) shape.form value
      (by rw [shape.binderScheme]; rfl) extension (by rw [shape.binderScheme]; exact .append)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.unit unitResult body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedCompletion
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompletionFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

inductive Example where
  | branch (flag : Bool)
  | tail
  | unit
  | letUnit
  deriving DecidableEq, Repr

def Example.workspace (spec : Example) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    match spec with
    | .branch _ => "function choose(flag: Bool, value: Word) returns (Word) { if (flag) { let copy: Word = value; return copy; } else { return value; } }"
    | .tail => "function identity(value: Word) returns (Word) { value }"
    | .unit => "function empty() {}"
    | .letUnit => "function consume(value: Word) { let copy: Word = value; }"}] }

def Example.Shape (spec : Example) (function : CheckedFunction) (signature : ProgramFunctionSignature) : Type :=
  match spec with
  | .branch _ => Tests.SourceCoreNamedBranch.FactoryShape function signature
  | .tail => TailShape function.typedBody
  | .unit => PLift (UnitShape function.typedBody)
  | .letUnit => LetUnitShape function.typedBody

def Example.resultType : Example → TypeSystem.Ty
  | .branch _ | .tail => .word
  | .unit | .letUnit => .unit

def Example.arguments : Example → List SourceCorePublicValues.Value
  | .branch flag => [.bool flag, .word (Word.ofNatModulo 37)]
  | .tail | .letUnit => [.word (Word.ofNatModulo 37)]
  | .unit => []

def Example.values : Example → List Dynamic.Value
  | .branch flag => [.bool flag, .word (Word.ofNatModulo 37)]
  | .tail | .letUnit => [.word (Word.ofNatModulo 37)]
  | .unit => []

def Example.result : Example → Dynamic.Value
  | .branch _ | .tail => .word (Word.ofNatModulo 37)
  | .unit | .letUnit => .unit

def Example.heap : Example → Dynamic.Heap
  | .branch flag => branchHeap flag (Word.ofNatModulo 37)
  | .tail => tailHeap (Word.ofNatModulo 37)
  | .unit => ⟨[]⟩
  | .letUnit => letUnitHeap (Word.ofNatModulo 37)

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def observeShape (spec : Example) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (spec.Shape function signature) := by
  cases spec with
  | branch flag => exact Tests.SourceCoreNamedBranch.observeShape function signature
  | tail => exact do
    match inputs : function.typedBody.inputs with
    | [binder] =>
      match roots : function.typedBody.roots with
      | [.statement id] =>
        let some statement := function.typedBody.lookupStatement? id
          | throw (IO.userError "completion tail statement")
        match form : statement.form with
        | .expression expression false =>
          let some node := function.typedBody.lookupExpression? expression
            | throw (IO.userError "completion tail read")
          let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder node .word
          let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "completion tail scheme"
          let ⟨found⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "completion tail lookup"
          let ⟨rootEq⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "completion tail root"
          let ⟨formEq⟩ ← observed (statement.form = .expression read.node.id false) "completion tail form"
          return ⟨binder, read, statement, inputs, binderScheme, rootEq, found, formEq⟩
        | _ => throw (IO.userError "completion tail expression form")
      | _ => throw (IO.userError "completion tail roots")
    | _ => throw (IO.userError "completion tail inputs")
  | unit => exact do
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = []) "completion unit inputs"
    let ⟨roots⟩ ← observed (function.typedBody.roots = []) "completion unit roots"
    return ⟨⟨inputs, roots⟩⟩
  | letUnit => exact do
    match inputs : function.typedBody.inputs with
    | [argument] =>
      match roots : function.typedBody.roots with
      | [.statement id] =>
        let some statement := function.typedBody.lookupStatement? id
          | throw (IO.userError "completion Unit local statement")
        match form : statement.form with
        | .letDecl binder (some expression) =>
          let some node := function.typedBody.lookupExpression? expression
            | throw (IO.userError "completion Unit local initializer")
          let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument node .word
          let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "completion Unit argument scheme"
          let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "completion Unit local scheme"
          let ⟨found⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "completion Unit local lookup"
          let ⟨rootEq⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "completion Unit local root"
          let ⟨formEq⟩ ← observed (statement.form = .letDecl binder (some read.node.id)) "completion Unit local form"
          return ⟨argument, binder, read, statement, inputs, argumentScheme, binderScheme, rootEq, found, formEq⟩
        | _ => throw (IO.userError "completion Unit local form")
      | _ => throw (IO.userError "completion Unit local roots")
    | _ => throw (IO.userError "completion Unit local inputs")

structure Fixture (spec : Example) where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram spec.workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  signature : ProgramFunctionSignature
  shape : spec.Shape named.specialized.function signature
  resultType : named.specialized.function.inferredBodyType = spec.resultType
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture (spec : Example) : IO (Fixture spec) := do
  match checked : checkProgram spec.workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "completion artifact absent")
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
            have original : checkProgram spec.workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "completion selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "completion original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let [signature] := recipe.compiled.sourceProgram.signatures.functions
                  | throw (IO.userError "completion original signature")
                let shape ← observeShape spec named.specialized.function signature
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = spec.resultType) "completion function result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "completion substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "completion function marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "completion parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "completion physical slot"
                return {
                  recipe := recipe
                  checked := original
                  seeds := seeds
                  facade := publicCompiled
                  accepted := accepted
                  selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade
                  profile := profile
                  original := originalRow
                  originalMember := by
                    rw [originals]
                    exact List.mem_cons_self
                  named := named
                  functions := functions
                  signature := signature
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "completion cache shape")

theorem Fixture.eligible {spec : Example} (fixture : Fixture spec) :
    Nonempty (SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted
    fixture.selected fixture.originalMember
  have member := List.mem_of_getElem? prepared.selected
  rw [fixture.functions] at member
  have same := List.mem_singleton.mp member
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram fixture.named.specialized := by
    rw [← same, prepared.same]
    exact prepared.origin
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      fixture.named.specialized.parameterSubstitution := by
    rw [fixture.substitution]
    intro parameter replacement impossible
    cases impossible
  exact ⟨⟨fixture.named, 0, fixture.named.signature,
    by rw [fixture.functions]; rfl, fixture.slot, rfl,
    ⟨origin, range, fixture.ordinary, fixture.ordinaryInputs⟩⟩⟩

structure Started {spec : Example} (fixture : Fixture spec) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key spec.arguments runOptions

def observeStarted {spec : Example} (fixture : Fixture spec) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "completion bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key spec.arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedCompletion
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompletionSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue SourceCall)

def Example.types : Example → List TypeSystem.Ty
  | .branch _ => [.bool, .word]
  | .tail | .letUnit => [.word]
  | .unit => []

theorem Fixture.input_types {spec : Example} (fixture : Fixture spec)
    (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (sourceEq : header.function.source = fixture.named.specialized.function.typedBody) :
    header.types = spec.types := by
  cases spec with
  | branch flag => exact branch_input_types header fixture.shape sourceEq
  | tail =>
    have shape : TailShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact tail_input_types header shape
  | unit =>
    have shape : UnitShape header.function.source := by rw [sourceEq]; exact fixture.shape.down
    exact unit_input_types header shape
  | letUnit =>
    have shape : LetUnitShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact let_unit_input_types header shape

theorem Fixture.ordinary_call {spec : Example} (fixture : Fixture spec)
    (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (sourceEq : header.function.source = fixture.named.specialized.function.typedBody)
    (resultEq : header.function.resultType = spec.resultType)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) :
    PlainValue header header invocation ⟨[]⟩ spec.values spec.result spec.heap := by
  cases spec with
  | branch flag => exact branch_call header fixture.shape sourceEq certified sourceAt invocation flag (Word.ofNatModulo 37)
  | tail =>
    have shape : TailShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact tail_call header shape sourceAt invocation (Word.ofNatModulo 37)
  | unit =>
    have shape : UnitShape header.function.source := by rw [sourceEq]; exact fixture.shape.down
    exact unit_call header shape resultEq sourceAt invocation
  | letUnit =>
    have shape : LetUnitShape header.function.source := by rw [sourceEq]; exact fixture.shape
    exact let_unit_call header shape resultEq certified sourceAt invocation (Word.ofNatModulo 37)

/-- Actual checking, compilation and startup are the only preceding receipts.
The ordinary Source execution is constructed before public execution completes. -/
structure InitialMeaning {spec : Example} (fixture : Fixture spec) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = fixture.named.specialized.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ spec.values spec.result spec.heap
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ spec.values (.value spec.result) spec.heap ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint spec.result spec.heap) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation spec.values

theorem from_source {spec : Example} (fixture : Fixture spec) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) (namedEq.trans rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) (namedEq.trans rowSame)).trans fixture.resultType)
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified
    (SelectedCompilationCheckedBodyTyping.of_checked fixture.checked fixture.profile) initial.header
  have plain := fun invocation => fixture.ordinary_call initial.header sourceEq resultEq certified sourceAt invocation
  have simple : ∀ value ∈ spec.arguments, SourceCoreIndexedSession.SimplePublic value := by
    cases spec with
    | branch flag =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact .bool flag
      · cases List.mem_singleton.mp member; exact .word (Word.ofNatModulo 37)
    | tail | letUnit =>
      intro value member
      cases List.mem_singleton.mp member; exact .word (Word.ofNatModulo 37)
    | unit => intro value member; cases member
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context spec.arguments initial.header.types := by
    rw [fixture.input_types initial.header sourceEq]
    cases spec with
    | branch flag =>
      exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        (.cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil)
    | tail | letUnit => exact .cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil
    | unit => exact .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings spec.arguments spec.values := by
    cases spec with
    | branch flag =>
      exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        (.cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil)
    | tail | letUnit => exact .cons ⟨.word (Word.ofNatModulo 37), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word (Word.ofNatModulo 37)⟩ .nil
    | unit => exact .nil
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedCompletion
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompletionProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"completion checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"completion compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "completion cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "completion selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "completion actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"completion recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "completion root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "completion public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "completion bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "completion startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "completion zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "completion success missing")
  require (completed.value == value) "completion result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "completion fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "completion absent read did not fail")
  let some diagnostic ← get "completion diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "completion diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "completion failure reason changed"
  pure after

def casesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function letUnit() { let value: Word = 37; }",
    "function missing() returns (Word) { let value: Word; value }",
    "function reuse(value: Word) returns (Word) { value }",
    "function discarded(value: Word) returns (Word) { { value; } return 41; }",
    "function conditionFault(flag: Bool) returns (Word) { if (flag) { let value: Word; return value; } else { return 7; } }",
    "function matchReturn(value: Word) returns (Word) { match (value) { case 0 { return 41; } default { return 7; } } }",
    "function blockReturn(value: Word) returns (Word) { { let copy: Word = value; return copy; } }"
  ]}]
}

def factoryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(value: Word) returns (function(Word) returns ()) { return lam(next: Word) -> Unit { value = next; }; }"}]
}

private def expected : Example → SourceCorePublicValues.Value
  | .branch _ | .tail => word 37
  | .unit | .letUnit => .unit

private def nativeHeaps : Example → List Nat
  | .branch true => [2, 11]
  | .branch false => [2, 8]
  | .tail => [2, 5]
  | .unit => [2, 2]
  | .letUnit => [2, 8]

private def sourceFirst (spec : Example) : IO Unit := do
  let fixture ← fixture spec
  require (fixture.recipe.compiled.indexed.base.functions.length == 1 && fixture.profile.table.rows.length == 1)
    "completion independent cache/table changed"
  require (AcceptedCompilerBodyProfile.validate fixture.named.specialized.function.typedBody
    (fun _ => True)).isSome "completion actual body profile rejected"
  match spec with
  | .unit => pure ()
  | _ => require (AcceptedCompilerBodyProfile.validate fixture.named.specialized.function.typedBody
      (fun _ => False)).isNone "completion missing expression coverage accepted"
  let source := fixture.named.specialized.function.typedBody
  let statements := source.roots.filterMap fun | .statement id => some id | _ => none
  require (AcceptedCompilerBodyCompletion.finish? source spec.resultType true statements).isSome
    "completion actual raw result refused"
  match spec with
  | .tail =>
    require (AcceptedCompilerBodyCompletion.finish? source .bool true statements).isNone
      "completion wrong raw tail result accepted"
    require (AcceptedCompilerBodyCompletion.finish? source .word true (statements ++ statements)).isNone
      "completion nonfinal bare expression accepted"
  | .unit | .letUnit =>
    require (AcceptedCompilerBodyCompletion.finish? source .word true statements).isNone
      "completion non-Unit fallthrough accepted"
  | .branch _ => pure ()
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "completion initial zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "completion independent Source execution failed")
  require (completed.value == expected spec) "completion independent result changed"
  require ([started.session.heapSize, completed.session.heapSize] == nativeHeaps spec)
    "completion independent native stores changed"
  IO.println s!"COMPLETION_SOURCE_HEAPS: {reprStr spec}; {[started.session.heapSize, completed.session.heapSize]}"

/-- The profile expansion does not change the parser's nested-block policy. -/
private def parserBoundaries : IO Unit := do
  for content in [
      "function bad(value: Word) returns (Word) { { value } return 41; }",
      "function bad() returns (function(Word) returns (Word)) { return lam(value: Word) -> Word { value }; }"] do
    let workspace : Workspace.RawWorkspace := {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content}]}
    match checkProgram workspace options.checkingFuel with
    | .error errors =>
      require (errors.any fun
        | .loading (.sourceDiagnostics _ _ diagnostics) => diagnostics.any fun diagnostic =>
            match diagnostic.kind with
            | .constraintViolation .expressionRequiresSemicolon => true
            | _ => false
        | _ => false) "completion nested semicolon diagnostic changed"
    | .ok _ => throw (IO.userError "completion nested semicolon policy changed")

/-- A stopped structured head still emits its outer suffix; direct return does not. -/
private def completionSuffixGuards : IO Unit := do
  for (content, stopped) in [
      ("function suffix(flag: Bool, value: Word) returns (Word) { if (flag) { return value; } else { return value; } value }", true),
      ("function suffix(value: Word) returns (Word) { return value; value }", false)] do
    let workspace : Workspace.RawWorkspace := {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content}]}
    let .ok checked := checkProgram workspace options.checkingFuel
      | throw (IO.userError "completion suffix guard checking failed")
    let [function] := checked.functions
      | throw (IO.userError "completion suffix guard function changed")
    let source := function.typedBody
    let [head, tail] := source.roots.filterMap fun | .statement id => some id | _ => none
      | throw (IO.userError "completion suffix guard original roots changed")
    require (AcceptedCompilerBodyCompletion.finish? source .word true [head, tail]).isSome
      "completion original stopped suffix refused"
    let duplicated := (AcceptedCompilerBodyCompletion.finish? source .word true [head, tail, tail]).isSome
    require (duplicated == !stopped)
      "completion emitted versus omitted bare suffix boundary changed"

def run : IO Unit := do
  completionSuffixGuards
  parserBoundaries
  sourceFirst (.branch true)
  sourceFirst (.branch false)
  sourceFirst .tail
  sourceFirst .unit
  sourceFirst .letUnit
  runProgram casesWorkspace ["letUnit", "missing", "reuse", "discarded", "conditionFault", "matchReturn", "blockReturn"] 7 fun _ initial keys => do
    let [letUnit, missing, reuse, discarded, conditionFault, matchReturn, blockReturn] := keys
      | throw (IO.userError "completion corpus keys changed")
    let unitResult ← success initial letUnit [] .unit
    let missingResult ← failure unitResult missing []
    let reused ← success missingResult reuse [word 19] (word 19)
    let discardedResult ← success reused discarded [word 37] (word 41)
    let branchMissing ← failure discardedResult conditionFault [.bool true]
    let branchReused ← success branchMissing conditionFault [.bool false] (word 7)
    let matched ← success branchReused matchReturn [word 0] (word 41)
    let defaulted ← success matched matchReturn [word 1] (word 7)
    let blocked ← success defaulted blockReturn [word 37] (word 37)
    require ([initial.heapSize, unitResult.heapSize, missingResult.heapSize, reused.heapSize,
      discardedResult.heapSize, branchMissing.heapSize, branchReused.heapSize, matched.heapSize,
      defaulted.heapSize, blocked.heapSize] == [8, 11, 14, 17, 20, 26, 29, 35, 41, 47])
      "completion control and fault-continuation stores changed"
    IO.println s!"COMPLETION_CASE_HEAPS: {[initial.heapSize, unitResult.heapSize, missingResult.heapSize, reused.heapSize, discardedResult.heapSize, branchMissing.heapSize, branchReused.heapSize, matched.heapSize, defaulted.heapSize, blocked.heapSize]}"
  runProgram factoryWorkspace ["make"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "completion factory key")
    let checkpoint ← get "completion factory startup" (initial.start key [word 11])
    let .succeeded made ← checkpoint.resume 100000 1000
      | throw (IO.userError "completion factory failed")
    let .function handle := made.value | throw (IO.userError "completion factory handle missing")
    let firstCheckpoint ← get "completion captured startup" (made.session.startHandlePacked handle (word 12))
    let .succeeded first ← firstCheckpoint.resume 100000 1000
      | throw (IO.userError "completion captured invocation failed")
    require (first.value == .unit) "completion captured Unit result changed"
    let nextCheckpoint ← get "completion captured reuse" (first.session.startHandlePacked handle (word 23))
    let .succeeded next ← nextCheckpoint.resume 100000 1000
      | throw (IO.userError "completion captured reuse failed")
    require (next.value == .unit) "completion captured reuse result changed"
    require ([initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize] == [2, 8, 14, 20])
      "completion captured Unit fallthrough stores changed"
    IO.println s!"COMPLETION_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize]}"
  IO.println "COMPLETION_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedCompletion
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompositeProfile
/-! Unchanged source programs exercise the new composite profile through the
actual checker, compiler cache, automatic issuer, and public session runtime. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompositeProfile
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def entryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function keep<T>(input: T) returns (T) { let stored: T = input; return stored; }",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function staged(comptime input: (Word, Bool)) returns (Word, Bool) {",
    "  let stored: (Word, Bool) = input; return stored;",
    "}",
    "function nested(input: (Word, (Bool, Word))) returns (Word, (Bool, Word)) { return input; }",
    "function blocked(input: Word) returns (Word) { { return input; } }",
    "function scoped(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; { let value: Word = replacement; value = initial; }",
    "  if (flag) { value = replacement; } return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function loop(flag: Bool) { while (flag) { break; } }",
    "function stagedResult(comptime input: Word) returns (comptime<Word>) { return input; }",
    "function literalEvidence() returns (Word) { return 1; }"
  ] }]
  externalLibraries := []
}

def basicWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function sequence(flag: Bool, initial: Word, replacement: Word) returns (Word, Bool) {",
    "  let value: Word; value = initial; let copied: Word = value;",
    "  value = replacement; copied; return (copied, flag);",
    "}",
    "function early(initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; return value; value = replacement;",
    "}",
    "function initializerFailure(input: Word) returns (Word) {",
    "  let absent: Word; let never: Word = absent; let later: Word = input; return later;",
    "}",
    "function assignmentFailure(input: Word, replacement: Word) returns (Word) {",
    "  let target: Word = input; let absent: Word; target = absent;",
    "  target = replacement; return target;",
    "}",
    "function discardFailure(input: Word) returns (Word) {",
    "  let absent: Word; absent; let later: Word = input; return later;",
    "}",
    "function pairFailure(flag: Bool) returns (Word, Bool) {",
    "  let absent: Word; return (absent, flag);",
    "}",
    "function tail(value: Word) returns (Word) { value }",
    "function empty() { return; }",
    "function fallthrough() { true; }",
    "function unit() { return (); }",
    "function bool() returns (Bool) { return (true); }",
    "function literalEvidence() returns (Word) { return 1; }",
    "function blocked(value: Word) returns (Word) { { return value; } }"
  ] }]
  externalLibraries := []
}

def tupleContent : String := String.intercalate "\n" [
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function triple() returns ((Word, Bool, Word)) { return (side(7), true, 3 + 4); }",
  "function quadruple() returns ((Word, Bool, Word, Bool)) { return (side(11), false, side(13), true); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((side(17), true, 5 + 6), side(19), false); }",
  "function firstFault() returns ((Word, Word, Word)) { return (fail(), side(91), side(92)); }",
  "function laterFault() returns ((Word, Word, Word, Word)) { return (side(23), side(29), fail(), side(99)); }",
  "function singleton() returns (Word) { return (side(31)); }"
]

def tupleWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := tupleContent}]
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512
}
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"composite checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"composite compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "composite cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "composite selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "composite actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"composite recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "composite root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "composite public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "composite bootstrap missing")
            IO.println s!"COMPOSITE_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "composite startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "composite zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "composite success missing")
  require (completed.value == value) "composite result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "composite fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "composite absent read did not fail")
  let some diagnostic ← get "composite diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "composite diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "composite failure reason changed"
  pure after

theorem general_forms (first second third : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm false false false (.group first) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.tuple [first]) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.tuple [first, second, first]) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.conditional first second third) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem narrow_forms (first second third : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm true false false (.group first) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.tuple [first, second]) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.conditional first second third) = false := by
  exact ⟨rfl, rfl, rfl⟩

def run : IO Unit := do
  runProgram entryWorkspace ["mutate", "chooseFailure", "branchFailure"] 3 fun _ initial keys => do
    let [mutate, choose, branch] := keys | throw (IO.userError "composite entry keys changed")
    let first ← success initial mutate [.bool true, word 11, word 29] (.product (word 29) (.bool true))
    let selected ← success first choose [.bool true, word 37] (word 37)
    let failed ← failure selected choose [.bool false, word 41]
    let continued ← success failed mutate [.bool false, word 2, word 7] (.product (word 7) (.bool false))
    let left ← failure continued branch [.bool true]
    let right ← failure left branch [.bool false]
    require ([initial.heapSize, first.heapSize, selected.heapSize, failed.heapSize, continued.heapSize, left.heapSize, right.heapSize] == [4, 16, 25, 34, 46, 52, 58])
      "composite branch/write prefix heaps changed"
    IO.println s!"COMPOSITE_ENTRY_HEAPS: {[initial.heapSize, first.heapSize, selected.heapSize, failed.heapSize, continued.heapSize, left.heapSize, right.heapSize]}"
  runProgram basicWorkspace ["bool"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "composite group key changed")
    let after ← success initial key [] (.bool true)
    require (after.heapSize == initial.heapSize) "composite group allocated unexpectedly"
  runProgram tupleWorkspace ["quadruple", "firstFault", "laterFault", "singleton"] 6 fun _ initial keys => do
    let [quad, firstFault, laterFault, single] := keys | throw (IO.userError "composite tuple keys changed")
    let first ← success initial quad [] (.product (word 11) (.product (.bool false) (.product (word 13) (.bool true))))
    let early ← failure first firstFault []
    let late ← failure early laterFault []
    let after ← success late single [] (word 31)
    require ([initial.heapSize, first.heapSize, early.heapSize, late.heapSize, after.heapSize] == [7, 13, 19, 31, 34])
      "composite tuple ordering/fault prefix heaps changed"
    IO.println s!"COMPOSITE_TUPLE_HEAPS: {[initial.heapSize, first.heapSize, early.heapSize, late.heapSize, after.heapSize]}"
  IO.println "COMPOSITE_COMPILER_PROFILE_PASS: actual checker/profile/automatic issuer; unchanged source programs; ordered products, conditional branch fault, group, tuple fault prefixes, zero-fuel resume, same-session continuation"

end Tests.SourceCoreSelectedCompositeProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedBodyControlRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"body control checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"body control compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "body control cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "body control selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "body control actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"body control recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "body control root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "body control public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "body control bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "body control startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "body control zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "body control success missing")
  require (completed.value == value) "body control result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "body control fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "body control absent read did not fail")
  let some diagnostic ← get "body control diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "body control diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "body control failure reason changed"
  pure after

private def controlWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function blockReturn(first: Word, second: Word) returns (Word) {",
    "  { return first; } let later: Word = second; return later;",
    "}",
    "function branch(flag: Bool, first: Word, second: Word) returns (Word) {",
    "  let result: Word = first; if (flag) { return first; } else { result = second; } return result;",
    "}",
    "function branchFault(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; if (flag) { absent; } else { value; } let later: Word = value; return later;",
    "}"
  ]}] }

private def checkConditionalBoundary : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
      "function both(flag: Bool, first: Word, second: Word) returns (Word) { if (flag) { return first; } else { return second; } return first; }"}] }
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"body control boundary checking: {reprStr errors}")
  | .ok program =>
    let keys ← ["both"].mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (keys.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"body control boundary compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "body control boundary artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        require (cached.indexed.base.functions.any (fun named =>
          named.specialized.function.typedBody.nodes.any (fun node => match node with
            | .statement statement => match statement.form with
              | .ifThen _ _ _ => decide (statement.type ≠ .unit)
              | _ => false
            | _ => false))) "body control boundary lost its original non-unit annotation"
        match SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original with
        | none => throw (IO.userError "non-unit conditional profile rejected")
        | some _ => pure ()

def run : IO Unit := do
  checkConditionalBoundary
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "body control initial discard did not suspend")
  let .succeeded discarded ← suspended.resume 100000 1000
    | throw (IO.userError "body control initial discard did not complete")
  require (discarded.value == .word seed) "body control independent Source result changed"
  require ([started.session.heapSize, discarded.session.heapSize] == [2, 5])
    "body control independent Source heap changed"
  runProgram SourceCoreSelectedCompositeProfile.entryWorkspace ["scoped"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "body control scoped key changed")
    let selected ← success initial key [.bool true, word 11, word 29] (word 29)
    let unselected ← success selected key [.bool false, word 37, word 41] (word 37)
    require ([initial.heapSize, selected.heapSize, unselected.heapSize] == [2, 17, 32])
      "body control lexical scope restoration changed"
    IO.println s!"BODY_SCOPE_HEAPS: {[initial.heapSize, selected.heapSize, unselected.heapSize]}"
  runProgram SourceCoreSelectedCompositeProfile.basicWorkspace ["discardFailure", "sequence"] 2 fun _ initial keys => do
    let [discard, sequence] := keys | throw (IO.userError "body control sequence keys changed")
    let failed ← failure initial discard [word 11]
    let continued ← success failed sequence [.bool true, word 37, word 41] (.product (word 37) (.bool true))
    require ([initial.heapSize, failed.heapSize, continued.heapSize] == [3, 9, 24])
      "body control discard fault prefix or continuation changed"
    IO.println s!"BODY_DISCARD_HEAPS: {[initial.heapSize, failed.heapSize, continued.heapSize]}"
  runProgram controlWorkspace ["blockReturn", "branch", "branchFault"] 3 fun _ initial keys => do
    let [block, branch, fault] := keys | throw (IO.userError "body control branch keys changed")
    let escaped ← success initial block [word 5, word 7] (word 5)
    let early ← success escaped branch [.bool true, word 11, word 13] (word 11)
    let later ← success early branch [.bool false, word 17, word 19] (word 19)
    let failed ← failure later fault [.bool true, word 23]
    let continued ← success failed fault [.bool false, word 29] (word 29)
    require ([initial.heapSize, escaped.heapSize, early.heapSize, later.heapSize, failed.heapSize, continued.heapSize]
      == [4, 10, 22, 34, 43, 55]) "body control return or branch fault prefix changed"
    IO.println s!"BODY_BRANCH_HEAPS: {[initial.heapSize, escaped.heapSize, early.heapSize, later.heapSize, failed.heapSize, continued.heapSize]}"
  IO.println "SOURCE_FIRST_BODY_CONTROL_PASS: actual checker/compiler/profile/automatic issuer; independent discard Source trace before public execution; closed initial whole-output theorem; block return and lexical restoration; both conditional branches; discarded-read fault prefixes and same-session continuation; zero-fuel resume"

end Tests.SourceCoreSelectedBodyControl
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompoundSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompoundFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function add(left: Word, right: Word) returns (Word) { left += right; return left; } function divide(left: Word, right: Word) returns (Word) { left /= right; return left; } function missing(right: Word) returns (Word) { let value: Word; value /= right; return value; }"}] }
def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  nativeResult : global.resultType = .word
  resultType : original.function.inferredBodyType = .word
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "compound artifact absent")
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

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "compound original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "compound original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "compound global key"
      let ⟨nativeResult⟩ ← observed (global.resultType = .word) "compound native result"
      let ⟨resultType⟩ ← observed (original.function.inferredBodyType = .word) "compound raw result"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "compound substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "compound ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "compound ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        nativeResult := nativeResult
        resultType := resultType
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "compound unique physical slot")

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
  let .statement sid := id | throw (IO.userError "compound statement root")
  let some node := source.lookupStatement? sid | throw (IO.userError "compound statement lookup")
  return node

private def wordRead (source : TypedSource) (binder : TypedBinder) (id : ExpressionId) :
    IO (Tests.SourceCoreNamedBranch.WordRead source binder) := do
  let some node := source.lookupExpression? id | throw (IO.userError "compound read lookup")
  Tests.SourceCoreNamedBranch.observeRead source binder node .word

def observeCompound (source : TypedSource) (operation : Operation) : IO (CompoundShape source operation) := do
  let [left, right] := source.inputs | throw (IO.userError "compound parameter count")
  let [first, second] := source.roots | throw (IO.userError "compound statement count")
  let assignment ← statement source first
  let returned ← statement source second
  let .assignValue resolution _ rhsId := assignment.form | throw (IO.userError "compound assignment form")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "compound return form")
  let rhs ← wordRead source right rhsId
  let result ← wordRead source left resultId
  let ⟨inputs⟩ ← observed (source.inputs = [left, right]) "compound original inputs"
  let ⟨leftScheme⟩ ← observed (left.scheme = .mono .word) "compound left scheme"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "compound right scheme"
  let ⟨distinct⟩ ← observed (right.id ≠ left.id) "compound binder identity"
  let ⟨roots⟩ ← observed (source.roots = [.statement assignment.id, .statement returned.id]) "compound original roots"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "compound assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution operation.operator rhs.node.id) "compound original operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = left.id) "compound target identity"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "compound bare target"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "compound return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "compound return read"
  return ⟨left, right, resolution, assignment, returned, rhs, result, inputs, leftScheme, rightScheme,
    distinct, roots, assignmentFound, assignmentForm, targetRoot, targetBare, returnedFound, returnedForm⟩

def observeMissing (source : TypedSource) : IO (MissingShape source) := do
  let [right] := source.inputs | throw (IO.userError "missing parameter count")
  let [first, second, third] := source.roots | throw (IO.userError "missing statement count")
  let declared ← statement source first
  let assignment ← statement source second
  let returned ← statement source third
  let .letDecl binder none := declared.form | throw (IO.userError "missing local declaration")
  let .assignValue resolution .divide rhsId := assignment.form | throw (IO.userError "missing division assignment")
  let rhs ← wordRead source right rhsId
  let ⟨inputs⟩ ← observed (source.inputs = [right]) "missing inputs"
  let ⟨rightScheme⟩ ← observed (right.scheme = .mono .word) "missing input scheme"
  let ⟨localScheme⟩ ← observed (binder.scheme = .mono .word) "missing local scheme"
  let ⟨distinct⟩ ← observed (binder.id ≠ right.id) "missing distinct binders"
  let ⟨roots⟩ ← observed (source.roots = [.statement declared.id, .statement assignment.id, .statement returned.id]) "missing roots"
  let ⟨declaredFound⟩ ← observed (source.lookupStatement? declared.id = some declared) "missing declaration identity"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl binder none) "missing absent declaration"
  let ⟨assignmentFound⟩ ← observed (source.lookupStatement? assignment.id = some assignment) "missing assignment identity"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .divide rhs.node.id) "missing operator identity"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "missing target root"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "missing target projections"
  return ⟨right, binder, resolution, declared, assignment, returned, rhs, inputs, rightScheme, localScheme,
    distinct, roots, declaredFound, declaredForm, assignmentFound, assignmentForm, targetRoot, targetBare⟩

structure ObservedProgram (fixture : CompiledFixture) where
  addRow : Row fixture
  divideRow : Row fixture
  missingRow : Row fixture
  addShape : CompoundShape addRow.original.function.typedBody .add
  divideShape : CompoundShape divideRow.original.function.typedBody .divide
  missingShape : MissingShape missingRow.original.function.typedBody
  cacheSize : fixture.recipe.compiled.indexed.base.functions.length = 3

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let addRow ← observeRow fixture "add"
  let divideRow ← observeRow fixture "divide"
  let missingRow ← observeRow fixture "missing"
  let addShape ← observeCompound addRow.original.function.typedBody .add
  let divideShape ← observeCompound divideRow.original.function.typedBody .divide
  let missingShape ← observeMissing missingRow.original.function.typedBody
  let ⟨cacheSize⟩ ← observed (fixture.recipe.compiled.indexed.base.functions.length = 3) "compound cache size"
  return ⟨addRow, divideRow, missingRow, addShape, divideShape, missingShape, cacheSize⟩

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
  | .outOfFuel _ => throw (IO.userError "compound bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedCompound
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompoundSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall StartedCall)

private theorem body_types {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
  simpa only [header.parameters, List.map_map, Function.comp_def] using Dynamic.MonoBindersExtend.bodyTypes_eq header.extended

private theorem word_types (context : SourceSemantics.Context) (left right : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context
      [.word left, .word right] [.word, .word] :=
  .cons ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ (.cons ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ .nil)

private theorem word_meanings (left right : Word) :
    RecursiveNamedPublicDataInputs.Meanings [.word left, .word right] [.word left, .word right] :=
  .cons ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ (.cons ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ .nil)

private theorem word_inputs (entries : List RecursiveNamedPublicFunctionHistory.Entry)
    (context : SourceSemantics.Context) (left right : Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context
      [.word, .word] [.word left, .word right] [.word left, .word right] :=
  .cons (.data ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩ ⟨.word left, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word left⟩)
    (.cons (.data ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩) .nil)

structure InitialMeaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (started : Started fixture observed.addRow.original.key [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = observed.addRow.original.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
    [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.word (Word.ofNatModulo 42))
    (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42))
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩
        [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.value (.word (Word.ofNatModulo 42)))
        (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word (Word.ofNatModulo 42))
        started.call (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]

/-- Source execution is derived from the observed original body before the
initial public checkpoint completes. The compiler profile remains explicit. -/
theorem initial_from_source (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (started : Started fixture observed.addRow.original.key [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)]) :
    Nonempty (InitialMeaning fixture observed started) := by
  obtain ⟨row, rowSame, signatureSame⟩ := observed.addRow.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := initial.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans observed.addRow.resultType))
  have nativeEq : initial.header.output = .word := initial.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans observed.addRow.nativeResult))
  have shape : CompoundShape initial.header.function.source .add := by rw [sourceEq]; exact observed.addShape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] (.word (Word.ofNatModulo 42))
      (resultHeap ⟨[]⟩ (Word.ofNatModulo 5) (Word.ofNatModulo 42)) := by
    intro invocation
    exact compound_call initial.header shape sourceAt initial.header invocation ⟨[]⟩ (Word.ofNatModulo 37) (Word.ofNatModulo 5)
  have simple : ∀ value ∈ [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)],
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word (Word.ofNatModulo 37), .word (Word.ofNatModulo 5)] initial.header.types := by
    rw [compound_input_types initial.header shape]
    exact word_types _ _ _
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple types
      (word_meanings _ _) (.word (Word.ofNatModulo 42)) resultEq nativeEq (plain invocation)⟩⟩

variable {fixture : CompiledFixture} (issued : Profiled fixture.recipe)
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.toIssued.State anchor session entries)

structure LaterMeaning (row : Row fixture) (operation : Operation) (left right : Word)
    (call : StartedCall session row.original.key [.word left, .word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word left, .word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainValue anchor request.header invocation state.heap [.word left, .word right]
    (.word (operation.apply left right)) (resultHeap state.heap right (operation.apply left right))
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word left, .word right]
        (.value (.word (operation.apply left right))) (resultHeap state.heap right (operation.apply left right)) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.word (operation.apply left right))
        call (resultHeap state.heap right (operation.apply left right))) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word left, .word right]

/-- Subsequent arithmetic uses the same issued catalog and exact returned
Source heap; the ordinary trace is independent of public completion. -/
theorem later_from_source (row : Row fixture) {operation : Operation}
    (shape : CompoundShape row.original.function.typedBody operation) (left right : Word)
    (call : StartedCall session row.original.key [.word left, .word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (LaterMeaning issued state row operation left right call) := by
  obtain ⟨eligible, rowSame, signatureSame⟩ := row.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row state call eligible
  have sourceEq := request.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  have resultEq := request.header.agreement.result.trans
    ((congrArg (fun named => named.specialized.function.inferredBodyType) namedEq).trans
      ((congrArg (fun original => original.function.inferredBodyType) rowSame).trans row.resultType))
  have nativeEq : request.header.output = .word := request.header.resultType.symm.trans
    ((congrArg (fun named => named.signature.resultType) namedEq).trans
      ((congrArg (·.resultType) signatureSame).trans row.nativeResult))
  have actualShape : CompoundShape request.header.function.source operation := by rw [sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      request.header request.selected.member
  have plain := fun invocation => compound_call request.header actualShape sourceAt anchor invocation state.heap left right
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word left, .word right] [.word left, .word right] := by
    rw [body_types, compound_input_types request.header actualShape]
    exact word_inputs _ _ _ _
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.scalar issued state call request inputs ready
      (.word (operation.apply left right)) resultEq nativeEq (plain invocation)⟩⟩

structure MissingMeaning (row : Row fixture) (right : Word)
    (call : StartedCall session row.original.key [.word right] runOptions) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session row.original.key [.word right]
    runOptions.inputValidationFuel state.world state.store
  sourceEq : request.header.function.source = row.original.function.typedBody
  plain : ∀ invocation, PlainFault anchor request.header invocation state.heap [.word right]
    (.invalidAssignmentOperands .divide) (missingHeap state.heap right)
  forward : ∀ invocation,
    (SourceCall anchor request.header invocation state.heap [.word right]
        (.fault (.semantic (.invalidAssignmentOperands .divide))) (missingHeap state.heap right) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries) issued.catalog.rows
        anchor issued.initial issued.support.profile fixture.recipe (.semantic (.invalidAssignmentOperands .divide))
        call (missingHeap state.heap right)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation [.word right]

/-- The absent target faults after evaluating the RHS. This is the same
original body and current heap used by the public failure continuation. -/
theorem missing_from_source (row : Row fixture) (shape : MissingShape row.original.function.typedBody)
    (right : Word) (call : StartedCall session row.original.key [.word right] runOptions)
    (ready : session.ExportsReady) : Nonempty (MissingMeaning issued state row right call) := by
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
  have plain := fun invocation => missing_call request.header actualShape certified sourceAt anchor invocation state.heap right
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word right] [.word right] := by
    rw [body_types, missing_input_types request.header actualShape]
    exact .cons (.data ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩ ⟨.word right, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word right⟩) .nil
  exact ⟨⟨request, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedPublicForward.fault issued state call request inputs ready
      (.invalidAssignmentOperands .divide) (plain invocation)⟩⟩

/-- Every sufficiently fueled genuine operand failure returns a state for
this same issued catalog, and an independent addition trace starts from that
exact reached heap. No completed call is an input to this continuation. -/
theorem missing_then_reuse (missingRow addRow : Row fixture)
    (missingShape : MissingShape missingRow.original.function.typedBody)
    (addShape : CompoundShape addRow.original.function.typedBody .add)
    (right : Word) (call : StartedCall session missingRow.original.key [.word right] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    (∃ requiredExecution token,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ next : issued.toIssued.State anchor returned entries,
            next.heap = missingHeap state.heap right ∧
            CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics
              (.semantic (.invalidAssignmentOperands .divide)) token ∧
            ∀ nextCall : StartedCall returned addRow.original.key
                [.word (Word.ofNatModulo 20), .word (Word.ofNatModulo 22)] runOptions,
              Nonempty (LaterMeaning issued next addRow .add (Word.ofNatModulo 20)
                (Word.ofNatModulo 22) nextCall)) ∨
      ∃ meaning : MissingMeaning issued state missingRow right call,
        SelectedCompilationStagePublicForward.StageStopped issued state call meaning.request.header
          invocation [.word right] := by
  obtain ⟨meaning⟩ := missing_from_source issued state missingRow missingShape right call ready
  rcases meaning.forward invocation with semantic | stopped
  · obtain ⟨requiredExecution, token, forward⟩ := semantic.2
    refine .inl ⟨requiredExecution, token, ?_⟩
    intro executionFuel outputFuel outcome enough resumed
    obtain ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded⟩ :=
      forward executionFuel outputFuel outcome enough resumed
    refine ⟨returned, outcomeEq, returnedReady, next, heapEq, decoded, ?_⟩
    intro nextCall
    exact later_from_source issued next addRow addShape (Word.ofNatModulo 20)
      (Word.ofNatModulo 22) nextCall returnedReady
  · exact .inr ⟨meaning, stopped⟩

end Tests.SourceCoreSelectedCompound
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCompoundProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"compound checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"compound compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "compound cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "compound selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "compound actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"compound recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "compound root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "compound public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "compound bootstrap missing")
            IO.println s!"COMPOUND_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots


private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "compound zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "compound success missing")
  require (completed.value == value) "compound result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (operator : Syntax.ValueAssignOp) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "compound absent target did not fail")
  let some diagnostic ← get "compound diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "compound diagnostic missing")
  require (match diagnostic.error with
    | .invalidAssignmentOperands actual none (some .word) => actual == operator
    | _ => false) "compound operand diagnostic changed"
  pure after

private def sourceFirst : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "compound original selected profile rejected")
  require (fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.table.rows.length == 3)
    "compound original cache/table changed"
  let started ← observeStarted fixture observed.addRow.original.key [word 37, word 5]
  have _sourceFirst := initial_from_source fixture observed profile started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "compound initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "compound initial addition failed")
  require (first.value == word 42) "compound initial sum changed"
  let second ← success first.session observed.divideRow.original.key [word 42, word 0] (word 0)
  let third ← failure second observed.missingRow.original.key [word 0] .divide
  let fourth ← success third observed.addRow.original.key [word 20, word 22] (word 42)
  require ([started.session.heapSize, first.session.heapSize, second.heapSize, third.heapSize, fourth.heapSize]
    == [4, 10, 16, 22, 28]) "compound native stores changed"
  IO.println s!"COMPOUND_SOURCE_HEAPS: {[started.session.heapSize, first.session.heapSize, second.heapSize, third.heapSize, fourth.heapSize]}"

def headerWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function post(limit: Word) returns (Word) { let count: Word = 0; for (let i: Word = 0; limit > i; i += 1) { count += 1; continue; } return count; }",
    "function stop() returns (Word) { let missing: Word; for (let i: Word = 0; true; missing += 1) { break; } return 7; }",
    "function failedPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; missing += 1) { continue; } return 7; }",
    "function initialize(value: Word) returns (Word) { for (value += 1; false; value += 1) { } return value; }"
  ]}] }

/-- The runtime companion's retained closure starts every call from the value
it captured at creation: neither a successful call nor the indirect RHS call
before an operand fault carries its captured assignment over to a later call. -/
def captureWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(next: Word) -> Word { value += next; return value; }; }",
    "function missingRhs(action: function(Word) returns (Word)) returns (Word) { let missing: Word; missing += action(9); return missing; }"
  ]}] }

private def handleSuccess {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument expected : SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound captured startup" (session.startHandlePacked handle argument)
  let .succeeded completed ← started.resume 100000 1000
    | throw (IO.userError "compound captured invocation failed")
  require (completed.value == expected) "compound captured result changed"
  pure completed.session

def run : IO Unit := do
  sourceFirst
  runProgram headerWorkspace ["post", "stop", "failedPost", "initialize"] 4 fun _ initial keys => do
    let [post, stop, failedPost, initializer] := keys
      | throw (IO.userError "compound header keys changed")
    let first ← success initial post [word 3] (word 3)
    let second ← success first stop [] (word 7)
    let third ← failure second failedPost [] .add
    let fourth ← success third post [word 2] (word 2)
    let fifth ← success fourth initializer [word 41] (word 42)
    require ([initial.heapSize, first.heapSize, second.heapSize, third.heapSize, fourth.heapSize, fifth.heapSize]
      == [5, 15, 22, 29, 39, 43]) "compound header native stores changed"
    IO.println s!"COMPOUND_HEADER_HEAPS: {[initial.heapSize, first.heapSize, second.heapSize, third.heapSize, fourth.heapSize, fifth.heapSize]}"
  runProgram captureWorkspace ["make", "missingRhs"] 2 fun _ initial keys => do
    let [make, missingRhs] := keys | throw (IO.userError "compound capture keys changed")
    let pending ← get "compound factory startup" (initial.start make [word 10])
    let .succeeded made ← pending.resume 100000 1000
      | throw (IO.userError "compound factory failed")
    let .function handle := made.value | throw (IO.userError "compound captured handle missing")
    let first ← handleSuccess made.session handle (word 7) (word 17)
    let second ← handleSuccess first handle (word 20) (word 30)
    let failed ← failure second missingRhs [.function handle] .add
    let reused ← handleSuccess failed handle (word 0) (word 10)
    require ([initial.heapSize, made.session.heapSize, first.heapSize, second.heapSize, failed.heapSize, reused.heapSize]
      == [3, 9, 15, 21, 33, 39]) "compound captured RHS native stores changed"
    IO.println s!"COMPOUND_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.heapSize, second.heapSize, failed.heapSize, reused.heapSize]}"
  IO.println "COMPOUND_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedCompound
end
