import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
import Solcore.Test.SourceCoreNamedMatchSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

def inputHeap (previous next : Word) : Dynamic.Heap :=
  ⟨[{type := .word, value := some (.word previous)}, {type := .word, value := some (.word next)}]⟩
def hiddenHeap (previous next : Word) : Dynamic.Heap :=
  ⟨(inputHeap previous next).cells ++ [{type := .word, value := some (.word next)}]⟩
def boundHeap (previous next : Word) : Dynamic.Heap :=
  ⟨(hiddenHeap previous next).cells ++ [{type := .word, value := some (.word next)}]⟩
def sourceHeap (next : Word) : Dynamic.Heap := boundHeap next next

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
  (shape : Tests.SourceCoreNamedMatch.FactoryShape function signature)
  (sourceEq : header.function.source = function.typedBody)

include shape sourceEq in
theorem input_types : header.types = [.word, .word] := by
  have params : header.function.parameters = [shape.value, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.valueScheme,
    shape.argumentScheme, TypeSystem.Scheme.mono] using types.symm

include shape sourceEq in
private theorem arm_extension (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ armContext, BindersExtend function.typedBody.owner header.context [shape.copyBinder] armContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.matchNode.id, shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  rw [roots, sourceEq] at typed
  cases typed with
  | cons head tail =>
    have readFound : function.typedBody.lookupExpression? shape.matching.scrutinee = some shape.initialRead.node := by
      rw [shape.scrutinee]; exact shape.initialRead.found
    obtain ⟨_, caseFacts, _, casesTyped, _⟩ := ScopedSourceMatchAdmission.statement_sites
      (sourceEq ▸ header.unique) shape.matchFound shape.matchForm readFound head
    obtain ⟨binders, arity, armContext, _, _, pattern, extension, _⟩ :=
      ScopedSourceMatchAdmission.case_typing (arm := shape.arm) casesTyped (by rw [shape.arms]; simp)
    have same := CompatiblePatternSourceBinders.pattern_binders pattern
    have sameBinders : [shape.copyBinder] = binders := by
      simpa [SourceCoreDataPlaces.patternBinders, shape.patternResolution,
        SourceCoreDataPlaces.instructionBinders] using same
    exact ⟨armContext, sameBinders ▸ extension⟩

include shape sourceEq in
/-- Allocate the hidden scrutinee and original pattern binder, mutate the outer
parameter, restore its scope, and return it. This trace is independent of Core execution. -/
theorem ordinary_call (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope)
    (previous next : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [.word previous, .word next] (.word next) (sourceHeap next) := by
  let environment : Dynamic.Environment := [(shape.argument.id, ⟨1⟩), (shape.value.id, ⟨0⟩)]
  let armEnvironment : Dynamic.Environment := (shape.copyBinder.id, ⟨3⟩) :: environment
  have params : header.function.parameters = [shape.value, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word previous, .word next]
      environment (inputHeap previous next) := by
    rw [params]
    exact .cons (by rw [shape.valueScheme]; exact .append)
      (.cons (by rw [shape.argumentScheme]; exact .append) (.nil _ _))
  have roots : header.function.body = [shape.matchNode.id, shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  have read {binder : TypedBinder} (value : Word)
      (node : Tests.SourceCoreNamedMatch.Read function.typedBody binder .word)
      (context : SourceSemantics.Context) (env : Dynamic.Environment) (heap : Dynamic.Heap)
      (location : Dynamic.Location)
      (lookup : Dynamic.Environment.LooksUp env binder.id location)
      (reads : Dynamic.Heap.Reads heap location ⟨.word, some (.word value), none⟩) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        context header.function.evidence function.typedBody env heap node.node.id (.word value) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [node.form]
      exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
    · rw [node.coercions]; exact .nil
  obtain ⟨armContext, extension⟩ := arm_extension header shape sourceEq certified
  have selected : Dynamic.MatchCasesSelect header.context (.word next) shape.matching.cases
      shape.matching.defaultBody (.arm [shape.assignment.id] [(shape.copyBinder, .word next)]) := by
    rw [shape.arms, ← shape.armBody]
    apply Dynamic.MatchCasesSelect.head
    apply Dynamic.PatternMatches.intro (rootArity := 0)
    · rw [shape.patternSource, shape.patternResolution]; exact .binder rfl
    · rw [shape.patternResolution]; exact .binder
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      armContext header.function.evidence function.typedBody armEnvironment (boundHeap previous next)
      shape.resolution.target
      {location := ⟨0⟩, rootType := .word, valueType := shape.resolution.target.type, projections := [], selected := some (.word previous)}
      (boundHeap previous next) := by
    apply Dynamic.SourcePlaceResolves.intro (currentCell := ⟨.word, some (.word previous), none⟩)
      (initialCell := ⟨.word, some (.word previous), none⟩)
    · rw [shape.targetRoot]; exact .tail shape.localValue (.tail shape.argumentValue .head)
    · exact .intro .head
    · rw [shape.targetBare]; exact .nil
    · exact .intro .head
    · exact .initialized
    · exact .nil
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      armContext header.function.evidence function.typedBody armEnvironment (boundHeap previous next)
      shape.assignment.id armContext (.fallthrough armEnvironment) (sourceHeap next) := by
    apply Dynamic.StatementExecutes.assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
    apply Dynamic.SourcePlaceAssignment.intro resolve
    · exact read next shape.localRead armContext armEnvironment (boundHeap previous next) ⟨3⟩ .head
        (.intro (.tail (.tail (.tail .head))))
    · exact .intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head)
  have matched : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence function.typedBody environment (inputHeap previous next)
      shape.matchNode.id header.context (.fallthrough environment) (sourceHeap next) := by
    apply Dynamic.StatementExecutes.matchArm (outcome := .fallthrough armEnvironment)
      (scrutineeNode := shape.initialRead.node) (armEnvironment := armEnvironment)
      (hiddenHeap := hiddenHeap previous next) (bound := boundHeap previous next)
      (lookupStatement?_sound shape.matchFound) shape.matchForm
      (shape.scrutinee ▸ lookupExpression?_sound shape.initialRead.found)
    · rw [shape.scrutinee]
      exact read next shape.initialRead header.context environment (inputHeap previous next) ⟨1⟩ .head (.intro (.tail .head))
    · rw [shape.initialRead.type]; exact .append
    · exact selected
    · rfl
    · rfl
    · exact extension
    · exact .cons (by rw [shape.localScheme]; exact .append) (.nil _ _)
    · exact .cons assigned .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap previous next)
      header.function.body header.context (.returned (.word next)) (sourceHeap next) := by
    rw [roots, sourceEq]
    apply Dynamic.FunctionStatementsExecute.cons matched
    exact .singleton (lookupStatement?_sound shape.statementFound)
      (by rw [shape.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm
        (read next shape.finalRead header.context environment (sourceHeap next) ⟨0⟩
          (.tail shape.argumentValue .head) (.intro .head)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedMatch
