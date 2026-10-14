import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Test.SourceCoreNamedBranchSource

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
