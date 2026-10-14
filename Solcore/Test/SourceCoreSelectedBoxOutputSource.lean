import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward

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
