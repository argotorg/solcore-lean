import Solcore.Test.SourceCoreNamedBranchSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.Frontend.SourceCompiler

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
