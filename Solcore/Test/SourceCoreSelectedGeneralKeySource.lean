import Solcore.Test.SourceCoreNamedBranchSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSource
import Solcore.Frontend.SourceCompiler

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

/-- The complete original probe program is retained, with every function seeded. -/
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Key { Key(Bool) }",
    "function pairRead(table: mapping((Bool, Bool) => Word)) returns (Word) { return table[(true, false)]; }",
    "function pairWrite(table: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { table[(true, false)] += 3; return table; }",
    "function proxyRead(table: mapping(@Word => Word)) returns (Word) { return table[@Word]; }",
    "function proxyWrite(table: mapping(@Word => Word)) returns (mapping(@Word => Word)) { table[@Word] += 3; return table; }",
    "function nominalRead(table: mapping(Key => Word)) returns (Word) { return table[Key(true)]; }"]}] }
def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

inductive Key where
  | pair (left right : Bool)
  | proxy (inner : TypeSystem.Ty)
  | nominal (metadata : DataConstructorInstantiation) (argument : Bool)

def Key.type : Key → TypeSystem.Ty
  | .pair .. => .product .bool .bool
  | .proxy inner => .proxy inner
  | .nominal metadata _ => metadata.resultType

def Key.value : Key → Dynamic.Value
  | .pair left right => .product (.bool left) (.bool right)
  | .proxy inner => .proxy inner
  | .nominal metadata argument => .constructed metadata [.bool argument]

def Key.Valid (context : SourceSemantics.Context) : Key → Prop
  | .pair .. | .proxy .. => True
  | .nominal metadata _ => DataConstructorInstantiation.Valid context metadata

def Key.Simple : Key → Prop
  | .pair .. | .proxy .. => True
  | .nominal .. => False

theorem Key.simple_valid (key : Key) (simple : key.Simple) (context : SourceSemantics.Context) :
    key.Valid context := by
  cases key with
  | pair | proxy => trivial
  | nominal => exact False.elim simple

theorem Key.comparable (key : Key) : Dynamic.ValueComparable key.value := by
  cases key with
  | pair left right => exact .product (.bool left) (.bool right)
  | proxy inner => exact .proxy inner
  | nominal metadata argument =>
    exact .constructed metadata [.bool argument] (by intro value member; cases List.mem_singleton.mp member; exact .bool argument)

structure BoolNode (source : TypedSource) (value : Bool) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  name : String
  form : node.form = .reference name (.builtinBoolean value)
  requirements : node.requirements = []
  coercions : node.coercions = []

inductive KeyForm (source : TypedSource) : ExpressionNode → Key → Type where
  | pair {node left right} (first : BoolNode source left) (second : BoolNode source right)
      (form : node.form = .tuple [first.node.id,second.node.id]) : KeyForm source node (.pair left right)
  | proxy {node inner} (form : node.form = .proxy inner) : KeyForm source node (.proxy inner)
  | nominal {node metadata argument} (child : BoolNode source argument)
      (form : node.form = .constructor metadata [child.node.id])
      (substitution : metadata.parameterSubstitution = [])
      (payload : metadata.payloadTypes = [.bool]) : KeyForm source node (.nominal metadata argument)

structure KeyNode (source : TypedSource) (key : Key) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  type : node.type = key.type
  requirements : node.requirements = []
  coercions : node.coercions = []
  shape : KeyForm source node key

private theorem bool_evaluates {source : TypedSource} {value : Bool} (node : BoolNode source value)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id (.bool value) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .builtinBoolean (by rw [node.requirements,node.coercions]; rfl)
  · rw [node.coercions]; exact .nil

/-- Key execution follows the original literal/tuple/constructor nodes. -/
theorem KeyNode.evaluates {source : TypedSource} {key : Key} (node : KeyNode source key)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (valid : key.Valid context) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id key.value heap := by
  cases node.shape with
  | pair first second form =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .tuple (by rw [node.requirements,node.coercions]; rfl)
        (.cons (bool_evaluates first _ _ _ _) (.cons (bool_evaluates second _ _ _ _) .nil)) (.cons (.singleton _))
    · rw [node.coercions]; exact .nil
  | proxy form =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .proxy (by rw [node.requirements,node.coercions]; rfl)
    · rw [node.coercions]; exact .nil
  | nominal child form _ _ =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .constructor (by rw [node.requirements,node.coercions]; rfl)
        valid (.cons (bool_evaluates child _ _ _ _) .nil)
    · rw [node.coercions]; exact .nil

/-- Nominal validity comes from the checked original key typing. -/
theorem KeyNode.valid {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    key.Valid context := by
  cases node.shape with
  | pair | proxy => trivial
  | nominal child form substitution _ =>
    cases typed with
    | intro contains raw _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      cases same
      rw [form] at raw
      cases raw with
      | constructor valid _ =>
        cases valid with
        | intro dataType signature dataMember signatureMember owner constructorEq exact range payload result =>
          exact .intro dataType signature dataMember signatureMember owner constructorEq exact
            (by rw [substitution]; intro parameter replacement impossible; cases impossible) payload result

def mappingType (key : Key) : TypeSystem.Ty := .mapping key.type .word
def mappingValue (key : Key) (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Value :=
  .mapping key.type .word entries
def mappingHeap (before : Dynamic.Heap) (key : Key) (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨mappingType key, some (mappingValue key entries), none⟩]⟩
def location (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩

structure ReadShape (source : TypedSource) (key : Key) where
  binder : TypedBinder
  keyNode : KeyNode source key
  base : Tests.SourceCoreNamedBranch.Read source binder (mappingType key)
  index : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono (mappingType key)
  roots : source.roots = [.statement returned.id]
  indexFound : source.lookupExpression? index.id = some index
  indexForm : index.form = .index base.node.id keyNode.node.id
  indexRequirements : index.requirements = []
  indexCoercions : index.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some index.id)

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons,List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

private theorem read_value {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source binder type)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (loc : Dynamic.Location) (value : Dynamic.Value)
    (lookup : Dynamic.Environment.LooksUp environment binder.id loc)
    (reads : Dynamic.Heap.Reads heap loc ⟨type,some value,none⟩) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .local (by rw [node.requirements,node.coercions]; rfl) lookup reads rfl rfl
  · rw [node.coercions]; exact .nil

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem read_input_types {key : Key} (shape : ReadShape header.function.source key) :
    header.types = [mappingType key] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params,List.map_cons,List.map_nil,shape.scheme,TypeSystem.Scheme.mono] using types.symm

theorem read_key_valid {key : Key} (shape : ReadShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) : key.Valid header.context := by
  obtain ⟨final,facts,statements,_⟩ := certified.statements
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at statements
  cases statements with
  | singleton statement =>
    cases statement with
    | returnValue contains form expression _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.returnedFound)
      cases same
      rw [shape.returnedForm] at form
      cases Option.some.inj (StatementForm.returnStmt.inj form)
      have originalTyped := expression
      obtain ⟨actual, actualContains, actualType⟩ := expression.stored_type
      have same := Option.some.inj ((lookupExpression?_complete header.unique actualContains).symm.trans shape.indexFound)
      cases same
      rw [← actualType] at originalTyped
      obtain ⟨_,_,keyTyped⟩ := CompatibleExpressionIndices.index_source_types header.unique shape.indexFound
        shape.indexForm shape.indexCoercions originalTyped
      exact shape.keyNode.valid header.unique keyTyped
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique (by assumption)).symm.trans shape.returnedFound)
      cases same
      simp_all [shape.returnedForm]

/-- First-match lookup keeps later duplicate entries and the parameter heap. -/
theorem read_plain {key : Key} (shape : ReadShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (first : Word)
    (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before [mappingValue key ((key.value,.word first)::tail)] (.word first)
      (mappingHeap before key ((key.value,.word first)::tail)) := by
  let entries := (key.value,.word first)::tail
  let value := mappingValue key entries
  let after := mappingHeap before key entries
  let environment := [(shape.binder.id,location before)]
  have allocated : Dynamic.Heap.Allocates before (mappingType key) (some value) (location before) after := .append
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [value] environment after := by
    rw [params]; exact .cons (by rw [shape.scheme]; exact allocated) (.nil _ _)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after shape.index.id (.word first) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.indexFound)
    · rw [shape.indexForm]
      exact .indexFound (by rw [shape.indexRequirements,shape.indexCoercions]; rfl)
        (read_value shape.base _ _ _ _ _ _ .head allocated.reads_new)
        (shape.keyNode.evaluates _ _ _ _ (read_key_valid header shape certified)) (.head (Dynamic.ValueEquivalent.refl key.comparable))
    · rw [shape.indexCoercions]; exact .nil
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after header.function.body
      header.context (.returned (.word first)) after := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD,global,sourceAt,.global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedGeneralKey
