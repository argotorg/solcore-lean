import Solcore.Test.SourceCoreSelectedGeneralKeySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure WriteShape (source : TypedSource) (key : Key) where
  binder : TypedBinder
  keyNode : KeyNode source key
  simple : key.Simple
  right : WordNode source
  result : Tests.SourceCoreNamedBranch.Read source binder (mappingType key)
  assignment : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono (mappingType key)
  roots : source.roots = [.statement assigned.id,.statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignValue assignment .add right.node.id
  targetRoot : assignment.target.root = binder.id
  targetProjections : assignment.target.projections = [.index keyNode.node.id]
  targetType : assignment.target.type = .word
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
      simp only [List.map_cons,List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

private theorem write_append (previousCells : List Dynamic.Cell) (old next : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite (previousCells ++ [old]) previousCells.length next (previousCells ++ [next]) := by
  induction previousCells with
  | nil => exact .head
  | cons head rest ih => exact .tail ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem write_input_types {key : Key} (shape : WriteShape header.function.source key) :
    header.types = [mappingType key] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params,List.map_cons,List.map_nil,shape.scheme,TypeSystem.Scheme.mono] using types.symm

theorem write_rhs_typed {key : Key} (shape : WriteShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ExpressionHasType header.function.source header.context shape.right.node.id .word := by
  obtain ⟨final,facts,statements,_⟩ := certified.statements
  have roots : header.function.body = [shape.assigned.id,shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at statements
  cases statements with
  | cons statement _ =>
    cases statement with
    | assignValue contains form assigned _ =>
      cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.assignedFound)
      rw [shape.assignedForm] at form
      cases form
      cases assigned with | wordCompound _ _ typed _ => exact typed
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique (by assumption)).symm.trans shape.assignedFound)
      cases same
      simp_all [shape.assignedForm]

/-- The original key and literal RHS are evaluated before first-match update;
no later duplicate entry is replaced. -/
theorem write_plain {key : Key} (shape : WriteShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (first : Word)
    (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before [mappingValue key ((key.value,.word first)::tail)]
      (mappingValue key ((key.value,.word (first + Word.ofNatModulo shape.right.resolution.rawValue))::tail))
      (mappingHeap before key ((key.value,.word (first + Word.ofNatModulo shape.right.resolution.rawValue))::tail)) := by
  let original := mappingValue key ((key.value,.word first)::tail)
  let updated := first + Word.ofNatModulo shape.right.resolution.rawValue
  let replacement := mappingValue key ((key.value,.word updated)::tail)
  let current := mappingHeap before key ((key.value,.word first)::tail)
  let after := mappingHeap before key ((key.value,.word updated)::tail)
  let environment := [(shape.binder.id,location before)]
  have allocation : Dynamic.Heap.Allocates before (mappingType key) (some original) (location before) current := .append
  have rootRead := allocation.reads_new
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [original] environment current := by
    rw [params]; exact .cons (by rw [shape.scheme]; exact allocation) (.nil _ _)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assignment.target
      {location := location before,rootType := mappingType key,valueType := shape.assignment.target.type,
        projections := [.index key.value],selected := some (.word first)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType key,some original,none⟩) (currentCell := ⟨mappingType key,some original,none⟩)
    · rw [shape.targetRoot]; exact .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (shape.keyNode.evaluates _ _ _ _ (key.simple_valid shape.simple _)) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head (Dynamic.ValueEquivalent.refl key.comparable)) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement) after := by
    apply Dynamic.Heap.Writes.intro rootRead
    exact write_append before.cells ⟨mappingType key,some original,none⟩ ⟨mappingType key,some replacement,none⟩
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assigned.id
      header.context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.assignValue (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve (shape.right.evaluates _ _ _ header.unique (write_rhs_typed header shape certified)) ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head (Dynamic.ValueEquivalent.refl key.comparable)) (.leaf (.add (.wordAdd _ _)))
        (.update (.head (Dynamic.ValueEquivalent.refl key.comparable)))) write
  have finalRootRead : Dynamic.Heap.Reads after (location before) ⟨mappingType key,some replacement,none⟩ := by
    obtain ⟨cell,readBefore,readAfter⟩ := write.reads_updated
    cases readBefore.functional rootRead
    exact readAfter
  have result : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after shape.result.node.id replacement after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.result.found)
    · rw [shape.result.form]
      exact .local (by rw [shape.result.requirements,shape.result.coercions]; rfl) .head finalRootRead rfl rfl
    · rw [shape.result.coercions]; exact .nil
  have roots : header.function.body = [shape.assigned.id,shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned replacement) after := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm result))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD,global,sourceAt,.global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedGeneralKey
