import Solcore.Test.SourceCoreGeneralizedExportSource
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Independent ordinary Source factory traces. The returned handles denote
materialized instances of the actual stored descriptor and captured environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read)

theorem LambdaShape.materializes {source : TypedSource} (shape : LambdaShape source)
    {type : TypeSystem.Ty} (readNode : Read source shape.binder type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (stored : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiated : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder type [] substitution produced) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap readNode.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) heap := by
  apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
    (lookupExpression?_sound readNode.found) readNode.form
    (by rw [readNode.requirements, readNode.coercions]; rfl)
    lookup stored descriptor fields
  · rw [readNode.raw]; exact instantiated
  · rw [readNode.coercions]; exact .nil

theorem MakeShape.instance {source : TypedSource} (shape : MakeShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.principal.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.principal.binder
      (.function type type) [] [(shape.principal.typeVariable,type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.principal.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.principal.scheme]; exact ExactSubstitution.singleton _ _
  · intro metavariable replacement member
    have same := List.mem_singleton.mp member
    cases same; exact ground
  · simp [shape.principal.scheme,shape.resultType,TypeSystem.Substitution.apply,TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates,shape.principal.schemeRequirements]; exact .nil

theorem CaptureShape.instance {source : TypedSource} (shape : CaptureShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (wellformed : SchemeWellFormed context shape.principal.binder.scheme)
    (boolean : TypeWellFormed context .bool) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.principal.binder
      (.function .bool .word) [] [(shape.principal.typeVariable,.bool)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.principal.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.principal.scheme]; exact ExactSubstitution.singleton _ _
  · intro metavariable replacement member
    have same := List.mem_singleton.mp member
    cases same; exact boolean
  · simp [shape.principal.scheme,shape.resultType,TypeSystem.Substitution.apply,TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates,shape.principal.schemeRequirements]; exact .nil

def MakeShape.value {source : TypedSource} (shape : MakeShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) : Dynamic.Value :=
  .product
    (.closure ((shape.principal.descriptor context environment).instantiate
      [(shape.principal.typeVariable,.word)] (evidence.applySubstitution [(shape.principal.typeVariable,.word)])))
    (.closure ((shape.principal.descriptor context environment).instantiate
      [(shape.principal.typeVariable,.bool)] (evidence.applySubstitution [(shape.principal.typeVariable,.bool)])))

def CaptureShape.value {source : TypedSource} (shape : CaptureShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) : Dynamic.Value :=
  .closure ((shape.principal.descriptor context environment).instantiate
    [(shape.principal.typeVariable,.bool)] (evidence.applySubstitution [(shape.principal.typeVariable,.bool)]))

theorem MakeShape.body_trace {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {context next : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (extended : BinderExtends source.owner context shape.principal.binder next)
    (fields : Dynamic.RuntimeContextFields context next)
    (wellformed : SchemeWellFormed next shape.principal.binder.scheme)
    (word : TypeWellFormed next .word) (boolean : TypeWellFormed next .bool) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context environment evidence))
      (shape.principal.allocatedHeap context environment before) := by
  let heap := shape.principal.allocatedHeap context environment before
  let locals := (shape.principal.binder.id,⟨before.cells.length⟩) :: environment
  have allocated : Dynamic.Heap.AllocatesGeneralized before (shape.principal.descriptor context environment)
      ⟨before.cells.length⟩ heap := .append
  have first := shape.principal.materializes (program := program) shape.wordRead environment locals
    [(shape.principal.typeVariable,.word)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed word)
  have second := shape.principal.materializes (program := program) shape.boolRead environment locals
    [(shape.principal.typeVariable,.bool)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed boolean)
  have tuple : Dynamic.ExpressionEvaluates program next evidence source locals heap shape.tuple.id
      (shape.value context environment evidence) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
    · rw [shape.tupleForm]
      exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
        (.cons first (.cons second .nil)) (.cons (.singleton _))
    · rw [shape.tupleCoercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.cons (shape.principal.initializes evidence environment before extended)
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tuple

theorem CaptureShape.body_trace {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {context next : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (extended : BinderExtends source.owner context shape.principal.binder next)
    (fields : Dynamic.RuntimeContextFields context next)
    (wellformed : SchemeWellFormed next shape.principal.binder.scheme)
    (boolean : TypeWellFormed next .bool) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context environment evidence))
      (shape.principal.allocatedHeap context environment before) := by
  let heap := shape.principal.allocatedHeap context environment before
  let locals := (shape.principal.binder.id,⟨before.cells.length⟩) :: environment
  have allocated : Dynamic.Heap.AllocatesGeneralized before (shape.principal.descriptor context environment)
      ⟨before.cells.length⟩ heap := .append
  have materialized := shape.principal.materializes (program := program) shape.read environment locals
    [(shape.principal.typeVariable,.bool)] evidence [] Dynamic.Environment.LooksUp.head
    allocated.reads_new rfl fields (shape.instance evidence wellformed boolean)
  apply Dynamic.FunctionStatementsExecute.cons (shape.principal.initializes evidence environment before extended)
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm materialized

theorem TickShape.body_trace {source : TypedSource} (shape : TickShape source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (flag : Bool) {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.input.id location)
    (stored : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = none) (value : cell.value = some (.bool flag)) :
    Dynamic.FunctionStatementsExecute program context evidence source environment heap
      [shape.returned.id] context (.returned (.bool flag)) heap := by
  have read : Dynamic.ExpressionEvaluates program context evidence source environment heap
      shape.read.node.id (.bool flag) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.read.found)
    · rw [shape.read.form]
      exact .local (by rw [shape.read.requirements,shape.read.coercions]; rfl) lookup stored descriptor value
    · rw [shape.read.coercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm read

end Tests.SourceCoreGeneralizedExport
