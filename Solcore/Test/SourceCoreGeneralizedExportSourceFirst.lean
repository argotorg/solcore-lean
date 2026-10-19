import Solcore.Test.SourceCoreGeneralizedExportTrace

/-! The genuine original declaration typing supplies each exact scheme
instance before constructing the complete independent Source factory trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_,_,_,head,.nil _ _⟩
  | cons head tail => exact ⟨_,_,_,head,tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual,contains,original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

theorem LambdaShape.context_after {source : TypedSource} (shape : LambdaShape source)
    {control : ControlContext} {context next : SourceSemantics.Context} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.initialized.id next facts) :
    BinderExtends source.owner context shape.binder next ∧
      SchemeWellFormed next shape.binder.scheme ∧ Dynamic.RuntimeContextFields context next := by
  have original := form_at unique shape.initializedFound typed
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ => rw [shape.scheme] at monomorphic; cases monomorphic
  | letInitializedGeneralized _ _ _ _ extended =>
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    cases extended with
    | intro wellformed fresh =>
      exact ⟨.intro wellformed fresh, {
        binders := wellformed.scheme.binders.withLocal _ _ _
        quantified_nodup := wellformed.scheme.quantified_nodup
        body := wellformed.scheme.body.withLocal _ _ _ },fields⟩

theorem MakeShape.body_from_source {source : TypedSource} (shape : MakeShape source)
    {program : SourceSemantics.Program} {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context
      [shape.principal.initialized.id,shape.returned.id] final facts) :
    ∃ next, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context environment evidence))
      (shape.principal.allocatedHeap context environment before) := by
  obtain ⟨next,_,_,first,_⟩ := head_tail typed
  obtain ⟨extended,wellformed,fields⟩ := shape.principal.context_after unique first
  exact ⟨next,shape.body_trace evidence environment before extended fields wellformed
    ⟨wellformed.binders,.builtin .word⟩ ⟨wellformed.binders,.builtin .bool⟩⟩

theorem CaptureShape.body_from_source {source : TypedSource} (shape : CaptureShape source)
    {program : SourceSemantics.Program} {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context
      [shape.principal.initialized.id,shape.returned.id] final facts) :
    ∃ next, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.principal.initialized.id,shape.returned.id] next
      (.returned (shape.value context environment evidence))
      (shape.principal.allocatedHeap context environment before) := by
  obtain ⟨next,_,_,first,_⟩ := head_tail typed
  obtain ⟨extended,wellformed,fields⟩ := shape.principal.context_after unique first
  exact ⟨next,shape.body_trace evidence environment before extended fields wellformed
    ⟨wellformed.binders,.builtin .bool⟩⟩

end Tests.SourceCoreGeneralizedExport
