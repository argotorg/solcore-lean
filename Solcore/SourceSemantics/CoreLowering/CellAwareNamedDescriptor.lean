import Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution

/-! The actual named entry and the original lexical capture determine the
stored descriptor's source and binding. Neither projected function types nor
native closure headers are used to reconstruct Source identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source state)
open CallableIndexedHistory

/-- The original catalog observation supplies the stored binding; the actual
named hook supplies its paired Source metadata and lexical frame. -/
theorem of_capture {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {binder : TypedBinder} {initializer : ExpressionId}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer function)
    {id : Word} {native : NativeFrame}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      native (.named id) (some (state named))) :
    ∃ origin : GeneralizedLocalDescriptorOrigin.Origin prepared function site.binding [],
      origin.native = native ∧ origin.ghost = .named id ∧ origin.metadata = state named ∧
      origin.metadata = ⟨⟨site.binding.caller, [], site.binding.source⟩, []⟩ ∧
      Nonempty (GeneralizedLocalLocatedRows.Attachment
        (GeneralizedLocalInstanceValues.model prepared) function site.binding []) ∧
      function.source = site.binding.source ∧ function.binder = site.binding.binder ∧
      function.initializer = site.binding.initializer := by
  have binderEq : site.binding.binder = binder := by
    simpa only [EmptySourceSubstitution.binder] using site.bindingMetadata
  have sourceEq : site.binding.source = source named := by
    simpa only [EmptySourceSubstitution.source] using site.bindingSource
  have selfCapture : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function := by
    simpa only [captures.definitionContext_eq, captures.source_eq, captures.captured_eq,
      captures.binder_eq, captures.initializer_eq] using captures
  let origin : GeneralizedLocalDescriptorOrigin.Origin prepared function site.binding [] := {
    native
    ghost := .named id
    metadata := state named
    carried
    paired := by
      rw [captures.source_eq]
      exact .named (CallableIndexedNamedGeneration.seed prepared selected record)
    owner := site.bindingCaller.symm
    active := rfl }
  have registered : prepared.base.locals.binding site.binding.caller site.binding.binder.id = .ok site.binding := by
    rw [site.bindingCaller, binderEq]
    exact site.located
  have namedMetadata : origin.metadata = ⟨⟨site.binding.caller, [], site.binding.source⟩, []⟩ := by
    change state named = _
    rw [site.bindingCaller, sourceEq]
    rfl
  exact ⟨origin, rfl, rfl, rfl, namedMetadata, ⟨⟨registered, selfCapture, ⟨origin⟩,
      congrArg TypedBinder.id (captures.binder_eq.trans binderEq.symm),
      captures.initializer_eq.trans site.bindingInitializer.symm⟩⟩,
    captures.source_eq.trans sourceEq.symm, captures.binder_eq.trans binderEq.symm,
    captures.initializer_eq.trans site.bindingInitializer.symm⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
