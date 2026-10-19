import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! The materialized association retains the actual contextual binder compiler.
Its original Source frame and ordered argument row determine native arguments;
no count or raw type is recovered from a projected type alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation

private theorem binder_projection {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerBinder checked source scope binder = .ok type) :
    checked.catalog.project binder.scheme.body = .ok type := by
  apply CompatibleExpressionReads.projectType_of_accepted
  simp only [SourceCoreCompatibleDataExpressions.lowerBinder, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  exact accepted

private theorem parameter_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {representation : SourceCoreGeneralFunctions.Representation} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {policy : SourceCoreFunctions.Policy} {source : TypedSource} {scope finalScope : SourceCoreLocalCell.Scope}
    {parameters : List TypedBinder} {bindings : List CallableIndexedParameterCertificates.Binding}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (bindings, finalScope))
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals owner active)
    (ordinaryPolicy : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder checked)
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = []) :
    ∀ binding ∈ bindings, checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  have tree := FunctionCode.Parameters.of_accepted accepted
  clear accepted
  induction tree with
  | nil => simp
  | @cons scope finalScope parameter parameters type bindings head tail ih =>
    rw [binderPolicy, SourceCoreGeneralFunctions.contextualBinder,
      monomorphic parameter (by simp), List.isEmpty_nil, if_pos rfl, ordinaryPolicy] at head
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact binder_projection head
    · exact ih (fun binder h => monomorphic binder (List.mem_cons_of_mem _ h)) binding member

private theorem frame_monomorphic {program : Program} {function : Dynamic.Closure}
    (frame : Dynamic.ClosureFrame program function) :
    ∀ binder ∈ function.parameters, binder.scheme.quantified = [] := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique extended bodyTyped completes =>
    exact CallableIndexedOwnedLambdaBinderProjections.monomorphic extended

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem projected_bindings (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases member with
  | viewed material _ _ =>
    apply parameter_projections material.code.receipt.parametersCompiled
    · rw [material.policy]
      rfl
    · unfold GeneralizedLocalLambdaCompilation.representation
      rw [material.indexed.represented]
      rfl
    · exact frame_monomorphic frame

theorem parameter_core (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  have projections := projected_bindings member frame
  cases member with
  | viewed material _ _ =>
    apply CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack material.code profile projections
    have projector : material.code.policy.projectType =
        SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked := by
      rw [material.policy]
      change (GeneralizedLocalLambdaCompilation.representation material.inputs
        material.packet.original.emission.prepared).expressions.projectType = _
      unfold GeneralizedLocalLambdaCompilation.representation
      rw [material.indexed.represented]
      rfl
    have result := material.code.receipt.resultProjected
    rw [projector] at result
    exact CompatibleExpressionReads.projectType_of_accepted result

/-- The independent Source count fixes the packing ambiguity at zero and one.
Both raw and native ordered bundles then align with the actual binder list. -/
theorem arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (arity : sources.length = function.parameters.length)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes types = parameter) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  have bindingArity : sources.length = bindings.length := by
    have lengths := congrArg List.length member.source_binders
    simp only [List.length_map] at lengths
    exact arity.trans lengths.symm
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented bindingArity
    (sourceBundle.trans (congrArg TypeSystem.Ty.productMany member.source_binders).symm)
    (nativeBundle.trans (parameter_core member frame profile))

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
