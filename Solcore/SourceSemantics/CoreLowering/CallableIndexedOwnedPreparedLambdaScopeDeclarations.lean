import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
import Solcore.SourceSemantics.Staging.RecursiveScope

/-! The actual lambda occurrence supplies declaration membership for every
parameter. Original parameter typing extends a genuine captured-scope lookup
correspondence to the compiler's reversed body scope. Native parameter types
remain arbitrary; they do not determine the original source schemes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
open Core Frontend SourceInference
open CallableIndexedLambdaValues

/-- The original typed lambda, rather than a native type projection, locates
its parameter declarations in the full source node table. -/
theorem parameters_declared {program : Program} {function : Dynamic.Closure}
    (frame : Dynamic.ClosureFrame program function) :
    ∀ binder ∈ function.parameters, binder ∈ SourceCoreDataPlaces.declaredBinders function.source := by
  intro binder member
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.expression node, contains.1, ?_⟩
  simpa only [form] using member

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty))
    (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih =>
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The same accepted parameter vector and raw context extension supply the
body's lookup correspondence. Captured declarations remain genuine inputs. -/
theorem at_parameters {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context) :
    CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      inputs.context := by
  have parameters := CallableIndexedLambdaEntryPrefix.parameters code
  have member : ∀ binding ∈ code.receipt.loweredParameters,
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders function.source := by
    intro binding present
    apply parameters_declared frame
    rw [parameters]
    exact List.mem_map.mpr ⟨binding, present, rfl⟩
  have extended := inputs.extended
  rw [parameters] at extended
  have declarations := RecursiveNamedHeaderScopeDeclarations.parameters member extended captured
  simpa only [reversed_scope] using declarations

/-- Every actual staged closure scope retains the same source declarations. -/
theorem at_selected_scope {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child) :
    CompatibleExpressionReads.ScopeDeclarations child.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      inputs.context := by
  rw [stages.source selected]
  exact at_parameters code inputs frame captured

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
