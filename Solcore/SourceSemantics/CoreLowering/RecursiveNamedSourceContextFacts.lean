import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog

/-! Named source bodies retain the declaration's residual-variable scope.
These facts use structural source instantiation and binder installation only;
no native type, runtime trace, or change to the source context is involved. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

/-- Instantiated declarations have no lexical inference-variable binders and
retain the independent residual-occurrence scope. -/
theorem frame_fields {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (frame : NamedCalls.SourceFrame program instantiation body function) :
    function.context.typeVariables = [] ∧ function.context.residualTypeVariables = true := by
  rw [frame.context]
  cases frame.instantiated with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    exact ⟨rfl, rfl⟩

/-- Monomorphic parameters preserve both flexible-variable scope fields. -/
theorem mono_fields {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context binders types final) :
    final.typeVariables = context.typeVariables ∧
      final.residualTypeVariables = context.residualTypeVariables := by
  induction extended with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ head _ ih =>
    exact ⟨ih.1.trans head.typeVariables_eq, ih.2.trans head.residualTypeVariables_eq⟩

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The actual catalog header uses the source declaration context after its
real monomorphic input binders have been installed. -/
theorem header_fields (header : Header prepared values definitions program) :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true := by
  have inherited := mono_fields header.extended
  have declaration := frame_fields header.frame
  exact ⟨inherited.1.trans declaration.1, inherited.2.trans declaration.2⟩

theorem header_typeVariables (header : Header prepared values definitions program) :
    header.context.typeVariables = [] := (header_fields header).1

theorem header_residual (header : Header prepared values definitions program) :
    header.context.residualTypeVariables = true := (header_fields header).2

/-- A factory fixed to `false` cannot serve a legitimate named source header. -/
theorem header_not_false (header : Header prepared values definitions program) :
    header.context.residualTypeVariables ≠ false := by
  rw [header_residual header]
  decide

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
