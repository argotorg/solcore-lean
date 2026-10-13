import Solcore.Test.SourceCoreMethodOriginEvidenceInventory
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission

/-! Actual factory Headers retain the original returned lambda and its body.
The same two factory roots complete the shared program certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {row : ObservedRow fixture signature} {generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}

theorem ActualHeader.factory_compiler_roots
    (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (actual : ActualHeader fixture row.row) :
    actual.header.function.body = [shape.outerReturn.id] := by
  rw [actual.aligned.function]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, shape.roots] at accepted
  exact (Except.ok.inj accepted).symm


/-- The exact accepted returned-lambda action supplies the formation receipt.
Original source facts identify the outer and inner returns without scanning. -/
theorem ActualHeader.factory_compiler_certificate
    (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled row.named) := by
  have issued := AcceptedNamedFactoryAdmission.of_returning actual.prepared actual.aligned
    (actual.factory_compiler_roots shape)
    (by rw [actual.source]; exact shape.outerReturnFound) shape.outerReturnForm
    (by rw [actual.source]; exact shape.expression.found) shape.lambda
    shape.expression.requirements shape.expression.coercions
    (by simp only [noLocals, List.find?_nil])
    (by rw [actual.source]; exact shape.statementFound) shape.statementForm fixture.source_wellFormed
  obtain ⟨certificate⟩ := issued
  exact AcceptedNamedFactoryAdmission.source_of_header actual.prepared actual.aligned
    row.cached row.same certificate

theorem ObservedProgram.makeWord_factory_certificate (observed : ObservedProgram fixture) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled observed.makeWordRow.named) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeWordHeader.factory_compiler_certificate observed.makeWordShape observed.noLocals

theorem ObservedProgram.makeBool_factory_certificate (observed : ObservedProgram fixture) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled observed.makeBoolRow.named) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeBoolHeader.factory_compiler_certificate observed.makeBoolShape observed.noLocals

end Tests.SourceCoreMethodOriginEvidence
