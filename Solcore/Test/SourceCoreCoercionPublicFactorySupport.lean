import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

/-- The executable certificate retains the actual cached factory row. Its
inner call still carries the original ordered evidence and coercion path. -/
structure ObservedFactory (fixture : CompiledFixture) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) where
  certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled row.named
  accepted : CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory
    fixture.recipe.compiled row.named = some certificate

def observeFactorySupport (fixture : CompiledFixture) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) : IO (ObservedFactory fixture row) := do
  match accepted : CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory
      fixture.recipe.compiled row.named with
  | none => throw (IO.userError "actual cached factory source admission failed")
  | some certificate => return ⟨certificate, accepted⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  make : ObservedFactory fixture observed.makeRow.toObservedRow

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.makeRow.toObservedRow⟩

theorem ActualHeader.factory_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {mark coercion : ProgramTraitSignature} (_shape : FactoryShape row.row.function signature generic parameter mark coercion)
    (extra : ObservedFactory fixture row) (actual : ActualHeader fixture row.row)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {stages : Staging.Recursive.Registry} :
    ∃ terminal : Terminal actual.header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) actual.header terminal) := by
  exact CallableIndexedOwnedPreparedNamedFactoryAdmission.of_actual actual.prepared actual.aligned
    row.cached row.same extra.certificate fixture.recipePrepared actual.diagnostic
    fixture.source_wellFormed observed.profile observed.makeRow.entryMember

end Tests.SourceCoreCoercionPublic
