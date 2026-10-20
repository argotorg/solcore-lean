import Solcore.SourceSemantics.SourceCompiledCachedMethodInputs

/-! A shared body retains its real ordinary or implementation-method origin.
Both origins use one successful body check and one parameter specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledMethodFinalization

inductive BodyOrigin (program : CheckedProgram) :
    CheckedFunction → ProgramFunctionSignature → Prop where
  | ordinary {original : CheckedFunction} {signature : ProgramFunctionSignature}
      (originalMember : original ∈ program.functions)
      (signatureMember : signature ∈ program.signatures.functions) :
      BodyOrigin program original signature
  | method {retained : CheckedImplementationMethod}
      {implementation : ProgramImplementationSignature}
      {method : ProgramImplMethodSignature} {trait : ProgramTraitSignature}
      (retainedMember : retained ∈ program.methods)
      (implementationMember : implementation ∈ program.signatures.implementations)
      (methodMember : method ∈ implementation.methods)
      (traitLookup : program.signatures.trait? method.traitMethod.trait = some trait)
      (methodId : retained.id = method.id) :
      BodyOrigin program retained.checked
        (implementation.functionSignatureOfMethodWithTrait trait method)

structure BodySelection (compiled : SourceCoreCompiler.Compiled)
    (row : SourceSpecialization.SpecializedFunction) (fuel : Nat) where
  original : CheckedFunction
  signature : ProgramFunctionSignature
  body : BodyReceipt compiled.program.environment compiled.program.signatures signature fuel original
  origin : BodyOrigin compiled.program original signature
  specialized : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original

namespace Selected
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def toBodySelection (selected : Selected compiled row fuel) : BodySelection compiled row fuel :=
  { original := selected.original, signature := selected.signature, body := selected.body,
    origin := .ordinary selected.originalMember selected.signatureMember,
    specialized := selected.specialized }

instance : Coe (Selected compiled row fuel) (BodySelection compiled row fuel) :=
  ⟨toBodySelection⟩

theorem toBodySelection_original (selected : Selected compiled row fuel) :
    selected.toBodySelection.original = selected.original := rfl

theorem toBodySelection_signature (selected : Selected compiled row fuel) :
    selected.toBodySelection.signature = selected.signature := rfl

theorem toBodySelection_body (selected : Selected compiled row fuel) :
    selected.toBodySelection.body = selected.body := rfl

end Selected

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem source (selected : BodySelection compiled row fuel) :
    row.function.typedBody = SourceSpecialization.applyTypedSource row.parameterSubstitution
      selected.body.finalized.typedSource := by
  rw [selected.specialized, ← selected.body.source]
  rfl

theorem solved (selected : BodySelection compiled row fuel) :
    row.function.solvedRequirements = selected.body.finalized.solvedRequirements.map
      (SourceSpecialization.applySolvedRequirement row.parameterSubstitution) := by
  rw [selected.specialized, ← selected.body.solved]
  rfl

/-- Eliminate the genuine origin while retaining this exact body receipt.
The method branch constructs its receipt from the same body field. -/
theorem of_origins {motive : BodySelection compiled row fuel → Prop}
    (selected : BodySelection compiled row fuel)
    (ordinary : ∀ value : Selected compiled row fuel, motive value.toBodySelection)
    (method : ∀ {retained : CheckedImplementationMethod}
      (receipt : MethodBodyReceipt compiled.program retained fuel)
      (member : retained ∈ compiled.program.methods)
      (specialized : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution retained.checked),
      motive {
        original := retained.checked
        signature := receipt.signature
        body := receipt.body
        origin := .method member receipt.implementationMember receipt.methodMember receipt.traitLookup receipt.methodId
        specialized }) :
    motive selected := by
  rcases selected with ⟨original, signature, body, origin, specialized⟩
  cases origin with
  | ordinary originalMember signatureMember =>
      exact ordinary { original, originalMember, signature, signatureMember, body, specialized }
  | @method retained implementation declaration trait member implementationMember methodMember lookup identity =>
      exact method
        ⟨implementation, declaration, trait, implementationMember, methodMember, lookup, identity, body⟩
        member specialized

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
