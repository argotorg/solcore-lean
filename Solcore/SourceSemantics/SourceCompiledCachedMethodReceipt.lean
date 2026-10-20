import Solcore.SourceSemantics.SourceCompiledNormalizedFormation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.SourceProgramCheckingSoundness

/-! A real cached method retains the original method catalog entry and its
actual checker receipt at the program checking budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

structure MethodBodyReceipt (program : CheckedProgram)
    (retained : CheckedImplementationMethod) (fuel : Nat) where
  implementation : ProgramImplementationSignature
  method : ProgramImplMethodSignature
  trait : ProgramTraitSignature
  implementationMember : implementation ∈ program.signatures.implementations
  methodMember : method ∈ implementation.methods
  traitLookup : program.signatures.trait? method.traitMethod.trait = some trait
  methodId : retained.id = method.id
  body : BodyReceipt program.environment program.signatures
    (implementation.functionSignatureOfMethodWithTrait trait method) fuel retained.checked

namespace MethodBodyReceipt
variable {program : CheckedProgram} {retained : CheckedImplementationMethod} {fuel : Nat}

def signature (receipt : MethodBodyReceipt program retained fuel) : ProgramFunctionSignature :=
  receipt.implementation.functionSignatureOfMethodWithTrait receipt.trait receipt.method

theorem of_checked {raw : Workspace.RawWorkspace}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    (member : retained ∈ program.methods) :
    Nonempty (MethodBodyReceipt program retained fuel) := by
  obtain ⟨implementation, method, trait, implementationMember, methodMember,
    traitLookup, methodId, accepted⟩ := Frontend.checkProgram_success_method_body checked member
  obtain ⟨body⟩ := BodyReceipt.of_check accepted
  exact ⟨⟨implementation, method, trait, implementationMember, methodMember, traitLookup, methodId, body⟩⟩

theorem header {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    CheckedBodyHeaderWellFormed program.signatures receipt.signature retained.checked := by
  have implementation := (SignatureCatalogWellFormed.ofCheckProgram checked).implementations_semantic
    receipt.implementation receipt.implementationMember
  exact CheckedBodyHeaderWellFormed.ofCheckImplementationMethod implementation
    (implementation.methods receipt.method receipt.methodMember) receipt.body.accepted

theorem canonical {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    SignatureParametersWellFormed receipt.signature.id receipt.signature.scheme.parameters := by
  exact (Frontend.checkProgram_success_signature_parameters_wellFormed checked).implementations
    receipt.implementation receipt.implementationMember

/-- The trait looked up by the original checker is the implementation head's
actual trait, as witnessed by the same method in the validated catalog. -/
theorem trait_origin {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    receipt.trait ∈ program.signatures.traits ∧
      receipt.implementation.head.trait = .declaration receipt.trait.id := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementation := catalog.implementations_semantic receipt.implementation receipt.implementationMember
  have method := implementation.methods receipt.method receipt.methodMember
  obtain ⟨trait, signature, traitMember, head, signatureMember, signatureId, _⟩ := method.trait_method
  have selectedMember : receipt.trait ∈ program.signatures.traits := List.mem_of_find?_eq_some receipt.traitLookup
  have selectedId : receipt.trait.id = receipt.method.traitMethod.trait := of_decide_eq_true
    (List.find?_some (p := fun candidate : ProgramTraitSignature => decide (candidate.id = receipt.method.traitMethod.trait)) receipt.traitLookup)
  have semanticId : trait.id = receipt.method.traitMethod.trait := by
    rw [← ((catalog.traits_semantic trait traitMember).methods signature signatureMember).owner]
    exact congrArg ProgramTraitMethodId.trait signatureId
  have same : trait = receipt.trait := Frontend.trait_signature_eq_of_mem_of_id_eq
    catalog.trait_ids traitMember selectedMember (semanticId.trans selectedId.symm)
  exact ⟨selectedMember, same ▸ head⟩

theorem predicates_fixed {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    (substitution : Substitution) :
    receipt.signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution substitution) = receipt.signature.scheme.predicates := by
  have trait := receipt.trait_origin checked
  exact methodAssumptions_applySubstitution_eq_self (SignatureCatalogWellFormed.ofCheckProgram checked)
    receipt.implementationMember receipt.methodMember trait.1 trait.2 substitution

/-- The catalog identities recover the same complete synthetic signature as
an independently retained executable-method selection. -/
theorem selection_signature {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {selected : ExecutableImplMethods.CheckedMethod}
    (selection : CoreLowering.CallableCoercionBodyProvenance.Selection program selected)
    (identity : retained.id = selected.id) :
    receipt.signature = selection.implementation.functionSignatureOfMethodWithTrait
      selection.trait selection.declaration := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have methodId : receipt.method.id = selection.declaration.id :=
    receipt.methodId.symm.trans (identity.trans selection.methodId)
  have unique : ((program.signatures.implementations.flatMap (·.methods)).map
      (fun method => method.id)).Nodup := by
    simpa only [List.map_flatMap] using catalog.implementation_method_ids
  have methodEq := eq_of_mem_of_nodup_map unique
    (List.mem_flatMap.mpr ⟨receipt.implementation, receipt.implementationMember, receipt.methodMember⟩)
    (List.mem_flatMap.mpr ⟨selection.implementation, selection.implementationMember, selection.methodMember⟩)
    methodId
  have owner := ((catalog.implementations_semantic receipt.implementation receipt.implementationMember).methods
    receipt.method receipt.methodMember).owner
  have implementationId : receipt.implementation.id = selection.implementation.id :=
    owner.symm.trans ((congrArg ProgramImplMethodId.implementation methodId).trans selection.methodOwner)
  have implementationEq := eq_of_mem_of_nodup_map catalog.implementation_ids
    receipt.implementationMember selection.implementationMember implementationId
  have traitEq : receipt.trait = selection.trait := by
    have lookup := receipt.traitLookup
    rw [methodEq] at lookup
    exact Option.some.inj (lookup.symm.trans selection.traitLookup)
  simp only [signature, implementationEq, methodEq, traitEq]

end MethodBodyReceipt

/-- The cached index and method-selection receipt remain attached to the same
retained original method. No ordinary-function membership is manufactured. -/
structure CachedMethodBody (compiled : SourceCoreCompiler.Compiled)
    (cached : SourceCoreCompiler.Cached) (retained : CheckedImplementationMethod) (fuel : Nat) where
  artifact : compiled.artifact? = some cached
  selected : CoreLowering.SelectedCompilationBodyTyping.MethodSource cached retained
  receipt : MethodBodyReceipt compiled.program retained fuel

theorem cached_method_body {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    {retained : CheckedImplementationMethod}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (artifact : compiled.artifact? = some cached)
    (selected : CoreLowering.SelectedCompilationBodyTyping.MethodSource cached retained) :
    Nonempty (CachedMethodBody compiled cached retained fuel) := by
  obtain ⟨index, named, method, atIndex, specialized, selection, member, identity, original⟩ := selected
  have memberOriginal : retained ∈ compiled.program.methods := by
    rw [← (compiled.artifact_fields artifact).1]
    exact member
  obtain ⟨receipt⟩ := MethodBodyReceipt.of_checked checked memberOriginal
  exact ⟨⟨artifact, ⟨index, named, method, atIndex, specialized, selection, member, identity, original⟩, receipt⟩⟩

end Solcore.SourceSemantics.SourceCompiledMethodFinalization
