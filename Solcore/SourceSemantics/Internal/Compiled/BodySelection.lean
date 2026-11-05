import Solcore.SourceSemantics.Internal.Compiled.Finalization
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms

/-!
# The selected body

A body with its ordinary or implementation-method origin.
`SourceCompiledLocalFinalization.BodySelection` is the carrier that the rest of the compiled route
shares. Static formation, normalized templates and the receipts of cached methods are here too.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedMethodReceipt
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledMethodNormalizedFormation
/-! The real implementation signature and finalizer supply normalized body
and ledger formation before any semantic body-typing judgment is available. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceRequirementFormation
open SourceInferenceNormalizedCoercionFormation

private theorem predicate_transport {source target : SourceSemantics.Context}
    {predicate : ProgramPredicate}
    (signatures : target.signatures = source.signatures)
    (parameters : target.typeParameters = source.typeParameters)
    (owner : target.currentDeclaration = source.currentDeclaration)
    (formed : PredicateWellFormed source predicate) : PredicateWellFormed target predicate := by
  refine ⟨StructuralSubstitution.TypeWellFormed.transportContext
    (source := source) signatures parameters owner formed.subject,
    fun argument present => StructuralSubstitution.TypeWellFormed.transportContext
      (source := source) signatures parameters owner (formed.arguments argument present), ?_⟩
  cases choice : predicate.trait <;> simpa only [choice, signatures] using formed.trait

namespace MethodBodyReceipt
variable {program : CheckedProgram} {retained : CheckedImplementationMethod} {fuel : Nat}

/-- Method assumptions use the implementation's rigid scope, including the
trait predicates instantiated at its actual head. -/
theorem predicates_formed {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    PredicatesWellFormed (signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates)
      receipt.signature.scheme.predicates := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementation := catalog.implementations_semantic receipt.implementation receipt.implementationMember
  have method := implementation.methods receipt.method receipt.methodMember
  obtain ⟨trait, traitMember, head, _exact, _range, inherited⟩ := implementation.trait_catalog
  have actual := receipt.trait_origin checked
  have idEq : trait.id = receipt.trait.id := by
    have same := head.symm.trans actual.2
    injection same
  have same := Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids traitMember actual.1 idEq
  subst trait
  intro predicate member
  change predicate ∈ receipt.implementation.methodAssumptions receipt.trait receipt.method at member
  simp only [ProgramImplementationSignature.methodAssumptions, List.mem_append] at member
  rcases member with (inheritedMember | implementationMember) | methodMember
  · have formed := implementation.predicates predicate (inherited predicate inheritedMember)
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters receipt.implementation.wherePredicates) rfl rfl rfl formed
  · have formed := implementation.predicates predicate implementationMember
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters receipt.implementation.wherePredicates) rfl rfl rfl formed
  · have formed := method.predicates predicate methodMember
    exact predicate_transport (source := signatureContext program.signatures receipt.implementation.id receipt.implementation.parameters (receipt.implementation.wherePredicates ++ receipt.method.wherePredicates)) rfl rfl rfl formed

theorem inferenceProgress {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    BodyInferenceProgress receipt.body := by
  have formation := Frontend.checkProgram_success_signature_formation checked
  have functions : ∀ candidate ∈ program.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
    intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have ready : (initial receipt.signature receipt.body.declaration).InferenceReady :=
    State.InferenceReady.initial _ _ _
  have returns : (Ty.productMany receipt.signature.returnTypes).VariablesBelow
      (initial receipt.signature receipt.body.declaration).inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member metavariable occurs
    rw [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
      ((receipt.header checked).return_types type member)] at occurs
    cases occurs
  have body := Detail.inferStatementsFuel_inferenceProperties ready formation functions returns receipt.body.inferred
  have returnBound := returns.weaken body.1.next_le
  have unified := Detail.unify_inferenceProgress body.2.1.solved body.2.2 returnBound receipt.body.unified
  have returned := Detail.unify_preserves_inferenceReady body.2.1 body.2.2 returnBound receipt.body.unified
  exact ⟨ready, returns, body.1, body.2.1, body.2.2, unified, returned,
    receipt.body.resources.progress_of_ready returned⟩

def normalizedContext (receipt : MethodBodyReceipt program retained fuel) : SourceSemantics.Context :=
  declarationContext program.signatures receipt.signature.id receipt.signature.scheme.parameters
    receipt.signature.scheme.predicates receipt.body.finalized.solvedRequirements

theorem normalizedFormationContext {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = program.signatures)
    (parameters : semantic.typeParameters = receipt.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some receipt.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context program.environment program.signatures receipt.signature receipt.body.declaration)
      receipt.body.finalized.substitution := by
  have catalog : SignatureCatalogWellFormed semantic.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical := receipt.canonical checked
  have declarationEq := (ProgramEnvironment.declaration?_sound receipt.body.declared).2
  have binders : TypeParameterBindersWellFormed semantic :=
    StructuralSubstitution.TypeParameterBindersWellFormed.transportContext parameters owner
      (SourceSemantics.SignatureParametersWellFormed.declarationContextBinders
        (signatures := program.signatures) canonical receipt.signature.scheme.predicates [])
  have scope : ProducerScope
      (context program.environment program.signatures receipt.signature receipt.body.declaration)
      semantic := {
    binders, signatures, parameters, residual, catalog
    owner := by simpa only [signature, context, ProgramTypeScope.ofDeclaration, declarationEq] using owner }
  have assumptions : ∀ predicate ∈ receipt.signature.scheme.predicates,
      PredicateWellFormed semantic predicate := by
    intro predicate member
    have formed := receipt.predicates_formed checked predicate member
    exact predicate_transport (source := signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates) signatures parameters owner formed
  refine {
    signatures := signatures
    catalog := catalog
    residual := residual
    assumptions := assumptions
    range := receipt.body.resources.producerRange scope
    scope := scope
    canonical := ?_
    validated := Frontend.checkProgram_success_signature_formation checked
    functionShapes := ?_ }
  · simpa only [signature, context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical
  · intro candidate member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2

theorem normalizedBodyFormation {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = program.signatures)
    (parameters : semantic.typeParameters = receipt.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some receipt.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (receipt.body.finalized.substitution.apply receipt.body.body.type) ∧
      NormalizedStateFormation semantic receipt.body.finalized.substitution receipt.body.body.state := by
  have formation := receipt.normalizedFormationContext checked signatures parameters owner residual
  have progress := receipt.inferenceProgress checked
  have entry : NormalizedStateFormation semantic receipt.body.finalized.substitution
      (initial receipt.signature receipt.body.declaration) := by
    apply NormalizedStateFormation.initial
    · intro entry member
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro entry member
      obtain ⟨parameter, present, rfl⟩ := List.mem_map.mp member
      have formed := (receipt.header checked).parameter_types parameter.2 (List.of_mem_zip present).2
      apply type_applySubstitution_residual residual formation.range
      exact TypeAdmissible.ofWellFormed
        (StructuralSubstitution.TypeWellFormed.transportContext
          (source := checkedBodyContext program.signatures receipt.signature retained.checked)
          signatures parameters owner formed)
  have returns : ∀ type ∈ receipt.signature.returnTypes,
      TypeAdmissible semantic (receipt.body.finalized.substitution.apply type) := by
    intro type member
    apply type_applySubstitution_residual residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := checkedBodyContext program.signatures receipt.signature retained.checked)
      signatures parameters owner ((receipt.header checked).return_types type member))
  have capture : NoCaptureNodes receipt.body.finalized.substitution receipt.body.body.state.nodes := by
    rw [← receipt.body.returned_nodes]
    exact NoCaptureNodes.of_finalizer receipt.body.resources
  exact inferStatementsFuel_normalized_formation semantic receipt.body.finalized.substitution
    fuel _ _ _ _ progress.initialReady (State.initial_nodesBelowNextOccurrence _ _ _)
    entry formation progress.returnBelow (normalized_productMany formation.scope.binders returns)
    _ receipt.body.inferred progress.final_substitution capture

theorem normalizedLedger {raw : Workspace.RawWorkspace}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) :
    ∀ requirement ∈ receipt.body.body.state.requirements,
      PredicateAdmissible receipt.normalizedContext
        (TypedTraitResolution.applySubstitution receipt.body.finalized.substitution requirement.predicate) :=
  (receipt.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end MethodBodyReceipt
end Solcore.SourceSemantics.SourceCompiledMethodFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedMethodInputs
/-! Complete actual method-checking inputs for a shared generalized body
consumer, recovered from the same cached method and raw compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceNormalizedCoercionFormation

namespace CachedMethodBody
variable {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
  {retained : CheckedImplementationMethod} {fuel : Nat}

/-- The executable cache validates the actual method specialization; reversing
that exact structural substitution supplies the original body's interfaces. -/
theorem interfaces (actual : CachedMethodBody compiled cached retained fuel) :
    ExecutableCoercionInterfaces.BodyInterfaces compiled.program.signatures retained.checked := by
  obtain ⟨index, named, method, atIndex, same, selection, _member, _identity, original⟩ := actual.selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [original, same] using selection.specialized
  have recorded := CoreLowering.SelectedCompilationCoercionInterfaces.cached cached atIndex
  rw [(CoreLowering.CallableCoercionBodyProvenance.specialization_fields accepted).1] at recorded
  have originalInterfaces := CoreLowering.SelectedCompilationCoercionInterfaces.of_applied recorded
  simpa only [(compiled.artifact_fields actual.artifact).1] using originalInterfaces

end CachedMethodBody

/-- All formation and continuation facts belong to this receipt's original
method and finalizer. Semantic body typing and generalized barriers are not
fields of this input record. -/
structure MethodBodyInputs {program : CheckedProgram} {retained : CheckedImplementationMethod} {fuel : Nat}
    (receipt : MethodBodyReceipt program retained fuel) : Prop where
  header : CheckedBodyHeaderWellFormed program.signatures receipt.signature retained.checked
  canonical : SignatureParametersWellFormed receipt.signature.id receipt.signature.scheme.parameters
  predicates : PredicatesWellFormed
    (signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates)
    receipt.signature.scheme.predicates
  predicatesFixed : receipt.signature.scheme.predicates.map
    (TypedTraitResolution.applySubstitution retained.checked.substitution) = receipt.signature.scheme.predicates
  progress : BodyInferenceProgress receipt.body
  normalized : TypeAdmissible receipt.normalizedContext
      (receipt.body.finalized.substitution.apply receipt.body.body.type) ∧
    NormalizedStateFormation receipt.normalizedContext receipt.body.finalized.substitution receipt.body.body.state

theorem MethodBodyReceipt.inputs {raw : Workspace.RawWorkspace} {program : CheckedProgram}
    {retained : CheckedImplementationMethod} {fuel : Nat}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) : MethodBodyInputs receipt :=
  ⟨receipt.header checked, receipt.canonical checked, receipt.predicates_formed checked,
    receipt.predicates_fixed checked retained.checked.substitution, receipt.inferenceProgress checked,
    receipt.normalizedBodyFormation checked rfl rfl rfl rfl⟩

/-- Public compiler success supplies the original method-checking carrier,
its executable interfaces and the complete normalized inference inputs. -/
theorem compile_cached_method_inputs {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    {retained : CheckedImplementationMethod}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    (selected : CoreLowering.SelectedCompilationBodyTyping.MethodSource cached retained) :
    ∃ actual : CachedMethodBody compiled cached retained options.checkingFuel,
      MethodBodyInputs actual.receipt ∧
      ExecutableCoercionInterfaces.BodyInterfaces compiled.program.signatures retained.checked := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  obtain ⟨actual⟩ := cached_method_body checked artifact selected
  exact ⟨actual, actual.receipt.inputs checked, actual.interfaces⟩

end Solcore.SourceSemantics.SourceCompiledMethodFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBodySelection
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBodyCallIndex
/-! A selected ordinary or method body supplies the exact root inference call
from its successful checker receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def inferenceCall (selected : BodySelection compiled row fuel) : CallIndex :=
  .statements fuel
    (context compiled.program.environment compiled.program.signatures
      selected.signature selected.body.declaration)
    selected.signature.source.value.body.value
    (Ty.productMany selected.signature.returnTypes)
    (initial selected.signature selected.body.declaration)
    selected.body.body

theorem inferenceCall_accepted (selected : BodySelection compiled row fuel) :
    selected.inferenceCall.Accepted :=
  selected.body.inferred

def InferenceCall (selected : BodySelection compiled row fuel) : CallIndex → Prop :=
  CallOccurrence selected.inferenceCall

theorem inferenceCall_root (selected : BodySelection compiled row fuel) :
    selected.InferenceCall selected.inferenceCall :=
  .root selected.inferenceCall_accepted

theorem inferenceCall_closed (selected : BodySelection compiled row fuel) :
    ChildClosed selected.InferenceCall :=
  CallOccurrence.childClosed selected.inferenceCall

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
/-! Static formation and normalized inference come from the selected body's
actual catalog origin. The shared carrier introduces no typing assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledMethodFinalization SourceInferenceRequirementFormation
open SourceInferenceNormalizedCoercionFormation

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem header (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    CheckedBodyHeaderWellFormed compiled.program.signatures selected.signature selected.original := by
  apply selected.of_origins
  · intro ordinary
    obtain ⟨signature, member, formed⟩ :=
      checkedFunctionHeaderWellFormed_ofCheckProgram checked ordinary.originalMember
    have same := eq_of_mem_of_nodup_map
      (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids member ordinary.signatureMember
      (formed.declaration_eq.symm.trans (checkFunctionBody_success_declaration ordinary.body.accepted))
    subst signature
    exact formed
  · intro retained receipt _ _
    exact receipt.header checked

theorem canonical (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureParametersWellFormed selected.signature.id selected.signature.scheme.parameters := by
  apply selected.of_origins
  · intro ordinary
    exact (Frontend.checkProgram_success_signature_parameters_wellFormed checked).functions
      ordinary.signature ordinary.signatureMember
  · intro retained receipt _ _
    exact receipt.canonical checked

theorem predicates_fixed (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) (substitution : Substitution) :
    selected.signature.scheme.predicates.map (TypedTraitResolution.applySubstitution substitution) =
      selected.signature.scheme.predicates := by
  apply selected.of_origins
  · intro ordinary
    exact ((Frontend.checkProgram_success_signature_formation checked).functions
      ordinary.signature ordinary.signatureMember).2.2.apply_eq_self substitution
  · intro retained receipt _ _
    exact receipt.predicates_fixed checked substitution

theorem returns_closed (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 := by
  apply Ty.variablesBelow_productMany
  intro type member metavariable occurs
  rw [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
    ((selected.header checked).return_types type member)] at occurs
  cases occurs

theorem inferenceProgress (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    BodyInferenceProgress selected.body := by
  apply selected.of_origins
  · intro ordinary
    exact ordinary.inferenceProgress checked
  · intro retained receipt _ _
    exact receipt.inferenceProgress checked

def normalizedContext (selected : BodySelection compiled row fuel) : SourceSemantics.Context :=
  declarationContext compiled.program.signatures selected.signature.id
    selected.signature.scheme.parameters selected.signature.scheme.predicates
    selected.body.finalized.solvedRequirements

theorem normalizedFormationContext (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    InferenceFormationContext semantic
      (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized.substitution := by
  revert parameters owner
  apply selected.of_origins
  · intro ordinary parameters owner
    exact ordinary.normalizedFormationContext checked signatures parameters owner residual
  · intro retained receipt _ _ parameters owner
    exact receipt.normalizedFormationContext checked signatures parameters owner residual

theorem normalizedBodyFormation (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    TypeAdmissible semantic (selected.body.finalized.substitution.apply selected.body.body.type) ∧
      NormalizedStateFormation semantic selected.body.finalized.substitution selected.body.body.state := by
  revert parameters owner
  apply selected.of_origins
  · intro ordinary parameters owner
    exact ordinary.normalizedBodyFormation checked signatures parameters owner residual
  · intro retained receipt _ _ parameters owner
    exact receipt.normalizedBodyFormation checked signatures parameters owner residual

theorem normalizedLedger (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ requirement ∈ selected.body.body.state.requirements,
      PredicateAdmissible selected.normalizedContext
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate) :=
  (selected.normalizedBodyFormation checked rfl rfl rfl rfl).2.requirements

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedBodySelection
/-! Actual method cache positions supply the shared body carrier. The method
receipt and executable specialization remain attached to the same source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

namespace MethodBodyReceipt
variable {compiled : SourceCoreCompiler.Compiled} {retained : CheckedImplementationMethod}
  {fuel : Nat} {row : SourceSpecialization.SpecializedFunction}

def toBodySelection (receipt : MethodBodyReceipt compiled.program retained fuel)
    (member : retained ∈ compiled.program.methods)
    (specialized : row.function =
      SourceSpecialization.applyCheckedFunction row.parameterSubstitution retained.checked) :
    BodySelection compiled row fuel := {
  original := retained.checked
  signature := receipt.signature
  body := receipt.body
  origin := .method member receipt.implementationMember receipt.methodMember receipt.traitLookup receipt.methodId
  specialized }

theorem toBodySelection_body (receipt : MethodBodyReceipt compiled.program retained fuel)
    (member : retained ∈ compiled.program.methods)
    (specialized : row.function =
      SourceSpecialization.applyCheckedFunction row.parameterSubstitution retained.checked) :
    (receipt.toBodySelection member specialized).body = receipt.body := rfl

end MethodBodyReceipt

theorem CachedMethodBody.bodySelection
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    {retained : CheckedImplementationMethod} {fuel : Nat}
    (actual : CachedMethodBody compiled cached retained fuel) :
    ∃ (row : SourceSpecialization.SpecializedFunction)
      (selected : BodySelection compiled row fuel),
      selected.original = retained.checked ∧
      selected.signature = actual.receipt.signature ∧
      HEq selected.body actual.receipt.body ∧
      (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
        cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) ∧
      ExecutableCoercionInterfaces.SourceInterfaces compiled.program.signatures
        selected.body.finalized.solvedRequirements selected.body.finalized.typedSource := by
  obtain ⟨index, named, method, atIndex, same, selection, member, _identity, original⟩ := actual.selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [original, same] using selection.specialized
  have retainedMember : retained ∈ compiled.program.methods := by
    rw [← (compiled.artifact_fields actual.artifact).1]
    exact member
  let selected := actual.receipt.toBodySelection retainedMember
    (CoreLowering.CallableCoercionBodyProvenance.specialization_fields accepted).1
  refine ⟨named.specialized, selected, rfl, rfl, HEq.rfl, ⟨index, named, atIndex, rfl⟩, ?_⟩
  change ExecutableCoercionInterfaces.SourceInterfaces compiled.program.signatures
    actual.receipt.body.finalized.solvedRequirements actual.receipt.body.finalized.typedSource
  rw [← actual.receipt.body.solved, ← actual.receipt.body.source]
  exact actual.interfaces

end Solcore.SourceSemantics.SourceCompiledMethodFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
/-! The real public compilation and every final cached row supply the closed
non-template branch of the original finalizer ledger. Later helper and method
rows use their actual accepted preparation and specialization receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
open Frontend SourceInference TypeSystem
open SourceCompiledLocalFinalization
open SourceSpecializedNonTemplateLedger

def Closed (row : SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ requirement ∈ row.function.solvedRequirements,
    requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody →
      TypedTraitResolution.predicateVariables requirement.predicate = []

theorem initial_closed {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) : Closed row := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, _, signature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  exact fun _ present ordinary => specialized_closed specialized present ordinary

/-- This includes rows added by implementation-method selection and their
ordinary descendants, without initial-worklist membership. -/
theorem cached_closed (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    Closed named.specialized := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CoreLowering.CallablePreparedFinalSpecializationOrigins.of_default_preparation prepared _ member
  exact fun _ present ordinary => specialized_closed specialized present ordinary

theorem finalized_closed {row : SourceSpecialization.SpecializedFunction}
    {original : CheckedFunction} {environment : ProgramEnvironment}
    {signatures : ProgramSignatures} {signature : ProgramFunctionSignature} {fuel : Nat}
    (body : BodyReceipt environment signatures signature fuel original)
    (same : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original)
    (closed : Closed row)
    {requirement : SolvedRequirement}
    (member : requirement ∈ body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  apply original_closed_of_application closed same
  · simpa only [body.solved] using member
  · simpa only [body.source] using ordinary

theorem selected_closed {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (closed : Closed row)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  finalized_closed selected.body selected.specialized closed member ordinary

theorem compile_selected_closed {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (rowMember : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  selected_closed selected (initial_closed accepted rowMember) member ordinary

theorem cached_selected_closed {compiled : SourceCoreCompiler.Compiled}
    (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {row : SourceSpecialization.SpecializedFunction} (same : named.specialized = row)
    {fuel : Nat} (selected : Selected compiled row fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  apply selected_closed selected _ member ordinary
  simpa only [same] using cached_closed cached position

end Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledNormalizedTemplates
/-! Whole-body producer formation follows the real solver's row correspondence
to the exact templates owned by retained generalized initializers. No predicate
formation is inferred from evidence validity or template ownership alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceNormalizedCoercionFormation

private theorem solved_predicates_formed
    {context : SourceInference.Context} {state : State}
    {rows : List Requirement} {solved : List SolvedRequirement}
    {semantic : SourceSemantics.Context}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧ row.predicate = Detail.applyPredicate state requirement.predicate ∧
      Detail.solveRequirementEvidence context state requirement = .ok row.evidence) rows solved)
    (formed : ∀ requirement ∈ rows, PredicateAdmissible semantic
      (Detail.applyPredicate state requirement.predicate)) :
    ∀ row ∈ solved, PredicateAdmissible semantic row.predicate := by
  induction corresponds with
  | nil => simp
  | @cons requirement row requirements solved head tail ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · rw [head.2.1]
      exact formed requirement (by simp)
    · exact ih (fun requirement member => formed requirement (by simp [member])) candidate member

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem normalizedSolvedLedger (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    ∀ requirement ∈ selected.body.finalized.solvedRequirements,
      PredicateAdmissible semantic requirement.predicate := by
  apply solved_predicates_formed (solveRequirements_corresponds selected.body.resources.solve_success)
  intro requirement member
  rw [selected.body.solver_requirements] at member
  have formed := (selected.normalizedBodyFormation checked signatures parameters owner residual).2.requirements
    requirement member
  simpa only [Detail.applyPredicate, ← selected.body.resources.substitution_eq] using formed

/-- A retained template's predicate equals the exact solved row whose
formation was proved through the complete original producer traversal. -/
theorem normalizedTemplatePredicate (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true)
    {template : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource template) :
    PredicateAdmissible semantic template.requirement.predicate := by
  obtain ⟨requirement, filtered, _, predicateEq, _⟩ := selected.body.resources.ledger.template_exact contains
  have present : requirement ∈ selected.body.finalized.solvedRequirements := by
    have filteredMember := filtered.symm ▸ List.mem_singleton_self requirement
    exact (List.mem_filter.mp filteredMember).1
  exact predicateEq ▸ selected.normalizedSolvedLedger checked signatures parameters owner residual requirement present

/-- Any actual finalized initializer receives qualified predicate formation,
including nested declarations and for-header items. -/
theorem normalizedBindingPredicates (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binding : InitializedLetBinding}
    (retained : binding ∈ initializedLetBindings selected.body.finalized.typedSource) :
    ∀ requirement ∈ binding.binder.schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target binding.binder) requirement.predicate := by
  intro requirement member
  apply selected.normalizedTemplatePredicate checked
    (semantic := localSchemeInitializerContext target binding.binder) signatures parameters owner residual
    (template := {binder := binding.binder, initializer := binding.initializer, requirement})
  exact List.mem_flatMap.mpr ⟨binding, retained, List.mem_map.mpr ⟨requirement, member, rfl⟩⟩

/-- The input is a real raw retained template, transformed by this exact
finalizer. It directly supplies the finalPredicates certificate interface. -/
theorem originalBindingPredicates (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binder : TypedBinder} {initializer : NodeId}
    (retained : ∀ requirement ∈ binder.schemeRequirements,
      ContainsLocalSchemeTemplate
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
        {binder, initializer, requirement}) :
    ∀ requirement ∈ (binder.applySubstitution selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (binder.applySubstitution selected.body.finalized.substitution)) requirement.predicate := by
  intro requirement member
  rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  apply selected.normalizedTemplatePredicate checked
    (semantic := localSchemeInitializerContext target
      (binder.applySubstitution selected.body.finalized.substitution)) signatures parameters owner residual
    (template := FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution
      {binder, initializer, requirement := original})
  rw [selected.body.resources.source_eq]
  exact FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
    selected.body.finalized.substitution (retained original originalMember)

end BodySelection


namespace Selected
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem normalizedSolvedLedger (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    ∀ requirement ∈ selected.body.finalized.solvedRequirements,
      PredicateAdmissible semantic requirement.predicate :=
  selected.toBodySelection.normalizedSolvedLedger checked signatures parameters owner residual

theorem normalizedTemplatePredicate (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true)
    {template : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource template) :
    PredicateAdmissible semantic template.requirement.predicate :=
  selected.toBodySelection.normalizedTemplatePredicate checked signatures parameters owner residual contains

theorem normalizedBindingPredicates (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binding : InitializedLetBinding}
    (retained : binding ∈ initializedLetBindings selected.body.finalized.typedSource) :
    ∀ requirement ∈ binding.binder.schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target binding.binder) requirement.predicate :=
  selected.toBodySelection.normalizedBindingPredicates checked signatures parameters owner residual retained

theorem originalBindingPredicates (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binder : TypedBinder} {initializer : NodeId}
    (retained : ∀ requirement ∈ binder.schemeRequirements,
      ContainsLocalSchemeTemplate
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
        {binder, initializer, requirement}) :
    ∀ requirement ∈ (binder.applySubstitution selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (binder.applySubstitution selected.body.finalized.substitution)) requirement.predicate :=
  selected.toBodySelection.originalBindingPredicates checked signatures parameters owner residual retained

end Selected

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end
