import Solcore.Test.SourceCoreMethodOwnEvidenceFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure GenericImplementation (implementation : ProgramImplementationSignature) : Prop where
  head : ∃ parameter, implementation.parameters = [parameter] ∧ implementation.head.subject = .parameter parameter
  arguments : implementation.head.arguments = []
  methods : ∀ method, method ∈ implementation.methods → method.wherePredicates = []

theorem GenericImplementation.formed {implementation : ProgramImplementationSignature}
    (given : GenericImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  obtain ⟨parameter, parameters, subject⟩ := given.head
  refine ⟨parameters ▸ List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_, ?_, ?_⟩
  · intro metavariable
    simp [TypedTraitResolution.VariableOccursInPredicate, subject, given.arguments, TypeSystem.Ty.freeVariables]
  · intro actual occurs
    have same : parameter = actual := by
      simpa [TypedTraitResolution.ParameterOccursInPredicate, subject, given.arguments,
        TypeSystem.TypeParameterOccurs] using occurs
    rw [parameters, ← same]
    simp
  · intro predicate predicateMember actual _occurs
    rw [given.methods method member] at predicateMember
    cases predicateMember

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeGenericImplementation (implementation : ProgramImplementationSignature) :
    IO (PLift (GenericImplementation implementation)) := do
  match parameters : implementation.parameters with
  | [parameter] =>
    let ⟨subject⟩ ← observed (implementation.head.subject = .parameter parameter) "generic implementation head"
    let ⟨arguments⟩ ← observed (implementation.head.arguments = []) "method implementation head arguments"
    let ⟨methods⟩ ← observed (implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true) "method predicates"
    return ⟨⟨⟨parameter, parameters, subject⟩, arguments, fun method member =>
      of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩
  | _ => throw (IO.userError "generic implementation parameter")

private def observeGenericImplementations : (implementations : List ProgramImplementationSignature) →
    IO (PLift (∀ implementation, implementation ∈ implementations → GenericImplementation implementation))
  | [] => pure ⟨by intro implementation member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← observeGenericImplementation first
    let ⟨tail⟩ ← observeGenericImplementations rest
    return ⟨by
      intro implementation member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail implementation member⟩

/-- The actual final compiler table issues the method evidence prerequisites.
Implementation assumptions are retained, while complete dictionary agreement
is checked internally by the executable resolver receipt. -/
def observeMethodCatalog (fixture : CompiledFixture) :
    IO (PLift (CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)) := do
  let compiled := fixture.recipe.compiled
  let ⟨shapes⟩ ← observeGenericImplementations compiled.sourceProgram.signatures.implementations
  let some ⟨ready⟩ := CallableMethodResolverTable.validate compiled.sourceProgram compiled.indexed.base.plan.specializations
    | throw (IO.userError "actual method materializer/resolver table is unsupported")
  let trait : ProgramTraitId := .declaration fixture.mark.id
  let rules := compiled.sourceProgram.signatures.resolutionRules
  let ⟨entries⟩ ← observed (rules.all (fun rule => decide
    (rule.head.trait = trait → rule.id = fixture.markImplementation.id ∧ rule.wherePredicates = [])) = true)
    "actual Mark evidence catalog"
  let leaf : LeafTraitEvidenceCoherence.Catalog rules trait fixture.markImplementation.id :=
    ⟨fun rule member => of_decide_eq_true (List.all_eq_true.mp entries rule member)⟩
  let some ⟨coherent⟩ := CachedMethodEvidenceCoherence.of_leaf? compiled leaf
    | throw (IO.userError "actual cached method evidence coherence is unsupported")
  return ⟨⟨⟨fun implementation member _method methodMember =>
    (shapes implementation member).formed methodMember⟩, ready, coherent⟩⟩

theorem CompiledFixture.loaded (fixture : CompiledFixture) :
    ∃ loaded, Frontend.checkLoadedProgram loaded 1024 = .ok fixture.recipe.compiled.sourceProgram := by
  obtain ⟨loaded, _loaded, checked⟩ := checkProgram_success_load fixture.checked
  exact ⟨loaded, fixture.sameProgram.symm ▸ checked⟩

end Tests.SourceCoreMethodOwnEvidence
