import Solcore.Test.SourceCoreMethodGenericSubstitutionFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodGenericSubstitution
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure GenericImplementation (implementation : ProgramImplementationSignature) : Prop where
  head : ∃ parameter, implementation.parameters = [parameter] ∧ implementation.head.subject = .parameter parameter
  arguments : implementation.head.arguments = []
  predicates : implementation.wherePredicates = []
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
    let ⟨predicates⟩ ← observed (implementation.wherePredicates = []) "method implementation predicates"
    let ⟨methods⟩ ← observed (implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true) "method predicates"
    return ⟨⟨⟨parameter, parameters, subject⟩, arguments, predicates, fun method member =>
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

def observeMethodCatalog (fixture : CompiledFixture) :
    IO (PLift (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)) := do
  let ⟨shapes⟩ ← observeGenericImplementations fixture.recipe.compiled.sourceProgram.signatures.implementations
  let ⟨traits⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.traits.all
    (fun trait => decide (trait.wherePredicates = [])) = true) "method trait predicates"
  return ⟨{
    formed := fun implementation member method methodMember => (shapes implementation member).formed methodMember
    assumptions := by
      intro implementation member method methodMember trait traitMember
      have traitEmpty : trait.wherePredicates = [] := of_decide_eq_true (List.all_eq_true.mp traits trait traitMember)
      simp [ProgramImplementationSignature.methodAssumptions, traitEmpty,
        (shapes implementation member).predicates, (shapes implementation member).methods method methodMember] }⟩

theorem CompiledFixture.loaded (fixture : CompiledFixture) :
    ∃ loaded, Frontend.checkLoadedProgram loaded 1024 = .ok fixture.recipe.compiled.sourceProgram := by
  obtain ⟨loaded, _loaded, checked⟩ := checkProgram_success_load fixture.checked
  exact ⟨loaded, fixture.sameProgram.symm ▸ checked⟩

end Tests.SourceCoreMethodGenericSubstitution
