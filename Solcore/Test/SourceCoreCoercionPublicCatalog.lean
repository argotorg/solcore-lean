import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ClosedImplementation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters = []
  subject : implementation.head.subject = .word ∨ implementation.head.subject = .bool
  arguments : implementation.head.arguments = [] ∨ implementation.head.arguments = [.word]
  predicates : implementation.wherePredicates = []
  methods : ∀ method, method ∈ implementation.methods → method.wherePredicates = []

theorem ClosedImplementation.formed {implementation : ProgramImplementationSignature}
    (closed : ClosedImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨closed.parameters ▸ List.nodup_nil, ?_, ?_, ?_⟩
  · intro metavariable
    rcases closed.arguments with args | args <;> rcases closed.subject with scalar | scalar <;>
      simp [TypedTraitResolution.VariableOccursInPredicate, scalar, args, TypeSystem.Ty.word, TypeSystem.Ty.bool, TypeSystem.Ty.freeVariables]
  · intro parameter occurs
    have noWord : ¬ TypeSystem.TypeParameterOccurs parameter .word := by intro h; cases h
    have noBool : ¬ TypeSystem.TypeParameterOccurs parameter .bool := by intro h; cases h
    rcases closed.arguments with args | args <;> rcases closed.subject with scalar | scalar <;>
      simp [TypedTraitResolution.ParameterOccursInPredicate, scalar, args, noWord, noBool] at occurs
  · intro predicate predicateMember parameter _occurs
    rw [closed.methods method member] at predicateMember
    cases predicateMember

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeClosedImplementation (implementation : ProgramImplementationSignature) :
    IO (PLift (ClosedImplementation implementation)) := do
  let ⟨parameters⟩ ← observed (implementation.parameters = []) "method implementation parameters"
  let ⟨subject⟩ ← observed (implementation.head.subject = .word ∨ implementation.head.subject = .bool) "method implementation subject"
  let ⟨arguments⟩ ← observed (implementation.head.arguments = [] ∨ implementation.head.arguments = [.word]) "method implementation head arguments"
  let ⟨predicates⟩ ← observed (implementation.wherePredicates = []) "method implementation predicates"
  let ⟨methods⟩ ← observed (implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true) "method predicates"
  return ⟨⟨parameters, subject, arguments, predicates, fun method member =>
    of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩

private def observeClosedImplementations : (implementations : List ProgramImplementationSignature) →
    IO (PLift (∀ implementation, implementation ∈ implementations → ClosedImplementation implementation))
  | [] => pure ⟨by intro implementation member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← observeClosedImplementation first
    let ⟨tail⟩ ← observeClosedImplementations rest
    return ⟨by
      intro implementation member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail implementation member⟩

def observeMethodCatalog (fixture : CompiledFixture) :
    IO (PLift (CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)) := do
  let ⟨closed⟩ ← observeClosedImplementations fixture.recipe.compiled.sourceProgram.signatures.implementations
  let ⟨traits⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.traits.all
    (fun trait => decide (trait.wherePredicates = [])) = true) "method trait predicates"
  let some ⟨shapes⟩ := CallableCoercionSourceShapeTable.validate fixture.recipe.compiled.sourceProgram fixture.recipe.compiled.indexed.base.plan.specializations
    | throw (IO.userError "actual coercion method source shapes")
  return ⟨{
    shapes := shapes
    parameters := fun implementation member _method _methodMember => (closed implementation member).parameters
    formed := fun implementation member method methodMember => (closed implementation member).formed methodMember
    assumptions := by
      intro implementation member method methodMember trait traitMember
      have traitEmpty : trait.wherePredicates = [] := of_decide_eq_true (List.all_eq_true.mp traits trait traitMember)
      simp [ProgramImplementationSignature.methodAssumptions, traitEmpty,
        (closed implementation member).predicates, (closed implementation member).methods method methodMember] }⟩

theorem CompiledFixture.loaded (fixture : CompiledFixture) :
    ∃ loaded, Frontend.checkLoadedProgram loaded 1024 = .ok fixture.recipe.compiled.sourceProgram := by
  obtain ⟨loaded, _loaded, checked⟩ := checkProgram_success_load fixture.checked
  exact ⟨loaded, fixture.sameProgram.symm ▸ checked⟩

end Tests.SourceCoreCoercionPublic
