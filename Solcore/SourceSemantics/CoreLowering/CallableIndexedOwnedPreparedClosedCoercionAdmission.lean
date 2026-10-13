import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection

/-! Finite checks on original implementation heads, predicates and actual
selected method shapes construct the closed coercion catalog. Full Source
well-formedness remains an independent premise of its semantic consumer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
open Core Frontend SourceInference

structure ClosedImplementation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters = []
  variables : TypedTraitResolution.predicateVariables implementation.head = []
  headParameters : TypedTraitResolution.predicateParameters implementation.head = []
  predicates : implementation.wherePredicates = []
  methods : ∀ method ∈ implementation.methods, method.wherePredicates = []

theorem ClosedImplementation.formed {implementation : ProgramImplementationSignature}
    (closed : ClosedImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨closed.parameters ▸ List.nodup_nil, ?_, ?_, ?_⟩
  · intro metavariable occurs
    have present := TypedTraitResolution.mem_predicateVariables_iff.mpr occurs
    rw [closed.variables] at present
    cases present
  · intro parameter occurs
    have present := TypedTraitResolution.mem_predicateParameters_iff.mpr occurs
    rw [closed.headParameters] at present
    cases present
  · intro predicate present _parameter _occurs
    rw [closed.methods method member] at present
    cases present

def implementation? (implementation : ProgramImplementationSignature) :
    Option (PLift (ClosedImplementation implementation)) :=
  if parameters : implementation.parameters = [] then
    if variables : TypedTraitResolution.predicateVariables implementation.head = [] then
      if headParameters : TypedTraitResolution.predicateParameters implementation.head = [] then
        if predicates : implementation.wherePredicates = [] then
          if methods : implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true then
            some ⟨⟨parameters, variables, headParameters, predicates,
              fun method member => of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩
          else none
        else none
      else none
    else none
  else none

def implementations? : (implementations : List ProgramImplementationSignature) →
    Option (PLift (∀ implementation ∈ implementations, ClosedImplementation implementation))
  | [] => some ⟨by intro implementation member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← implementation? first
      let ⟨tail⟩ ← implementations? rest
      pure ⟨by
        intro implementation member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail implementation member⟩

/-- Every implementation and trait in the original finite signatures is checked.
The shape validator retains all original sites in the final specialization plan. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Option (PLift (CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)) := do
  let ⟨closed⟩ ← implementations? compiled.sourceProgram.signatures.implementations
  if traits : compiled.sourceProgram.signatures.traits.all
      (fun trait => decide (trait.wherePredicates = [])) = true then
    let ⟨shapes⟩ ← CallableCoercionSourceShapeTable.validate compiled.sourceProgram
      compiled.indexed.base.plan.specializations
    pure ⟨{
      shapes := shapes
      parameters := fun implementation member _method _methodMember => (closed implementation member).parameters
      formed := fun implementation member method methodMember => (closed implementation member).formed methodMember
      assumptions := by
        intro implementation member method methodMember trait traitMember
        have traitEmpty : trait.wherePredicates = [] := of_decide_eq_true (List.all_eq_true.mp traits trait traitMember)
        simp [ProgramImplementationSignature.methodAssumptions, traitEmpty,
          (closed implementation member).predicates, (closed implementation member).methods method methodMember] }⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
