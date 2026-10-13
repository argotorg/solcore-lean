import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection

/-! Finite checks retain generic implementation parameters and complete method
predicates. The final compiler table supplies authentic evidence origins. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
open Core Frontend SourceInference

structure ImplementationFormation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters.Nodup
  variables : TypedTraitResolution.predicateVariables implementation.head = []
  headParameters : ∀ parameter ∈ TypedTraitResolution.predicateParameters implementation.head,
    parameter ∈ implementation.parameters
  methodParameters : ∀ method ∈ implementation.methods, ∀ predicate ∈ method.wherePredicates,
    ∀ parameter ∈ TypedTraitResolution.predicateParameters predicate, parameter ∈ implementation.parameters

theorem ImplementationFormation.formed {implementation : ProgramImplementationSignature}
    (formation : ImplementationFormation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨formation.parameters, ?_, ?_, ?_⟩
  · intro metavariable occurs
    have present := TypedTraitResolution.mem_predicateVariables_iff.mpr occurs
    rw [formation.variables] at present
    cases present
  · intro parameter occurs
    exact formation.headParameters parameter (TypedTraitResolution.mem_predicateParameters_iff.mpr occurs)
  · intro predicate present parameter occurs
    exact formation.methodParameters method member predicate present parameter
      (TypedTraitResolution.mem_predicateParameters_iff.mpr occurs)

def implementation? (implementation : ProgramImplementationSignature) :
    Option (PLift (ImplementationFormation implementation)) :=
  if parameters : implementation.parameters.Nodup then
    if variables : TypedTraitResolution.predicateVariables implementation.head = [] then
      if head : (TypedTraitResolution.predicateParameters implementation.head).all
          (fun parameter => decide (parameter ∈ implementation.parameters)) = true then
        if methods : implementation.methods.all (fun method => method.wherePredicates.all
            (fun predicate => (TypedTraitResolution.predicateParameters predicate).all
              (fun parameter => decide (parameter ∈ implementation.parameters)))) = true then
          some ⟨⟨parameters, variables,
            fun parameter member => of_decide_eq_true (List.all_eq_true.mp head parameter member),
            by
              intro method member predicate present parameter occurs
              exact of_decide_eq_true (List.all_eq_true.mp
                (List.all_eq_true.mp (List.all_eq_true.mp methods method member) predicate present)
                parameter occurs)⟩⟩
        else none
      else none
    else none
  else none

def implementations? : (implementations : List ProgramImplementationSignature) →
    Option (PLift (∀ implementation ∈ implementations, ImplementationFormation implementation))
  | [] => some ⟨by intro implementation member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← implementation? first
      let ⟨tail⟩ ← implementations? rest
      pure ⟨by
        intro implementation member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail implementation member⟩

/-- The original finite signatures and actual final specialization table are
checked independently of any execution or Source typing assumption. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Option (PLift (CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)) := do
  let ⟨formed⟩ ← implementations? compiled.sourceProgram.signatures.implementations
  let ⟨ready⟩ ← CallableMethodOriginTable.validate compiled.sourceProgram
    compiled.indexed.base.plan.specializations
  pure ⟨⟨⟨fun implementation member _method methodMember =>
    (formed implementation member).formed methodMember⟩, ready⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
