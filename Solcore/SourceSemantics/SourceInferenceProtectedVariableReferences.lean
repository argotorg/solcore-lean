import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_closed {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) : type.VariablesBelow 0 := by
  intro metavariable member
  simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed] at member

theorem declaration_reference_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {signature : ProgramFunctionSignature}
    {source : Syntax.Expr} {id : ExpressionId} {name : String} {expected : Option Ty}
    {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted :
      let instantiated := signature.scheme.instantiate state.inference.next
      let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
      let batch := advanced.addRequirementsWithIds instantiated.predicates
      Detail.recordExpressionWithExpected context source id instantiated.body
        (.reference name (.declaration (DeclarationInstantiation.ofInstantiated signature instantiated)))
        batch.1 expected batch.2 = .ok result) :
    FixesProtected protectedVars result.2 := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  let batch := advanced.addRequirementsWithIds instantiated.predicates
  have formed := catalog.functions_semantic signature member
  have batchInference : batch.2.inference = advanced.inference := requirementBatch_inference _ _
  have sameSubstitution : batch.2.inference.substitution = state.inference.substitution := by
    simpa only [advanced] using congrArg InferState.substitution batchInference
  have initialTransport : SafeTransport protectedVars state batch.2 := .of_substitution_eq sameSubstitution
  have bodyClosed : signature.scheme.body.VariablesBelow 0 := by
    rw [formed.scheme_body]
    intro metavariable occurs
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with occurs | occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.parameter_types type member)) metavariable occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.return_types type member)) metavariable occurs
  have bodySafe : Safe protectedVars advanced instantiated.body :=
    safe_parameterApply (declaration_instantiation_private signature.scheme ready bound)
      (safe_closed _ _ bodyClosed)
  have completion : SafeTransport protectedVars advanced batch.2 :=
    .of_substitution_eq (congrArg InferState.substitution batchInference)
  exact recordExpressionWithExpected_fixes_protected (fixed.of_substitution_eq sameSubstitution)
    (completion _ bodySafe) (fun type member => initialTransport _ (expectedSafe type member)) accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
