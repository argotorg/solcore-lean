import Solcore.SourceSemantics.Coercions

/-!
Declarative profiles for resolved source calls.

These relations validate the call metadata retained by the occurrence graph.
They do not enumerate overload candidates, rank conversions, or run the source
checker.  Argument-expression typing is supplied by the main static-semantics
judgment.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A direct call instantiation exposes the exact catalog parameter list,
bundled result type, and instantiated declaration predicates. -/
inductive DeclarationApplicationValid (context : Context)
    (instantiation : DeclarationInstantiation) :
    List TypeSystem.Ty → TypeSystem.Ty → List ProgramPredicate → Prop where
  | intro
      {signature : ProgramFunctionSignature}
      {parameterTypes : List TypeSystem.Ty}
      {resultType : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      (signature_mem : signature ∈ context.signatures.functions)
      (valid : SourceSemantics.DeclarationInstantiation.Admissible
        context instantiation)
      (declaration_eq : instantiation.declaration = signature.id)
      (parameter_types_eq :
        signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            instantiation.parameterSubstitution) = parameterTypes)
      (result_type_eq :
        TypeSystem.ParameterSubstitution.apply
          instantiation.parameterSubstitution
          (TypeSystem.Ty.productMany signature.returnTypes) = resultType)
      (function_type_eq : instantiation.type =
        .function (TypeSystem.Ty.productMany parameterTypes) resultType)
      (predicates_eq : instantiation.predicates = predicates) :
      DeclarationApplicationValid context instantiation parameterTypes
        resultType predicates

/-- The synthetic callee inserted for a selected direct declaration call.
Its declaration predicates are owned by the call occurrence, so this reference
has neither requirements nor output coercions. -/
inductive DirectDeclarationCalleeValid
    (context : Context) (source : TypedSource) :
    ExpressionId → DeclarationInstantiation → Prop where
  | intro
      {id : ExpressionId}
      {node : ExpressionNode}
      {name : String}
      {instantiation : DeclarationInstantiation}
      (contains : ContainsExpression source id node)
      (form_eq : node.form = .reference name (.declaration instantiation))
      (instantiation_valid :
        SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
      (type_eq : node.type = instantiation.type)
      (requirements_eq : node.requirements = [])
      (coercions_eq : node.coercions = []) :
      DirectDeclarationCalleeValid context source id instantiation

/-- The synthetic callee inserted for a compiler-provided builtin call. -/
inductive DirectBuiltinCalleeValid (source : TypedSource) :
    ExpressionId → BuiltinFunctionId → Prop where
  | intro
      {id : ExpressionId}
      {node : ExpressionNode}
      {name : String}
      {function : BuiltinFunctionId}
      (contains : ContainsExpression source id node)
      (form_eq : node.form = .reference name (.builtinFunction function))
      (type_eq : node.type = function.type)
      (requirements_eq : node.requirements = [])
      (coercions_eq : node.coercions = []) :
      DirectBuiltinCalleeValid source id function

/-- Current direct-call metadata stores the selected-result coercions and any
later contextual coercions as one path.  This relation records the semantic
split and the exact interleaving of their evidence with signature evidence. -/
inductive DirectCallRequirementsValid (context : Context)
    (rawResult finalResult : TypeSystem.Ty)
    (predicates : List ProgramPredicate) :
    List RequirementId → List CoercionStep → Prop where
  | intro
      {selectedResult : TypeSystem.Ty}
      {selectedPath contextualPath : List CoercionStep}
      {signatureRequirements : List RequirementId}
      {requirements : List RequirementId}
      {coercions : List CoercionStep}
      (selected_valid : CoercionPathValid context rawResult selectedResult
        selectedPath)
      (contextual_valid : CoercionPathValid context selectedResult finalResult
        contextualPath)
      (signature_valid : RequirementSequenceProves context
        signatureRequirements predicates)
      (coercions_eq : coercions = selectedPath ++ contextualPath)
      (requirements_eq : requirements =
        coercionRequirementIds selectedPath ++
          (signatureRequirements ++ coercionRequirementIds contextualPath)) :
      DirectCallRequirementsValid context rawResult finalResult predicates
        requirements coercions

/-- Exact indirect-call metadata before the ordinary output coercion path. -/
inductive IndirectApplicationValid (context : Context)
    (metadata : IndirectCallResolution) (argumentTypes : List TypeSystem.Ty)
    (parameterType : TypeSystem.Ty) : Prop where
  | intro
      (count_eq : metadata.argumentCount = argumentTypes.length)
      (before_eq : metadata.argumentTypeBeforeCoercion =
        TypeSystem.Ty.productMany argumentTypes)
      (after_eq : metadata.argumentTypeAfterCoercion = parameterType)
      (path_valid : CoercionPathValid context
        metadata.argumentTypeBeforeCoercion parameterType
        metadata.argumentCoercions) :
      IndirectApplicationValid context metadata argumentTypes parameterType

namespace DirectCallRequirementsValid

theorem requirements_valid
    {context : Context} {rawResult finalResult : TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (valid : DirectCallRequirementsValid context rawResult finalResult
      predicates requirements coercions) :
    RequirementIdsValid context requirements := by
  cases valid with
  | @intro selectedResult selectedPath contextualPath
      signatureRequirements requirements coercions selectedValid contextualValid
      signatureValid coercionsEq requirementsEq =>
      subst requirements
      intro id member
      change id ∈ coercionRequirementIds selectedPath ++
        (signatureRequirements ++ coercionRequirementIds contextualPath) at member
      rw [List.mem_append] at member
      rcases member with selectedMember | signatureOrContext
      · exact selectedValid.requirements_valid id selectedMember
      · rw [List.mem_append] at signatureOrContext
        rcases signatureOrContext with signatureMember | contextMember
        · exact signatureValid.ids_valid id signatureMember
        · exact contextualValid.requirements_valid id contextMember

end DirectCallRequirementsValid

end Solcore.SourceSemantics
