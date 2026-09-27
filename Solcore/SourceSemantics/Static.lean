import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.Calls
import Solcore.SourceSemantics.Control
import Solcore.SourceSemantics.Literals
import Solcore.SourceSemantics.Operators
import Solcore.SourceSemantics.Patterns
import Solcore.SourceSemantics.Places

/-!
Complete declarative typing of the resolved source occurrence language.

The mutually inductive judgments cover every expression and statement form in
`TypedIR`.  Recursive edges are justified by declarative table membership;
name lookup, unification, overload ranking, trait search, and checker success
do not occur in any rule.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- One lexical scheme is instantiated by a single substitution shared by its
result type and every qualified predicate.  Actual requirement identities are
source-ordered, pairwise distinct, and cannot reuse the initializer's
assumption-template identities. -/
inductive LocalSchemeInstantiationValid (context : Context)
    (binder : TypedBinder) (type : TypeSystem.Ty)
    (actualRequirements : List RequirementId) : Prop where
  | intro
      (formation : LocalSchemeRequirementsWellFormed context binder)
      (scheme_well_formed : SchemeWellFormed context binder.scheme)
      (substitution : TypeSystem.Substitution)
      (exact : ExactSubstitution substitution binder.scheme.quantified)
      (range : SubstitutionRangeAdmissible context substitution)
      (result : substitution.apply binder.scheme.body = type)
      (actual_requirements_unique : actualRequirements.Nodup)
      (actual_templates_disjoint :
        ∀ id, id ∈ actualRequirements → id ∉ localSchemeTemplateIds binder)
      (requirements : RequirementSequenceProves context actualRequirements
        (instantiateLocalSchemePredicates substitution binder)) :
      LocalSchemeInstantiationValid context binder type actualRequirements

namespace LocalSchemeInstantiationValid

theorem actual_requirements_nodup
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    actualRequirements.Nodup := by
  cases valid with
  | intro _ _ _ _ _ _ unique _ _ => exact unique

theorem actual_templates_disjoint
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    ∀ id, id ∈ actualRequirements → id ∉ localSchemeTemplateIds binder := by
  cases valid with
  | intro _ _ _ _ _ _ _ disjoint _ => exact disjoint

theorem actual_requirements_valid
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    RequirementIdsValid context actualRequirements := by
  cases valid with
  | intro _ _ _ _ _ _ _ _ requirements =>
      exact requirements.ids_valid

/-- Expose the one witness which simultaneously determines the result type
and the complete ordered predicate spine. -/
theorem has_shared_substitution
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    ∃ substitution,
      ExactSubstitution substitution binder.scheme.quantified ∧
      SubstitutionRangeAdmissible context substitution ∧
      substitution.apply binder.scheme.body = type ∧
      RequirementSequenceProves context actualRequirements
        (instantiateLocalSchemePredicates substitution binder) := by
  cases valid with
  | intro _ _ substitution exact range result _ _ requirements =>
      exact ⟨substitution, exact, range, result, requirements⟩

theorem requirements_length_eq
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    actualRequirements.length = binder.schemeRequirements.length := by
  cases valid with
  | intro _ _ _ _ _ _ _ _ requirements =>
      rw [requirements.length_eq]
      simp [instantiateLocalSchemePredicates]

/-- The shared witness in a local use is in particular a valid scheme
instantiation at its use-site type. -/
theorem toSchemeInstantiatesAt
    {context : Context} {binder : TypedBinder} {type : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    SchemeInstantiatesAt context binder.scheme type := by
  cases valid with
  | intro _ schemeWellFormed substitution exact range result _ _ _ =>
      exact .intro schemeWellFormed substitution exact range result

end LocalSchemeInstantiationValid

/-- Complete static validity of one resolved reference occurrence.  For a
local reference this judgment deliberately owns both raw-type instantiation
and ordered evidence validation, preventing two independent substitutions
from justifying the type and its qualified predicates. -/
inductive ReferenceUseValid (context : Context) :
    ReferenceResolution → TypeSystem.Ty → List RequirementId → Prop where
  | local
      {binder : TypedBinder} {type : TypeSystem.Ty}
      {actualRequirements : List RequirementId}
      (scheme_lookup : context.LocalLookup binder.id binder.scheme)
      (requirements_lookup : context.LocalSchemeRequirementsLookup binder.id
        binder.schemeRequirements)
      (instantiation : LocalSchemeInstantiationValid context binder type
        actualRequirements) :
      ReferenceUseValid context (.local binder.id) type actualRequirements
  | declaration
      {instantiation : DeclarationInstantiation}
      {requirements : List RequirementId}
      (valid : SourceSemantics.DeclarationInstantiation.Admissible context
        instantiation)
      (proves : RequirementSequenceProves context requirements
        instantiation.predicates) :
      ReferenceUseValid context (.declaration instantiation)
        instantiation.type requirements
  | builtinFunction (function : BuiltinFunctionId) :
      ReferenceUseValid context (.builtinFunction function) function.type []
  | builtinBoolean (value : Bool) :
      ReferenceUseValid context (.builtinBoolean value) .bool []

namespace ReferenceUseValid

/-- Forget requirement ownership while retaining the raw reference type. -/
theorem raw_type
    {context : Context} {resolution : ReferenceResolution}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    (valid : ReferenceUseValid context resolution type requirements) :
    ReferenceHasRawType context resolution type := by
  cases valid with
  | «local» schemeLookup _ instantiation =>
      exact .local schemeLookup instantiation.toSchemeInstantiatesAt
  | declaration instantiationValid _ => exact .declaration instantiationValid
  | builtinFunction function => exact .builtinFunction function
  | builtinBoolean value => exact .builtinBoolean value

end ReferenceUseValid

/-- Shape-specific evidence layout before it is checked against an expression
node's retained requirement and coercion lists. -/
inductive ExpressionRequirementPlan where
  | ordinary (owned : List RequirementId)
  | directCall (predicates : List ProgramPredicate)
  | indirectCall (argumentCoercions : List CoercionStep)

namespace ExpressionRequirementPlan

/-- Exact requirement ownership and all coercion endpoints for one expression. -/
inductive Valid (context : Context) (rawType finalType : TypeSystem.Ty) :
    ExpressionRequirementPlan → List RequirementId →
      List CoercionStep → Prop where
  | ordinary
      {owned requirements : List RequirementId}
      {coercions : List CoercionStep}
      (owned_valid : RequirementIdsValid context owned)
      (path_valid : CoercionPathValid context rawType finalType coercions)
      (requirements_eq : requirements =
        owned ++ coercionRequirementIds coercions) :
      Valid context rawType finalType (.ordinary owned) requirements coercions
  | directCall
      {predicates : List ProgramPredicate}
      {requirements : List RequirementId}
      {coercions : List CoercionStep}
      (valid : DirectCallRequirementsValid context rawType finalType predicates
        requirements coercions) :
      Valid context rawType finalType (.directCall predicates)
        requirements coercions
  | indirectCall
      {argumentCoercions outputCoercions : List CoercionStep}
      {requirements : List RequirementId}
      (arguments_valid : RequirementIdsValid context
        (coercionRequirementIds argumentCoercions))
      (output_valid : CoercionPathValid context rawType finalType
        outputCoercions)
      (requirements_eq : requirements =
        coercionRequirementIds argumentCoercions ++
          coercionRequirementIds outputCoercions) :
      Valid context rawType finalType (.indirectCall argumentCoercions)
        requirements outputCoercions

namespace Valid

/-- Every valid requirement layout exposes the complete output-coercion path,
independently of whether the expression is ordinary, a direct call, or an
indirect call. -/
theorem outputPath
    {context : Context} {rawType finalType : TypeSystem.Ty}
    {plan : ExpressionRequirementPlan} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan
      requirements coercions) :
    CoercionPathValid context rawType finalType coercions := by
  cases valid with
  | ordinary _ path _ => exact path
  | directCall direct =>
      cases direct with
      | intro selected contextual signature coercions_eq requirements_eq =>
          subst coercions
          exact CoercionPathValid.append selected contextual
  | indirectCall _ output _ => exact output

/-- A valid shape-specific layout justifies every requirement identity stored
on the expression node. -/
theorem requirementsValid
    {context : Context} {rawType finalType : TypeSystem.Ty}
    {plan : ExpressionRequirementPlan} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan
      requirements coercions) :
    RequirementIdsValid context requirements := by
  cases valid with
  | ordinary ownedValid pathValid requirementsEq =>
      rw [requirementsEq]
      intro requirement member
      simp only [List.mem_append] at member
      exact member.elim (ownedValid requirement)
        (pathValid.requirements_valid requirement)
  | directCall direct => exact direct.requirements_valid
  | indirectCall argumentValid outputValid requirementsEq =>
      rw [requirementsEq]
      intro requirement member
      simp only [List.mem_append] at member
      exact member.elim (argumentValid requirement)
        (outputValid.requirements_valid requirement)

/-- Appending another semantically valid output path preserves every
shape-specific requirement layout.  This is the semantic counterpart of the
frontend's `attachExpressionCoercions` node refinement. -/
theorem appendOutput
    {context : Context} {rawType middleType finalType : TypeSystem.Ty}
    {plan : ExpressionRequirementPlan}
    {requirements : List RequirementId}
    {first second : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType middleType plan
      requirements first)
    (output : CoercionPathValid context middleType finalType second) :
    ExpressionRequirementPlan.Valid context rawType finalType plan
      (requirements ++ coercionRequirementIds second) (first ++ second) := by
  cases valid with
  | ordinary ownedValid pathValid requirementsEq =>
      apply ExpressionRequirementPlan.Valid.ordinary ownedValid
        (pathValid.append output)
      rw [requirementsEq, coercionRequirementIds_append]
      simp only [List.append_assoc]
  | directCall direct =>
      cases direct with
      | @intro selectedResult selectedPath contextualPath
          signatureRequirements directRequirements directCoercions
          selectedValid contextualValid
          signatureValid coercionsEq requirementsEq =>
          apply ExpressionRequirementPlan.Valid.directCall
          apply DirectCallRequirementsValid.intro selectedValid
            (contextualValid.append output) signatureValid
          · rw [coercionsEq]
            simp only [List.append_assoc]
          · rw [requirementsEq, coercionRequirementIds_append]
            simp only [List.append_assoc]
  | indirectCall argumentValid outputValid requirementsEq =>
      apply ExpressionRequirementPlan.Valid.indirectCall argumentValid
        (outputValid.append output)
      rw [requirementsEq, coercionRequirementIds_append]
      simp only [List.append_assoc]

end Valid

end ExpressionRequirementPlan

/-- One constructor-pattern arm covers a nominal constructor when all payload
patterns are irrefutable. -/
def PatternCoversConstructor (pattern : TypedMatchPattern)
    (constructor : ProgramDataConstructorId) : Prop :=
  ∃ instantiation instructions,
    pattern.resolution = .constructor instantiation instructions ∧
    instantiation.constructor = constructor ∧
    PatternInstructionsIrrefutable instructions
      instantiation.payloadTypes.length []

/-- Exhaustiveness accepted by the declarative resolved-source semantics. -/
inductive MatchExhaustive (context : Context) (scrutineeType : TypeSystem.Ty)
    (cases : List TypedMatchCase) : Option (List StatementId) → Prop where
  | default (body : List StatementId) :
      MatchExhaustive context scrutineeType cases (some body)
  | catchall
      {matchCase : TypedMatchCase}
      (member : matchCase ∈ cases)
      (irrefutable : TypedMatchPatternIrrefutable context matchCase.pattern) :
      MatchExhaustive context scrutineeType cases none
  | constructors
      {dataType : ProgramDataSignature}
      {substitution : TypeSystem.ParameterSubstitution}
      (cataloged : dataType ∈ context.signatures.dataTypes)
      (substitution_exact :
        ParameterSubstitution.Exact substitution dataType.parameters)
      (scrutinee_eq : scrutineeType = TypeSystem.Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments substitution
          dataType.parameters))
      (covered : ∀ constructor, constructor ∈ dataType.constructors →
        ∃ matchCase ∈ cases,
          PatternCoversConstructor matchCase.pattern constructor.id) :
      MatchExhaustive context scrutineeType cases none

/-- Legacy body-result flag used by the resolved carrier. -/
def allBodiesSawReturn (facts : List BodyFacts) : Bool :=
  facts.all fun body => body.sawReturn

/-- Combine the semantic transfers of mutually exclusive match arms. -/
def mergeBodyControls : List BodyFacts → Option BodyFacts → Option ControlSummary
  | [], none => none
  | [], some fallback => some fallback.control
  | body :: bodies, fallback =>
      match mergeBodyControls bodies fallback with
      | none => some body.control
      | some tail => some (body.control.branches tail)

mutual

  /-- A source expression occurrence has its retained post-coercion type. -/
  inductive ExpressionHasType (source : TypedSource) :
      Context → ExpressionId → TypeSystem.Ty → Prop where
    | intro
        {context : Context} {id : ExpressionId}
        {node : ExpressionNode} {rawType : TypeSystem.Ty}
        {plan : ExpressionRequirementPlan}
        (contains : ContainsExpression source id node)
        (form_type : ExpressionFormHasRawType source context node.form rawType plan)
        (raw_type_eq : node.rawType = rawType)
        (raw_well_formed : TypeAdmissible context rawType)
        (type_well_formed : TypeAdmissible context node.type)
        (requirements : ExpressionRequirementPlan.Valid context rawType node.type
          plan node.requirements node.coercions) :
        ExpressionHasType source context id node.type

  /-- Raw typing of every resolved expression shape. -/
  inductive ExpressionFormHasRawType (source : TypedSource) :
      Context → ExpressionForm → TypeSystem.Ty →
        ExpressionRequirementPlan → Prop where
    | literal
        {context : Context} {literal : Syntax.CoreLiteralValue}
        (valid : WordLiteralValid literal) :
        ExpressionFormHasRawType source context (.literal literal) .word
          (.ordinary [])
    | integerLiteral
        {context : Context} {literal : Syntax.CoreLiteralValue}
        {resolution : IntegerLiteralResolution}
        (valid : IntegerLiteralValid context literal resolution) :
        ExpressionFormHasRawType source context
          (.integerLiteral literal resolution) resolution.targetType
          (.ordinary [resolution.requirement])
    | reference
        {context : Context} {name : String}
        {resolution : ReferenceResolution} {type : TypeSystem.Ty}
        {requirements : List RequirementId}
        (valid : ReferenceUseValid context resolution type requirements) :
        ExpressionFormHasRawType source context (.reference name resolution) type
          (.ordinary requirements)
    | group
        {context : Context} {inner : ExpressionId} {type : TypeSystem.Ty}
        (inner_type : ExpressionHasType source context inner type) :
        ExpressionFormHasRawType source context (.group inner) type
          (.ordinary [])
    | tuple
        {context : Context} {elements : List ExpressionId}
        {types : List TypeSystem.Ty}
        (elements_type : ExpressionsHaveTypes source context elements types) :
        ExpressionFormHasRawType source context (.tuple elements)
          (TypeSystem.Ty.productMany types) (.ordinary [])
    | unary
        {context : Context} {operator : Syntax.UnaryOp}
        {operand : ExpressionId} {operandType resultType : TypeSystem.Ty}
        {requirements : List RequirementId}
        (operand_type : ExpressionHasType source context operand operandType)
        (operator_type : UnaryOperatorHasType context operator operandType
          resultType requirements) :
        ExpressionFormHasRawType source context (.unary operator operand)
          resultType (.ordinary requirements)
    | binary
        {context : Context} {operator : Syntax.BinaryOp}
        {left right : ExpressionId} {operandType resultType : TypeSystem.Ty}
        {requirements : List RequirementId}
        (left_type : ExpressionHasType source context left operandType)
        (right_type : ExpressionHasType source context right operandType)
        (operator_type : BinaryOperatorHasType context operator operandType
          operandType resultType requirements) :
        ExpressionFormHasRawType source context (.binary left operator right)
          resultType (.ordinary requirements)
    | conditional
        {context : Context} {condition thenBranch elseBranch : ExpressionId}
        {type : TypeSystem.Ty}
        (condition_type : ExpressionHasType source context condition .bool)
        (then_type : ExpressionHasType source context thenBranch type)
        (else_type : ExpressionHasType source context elseBranch type) :
        ExpressionFormHasRawType source context
          (.conditional condition thenBranch elseBranch) type (.ordinary [])
    | lambda
        {context lambdaContext finalContext : Context}
        {parameters : List TypedBinder} {parameterTypes : List TypeSystem.Ty}
        {returnType : TypeSystem.Ty} {body : List StatementId}
        {bodyFacts : BodyFacts}
        (names_unique : (parameters.map fun binder => binder.name).Nodup)
        (parameters_extend : MonoBindersExtend source.owner context parameters
          parameterTypes lambdaContext)
        (body_type : StatementsHaveType source
          { returnType, loopDepth := 0 } lambdaContext body finalContext bodyFacts)
        (body_completes : BodyCompletes returnType bodyFacts) :
        ExpressionFormHasRawType source context
          (.lambda parameters returnType body)
          (.function (TypeSystem.Ty.productMany parameterTypes) returnType)
          (.ordinary [])
    | directCall
        {context : Context} {callee : ExpressionId}
        {arguments : List ExpressionId}
        {instantiation : DeclarationInstantiation}
        {parameterTypes : List TypeSystem.Ty} {resultType : TypeSystem.Ty}
        {predicates : List ProgramPredicate}
        (callee_valid : DirectDeclarationCalleeValid context source callee
          instantiation)
        (application : DeclarationApplicationValid context instantiation
          parameterTypes resultType predicates)
        (arguments_type : ExpressionsHaveTypes source context arguments
          parameterTypes) :
        ExpressionFormHasRawType source context
          (.call callee arguments (.declaration instantiation)) resultType
          (.directCall predicates)
    | builtinCall
        {context : Context} {callee : ExpressionId}
        {arguments : List ExpressionId} {function : BuiltinFunctionId}
        (callee_valid : DirectBuiltinCalleeValid source callee function)
        (arguments_type : ExpressionsHaveTypes source context arguments
          function.parameterTypes) :
        ExpressionFormHasRawType source context
          (.call callee arguments (.builtinFunction function))
          function.returnType (.ordinary [])
    | indirectCall
        {context : Context} {callee : ExpressionId}
        {arguments : List ExpressionId} {argumentTypes : List TypeSystem.Ty}
        {parameterType resultType : TypeSystem.Ty}
        {metadata : IndirectCallResolution}
        (callee_type : ExpressionHasType source context callee
          (.function parameterType resultType))
        (arguments_type : ExpressionsHaveTypes source context arguments
          argumentTypes)
        (application : IndirectApplicationValid context metadata argumentTypes
          parameterType) :
        ExpressionFormHasRawType source context
          (.call callee arguments (.indirect metadata)) resultType
          (.indirectCall metadata.argumentCoercions)
    | constructor
        {context : Context} {instantiation : DataConstructorInstantiation}
        {arguments : List ExpressionId}
        (valid : DataConstructorInstantiation.Admissible context instantiation)
        (arguments_type : ExpressionsHaveTypes source context arguments
          instantiation.payloadTypes) :
        ExpressionFormHasRawType source context
          (.constructor instantiation arguments) instantiation.resultType
          (.ordinary [])
    | member
        {context : Context} {base : ExpressionId} {name : String} {index : Nat}
        {baseType memberType : TypeSystem.Ty}
        (base_type : ExpressionHasType source context base baseType)
        (member_type : UniformMemberProjection context baseType index memberType) :
        ExpressionFormHasRawType source context (.member base name index)
          memberType (.ordinary [])
    | proxy
        {context : Context} {inner : TypeSystem.Ty}
        (inner_well_formed : TypeAdmissible context inner) :
        ExpressionFormHasRawType source context (.proxy inner) (.proxy inner)
          (.ordinary [])
    | index
        {context : Context} {base key : ExpressionId}
        {keyType valueType : TypeSystem.Ty}
        (base_type : ExpressionHasType source context base
          (.mapping keyType valueType))
        (key_type : ExpressionHasType source context key keyType) :
        ExpressionFormHasRawType source context (.index base key) valueType
          (.ordinary [])

  /-- Pointwise expression typing in source order. -/
  inductive ExpressionsHaveTypes (source : TypedSource) :
      Context → List ExpressionId → List TypeSystem.Ty → Prop where
    | nil (context : Context) : ExpressionsHaveTypes source context [] []
    | cons
        {context : Context} {expression : ExpressionId}
        {expressions : List ExpressionId} {type : TypeSystem.Ty}
        {types : List TypeSystem.Ty}
        (head : ExpressionHasType source context expression type)
        (tail : ExpressionsHaveTypes source context expressions types) :
        ExpressionsHaveTypes source context (expression :: expressions)
          (type :: types)

  /-- Place projections specialized to the mutually recursive expression
  judgment. -/
  inductive SourceProjectionsHaveType (source : TypedSource) :
      Context → TypeSystem.Ty → List PlaceProjection →
        TypeSystem.Ty → Prop where
    | nil
        {context : Context} (type : TypeSystem.Ty) :
        SourceProjectionsHaveType source context type [] type
    | index
        {context : Context} {key : ExpressionId}
        {keyType valueType finalType : TypeSystem.Ty}
        {rest : List PlaceProjection}
        (key_type : ExpressionHasType source context key keyType)
        (rest_type : SourceProjectionsHaveType source context valueType rest
          finalType) :
        SourceProjectionsHaveType source context (.mapping keyType valueType)
          (.index key :: rest) finalType
    | member
        {context : Context} {name : String} {index : Nat}
        {baseType memberType finalType : TypeSystem.Ty}
        {rest : List PlaceProjection}
        (selected : UniformMemberProjection context baseType index memberType)
        (rest_type : SourceProjectionsHaveType source context memberType rest
          finalType) :
        SourceProjectionsHaveType source context baseType
          (.member name index :: rest) finalType

  /-- A source place rooted at a monomorphic writable local. -/
  inductive SourcePlaceHasType (source : TypedSource) :
      Context → PlaceResolution → TypeSystem.Ty → Prop where
    | intro
        {context : Context} {place : PlaceResolution}
        {rootType finalType : TypeSystem.Ty}
        (root_type : WritableLocal context place.root rootType)
        (projections_type : SourceProjectionsHaveType source context rootType
          place.projections finalType)
        (stored_type_eq : place.type = finalType) :
        SourcePlaceHasType source context place finalType

  /-- Value assignments in the current executable source profile. -/
  inductive SourceAssignmentHasType (source : TypedSource) :
      Context → AssignmentResolution → Syntax.ValueAssignOp →
        ExpressionId → Prop where
    | equal
        {context : Context} {assignment : AssignmentResolution}
        {value : ExpressionId} {type : TypeSystem.Ty}
        (target_type : SourcePlaceHasType source context assignment.target type)
        (value_type : ExpressionHasType source context value type)
        (requirements_eq : assignment.requirements = []) :
        SourceAssignmentHasType source context assignment .equal value
    | wordCompound
        {context : Context} {assignment : AssignmentResolution}
        {operator : Syntax.ValueAssignOp} {value : ExpressionId}
        (operator_kind : WordCompoundAssignmentOperator operator)
        (target_type : SourcePlaceHasType source context assignment.target .word)
        (value_type : ExpressionHasType source context value .word)
        (requirements_eq : assignment.requirements = []) :
        SourceAssignmentHasType source context assignment operator value

  /-- Bit-not assignment in the current executable source profile. -/
  inductive SourceBitNotAssignmentValid (source : TypedSource) :
      Context → AssignmentResolution → Prop where
    | intro
        {context : Context} {assignment : AssignmentResolution}
        (target_type : SourcePlaceHasType source context assignment.target .word)
        (requirements_eq : assignment.requirements = []) :
        SourceBitNotAssignmentValid source context assignment

  /-- Typing of one statement, including lexical-scope output and semantic
  control transfer. -/
  inductive StatementHasType (source : TypedSource) :
      ControlContext → Context → StatementId → Context →
        StatementFacts → Prop where
    | letUninitialized
        {control : ControlContext} {context final : Context}
        {id : StatementId} {node : StatementNode}
        {binder : TypedBinder}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (generalizes : SchemeGeneralizes context binder.scheme)
        (extension : BinderExtends source.owner context binder final)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id final {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | letInitialized
        {control : ControlContext} {context final : Context}
        {id : StatementId} {node : StatementNode}
        {binder : TypedBinder} {initializer : ExpressionId}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (initializer_type : ExpressionHasType source context initializer
          binder.scheme.body)
        (monomorphic : binder.scheme.quantified = [])
        (generalizes : SchemeGeneralizes context binder.scheme)
        (extension : BinderExtends source.owner context binder final)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id final {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | letInitializedGeneralized
        {control : ControlContext} {context final : Context}
        {id : StatementId} {node : StatementNode}
        {binder : TypedBinder} {initializer : ExpressionId}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (polymorphic : binder.scheme.quantified ≠ [])
        (requirements_well_formed :
          LocalSchemeRequirementsWellFormed context binder)
        (generalizes : SchemeGeneralizesExcept context
          (localSchemeTemplateIds binder) binder.scheme)
        (initializer_type : ExpressionHasType source
          (localSchemeInitializerContext context binder) initializer
          binder.scheme.body)
        (extension : BinderExtends source.owner context binder final)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id final {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | returnUnit
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt none)
        (return_type_eq : control.returnType = .unit)
        (type_eq : node.type = control.returnType) :
        StatementHasType source control context id context {
          type := control.returnType, hasValue := true, sawReturn := true
          control := .returned
        }
    | returnValue
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {value : ExpressionId}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some value))
        (value_type : ExpressionHasType source context value control.returnType)
        (type_eq : node.type = control.returnType) :
        StatementHasType source control context id context {
          type := control.returnType, hasValue := true, sawReturn := true
          control := .returned
        }
    | expressionValue
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {expression : ExpressionId} {type : TypeSystem.Ty}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression false)
        (expression_type : ExpressionHasType source context expression type)
        (type_eq : node.type = type) :
        StatementHasType source control context id context {
          type, hasValue := true, sawReturn := false
          control := .ordinary type
        }
    | expressionDiscard
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {expression : ExpressionId} {type : TypeSystem.Ty}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression true)
        (expression_type : ExpressionHasType source context expression type)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | assignValue
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
        {value : ExpressionId}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator value)
        (assignment_type : SourceAssignmentHasType source context assignment
          operator value)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | assignBitNot
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {assignment : AssignmentResolution}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (assignment_type : SourceBitNotAssignmentValid source context assignment)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
    | ifWithoutElse
        {control : ControlContext} {context thenFinal : Context}
        {id : StatementId} {node : StatementNode}
        {condition : ExpressionId} {thenBody : List StatementId}
        {thenFacts : BodyFacts}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody none)
        (condition_type : ExpressionHasType source context condition .bool)
        (then_type : StatementsHaveType source control context thenBody
          thenFinal thenFacts)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := thenFacts.control.branches (.ordinary .unit)
        }
    | ifWithElse
        {control : ControlContext} {context thenFinal elseFinal : Context}
        {id : StatementId} {node : StatementNode}
        {condition : ExpressionId}
        {thenBody elseBody : List StatementId}
        {thenFacts elseFacts : BodyFacts}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some elseBody))
        (condition_type : ExpressionHasType source context condition .bool)
        (then_type : StatementsHaveType source control context thenBody
          thenFinal thenFacts)
        (else_type : StatementsHaveType source control context elseBody
          elseFinal elseFacts)
        (type_eq : node.type = if thenFacts.sawReturn && elseFacts.sawReturn
          then control.returnType else .unit) :
        StatementHasType source control context id context {
          type := if thenFacts.sawReturn && elseFacts.sawReturn
            then control.returnType else .unit
          hasValue := thenFacts.sawReturn && elseFacts.sawReturn
          sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
          control := thenFacts.control.branches elseFacts.control
        }
    | block
        {control : ControlContext} {context innerFinal : Context}
        {id : StatementId} {node : StatementNode}
        {body : List StatementId} {bodyFacts : BodyFacts}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (body_type : StatementsHaveType source control context body innerFinal
          bodyFacts)
        (type_eq : node.type = bodyFacts.type) :
        StatementHasType source control context id context {
          type := bodyFacts.type
          hasValue := bodyFacts.sawReturn
          sawReturn := bodyFacts.sawReturn
          control := bodyFacts.control.eraseValue
        }
    | matchWithoutDefault
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        {resolution : MatchResolution} {scrutineeType : TypeSystem.Ty}
        {caseFacts : List BodyFacts} {summary : ControlSummary}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (default_eq : resolution.defaultBody = none)
        (scrutinee_type : ExpressionHasType source context
          resolution.scrutinee scrutineeType)
        (cases_type : MatchCasesHaveType source control context scrutineeType
          resolution.cases caseFacts)
        (requirements_eq : resolution.requirements =
          resolution.cases.flatMap fun matchCase =>
            matchCase.pattern.requirements)
        (exhaustive : MatchExhaustive context scrutineeType resolution.cases none)
        (merged : mergeBodyControls caseFacts none = some summary)
        (type_eq : node.type = if allBodiesSawReturn caseFacts
          then control.returnType else .unit) :
        StatementHasType source control context id context {
          type := if allBodiesSawReturn caseFacts then control.returnType else .unit
          hasValue := allBodiesSawReturn caseFacts
          sawReturn := allBodiesSawReturn caseFacts
          control := summary.eraseValue
        }
    | matchWithDefault
        {control : ControlContext} {context defaultFinal : Context}
        {id : StatementId} {node : StatementNode}
        {resolution : MatchResolution} {defaultBody : List StatementId}
        {scrutineeType : TypeSystem.Ty} {caseFacts : List BodyFacts}
        {defaultFacts : BodyFacts} {summary : ControlSummary}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (default_eq : resolution.defaultBody = some defaultBody)
        (scrutinee_type : ExpressionHasType source context
          resolution.scrutinee scrutineeType)
        (cases_type : MatchCasesHaveType source control context scrutineeType
          resolution.cases caseFacts)
        (default_type : StatementsHaveType source control context defaultBody
          defaultFinal defaultFacts)
        (requirements_eq : resolution.requirements =
          resolution.cases.flatMap fun matchCase =>
            matchCase.pattern.requirements)
        (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
        (type_eq : node.type =
          if allBodiesSawReturn caseFacts && defaultFacts.sawReturn
          then control.returnType else .unit) :
        StatementHasType source control context id context {
          type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn
            then control.returnType else .unit
          hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
          sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
          control := summary.eraseValue
        }
    | forLoop
        {control : ControlContext}
        {context loopContext postContext bodyFinal : Context}
        {id : StatementId} {node : StatementNode}
        {initializer post : List ForItemForm} {condition : ExpressionId}
        {body : List StatementId} {bodyFacts : BodyFacts}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializer_type : ForItemsHaveType source control context initializer
          loopContext)
        (condition_type : ExpressionHasType source loopContext condition .bool)
        (body_type : StatementsHaveType source control.enterLoop loopContext body
          bodyFinal bodyFacts)
        (post_type : ForItemsHaveType source control.enterLoop loopContext post
          postContext)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .loop bodyFacts.control
        }
    | whileLoop
        {control : ControlContext} {context bodyFinal : Context}
        {id : StatementId} {node : StatementNode}
        {condition : ExpressionId} {body : List StatementId}
        {bodyFacts : BodyFacts}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (condition_type : ExpressionHasType source context condition .bool)
        (body_type : StatementsHaveType source control.enterLoop context body
          bodyFinal bodyFacts)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .loop bodyFacts.control
        }
    | breakStmt
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .breakStmt)
        (allowed : control.loopAllowed)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .breaking
        }
    | continueStmt
        {control : ControlContext} {context : Context}
        {id : StatementId} {node : StatementNode}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .continueStmt)
        (allowed : control.loopAllowed)
        (type_eq : node.type = .unit) :
        StatementHasType source control context id context {
          type := .unit, hasValue := false, sawReturn := false
          control := .continuing
        }

  /-- Source-ordered statement sequence with lexical context threading. -/
  inductive StatementsHaveType (source : TypedSource) :
      ControlContext → Context → List StatementId → Context →
        BodyFacts → Prop where
    | nil (control : ControlContext) (context : Context) :
        StatementsHaveType source control context [] context .empty
    | singleton
        {control : ControlContext} {context final : Context}
        {statement : StatementId}
        {facts : StatementFacts}
        (head : StatementHasType source control context statement final facts) :
        StatementsHaveType source control context [statement] final
          (.singleton facts)
    | cons
        {control : ControlContext} {context middle final : Context}
        {statement next : StatementId}
        {rest : List StatementId} {headFacts : StatementFacts}
        {tailFacts : BodyFacts}
        (head : StatementHasType source control context statement middle
          headFacts)
        (tail : StatementsHaveType source control middle (next :: rest) final
          tailFacts) :
        StatementsHaveType source control context (statement :: next :: rest)
          final (.cons headFacts tailFacts)

  /-- Typing and lexical effect of one restricted `for` header item. -/
  inductive ForItemHasType (source : TypedSource) :
      ControlContext → Context → ForItemForm → Context → Prop where
    | letUninitialized
        {control : ControlContext} {context final : Context}
        {binder : TypedBinder}
        (monomorphic : binder.scheme.quantified = [])
        (generalizes : SchemeGeneralizes context binder.scheme)
        (extension : BinderExtends source.owner context binder final) :
        ForItemHasType source control context (.letDecl binder none) final
    | letInitialized
        {control : ControlContext} {context final : Context}
        {binder : TypedBinder}
        {initializer : ExpressionId}
        (initializer_type : ExpressionHasType source context initializer
          binder.scheme.body)
        (monomorphic : binder.scheme.quantified = [])
        (generalizes : SchemeGeneralizes context binder.scheme)
        (extension : BinderExtends source.owner context binder final) :
        ForItemHasType source control context
          (.letDecl binder (some initializer)) final
    | letInitializedGeneralized
        {control : ControlContext} {context final : Context}
        {binder : TypedBinder}
        {initializer : ExpressionId}
        (polymorphic : binder.scheme.quantified ≠ [])
        (requirements_well_formed :
          LocalSchemeRequirementsWellFormed context binder)
        (generalizes : SchemeGeneralizesExcept context
          (localSchemeTemplateIds binder) binder.scheme)
        (initializer_type : ExpressionHasType source
          (localSchemeInitializerContext context binder) initializer
          binder.scheme.body)
        (extension : BinderExtends source.owner context binder final) :
        ForItemHasType source control context
          (.letDecl binder (some initializer)) final
    | expression
        {control : ControlContext} {context : Context}
        {expression : ExpressionId} {type : TypeSystem.Ty}
        (expression_type : ExpressionHasType source context expression type) :
        ForItemHasType source control context (.expression expression) context
    | assignValue
        {control : ControlContext} {context : Context}
        {assignment : AssignmentResolution}
        {operator : Syntax.ValueAssignOp} {value : ExpressionId}
        (assignment_type : SourceAssignmentHasType source context assignment
          operator value) :
        ForItemHasType source control context
          (.assignValue assignment operator value) context
    | assignBitNot
        {control : ControlContext} {context : Context}
        {assignment : AssignmentResolution}
        (assignment_type : SourceBitNotAssignmentValid source context assignment) :
        ForItemHasType source control context (.assignBitNot assignment) context

  /-- Sequential lexical threading for `for` header items. -/
  inductive ForItemsHaveType (source : TypedSource) :
      ControlContext → Context → List ForItemForm → Context → Prop where
    | nil (control : ControlContext) (context : Context) :
        ForItemsHaveType source control context [] context
    | cons
        {control : ControlContext} {context middle final : Context}
        {item : ForItemForm}
        {items : List ForItemForm}
        (head : ForItemHasType source control context item middle)
        (tail : ForItemsHaveType source control middle items final) :
        ForItemsHaveType source control context (item :: items) final

  /-- One match arm, typed under its pattern-binder extension. -/
  inductive MatchCaseHasType (source : TypedSource) :
      ControlContext → Context → TypeSystem.Ty →
        TypedMatchCase → BodyFacts → Prop where
    | intro
        {control : ControlContext} {context : Context}
        {scrutineeType : TypeSystem.Ty}
        {matchCase : TypedMatchCase} {binders : List TypedBinder}
        {rootArity : Nat} {armContext finalContext : Context}
        {facts : BodyFacts}
        (pattern_type : TypedMatchPatternHasType context matchCase.pattern
          scrutineeType binders rootArity)
        (binders_extend : BindersExtend source.owner context binders armContext)
        (body_type : StatementsHaveType source control armContext matchCase.body
          finalContext facts) :
        MatchCaseHasType source control context scrutineeType matchCase facts

  /-- Source-ordered typing of all explicit match arms. -/
  inductive MatchCasesHaveType (source : TypedSource) :
      ControlContext → Context → TypeSystem.Ty →
        List TypedMatchCase → List BodyFacts → Prop where
    | nil (control : ControlContext) (context : Context)
        (scrutineeType : TypeSystem.Ty) :
        MatchCasesHaveType source control context scrutineeType [] []
    | cons
        {control : ControlContext} {context : Context}
        {scrutineeType : TypeSystem.Ty}
        {matchCase : TypedMatchCase} {cases : List TypedMatchCase}
        {facts : BodyFacts} {caseFacts : List BodyFacts}
        (head : MatchCaseHasType source control context scrutineeType
          matchCase facts)
        (tail : MatchCasesHaveType source control context scrutineeType
          cases caseFacts) :
        MatchCasesHaveType source control context scrutineeType
          (matchCase :: cases) (facts :: caseFacts)

end

/-- A declaration body is a statement-root list with no escaping loop control
and with every ordinary completion producing the declared result type. -/
def BodyHasType (source : TypedSource) (context : Context)
    (resultType : TypeSystem.Ty) (facts : BodyFacts) : Prop :=
  ∃ finalContext,
    StatementsHaveType source { returnType := resultType } context
      (source.roots.filterMap fun root =>
        match root with
        | .statement statement => some statement
        | .expression _ => none) finalContext facts ∧
    (∀ expression, .expression expression ∈ source.roots → False) ∧
    BodyCompletes resultType facts

namespace ExpressionHasType

/-- Assemble the common expression-typing envelope once a shape-specific
requirement plan and its output path have been validated. -/
theorem ofPlan
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {node : ExpressionNode}
    {rawType : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (contains : ContainsExpression source id node)
    (formType : ExpressionFormHasRawType source context node.form rawType plan)
    (rawAdmissible : TypeAdmissible context rawType)
    (finalAdmissible : TypeAdmissible context node.type)
    (requirements : ExpressionRequirementPlan.Valid context rawType node.type
      plan node.requirements node.coercions) :
    ExpressionHasType source context id node.type := by
  exact .intro contains formType
    requirements.outputPath.expressionNode_rawType rawAdmissible
    finalAdmissible requirements

/-- Assemble the common expression-typing envelope for forms whose own
requirements precede an ordinary output-coercion path. -/
theorem ofOrdinary
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {node : ExpressionNode}
    {rawType : TypeSystem.Ty} {owned : List RequirementId}
    (contains : ContainsExpression source id node)
    (formType : ExpressionFormHasRawType source context node.form rawType
      (.ordinary owned))
    (rawAdmissible : TypeAdmissible context rawType)
    (finalAdmissible : TypeAdmissible context node.type)
    (ownedValid : RequirementIdsValid context owned)
    (path : CoercionPathValid context rawType node.type node.coercions)
    (layout : node.requirements =
      owned ++ coercionRequirementIds node.coercions) :
    ExpressionHasType source context id node.type := by
  exact ofPlan contains formType rawAdmissible finalAdmissible
    (.ordinary ownedValid path layout)

theorem stored_type
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {type : TypeSystem.Ty}
    (typing : ExpressionHasType source context id type) :
    ∃ node, ContainsExpression source id node ∧ node.type = type := by
  cases typing with
  | intro contains => exact ⟨_, contains, rfl⟩

/-- Declarative expression typing always exposes an admissible retained result
type to enclosing expression and statement rules. -/
theorem type_admissible
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {type : TypeSystem.Ty}
    (typing : ExpressionHasType source context id type) :
    TypeAdmissible context type := by
  cases typing with
  | intro _ _ _ _ admissible _ => exact admissible

/-- Recover the admissible pre-coercion type and its complete semantic output
path from a typed expression occurrence. -/
theorem raw_type_and_output_path
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {type : TypeSystem.Ty}
    (typing : ExpressionHasType source context id type) :
    ∃ node rawType,
      ContainsExpression source id node ∧
        node.type = type ∧
        node.rawType = rawType ∧
        TypeAdmissible context rawType ∧
        CoercionPathValid context rawType type node.coercions := by
  cases typing with
  | @intro _ _ node rawType plan contains _ rawTypeEq rawAdmissible _ valid =>
      exact ⟨node, rawType, contains, rfl, rawTypeEq, rawAdmissible,
        valid.outputPath⟩

theorem requirements_valid
    {source : TypedSource} {context : Context}
    {id : ExpressionId} {type : TypeSystem.Ty}
    (typing : ExpressionHasType source context id type) :
    ∃ node, ContainsExpression source id node ∧
      RequirementIdsValid context node.requirements := by
  cases typing with
  | @intro _ _ node rawType plan contains _ _ _ _ requirements =>
      exact ⟨node, contains, requirements.requirementsValid⟩

end ExpressionHasType

end Solcore.SourceSemantics
