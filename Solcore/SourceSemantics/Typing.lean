import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Traits
import Solcore.SourceSemantics.WellFormed

/-!
Initial declarative typing judgments for resolved source occurrences.

The judgments in this module validate semantic choices already carried by the
resolved source representation.  They do not run name resolution, overload
selection, unification, or trait search.  In particular, a declaration
reference must provide a catalog-valid instantiation, while the separate
solved-requirement judgment demands an independently valid evidence tree.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- The raw type denoted by a resolved source reference.

Local schemes may be instantiated at every occurrence.  Top-level references
carry a rigid-parameter instantiation which is checked against the program
catalog.  Compiler-provided references have their fixed source types.  This
raw judgment validates and retains declaration predicates but does not yet
connect them to occurrence requirement IDs or discharge their evidence. -/
inductive ReferenceHasRawType (context : Context) :
    ReferenceResolution → TypeSystem.Ty → Prop where
  | local
      {binder : Resolved.LocalId}
      {scheme : TypeSystem.Scheme}
      {type : TypeSystem.Ty}
      (lookup : context.LocalLookup binder scheme)
      (instantiates : SchemeInstantiatesAt context scheme type) :
      ReferenceHasRawType context (.local binder) type
  | declaration
      {instantiation : DeclarationInstantiation}
      (valid : SourceSemantics.DeclarationInstantiation.Valid
        context instantiation) :
      ReferenceHasRawType context (.declaration instantiation)
        instantiation.type
  | builtinFunction (function : BuiltinFunctionId) :
      ReferenceHasRawType context (.builtinFunction function) function.type
  | builtinBoolean (value : Bool) :
      ReferenceHasRawType context (.builtinBoolean value) .bool

namespace ReferenceHasRawType

/-- Invert local-reference typing to the lexical scheme and its exact
instantiation. -/
theorem local_iff
    {context : Context}
    {binder : Resolved.LocalId}
    {type : TypeSystem.Ty} :
    ReferenceHasRawType context (.local binder) type ↔
      ∃ scheme, context.LocalLookup binder scheme ∧
        SchemeInstantiatesAt context scheme type := by
  constructor
  · intro typing
    cases typing with
    | «local» lookup instantiates => exact ⟨_, lookup, instantiates⟩
  · rintro ⟨scheme, lookup, instantiates⟩
    exact .local lookup instantiates

/-- Invert declaration-reference typing to catalog-valid instantiation. -/
theorem declaration_iff
    {context : Context}
    {instantiation : DeclarationInstantiation}
    {type : TypeSystem.Ty} :
    ReferenceHasRawType context (.declaration instantiation) type ↔
      SourceSemantics.DeclarationInstantiation.Valid context instantiation ∧
        type = instantiation.type := by
  constructor
  · intro typing
    cases typing with
    | declaration valid => exact ⟨valid, rfl⟩
  · rintro ⟨valid, rfl⟩
    exact .declaration valid

/-- A compiler-provided function reference has exactly its cataloged type. -/
theorem builtinFunction_iff
    {context : Context}
    {function : BuiltinFunctionId}
    {type : TypeSystem.Ty} :
    ReferenceHasRawType context (.builtinFunction function) type ↔
      type = function.type := by
  constructor
  · intro typing
    cases typing
    rfl
  · rintro rfl
    exact .builtinFunction function

/-- Both builtin boolean spellings have source type `Bool`. -/
theorem builtinBoolean_iff
    {context : Context}
    {value : Bool}
    {type : TypeSystem.Ty} :
    ReferenceHasRawType context (.builtinBoolean value) type ↔
      type = .bool := by
  constructor
  · intro typing
    cases typing
    rfl
  · rintro rfl
    exact .builtinBoolean value

end ReferenceHasRawType

/-- One resolved reference occurrence has the declared raw type in a typed
source graph.  Result coercions are deliberately a later judgment: this rule
characterizes the reference before any retained output-coercion path. -/
inductive ReferenceExpressionHasRawType
    (context : Context) (source : TypedSource) :
    ExpressionId → TypeSystem.Ty → Prop where
  | intro
      {id : ExpressionId}
      {node : ExpressionNode}
      {name : String}
      {resolution : ReferenceResolution}
      {type : TypeSystem.Ty}
      (contains : ContainsExpression source id node)
      (form_eq : node.form = .reference name resolution)
      (reference_type : ReferenceHasRawType context resolution type)
      (raw_type_eq : node.rawType = type) :
      ReferenceExpressionHasRawType context source id type

namespace ReferenceExpressionHasRawType

/-- Lookup is only an observation of a declarative reference judgment, never
its definition. -/
theorem lookup
    {context : Context}
    {source : TypedSource}
    {id : ExpressionId}
    {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typing : ReferenceExpressionHasRawType context source id type) :
    ∃ node name resolution,
      source.lookupExpression? id = some node ∧
      node.form = .reference name resolution ∧
      ReferenceHasRawType context resolution type ∧
      node.rawType = type := by
  cases typing with
  | intro contains form_eq reference_type raw_type_eq =>
      refine ⟨_, _, _, ?_, form_eq, reference_type, raw_type_eq⟩
      exact lookupExpression?_complete unique contains

end ReferenceExpressionHasRawType

/-- A solved obligation is valid when its retained evidence proves its exact
normalized predicate under the current assumptions and complete rule catalog.
This proposition does not mention the resolver's fuel or search result. -/
inductive SolvedRequirementValid (context : Context) :
    SolvedRequirement → Prop where
  | intro {requirement : SolvedRequirement}
      (evidence_valid : RetainedEvidenceValid context.assumptions
        context.signatures.resolutionRules requirement.predicate
        requirement.evidence) :
      SolvedRequirementValid context requirement

/-- Every retained obligation in a list has independently valid evidence. -/
def SolvedRequirementsValid (context : Context)
    (requirements : List SolvedRequirement) : Prop :=
  ∀ requirement, requirement ∈ requirements →
    SolvedRequirementValid context requirement

namespace SolvedRequirementValid

theorem entails
    {context : Context}
    {requirement : SolvedRequirement}
    (valid : SolvedRequirementValid context requirement) :
    Entails context.assumptions context.signatures.resolutionRules
      requirement.predicate := by
  cases valid with
  | intro evidence_valid => exact evidence_valid.entails

theorem evidence_goal_eq
    {context : Context}
    {requirement : SolvedRequirement}
    (valid : SolvedRequirementValid context requirement) :
    requirement.evidence.goal = requirement.predicate := by
  cases valid with
  | intro evidence_valid => exact evidence_valid.evidence_goal_eq

end SolvedRequirementValid

end Solcore.SourceSemantics
