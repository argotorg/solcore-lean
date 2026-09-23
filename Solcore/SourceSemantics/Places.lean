import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Types

/-!
Declarative typing for mutable source places and assignments.

The judgments are parameterized by expression typing.  Consequently this
module can state the place fragment without depending on the mutually
recursive whole-expression and whole-statement judgments.  Local lookup is
the resolved scope's first-match relation, and writable roots are deliberately
restricted to monomorphic schemes, matching the current executable profile.

Member names in `PlaceProjection.member` are retained for source diagnostics.
The semantic selection is its stable positional index.  Since the present
catalog has positional constructor payloads rather than named fields, the
member rule below conservatively requires that position to have one uniform
type in every constructor of the nominal data declaration.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A lexical local may root a mutable place exactly when its first-match
scheme is monomorphic. -/
inductive WritableLocal (context : Context) :
    Resolved.LocalId → TypeSystem.Ty → Prop where
  | intro
      {id : Resolved.LocalId}
      {scheme : TypeSystem.Scheme}
      {type : TypeSystem.Ty}
      (lookup : context.LocalLookup id scheme)
      (scheme_well_formed : SchemeWellFormed context scheme)
      (quantified_eq : scheme.quantified = [])
      (body_eq : scheme.body = type) :
      WritableLocal context id type

namespace WritableLocal

/-- Expose the exact first-match scheme selected for a writable local. -/
theorem scheme
    {context : Context} {id : Resolved.LocalId} {type : TypeSystem.Ty}
    (writable : WritableLocal context id type) :
    ∃ scheme, context.LocalLookup id scheme ∧
      SchemeWellFormed context scheme ∧
      scheme.quantified = [] ∧ scheme.body = type := by
  cases writable with
  | intro lookup scheme_well_formed quantified_eq body_eq =>
      exact ⟨_, lookup, scheme_well_formed, quantified_eq, body_eq⟩

/-- A directly bound monomorphic local is writable. -/
theorem withLocal_mono (context : Context) (id : Resolved.LocalId)
    (type : TypeSystem.Ty)
    (well_formed : TypeWellFormed (context.withLocal id (.mono type)) type) :
    WritableLocal (context.withLocal id (.mono type)) id type := by
  exact .intro (.head) (SchemeWellFormed.mono well_formed) rfl rfl

/-- A writable root's monomorphic body is a closed, well-formed source type. -/
theorem type_well_formed
    {context : Context} {id : Resolved.LocalId} {type : TypeSystem.Ty}
    (writable : WritableLocal context id type) :
    TypeWellFormed context type := by
  cases writable with
  | intro _ scheme_well_formed quantified_eq body_eq =>
      exact {
        binders := scheme_well_formed.binders
        typeWellScoped := by
          rw [← body_eq]
          simpa [quantified_eq] using scheme_well_formed.body
      }

end WritableLocal

/-- Positional member selection is catalog-backed and uniform across every
constructor.  Requiring a nonempty constructor list prevents the universal
condition from allowing arbitrary fields for an empty data declaration. -/
inductive UniformMemberProjection (context : Context) :
    TypeSystem.Ty → Nat → TypeSystem.Ty → Prop where
  | intro
      {base member : TypeSystem.Ty}
      {index : Nat}
      {dataType : ProgramDataSignature}
      {substitution : TypeSystem.ParameterSubstitution}
      (dataType_mem : dataType ∈ context.signatures.dataTypes)
      (substitution_exact :
        ParameterSubstitution.Exact substitution dataType.parameters)
      (base_eq : base = TypeSystem.Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments substitution
          dataType.parameters))
      (base_well_formed : TypeWellFormed context base)
      (member_well_formed : TypeWellFormed context member)
      (constructors_nonempty : dataType.constructors ≠ [])
      (member_uniform : ∀ constructor,
        constructor ∈ dataType.constructors →
          (constructor.payloadTypes.map
            (TypeSystem.ParameterSubstitution.apply substitution))[index]? =
              some member)
      /- The catalog-level projection is stable for every semantically valid
      constructor value at the same nominal base type.  This keeps the
      standalone judgment sound even when it is used with a forgeable Context
      before whole-program catalog uniqueness has been established. -/
      (valid_instantiations : ∀ instantiation,
        DataConstructorInstantiation.Valid context instantiation →
        instantiation.resultType = base →
        instantiation.payloadTypes[index]? = some member) :
      UniformMemberProjection context base index member

namespace UniformMemberProjection

/-- Any valid constructor value at the projected nominal base exposes the
same payload type at this position, independently of substitution-list order. -/
theorem valid_payload
    {context : Context} {base member : TypeSystem.Ty} {index : Nat}
    (projection : UniformMemberProjection context base index member)
    {instantiation : DataConstructorInstantiation}
    (valid : DataConstructorInstantiation.Valid context instantiation)
    (result_eq : instantiation.resultType = base) :
    instantiation.payloadTypes[index]? = some member := by
  cases projection with
  | intro _ _ _ _ _ _ _ valid_instantiations =>
      exact valid_instantiations instantiation valid result_eq

end UniformMemberProjection

/-- Left-to-right typing of a retained place-projection path. -/
inductive ProjectionsHaveType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil (type : TypeSystem.Ty) :
      ProjectionsHaveType context ExpressionTyping type [] type
  | index
      {key : ExpressionId}
      {keyType valueType finalType : TypeSystem.Ty}
      {rest : List PlaceProjection}
      (key_type : ExpressionTyping key keyType)
      (rest_type : ProjectionsHaveType context ExpressionTyping
        valueType rest finalType) :
      ProjectionsHaveType context ExpressionTyping
        (.mapping keyType valueType) (.index key :: rest) finalType
  | member
      {name : String}
      {index : Nat}
      {baseType memberType finalType : TypeSystem.Ty}
      {rest : List PlaceProjection}
      (selected : UniformMemberProjection context baseType index memberType)
      (rest_type : ProjectionsHaveType context ExpressionTyping
        memberType rest finalType) :
      ProjectionsHaveType context ExpressionTyping baseType
        (.member name index :: rest) finalType

namespace ProjectionsHaveType

/-- An empty projection path preserves its input type. -/
theorem nil_iff
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {source target : TypeSystem.Ty} :
    ProjectionsHaveType context ExpressionTyping source [] target ↔
      target = source := by
  constructor
  · intro typing
    cases typing
    rfl
  · rintro rfl
    exact .nil _

/-- The first mapping projection types its key at the mapping key type. -/
theorem index_head
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {key : ExpressionId}
    {keyType valueType finalType : TypeSystem.Ty}
    {rest : List PlaceProjection}
    (typing : ProjectionsHaveType context ExpressionTyping
      (.mapping keyType valueType) (.index key :: rest) finalType) :
    ExpressionTyping key keyType ∧
      ProjectionsHaveType context ExpressionTyping
        valueType rest finalType := by
  cases typing with
  | index key_type rest_type => exact ⟨key_type, rest_type⟩

/-- A retained member head has a catalog-backed uniform positional field,
independently of the diagnostic name carried by the projection. -/
theorem member_head
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {baseType finalType : TypeSystem.Ty}
    {name : String} {index : Nat}
    {rest : List PlaceProjection}
    (typing : ProjectionsHaveType context ExpressionTyping baseType
      (.member name index :: rest) finalType) :
    ∃ memberType,
      UniformMemberProjection context baseType index memberType ∧
      ProjectionsHaveType context ExpressionTyping
        memberType rest finalType := by
  cases typing with
  | member selected rest_type => exact ⟨_, selected, rest_type⟩

end ProjectionsHaveType

/-- A retained place begins at a writable local, follows a well-typed
projection path, and records exactly the path's final type. -/
inductive PlaceHasType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    PlaceResolution → TypeSystem.Ty → Prop where
  | intro
      {place : PlaceResolution}
      {rootType finalType : TypeSystem.Ty}
      (root_type : WritableLocal context place.root rootType)
      (projections_type : ProjectionsHaveType context ExpressionTyping
        rootType place.projections finalType)
      (stored_type_eq : place.type = finalType) :
      PlaceHasType context ExpressionTyping place finalType

namespace PlaceHasType

/-- The external result of place typing is the authoritative retained type. -/
theorem type_eq
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : PlaceHasType context ExpressionTyping place type) :
    place.type = type := by
  cases typing with
  | intro _ _ stored_type_eq => exact stored_type_eq

/-- Invert a place judgment to its monomorphic root and complete projection
derivation. -/
theorem components
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : PlaceHasType context ExpressionTyping place type) :
    ∃ rootType,
      WritableLocal context place.root rootType ∧
      ProjectionsHaveType context ExpressionTyping
        rootType place.projections type := by
  cases typing with
  | intro root_type projections_type stored_type_eq =>
      subst stored_type_eq
      exact ⟨_, root_type, projections_type⟩

end PlaceHasType

/-- The compound assignment spellings supported by the current source
runtime.  Every one is the homogeneous Word operation. -/
inductive WordCompoundAssignmentOperator : Syntax.ValueAssignOp → Prop where
  | add : WordCompoundAssignmentOperator .add
  | subtract : WordCompoundAssignmentOperator .subtract
  | multiply : WordCompoundAssignmentOperator .multiply
  | divide : WordCompoundAssignmentOperator .divide
  | modulo : WordCompoundAssignmentOperator .modulo
  | bitAnd : WordCompoundAssignmentOperator .bitAnd
  | bitXor : WordCompoundAssignmentOperator .bitXor
  | bitOr : WordCompoundAssignmentOperator .bitOr

/-- A value assignment validates its place and right-hand occurrence.  Plain
assignment is homogeneous at any place type; current compound forms are
homogeneous at Word.  Neither form owns trait requirements in this runtime
profile. -/
inductive AssignmentHasType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop where
  | equal
      {assignment : AssignmentResolution}
      {value : ExpressionId}
      {type : TypeSystem.Ty}
      (target_type : PlaceHasType context ExpressionTyping assignment.target type)
      (value_type : ExpressionTyping value type)
      (requirements_eq : assignment.requirements = []) :
      AssignmentHasType context ExpressionTyping assignment .equal value
  | wordCompound
      {assignment : AssignmentResolution}
      {operator : Syntax.ValueAssignOp}
      {value : ExpressionId}
      (operator_kind : WordCompoundAssignmentOperator operator)
      (target_type : PlaceHasType context ExpressionTyping
        assignment.target .word)
      (value_type : ExpressionTyping value .word)
      (requirements_eq : assignment.requirements = []) :
      AssignmentHasType context ExpressionTyping assignment operator value

namespace AssignmentHasType

/-- Assignments in the current runtime profile own no requirement IDs. -/
theorem requirements_empty
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp}
    {value : ExpressionId}
    (typing : AssignmentHasType context ExpressionTyping
      assignment operator value) :
    assignment.requirements = [] := by
  cases typing <;> assumption

/-- Both plain and compound assignments type the right-hand occurrence at the
final place type. -/
theorem operand_types
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp}
    {value : ExpressionId}
    (typing : AssignmentHasType context ExpressionTyping
      assignment operator value) :
    ∃ type,
      PlaceHasType context ExpressionTyping assignment.target type ∧
      ExpressionTyping value type := by
  cases typing with
  | equal target_type value_type => exact ⟨_, target_type, value_type⟩
  | wordCompound _ target_type value_type =>
      exact ⟨.word, target_type, value_type⟩

end AssignmentHasType

/-- Bit-not assignment is valid only at a Word place and, like the other
current assignment forms, owns no requirements. -/
inductive BitNotAssignmentValid
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    AssignmentResolution → Prop where
  | intro
      {assignment : AssignmentResolution}
      (target_type : PlaceHasType context ExpressionTyping
        assignment.target .word)
      (requirements_eq : assignment.requirements = []) :
      BitNotAssignmentValid context ExpressionTyping assignment

namespace BitNotAssignmentValid

theorem requirements_empty
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    (valid : BitNotAssignmentValid context ExpressionTyping assignment) :
    assignment.requirements = [] := by
  cases valid
  assumption

theorem target_word
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    (valid : BitNotAssignmentValid context ExpressionTyping assignment) :
    PlaceHasType context ExpressionTyping assignment.target .word := by
  cases valid
  assumption

end BitNotAssignmentValid

end Solcore.SourceSemantics
