import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.Literals

/-!
Declarative typing for the flattened source-pattern carrier.

`MatchPatternInstruction` is a prefix program: constructor and tuple
instructions are followed by exactly the number of self-delimiting children
recorded at their root.  The mutually inductive judgments below consume that
program directly.  Consequently neither pattern inference nor the executable
pattern consumers occur in the specification.

The source carrier deliberately preserves groups and the outer spelling of a
constructor, but it does not retain the nested source terms below constructor
or tuple roots.  Therefore `MatchPatternSourceRepresents` can validate the
root spelling and arity while the instruction judgments validate the complete
nested semantic tree.  A future lossless nested source carrier can strengthen
that correspondence without changing prefix typing.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A pattern binder is monomorphic at the matched value type, is a runtime
binder, and belongs to the declaration currently being checked when such a
declaration has been installed in the context. -/
structure PatternBinderValid (context : Context) (type : TypeSystem.Ty)
    (binder : TypedBinder) : Prop where
  scheme_eq : binder.scheme = .mono type
  runtime : binder.comptime = false
  wellFormed : ∀ declaration,
    context.currentDeclaration = some declaration →
      BinderWellFormed context declaration binder

/-- Stable identities and source spellings introduced by one pattern are both
pairwise distinct. -/
structure PatternBindersDistinct (binders : List TypedBinder) : Prop where
  ids : (binders.map (fun binder => binder.id)).Nodup
  names : (binders.map (fun binder => binder.name)).Nodup

mutual

  /-- Consume one well-typed self-delimiting pattern instruction and return
  its exact requirement IDs, binders, and unconsumed suffix. -/
  inductive PatternInstructionHasType (context : Context) :
      List MatchPatternInstruction → TypeSystem.Ty →
        List RequirementId → List TypedBinder →
          List MatchPatternInstruction → Prop where
    | wildcard {rest type} :
        PatternInstructionHasType context (.wildcard :: rest) type [] [] rest
    | integerLiteral
        {rest source resolution}
        (valid : IntegerLiteralValid context source resolution) :
        PatternInstructionHasType context
          (.integerLiteral source resolution :: rest)
          resolution.targetType [resolution.requirement] [] rest
    | binder
        {rest binder type}
        (valid : PatternBinderValid context type binder) :
        PatternInstructionHasType context (.binder binder :: rest)
          type [] [binder] rest
    | constructor
        {instructions rest instantiation argumentCount requirements binders}
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (arity : argumentCount = instantiation.payloadTypes.length)
        (arguments : PatternInstructionsHaveTypes context instructions
          instantiation.payloadTypes requirements binders rest) :
        PatternInstructionHasType context
          (.constructor instantiation argumentCount :: instructions)
          instantiation.resultType requirements binders rest
    | tuple
        {instructions rest elementCount elementTypes requirements binders}
        (arity : elementCount = elementTypes.length)
        (elements : PatternInstructionsHaveTypes context instructions
          elementTypes requirements binders rest) :
        PatternInstructionHasType context
          (.tuple elementCount :: instructions)
          (TypeSystem.Ty.productMany elementTypes) requirements binders rest

  /-- Consume a source-ordered sequence of pattern trees at the corresponding
  source types.  Requirements and binders are concatenated in that same order. -/
  inductive PatternInstructionsHaveTypes (context : Context) :
      List MatchPatternInstruction → List TypeSystem.Ty →
        List RequirementId → List TypedBinder →
          List MatchPatternInstruction → Prop where
    | nil {instructions} :
        PatternInstructionsHaveTypes context instructions [] [] [] instructions
    | cons
        {instructions afterHead rest type types
          headRequirements tailRequirements headBinders tailBinders}
        (head : PatternInstructionHasType context instructions type
          headRequirements headBinders afterHead)
        (tail : PatternInstructionsHaveTypes context afterHead types
          tailRequirements tailBinders rest) :
        PatternInstructionsHaveTypes context instructions (type :: types)
          (headRequirements ++ tailRequirements)
          (headBinders ++ tailBinders) rest

end

/-- Reconstitute the complete prefix program represented by a root
resolution. -/
def matchPatternResolutionInstructions :
    MatchPatternResolution → Nat → List MatchPatternInstruction
  | .wildcard, _ => [.wildcard]
  | .integerLiteral source resolution, _ => [.integerLiteral source resolution]
  | .binder binder, _ => [.binder binder]
  | .constructor instantiation arguments, rootArity =>
      .constructor instantiation rootArity :: arguments
  | .tuple elements, rootArity => .tuple rootArity :: elements

/-- The root resolution is a complete, exactly consumed pattern program. -/
def MatchPatternResolutionHasType (context : Context)
    (resolution : MatchPatternResolution) (type : TypeSystem.Ty)
    (requirements : List RequirementId) (binders : List TypedBinder)
    (rootArity : Nat) : Prop :=
  PatternInstructionHasType context
    (matchPatternResolutionInstructions resolution rootArity)
    type requirements binders []

/-- A constructor spelling selects the catalog constructor retained in its
instantiation.  Qualifier/import-path validity is established by the resolved
source layer; the current compact source carrier retains qualifier spellings
but not the resolution trace needed to restate that judgment here. -/
def ConstructorPatternSpellingValid (context : Context) (name : String)
    (instantiation : DataConstructorInstantiation) : Prop :=
  ∃ signature,
    signature ∈ context.signatures.dataTypes ∧
    ∃ constructor,
      constructor ∈ signature.constructors ∧
      constructor.id = instantiation.constructor ∧
      constructor.name = name

/-- Correspondence available from the compact source-pattern carrier to the
semantic root resolution.  Groups intentionally leave the resolution
unchanged. -/
inductive MatchPatternSourceRepresents (context : Context) :
    MatchPatternSource → MatchPatternResolution → Nat → Prop where
  | wildcard {span marker} :
      MatchPatternSourceRepresents context (.wildcard span marker) .wildcard 0
  | integerLiteral {span literal source resolution}
      (source_eq : literal.value = source) :
      MatchPatternSourceRepresents context (.integerLiteral span literal)
        (.integerLiteral source resolution) 0
  | binder {span name binder}
      (name_eq : binder.name = name) :
      MatchPatternSourceRepresents context (.binder span name) (.binder binder) 0
  | constructor
      {span leadingDot qualifiers name argumentCount instantiation arguments}
      (spelling : ConstructorPatternSpellingValid context name instantiation) :
      MatchPatternSourceRepresents context
        (.constructor span leadingDot qualifiers name argumentCount)
        (.constructor instantiation arguments) argumentCount
  | tuple {span elementCount elements} :
      MatchPatternSourceRepresents context (.tuple span elementCount)
        (.tuple elements) elementCount
  | group {span inner resolution rootArity}
      (inner_represents :
        MatchPatternSourceRepresents context inner resolution rootArity) :
      MatchPatternSourceRepresents context (.group span inner) resolution rootArity

/-- Complete source-level pattern typing.  The result exposes binders so a
match-arm judgment can extend its lexical context without inspecting the
carrier. -/
structure TypedMatchPatternHasType (context : Context)
    (pattern : TypedMatchPattern) (type : TypeSystem.Ty)
    (binders : List TypedBinder) (rootArity : Nat) : Prop where
  type_eq : pattern.type = type
  source_represents :
    MatchPatternSourceRepresents context pattern.source pattern.resolution rootArity
  resolution_type : MatchPatternResolutionHasType context pattern.resolution
    type pattern.requirements binders rootArity
  binders_distinct : PatternBindersDistinct binders

/-- A closed validity view when a consumer does not need the binder list. -/
def TypedMatchPatternValid (context : Context)
    (pattern : TypedMatchPattern) : Prop :=
  ∃ binders rootArity,
    TypedMatchPatternHasType context pattern pattern.type binders rootArity

mutual

  /-- Declarative irrefutability for one prefix instruction.  Constructor and
  integer roots have no constructor, matching their refutable semantics. -/
  inductive PatternInstructionIrrefutable :
      List MatchPatternInstruction → List MatchPatternInstruction → Prop where
    | wildcard {rest} : PatternInstructionIrrefutable (.wildcard :: rest) rest
    | binder {rest binder} :
        PatternInstructionIrrefutable (.binder binder :: rest) rest
    | tuple {instructions rest elementCount}
        (elements : PatternInstructionsIrrefutable instructions elementCount rest) :
        PatternInstructionIrrefutable
          (.tuple elementCount :: instructions) rest

  /-- Every pattern in a fixed-length prefix sequence is irrefutable. -/
  inductive PatternInstructionsIrrefutable :
      List MatchPatternInstruction → Nat → List MatchPatternInstruction → Prop where
    | zero {instructions} :
        PatternInstructionsIrrefutable instructions 0 instructions
    | succ {instructions afterHead rest count}
        (head : PatternInstructionIrrefutable instructions afterHead)
        (tail : PatternInstructionsIrrefutable afterHead count rest) :
        PatternInstructionsIrrefutable instructions (count + 1) rest

end

/-- A root pattern resolution is irrefutable exactly when its complete prefix
program has an irrefutability derivation consuming all instructions. -/
def MatchPatternResolutionIrrefutable
    (resolution : MatchPatternResolution) (rootArity : Nat) : Prop :=
  PatternInstructionIrrefutable
    (matchPatternResolutionInstructions resolution rootArity) []

/-- Source-connected irrefutability uses the retained root arity, which is
essential because tuple resolutions store a flat child stream. -/
def TypedMatchPatternIrrefutable (context : Context)
    (pattern : TypedMatchPattern) : Prop :=
  ∃ rootArity,
    MatchPatternSourceRepresents context pattern.source pattern.resolution
      rootArity ∧
    MatchPatternResolutionIrrefutable pattern.resolution rootArity

private theorem requirementIdsValid_append
    {context : Context} {left right : List RequirementId}
    (leftValid : RequirementIdsValid context left)
    (rightValid : RequirementIdsValid context right) :
    RequirementIdsValid context (left ++ right) := by
  intro id member
  simp only [List.mem_append] at member
  exact member.elim (leftValid id) (rightValid id)

namespace PatternInstructionHasType

/-- All requirement identities emitted by one typed pattern instruction are
independently valid. -/
theorem requirements_valid
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionHasType context instructions type requirements
      binders rest) :
    RequirementIdsValid context requirements := by
  refine PatternInstructionHasType.rec
    (motive_1 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    (motive_2 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intros
    simp [RequirementIdsValid]
  · intros
    intro id member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst id
    exact IntegerLiteralValid.requirement_valid (by assumption)
  · intros
    simp [RequirementIdsValid]
  · intros
    assumption
  · intros
    assumption
  · intros
    simp [RequirementIdsValid]
  · intros
    apply requirementIdsValid_append <;> assumption

end PatternInstructionHasType

namespace PatternInstructionsHaveTypes

/-- A typed sequence likewise emits only valid requirement identities. -/
theorem requirements_valid
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {types : List TypeSystem.Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionsHaveTypes context instructions types
      requirements binders rest) :
    RequirementIdsValid context requirements := by
  refine PatternInstructionsHaveTypes.rec
    (motive_1 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    (motive_2 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intros
    simp [RequirementIdsValid]
  · intros
    intro id member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst id
    exact IntegerLiteralValid.requirement_valid (by assumption)
  · intros
    simp [RequirementIdsValid]
  · intros
    assumption
  · intros
    assumption
  · intros
    simp [RequirementIdsValid]
  · intros
    apply requirementIdsValid_append <;> assumption

end PatternInstructionsHaveTypes

namespace TypedMatchPatternHasType

theorem requirements_valid
    {context : Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {rootArity : Nat}
    (typing :
      TypedMatchPatternHasType context pattern type binders rootArity) :
    RequirementIdsValid context pattern.requirements :=
  typing.resolution_type.requirements_valid

end TypedMatchPatternHasType

end Solcore.SourceSemantics
