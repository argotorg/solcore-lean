import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.Patterns

/-!
Declarative source-pattern dynamics.

The retained pattern representation is a self-delimiting prefix program.  The
relations in this module consume that program directly: constructor and tuple
roots consume all of their children, successful bindings are concatenated in
source order, and a failed pattern still has an exact unconsumed suffix.  No
executable pattern matcher is used as a premise.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference

/-- The source product encoding of a value sequence.  This is the dynamic
counterpart of `Ty.productMany`: zero values use Unit, one value is left
unwrapped, and two or more values form a right-associated product. -/
inductive ValuesPack : List Value → Value → Prop where
  | nil : ValuesPack [] .unit
  | singleton (value : Value) : ValuesPack [value] value
  | cons
      {first second : Value} {rest : List Value} {packed : Value}
      (tail : ValuesPack (second :: rest) packed) :
      ValuesPack (first :: second :: rest) (.product first packed)

namespace ValuesPack

/-- The product encoding determines its packed value. -/
theorem functional {values : List Value} {left right : Value}
    (leftPack : ValuesPack values left) (rightPack : ValuesPack values right) :
    left = right := by
  induction leftPack generalizing right with
  | nil => cases rightPack; rfl
  | singleton value => cases rightPack; rfl
  | cons tail inductionHypothesis =>
      cases rightPack with
      | cons otherTail => rw [inductionHypothesis otherTail]

/-- At a fixed arity, the packed value also determines the source-ordered
value sequence. -/
theorem injective_of_length_eq
    {left right : List Value} {packed : Value}
    (leftPack : ValuesPack left packed) (rightPack : ValuesPack right packed)
    (sameLength : left.length = right.length) : left = right := by
  induction leftPack generalizing right with
  | nil =>
      cases rightPack <;> simp_all
  | singleton value =>
      cases rightPack <;> simp_all
  | cons tail inductionHypothesis =>
      cases rightPack with
      | singleton => simp at sameLength
      | cons otherTail =>
          have tailLength := Nat.succ.inj sameLength
          rw [inductionHypothesis otherTail tailLength]

end ValuesPack

/-- Runtime-relevant equality of constructor instantiations.  Association-list
order in a rigid-parameter substitution is proof metadata; constructor
selection and all instantiated payload/result types are the observable
content used by matching. -/
structure ConstructorInstantiationsAgree
    (left right : DataConstructorInstantiation) : Prop where
  constructor_eq : left.constructor = right.constructor
  payload_types_eq : left.payloadTypes = right.payloadTypes
  result_type_eq : left.resultType = right.resultType

namespace ConstructorInstantiationsAgree

theorem refl (instantiation : DataConstructorInstantiation) :
    ConstructorInstantiationsAgree instantiation instantiation :=
  ⟨rfl, rfl, rfl⟩

theorem symm
    {left right : DataConstructorInstantiation}
    (agree : ConstructorInstantiationsAgree left right) :
    ConstructorInstantiationsAgree right left :=
  ⟨agree.constructor_eq.symm, agree.payload_types_eq.symm,
    agree.result_type_eq.symm⟩

end ConstructorInstantiationsAgree

mutual

  /-- Consume one self-delimiting instruction without inspecting a value. -/
  inductive PatternInstructionSkips :
      List MatchPatternInstruction → List MatchPatternInstruction → Prop where
    | wildcard {rest} :
        PatternInstructionSkips (.wildcard :: rest) rest
    | integerLiteral {rest source resolution} :
        PatternInstructionSkips (.integerLiteral source resolution :: rest) rest
    | binder {rest binder} :
        PatternInstructionSkips (.binder binder :: rest) rest
    | constructor {instructions rest instantiation argumentCount}
        (children : PatternInstructionsSkip instructions argumentCount rest) :
        PatternInstructionSkips
          (.constructor instantiation argumentCount :: instructions) rest
    | tuple {instructions rest elementCount}
        (children : PatternInstructionsSkip instructions elementCount rest) :
        PatternInstructionSkips (.tuple elementCount :: instructions) rest

  /-- Consume exactly `count` consecutive self-delimiting instructions. -/
  inductive PatternInstructionsSkip :
      List MatchPatternInstruction → Nat →
        List MatchPatternInstruction → Prop where
    | zero {instructions} : PatternInstructionsSkip instructions 0 instructions
    | succ {instructions afterHead rest count}
        (head : PatternInstructionSkips instructions afterHead)
        (tail : PatternInstructionsSkip afterHead count rest) :
        PatternInstructionsSkip instructions (count + 1) rest

end

mutual

  /-- Match one value against one prefix instruction and expose the exact
  source-ordered bindings and unconsumed suffix. -/
  inductive PatternInstructionMatches (context : Context) :
      Value → List MatchPatternInstruction →
        List (TypedBinder × Value) → List MatchPatternInstruction → Prop where
    | wildcard {value rest} :
        PatternInstructionMatches context value (.wildcard :: rest) [] rest
    | integerLiteral
        {source resolution value rest}
        (constructs :
          ResolvedIntegerLiteralConstructs context source resolution value) :
        PatternInstructionMatches context value
          (.integerLiteral source resolution :: rest) [] rest
    | binder {value binder rest} :
        PatternInstructionMatches context value (.binder binder :: rest)
          [(binder, value)] rest
    | constructor
        {actual expected : DataConstructorInstantiation}
        {arguments : List Value}
        {instructions rest : List MatchPatternInstruction}
        {argumentCount : Nat} {bindings : List (TypedBinder × Value)}
        (instantiations_agree : ConstructorInstantiationsAgree actual expected)
        (arity : arguments.length = argumentCount)
        (children : PatternInstructionsMatch context arguments instructions
          bindings rest) :
        PatternInstructionMatches context (.constructed actual arguments)
          (.constructor expected argumentCount :: instructions) bindings rest
    | tuple
        {value : Value} {elements : List Value}
        {instructions rest : List MatchPatternInstruction}
        {elementCount : Nat} {bindings : List (TypedBinder × Value)}
        (packed : ValuesPack elements value)
        (arity : elements.length = elementCount)
        (children : PatternInstructionsMatch context elements instructions
          bindings rest) :
        PatternInstructionMatches context value
          (.tuple elementCount :: instructions) bindings rest

  /-- Match a source-ordered value vector against the same number of prefix
  pattern trees.  Appending head bindings before tail bindings fixes binding
  order to source order. -/
  inductive PatternInstructionsMatch (context : Context) :
      List Value → List MatchPatternInstruction →
        List (TypedBinder × Value) → List MatchPatternInstruction → Prop where
    | nil {instructions} :
        PatternInstructionsMatch context [] instructions [] instructions
    | cons
        {value values instructions afterHead rest headBindings tailBindings}
        (head : PatternInstructionMatches context value instructions
          headBindings afterHead)
        (tail : PatternInstructionsMatch context values afterHead
          tailBindings rest) :
        PatternInstructionsMatch context (value :: values) instructions
          (headBindings ++ tailBindings) rest

end

/-- One instruction is a semantic non-match when it has a well-defined full
prefix extent and no binding sequence can match over that same extent. -/
structure PatternInstructionDoesNotMatch (context : Context) (value : Value)
    (instructions rest : List MatchPatternInstruction) : Prop where
  consumes : PatternInstructionSkips instructions rest
  mismatch : ∀ bindings,
    ¬ PatternInstructionMatches context value instructions bindings rest

/-- A value vector is a semantic non-match when its corresponding sequence of
pattern trees is well-delimited and admits no successful binding sequence. -/
structure PatternInstructionsDoNotMatch (context : Context)
    (values : List Value) (instructions rest : List MatchPatternInstruction) : Prop where
  consumes : PatternInstructionsSkip instructions values.length rest
  mismatch : ∀ bindings,
    ¬ PatternInstructionsMatch context values instructions bindings rest

/-- Match a complete root resolution, including exact exhaustion of its
flattened child stream. -/
def PatternResolutionMatches (context : Context)
    (resolution : MatchPatternResolution) (rootArity : Nat)
    (value : Value) (bindings : List (TypedBinder × Value)) : Prop :=
  PatternInstructionMatches context value
    (matchPatternResolutionInstructions resolution rootArity) bindings []

/-- A complete, well-delimited root resolution fails to match. -/
def PatternResolutionDoesNotMatch (context : Context)
    (resolution : MatchPatternResolution) (rootArity : Nat)
    (value : Value) : Prop :=
  PatternInstructionDoesNotMatch context value
    (matchPatternResolutionInstructions resolution rootArity) []

/-- Dynamic success for a retained typed source pattern.  The source carrier
fixes the root arity used to reconstitute the prefix program. -/
inductive PatternMatches (context : Context) :
    TypedMatchPattern → Value → List (TypedBinder × Value) → Prop where
  | intro
      {pattern value bindings rootArity}
      (source_represents : MatchPatternSourceRepresents context pattern.source
        pattern.resolution rootArity)
      (matched : PatternResolutionMatches context pattern.resolution rootArity
        value bindings) :
      PatternMatches context pattern value bindings

/-- Dynamic non-match for a retained typed source pattern. -/
inductive PatternDoesNotMatch (context : Context) :
    TypedMatchPattern → Value → Prop where
  | intro
      {pattern value rootArity}
      (source_represents : MatchPatternSourceRepresents context pattern.source
        pattern.resolution rootArity)
      (does_not_match : PatternResolutionDoesNotMatch context pattern.resolution
        rootArity value) :
      PatternDoesNotMatch context pattern value

namespace PatternInstructionDoesNotMatch

/-- A declared non-match excludes a successful match over the same prefix. -/
theorem excludes
    {context : Context} {value : Value}
    {instructions rest : List MatchPatternInstruction}
    (failure : PatternInstructionDoesNotMatch context value instructions rest)
    {bindings : List (TypedBinder × Value)} :
    ¬ PatternInstructionMatches context value instructions bindings rest :=
  failure.mismatch bindings

end PatternInstructionDoesNotMatch

namespace PatternInstructionsDoNotMatch

theorem excludes
    {context : Context} {values : List Value}
    {instructions rest : List MatchPatternInstruction}
    (failure : PatternInstructionsDoNotMatch context values instructions rest)
    {bindings : List (TypedBinder × Value)} :
    ¬ PatternInstructionsMatch context values instructions bindings rest :=
  failure.mismatch bindings

end PatternInstructionsDoNotMatch

/-- Result of first-match case selection before a branch body is executed. -/
inductive MatchCaseSelection where
  | arm (body : List StatementId) (bindings : List (TypedBinder × Value))
  | default (body : List StatementId)
  | noBranch
  deriving Repr

/-- Select the first matching arm.  A default is considered only after every
ordered arm has an explicit semantic non-match derivation. -/
inductive MatchCasesSelect (context : Context) (value : Value) :
    List TypedMatchCase → Option (List StatementId) → MatchCaseSelection → Prop where
  | head
      {arm rest fallback bindings}
      (matched : PatternMatches context arm.pattern value bindings) :
      MatchCasesSelect context value (arm :: rest) fallback
        (.arm arm.body bindings)
  | tail
      {arm rest fallback selection}
      (does_not_match : PatternDoesNotMatch context arm.pattern value)
      (selected : MatchCasesSelect context value rest fallback selection) :
      MatchCasesSelect context value (arm :: rest) fallback selection
  | default {body} :
      MatchCasesSelect context value [] (some body) (.default body)
  | noBranch :
      MatchCasesSelect context value [] none .noBranch

end Solcore.SourceSemantics.Dynamic
