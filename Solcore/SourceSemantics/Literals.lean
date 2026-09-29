import Solcore.SourceSemantics.Requirements
import Solcore.Frontend.WordLiteral

/-!
Declarative numeric-literal meaning for resolved source occurrences.

Literal spelling is related to its mathematical natural-number value by the
existing proof-facing digit relation.  Selected integer targets are restricted
to the two source domains implemented by the language semantics, and their
stable evidence identity must prove the exact builtin `Int` predicate.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A retained integer-literal resolution denotes its stored mathematical
value and owns exact evidence for a supported target type. -/
inductive IntegerLiteralValid (context : Context) :
    Syntax.CoreLiteralValue → IntegerLiteralResolution → Prop where
  | word
      {source : Syntax.CoreLiteralValue}
      {resolution : IntegerLiteralResolution}
      (meaning : NumericLiteralDenotes source resolution.rawValue)
      (target_eq : resolution.targetType = .word)
      (evidence : RequirementProves context resolution.requirement
        (ProgramSignatures.builtinIntPredicate resolution.targetType)) :
      IntegerLiteralValid context source resolution
  | integer
      {source : Syntax.CoreLiteralValue}
      {resolution : IntegerLiteralResolution}
      (meaning : NumericLiteralDenotes source resolution.rawValue)
      (target_eq : resolution.targetType = .integer)
      (evidence : RequirementProves context resolution.requirement
        (ProgramSignatures.builtinIntPredicate resolution.targetType)) :
      IntegerLiteralValid context source resolution

namespace IntegerLiteralValid

theorem requirement_valid
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (valid : IntegerLiteralValid context source resolution) :
    RequirementValid context resolution.requirement := by
  cases valid with
  | word _ _ evidence | integer _ _ evidence => exact ⟨_, evidence⟩

theorem target_supported
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (valid : IntegerLiteralValid context source resolution) :
    resolution.targetType = .word ∨ resolution.targetType = .integer := by
  cases valid with
  | word _ target_eq _ => exact .inl target_eq
  | integer _ target_eq _ => exact .inr target_eq

/-- Every declaratively valid integer-literal resolution selects an
admissible primitive target type. -/
theorem target_type_admissible
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (binders : TypeParameterBindersWellFormed context)
    (valid : IntegerLiteralValid context source resolution) :
    TypeAdmissible context resolution.targetType := by
  cases valid with
  | word _ targetEq _ =>
      rw [targetEq]
      exact TypeAdmissible.word binders
  | integer _ targetEq _ =>
      rw [targetEq]
      exact TypeAdmissible.integer binders

/-- Literal validity is stable under lexical-context growth when the target
retains the same signature catalog and solved requirement ledger. -/
theorem transportContext
    {sourceContext targetContext : Context}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (signatures_eq : targetContext.signatures = sourceContext.signatures)
    (solved_eq : targetContext.solvedRequirements =
      sourceContext.solvedRequirements)
    (assumptions_mono : sourceContext.assumptions ⊆
      targetContext.assumptions)
    (valid : IntegerLiteralValid sourceContext source resolution) :
    IntegerLiteralValid targetContext source resolution := by
  cases valid with
  | word meaning target_eq evidence =>
      exact .word meaning target_eq
        (evidence.transportContext signatures_eq solved_eq assumptions_mono)
  | integer meaning target_eq evidence =>
      exact .integer meaning target_eq
        (evidence.transportContext signatures_eq solved_eq assumptions_mono)

end IntegerLiteralValid

/-- Compatibility literal nodes are the strict primitive-Word form. -/
inductive WordLiteralValid : Syntax.CoreLiteralValue → Prop where
  | intro {source : Syntax.CoreLiteralValue} {value : Nat}
      (meaning : NumericLiteralDenotes source value) :
      WordLiteralValid source

end Solcore.SourceSemantics
