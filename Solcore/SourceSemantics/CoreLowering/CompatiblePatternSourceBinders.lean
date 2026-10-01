import Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
import Solcore.SourceSemantics.Patterns

/-! The actual pattern compiler and independent source typing consume the
same prefix program. This yields the complete ordered source binders without
running a matcher or inferring source metadata from a native type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatiblePatternCertificates

theorem Tree.source_binders
    {compilation : Compilation} {source : TypedSource} {site : StatementId}
    {span : Syntax.SourceSpan} {scope : Scope} {expected : TypeSystem.Ty}
    {instructions rest : List MatchPatternInstruction} {compiled : Pattern}
    (tree : Tree compilation source site span scope expected instructions compiled rest) :
    ∀ {context : SourceSemantics.Context} {sourceType : TypeSystem.Ty}
      {requirements : List RequirementId} {binders : List TypedBinder}
      {sourceRest : List MatchPatternInstruction},
      PatternInstructionHasType context instructions sourceType requirements binders sourceRest →
      sourceRest = rest ∧ compiled.bindings.map Prod.fst = binders := by
  induction tree using Tree.rec
      (motive_2 := fun types instructions patterns rest _ =>
        ∀ {context : SourceSemantics.Context} {sourceTypes : List TypeSystem.Ty}
          {requirements : List RequirementId} {binders : List TypedBinder}
          {sourceRest : List MatchPatternInstruction},
          PatternInstructionsHaveTypes context instructions sourceTypes requirements binders sourceRest →
          sourceTypes.length = types.length →
          sourceRest = rest ∧ (patterns.flatMap (·.bindings)).map Prod.fst = binders) with
  | wildcard => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | binder => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | literal => intro context sourceType requirements binders sourceRest typed; cases typed; exact ⟨rfl, rfl⟩
  | tuple projection unpacked children projectedChildren ih =>
    intro context sourceType requirements binders sourceRest typed
    cases typed with
    | tuple arity elements =>
      exact ih elements (arity.symm.trans (unpackTypes_length unpacked).symm)
  | constructor projection result count resolved coreType raw children projectedChildren registered ih =>
    intro context sourceType requirements binders sourceRest typed
    cases typed with
    | constructor valid arity arguments => exact ih arguments rfl
  | nil =>
    rename_i context sourceTypes requirements binders sourceRest typed length
    have empty : sourceTypes = [] := List.length_eq_zero_iff.mp length
    subst sourceTypes
    cases typed
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i context sourceTypes requirements binders sourceRest typed length
    cases sourceTypes with
    | nil => simp at length
    | cons sourceType sourceTypes =>
      cases typed with
      | cons first remaining =>
        obtain ⟨rfl, firstBinders⟩ := headIH first
        obtain ⟨rfl, remainingBinders⟩ := tailIH remaining (Nat.succ.inj length)
        exact ⟨rfl, by simp only [List.flatMap_cons, List.map_append, firstBinders, remainingBinders]⟩

theorem source_arity_unique
    {firstContext secondContext : SourceSemantics.Context}
    {spelling : MatchPatternSource} {resolution : MatchPatternResolution} {first second : Nat}
    (left : MatchPatternSourceRepresents firstContext spelling resolution first)
    (right : MatchPatternSourceRepresents secondContext spelling resolution second) : first = second := by
  induction left with
  | wildcard => cases right; rfl
  | integerLiteral => cases right; rfl
  | binder => cases right; rfl
  | constructor => cases right; rfl
  | tuple => cases right; rfl
  | group inner ih => cases right with | group other => exact ih other

theorem instruction_binders
    {context : SourceSemantics.Context} {instructions rest : List MatchPatternInstruction}
    {type : TypeSystem.Ty} {requirements : List RequirementId} {binders : List TypedBinder}
    (typed : PatternInstructionHasType context instructions type requirements binders rest) :
    SourceCoreDataPlaces.instructionBinders instructions =
      binders ++ SourceCoreDataPlaces.instructionBinders rest := by
  induction typed using PatternInstructionHasType.rec
      (motive_2 := fun instructions _ _ binders rest _ =>
        SourceCoreDataPlaces.instructionBinders instructions =
          binders ++ SourceCoreDataPlaces.instructionBinders rest) with
  | wildcard => rfl
  | integerLiteral => rfl
  | binder => rfl
  | constructor valid arity arguments ih => exact ih
  | tuple arity elements ih => exact ih
  | nil => rfl
  | cons head tail headIH tailIH => rw [headIH, tailIH, List.append_assoc]

theorem pattern_binders
    {context : SourceSemantics.Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context pattern type binders arity) :
    SourceCoreDataPlaces.patternBinders pattern = binders := by
  have consumed := instruction_binders typed.resolution_type
  cases resolution : pattern.resolution <;>
    simpa [SourceCoreDataPlaces.patternBinders, resolution, MatchPatternResolutionHasType,
      matchPatternResolutionInstructions, SourceCoreDataPlaces.instructionBinders] using consumed

theorem Certificate.source_binders
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {span : Syntax.SourceSpan} {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : Certificate compilation source scope site span expected pattern compiled)
    {context : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context pattern expected binders arity) :
    compiled.bindings.map Prod.fst = binders := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨actualArity, sameInstructions, sourceRoot⟩ := rootInstructions_sound compilation context signatures
    pattern.source pattern.resolution instructions root
  have sameArity := source_arity_unique sourceRoot typed.source_represents
  subst actualArity
  subst instructions
  exact (Tree.source_binders tree typed.resolution_type).2

end Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
