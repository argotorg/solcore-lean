import Solcore.Frontend.RustHull.LiteralCorrespondence

/-! The actual pattern compiler preserves the independent source payload test.
Its supplied scrutinee is already evaluated by the match lowerer; the premise
below permits any expression that reads that value without changing the store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PatternCorrespondence
open Correspondence

inductive PatternResultRel (payload : Core.Ty) : Option Semantics.Value → Core.Value → Prop where
  | missed : PatternResultRel payload none (.inLeft payload .unit)
  | matched {source : Semantics.Value} {target : Core.Value}
      (related : ValueRel payload source target) :
      PatternResultRel payload (some source) (.inRight .unit target)

theorem index_preserves (shape : Semantics.Shape) {index : Nat}
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel (coreType shape) source target)
    {payload : Core.Ty} {test : Core.Expr → Core.Expr}
    (compiled : testPattern.test index (coreType shape) = .ok (payload, test))
    {value : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (supplied : Core.Evaluates environment store (value.rename mapping) target store) :
    ∃ result, PatternResultRel payload (Semantics.patternIndex? index shape source) result ∧
      Core.Evaluates environment store ((test value).rename mapping) result store := by
  induction shape generalizing index source target payload test value mapping environment with
  | sum left right _ ih =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, testPattern.test, ↓reduceIte] at compiled
        cases compiled
        cases related with
        | inl related =>
            exact ⟨_, .matched related, .caseLeft supplied (.inRight (.var rfl))⟩
        | inr related =>
            exact ⟨_, .missed, .caseRight supplied (.inLeft .unit)⟩
      · simp only [coreType, testPattern.test, zero, ↓reduceIte] at compiled
        obtain ⟨⟨nestedPayload, nestedTest⟩, nestedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        cases related with
        | inl related =>
            refine ⟨_, ?_, .caseLeft supplied (.inLeft .unit)⟩
            simpa only [Semantics.patternIndex?, zero, ↓reduceIte] using
              (PatternResultRel.missed (payload := nestedPayload))
        | inr related =>
            rename_i sourcePayload targetPayload
            have operand : Core.Evaluates (targetPayload :: environment) store
                ((Core.Expr.var 0).rename mapping.lift) targetPayload store := .var rfl
            obtain ⟨result, resultRelated, evaluated⟩ := ih related nestedCompiled operand
            exact ⟨result, by simpa only [Semantics.patternIndex?, zero, ↓reduceIte] using resultRelated,
              .caseRight supplied evaluated⟩
  | word | bool | unit | product =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, testPattern.test, ↓reduceIte] at compiled
        cases compiled
        exact ⟨_, .matched related, .inRight supplied⟩
      · simp [coreType, testPattern.test, zero, fail] at compiled

theorem test_preserves {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel type source target)
    {pattern : PatKind} {payload : Core.Ty} {test : Core.Expr → Core.Expr}
    (compiled : testPattern type pattern = .ok (payload, test))
    {value : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (supplied : Core.Evaluates environment store (value.rename mapping) target store) :
    ∃ result, PatternResultRel payload (Semantics.patternPayload? sourceType pattern source) result ∧
      Core.Evaluates environment store ((test value).rename mapping) result store := by
  cases pattern with
  | wildcard | var name =>
      cases compiled
      exact ⟨_, .matched related, .inRight supplied⟩
  | intLit text =>
      simp only [testPattern] at compiled
      obtain ⟨checked, matched, remaining⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      have same := expectType_eq_of_ok matched
      subst type
      obtain ⟨literal, parsed, returned⟩ := lower_bind_eq_ok.mp remaining
      cases returned
      cases related with
      | word word =>
          have compare : Core.Evaluates environment store
              ((Core.Expr.binary .wordEq value (.word literal)).rename mapping)
              (.bool (word == literal)) store := .binary supplied .word rfl
          cases equal : (word == literal) with
          | false =>
              refine ⟨_, ?_, .ifFalse (equal ▸ compare) (.inLeft .unit)⟩
              simpa only [Semantics.patternPayload?, parseWord_some_of_ok parsed, equal,
                Bool.false_eq_true, ↓reduceIte] using (PatternResultRel.missed (payload := .word))
          | true =>
              refine ⟨_, ?_, .ifTrue (equal ▸ compare) (.inRight supplied)⟩
              simpa only [Semantics.patternPayload?, parseWord_some_of_ok parsed, equal,
                ↓reduceIte] using (PatternResultRel.matched (ValueRel.word word))
  | con constructor =>
      cases constructor with
      | inl =>
          cases type <;> simp only [testPattern, fail] at compiled <;> try contradiction
          rename_i left right
          cases compiled
          cases related with
          | inl related => exact ⟨_, .matched related, .caseLeft supplied (.inRight (.var rfl))⟩
          | inr related => exact ⟨_, .missed, .caseRight supplied (.inLeft .unit)⟩
      | inr =>
          cases type <;> simp only [testPattern, fail] at compiled <;> try contradiction
          rename_i left right
          cases compiled
          cases related with
          | inl related => exact ⟨_, .missed, .caseLeft supplied (.inLeft .unit)⟩
          | inr related => exact ⟨_, .matched related, .caseRight supplied (.inRight (.var rfl))⟩
      | inK index =>
          obtain ⟨shape, sourceShape, typeShape⟩ := lowerType_shape typeCompiled
          subst type
          obtain ⟨result, resultRelated, evaluated⟩ := index_preserves shape related compiled supplied
          exact ⟨result, by simpa only [Semantics.patternPayload?, sourceShape,
            Bind.bind, Option.bind_some] using resultRelated, evaluated⟩

end Solcore.Frontend.RustHull.PatternCorrespondence
