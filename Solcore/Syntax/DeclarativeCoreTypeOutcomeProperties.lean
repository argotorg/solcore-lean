import Solcore.Syntax.DeclarativeCoreTypeBranchOutcomeProperties

/-! Deterministic parser-independent ordinary outcomes for Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One prioritized successor-fuel rejection layer excludes ordinary success. -/
theorem TypeExprCoreRejects.disjointOrdinary
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected : Remainder}
    (rejection : TypeExprCoreRejects nestedRejects input rejected) :
    ¬ ∃ value output, TypeExprParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | function branchRejected =>
      rcases branchRejected.keyword_token with ⟨span, rejectedKeyword⟩
      cases successful with
      | function _ successfulKeyword _ successfulParameters
            successfulReturns =>
          exact branchRejected.disjointFunction outcomes successfulKeyword
            successfulParameters successfulReturns
      | comptime _ _ _ successfulMarker _ _ _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | mapping _ _ _ _ successfulMarker _ _ _ _ _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedKeyword openingToken
      | named _ _ successfulName _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulName.2.2.1
  | comptime functionAbsent branchRejected =>
      rcases branchRejected.prefix_tokens with
        ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening
            successfulClosing _ successfulInner =>
          exact branchRejected.disjointComptime outcomes successfulMarker
            successfulOpening successfulInner successfulClosing
      | mapping _ _ _ _ successfulMarker _ _ _ _ _ _ =>
          have impossible := typeTokenAt_kind_eq rejectedMarker
            successfulMarker.1
          simp [ContextualKeyword.spelling] at impossible
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedMarker successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedMarker openingToken
      | named comptimeAbsent _ _ _ _ =>
          exact comptimeAbsent
            ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
  | mapping functionAbsent comptimeAbsent branchRejected =>
      rcases branchRejected.prefix_tokens with
        ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening successfulArrow
            successfulClosing _ successfulKey successfulValue =>
          exact branchRejected.disjointMapping outcomes successfulMarker
            successfulOpening successfulKey successfulArrow successfulValue
            successfulClosing
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedMarker successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedMarker openingToken
      | named _ mappingAbsent _ _ _ =>
          exact mappingAbsent
            ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
  | proxy functionAbsent comptimeAbsent mappingAbsent branchRejected =>
      cases branchRejected with
      | innerRejected markerSpan rejectedMarker innerRejected =>
          cases successful with
          | function _ successfulKeyword _ _ _ =>
              exact typeTokenAbsent_conflicts_token functionAbsent
                successfulKeyword.1
          | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
              exact comptimeAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
              exact mappingAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | proxy _ successfulMarker _ successfulInner =>
              have afterMarkerEq := typeExactToken_output_unique
                rejectedMarker successfulMarker
              subst afterMarkerEq
              exact outcomes.successRejectDisjoint innerRejected
                ⟨_, _, successfulInner⟩
          | tuple _ successfulValues =>
              rcases successfulValues.opening_token with
                ⟨_, openingToken⟩
              cases typeTokenAt_kind_eq rejectedMarker.1 openingToken
          | named _ _ successfulName _ _ =>
              cases typeTokenAt_kind_eq rejectedMarker.1
                successfulName.2.2.1
  | tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
        branchRejected =>
      cases branchRejected with
      | selected openingSpan openingParsed valuesRejected =>
          cases successful with
          | function _ successfulKeyword _ _ _ =>
              exact typeTokenAbsent_conflicts_token functionAbsent
                successfulKeyword.1
          | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
              exact comptimeAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
              exact mappingAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | proxy _ successfulMarker _ _ =>
              exact typeTokenAbsent_conflicts_token atAbsent
                successfulMarker.1
          | tuple _ successfulValues =>
              exact valuesRejected.disjointTypeList outcomes
                ⟨_, _, successfulValues⟩
          | named _ _ successfulName _ _ =>
              cases typeTokenAt_kind_eq openingParsed.1
                successfulName.2.2.1
  | named functionAbsent comptimeAbsent mappingAbsent atAbsent
        leftParenAbsent identifierPresent branchRejected =>
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
          exact mappingAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | proxy _ successfulMarker _ _ =>
          exact typeTokenAbsent_conflicts_token atAbsent successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          exact typeTokenAbsent_conflicts_token leftParenAbsent openingToken
      | named _ _ successfulName _ successfulArguments =>
          exact branchRejected.disjointNamed outcomes successfulName
            successfulArguments
  | final functionAbsent comptimeAbsent mappingAbsent atAbsent
        leftParenAbsent identifierAbsent =>
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
          exact mappingAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | proxy _ successfulMarker _ _ =>
          exact typeTokenAbsent_conflicts_token atAbsent successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          exact typeTokenAbsent_conflicts_token leftParenAbsent openingToken
      | named _ _ successfulName _ _ =>
          exact identifierAbsent ⟨_, _, successfulName.2.2.1⟩

/-- Every executable fuel layer has deterministic, exclusive outcomes. -/
theorem typeExprDeterministicOutcomeSpecWithFuel :
    ∀ fuel, DeterministicOutcomeSpec TypeExprOrdinaryParses
      (TypeExprRejectsWithFuel fuel)
  | 0 => {
      successOutputUnique := TypeExprParses.output_unique
      successRejectDisjoint := by simp [TypeExprRejectsWithFuel]
    }
  | fuel + 1 => {
      successOutputUnique := TypeExprParses.output_unique
      successRejectDisjoint := by
        intro input rejected rejection
        exact rejection.disjointOrdinary
          (typeExprDeterministicOutcomeSpecWithFuel fuel)
    }

/-- The public Core type grammar has deterministic ordinary success and exact
rejection outcomes. -/
theorem typeExprDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeExprOrdinaryParses TypeExprRejects where
  successOutputUnique := TypeExprParses.output_unique
  successRejectDisjoint := by
    intro input rejected rejection
    exact (typeExprDeterministicOutcomeSpecWithFuel
      (typeExprPublicFuel input)).successRejectDisjoint rejection

end Solcore.Syntax.DeclarativeGrammar
