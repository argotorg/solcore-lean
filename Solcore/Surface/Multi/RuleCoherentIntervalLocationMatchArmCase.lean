import Solcore.Surface.Multi.RuleCoherentIntervalLocation
import Solcore.Surface.Multi.SourceRuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

private theorem ofPatternList_eq_merge_map (patterns : List Pattern) :
    LocationFragment.ofPatternList patterns =
      LocationFragment.merge (patterns.map LocationFragment.ofPattern) := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofPatternList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;> simp

private theorem ofPatternNonempty_eq_merge_map
    (patterns : NonemptyList Pattern) :
    LocationFragment.ofPatternNonempty patterns =
      LocationFragment.merge
        ((patterns.head :: patterns.tail).map LocationFragment.ofPattern) := by
  rw [LocationFragment.ofPatternNonempty, ofPatternList_eq_merge_map]
  apply LocationFragment.eq_of_fields <;> simp

private theorem ofStatementList_eq_merge_map (statements : List Statement) :
    LocationFragment.ofStatementList statements =
      LocationFragment.merge
        (statements.map LocationFragment.ofStatement) := by
  induction statements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofStatementList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;> simp

@[simp] private theorem ofStatementList_roots (statements : List Statement) :
    (LocationFragment.ofStatementList statements).roots =
      statements.map (fun statement => statement.span) := by
  induction statements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofStatementList,
        LocationFragment.merge_roots]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        LocationFragment.ofStatement_roots, inductionHypothesis, List.map_cons]
      rfl

@[simp] private theorem getLastD_cons {alpha : Type}
    (fallback head : alpha) (tail : List alpha) :
    (head :: tail).getLastD fallback = tail.getLastD head := by
  cases tail <;> simp [List.getLastD]

private theorem getLastD_mem_cons {alpha : Type}
    (fallback : alpha) (tail : List alpha) :
    tail.getLastD fallback ∈ fallback :: tail := by
  induction tail generalizing fallback with
  | nil => simp [List.getLastD]
  | cons head rest inductionHypothesis =>
      have member := inductionHypothesis head
      simp [List.getLastD] at member ⊢

private theorem ordered_head_origin_le
    {file : WorkspaceFile} {tokens : List Token}
    (head : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens)
    (ordered : SourceAnchorTrace.Ordered (head :: tail)) :
    ∀ anchor ∈ head :: tail, head.origin.val ≤ anchor.origin.val := by
  intro anchor member
  rcases List.mem_cons.mp member with rfl | tailMember
  · exact Nat.le_refl _
  · have headBefore : head.finish.val ≤ anchor.origin.val :=
      (List.pairwise_cons.mp ordered).1 anchor tailMember
    exact Nat.le_trans head.occupied.1.2.1 headBefore

private theorem ordered_finish_le_getLastD_finish
    {file : WorkspaceFile} {tokens : List Token}
    (head : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens)
    (ordered : SourceAnchorTrace.Ordered (head :: tail)) :
    ∀ anchor ∈ head :: tail,
      anchor.finish.val ≤ (tail.getLastD head).finish.val := by
  induction tail generalizing head with
  | nil =>
      intro anchor member
      simp only [List.mem_singleton] at member
      subst anchor
      exact Nat.le_refl _
  | cons next rest inductionHypothesis =>
      rw [getLastD_cons]
      intro anchor member
      rcases List.mem_cons.mp member with rfl | tailMember
      · have lastMember : rest.getLastD next ∈ next :: rest :=
          getLastD_mem_cons next rest
        have beforeLast : anchor.finish.val ≤
            (rest.getLastD next).origin.val :=
          (List.pairwise_cons.mp ordered).1 _ lastMember
        exact Nat.le_trans beforeLast
          (rest.getLastD next).occupied.1.2.1
      · exact inductionHypothesis next (List.pairwise_cons.mp ordered).2
          anchor tailMember

private theorem ofBody_armBody
    {file : WorkspaceFile} {tokens : List Token}
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement) :
    LocationFragment.ofBody (RuleReduction.armBody fatArrow statements) =
      LocationFragment.locatedWithPromotedRoots
        (RuleReduction.armBody fatArrow statements).span [fatArrow.span]
        [LocationFragment.ofStatementList statements] := by
  cases statements with
  | nil =>
      unfold RuleReduction.armBody RuleReduction.emptyAt
      rw [LocationFragment.ofBody_matchArm]
  | cons first rest =>
      unfold RuleReduction.armBody RuleReduction.between
      rw [LocationFragment.ofBody_matchArm]

theorem matchArm_patterns_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofPatternNonempty patterns).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) := by
  rw [ofPatternNonempty_eq_merge_map]
  apply LocationFragment.IsSubfragmentOf.merge_map
  intro pattern member
  rcases List.mem_cons.mp member with head | tail
  · subst pattern
    have inside : EbnfValue.ContainsRuleValue file tokens
        (inputValue
          (RuleReduction.matchArm origin finish pipe patterns fatArrow
            statements witness)) .pattern patterns.head :=
      .sequence
        (.tail
          (.head
            (.list1Head (.rule .pattern patterns.head))))
    simpa [RuleLocationView.ofRuleValue] using
      inside.locationFragment_isSubfragment
  · have inside : EbnfValue.ContainsRuleValue file tokens
        (inputValue
          (RuleReduction.matchArm origin finish pipe patterns fatArrow
            statements witness)) .pattern pattern :=
      .sequence
        (.tail
          (.head
            (.list1Tail (List.mem_map_of_mem tail)
              (.rule .pattern pattern))))
    simpa [RuleLocationView.ofRuleValue] using
      inside.locationFragment_isSubfragment

theorem matchArm_statements_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofStatementList statements).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) := by
  rw [ofStatementList_eq_merge_map]
  apply LocationFragment.IsSubfragmentOf.merge_map
  intro statement member
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) .armStatement statement :=
    .sequence
      (.tail
        (.tail
          (.tail
            (.head
              (.star (List.mem_map_of_mem member)
                (.rule .armStatement statement))))))
  simpa [RuleLocationView.ofRuleValue] using
    inside.locationFragment_isSubfragment

theorem matchArm_fatArrow_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.raw fatArrow.span).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) := by
  have inside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
      (inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) (.symbol .fatArrow) fatArrow :=
    .sequence (.tail (.tail (.head (.terminal _ fatArrow))))
  simpa [MatchedTerminal.locationFragment] using
    inside.locationFragment_isSubfragment

private theorem matchArmBody_validFor
    {file : WorkspaceFile}
    (bodySpan fatArrowSpan : SourceSpan)
    (statements : LocationFragment)
    (bodyValid : bodySpan.ValidFor file)
    (fatArrowValid : fatArrowSpan.ValidFor file)
    (statementsValid : statements.ValidFor file) :
    (LocationFragment.locatedWithPromotedRoots bodySpan [fatArrowSpan]
      [statements]).ValidFor file := by
  intro span member
  rw [LocationFragment.locatedWithPromotedRoots_spans] at member
  rw [LocationFragment.merge_spans] at member
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
  rcases List.mem_cons.mp member with outer | member
  · subst span
    exact bodyValid
  rcases List.mem_append.mp member with arrow | childMember
  · simp only [List.mem_singleton] at arrow
    subst span
    exact fatArrowValid
  · exact statementsValid span childMember

private theorem matchArmBody_nested
    (bodySpan fatArrowSpan : SourceSpan)
    (statements : LocationFragment)
    (statementsContained : statements.RootsContainedBy bodySpan)
    (statementsNested : statements.Nested) :
    (LocationFragment.locatedWithPromotedRoots bodySpan [fatArrowSpan]
      [statements]).Nested := by
  intro containment member
  rw [LocationFragment.locatedWithPromotedRoots_containments] at member
  simp only [LocationFragment.merge_roots, LocationFragment.merge_containments,
    List.flatMap_singleton, List.mem_append] at member
  rcases member with direct | nested
  · rw [List.mem_map] at direct
    rcases direct with ⟨child, childMember, rfl⟩
    exact statementsContained child childMember
  · exact statementsNested containment nested

private theorem matchArmOutput_validFor
    {file : WorkspaceFile}
    (armSpan : SourceSpan)
    (patterns body : LocationFragment)
    (armValid : armSpan.ValidFor file)
    (patternsValid : patterns.ValidFor file)
    (bodyValid : body.ValidFor file) :
    (LocationFragment.located armSpan
      [LocationFragment.merge [patterns, body]]).ValidFor file := by
  intro span member
  rw [LocationFragment.located_spans] at member
  simp only [LocationFragment.merge_spans, List.flatMap_cons,
    List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append] at member
  rcases member with rfl | patternMember | bodyMember
  · exact armValid
  · exact patternsValid span patternMember
  · exact bodyValid span bodyMember

private theorem matchArmOutput_nested
    (armSpan : SourceSpan)
    (patterns body : LocationFragment)
    (patternsContained : patterns.RootsContainedBy armSpan)
    (bodyContained : body.RootsContainedBy armSpan)
    (patternsNested : patterns.Nested)
    (bodyNested : body.Nested) :
    (LocationFragment.located armSpan
      [LocationFragment.merge [patterns, body]]).Nested := by
  intro containment member
  rw [LocationFragment.located_containments] at member
  simp only [LocationFragment.merge_roots,
    LocationFragment.merge_containments, List.flatMap_cons,
    List.flatMap_nil, List.append_nil,
    List.mem_append] at member
  rcases member with direct | patternNested | bodyNestedMember
  · rw [List.mem_map] at direct
    rcases direct with ⟨child, childMember, rfl⟩
    rcases List.mem_append.mp childMember with patternRoot | bodyRoot
    · exact patternsContained child patternRoot
    · exact bodyContained child bodyRoot
  · exact patternsNested containment patternNested
  · exact bodyNested containment bodyNestedMember

/-- The three geometric facts introduced by the match-arm body constructor.
The enclosing arm span and every pre-existing child fragment are certified
separately by the ordinary interval evidence. -/
structure MatchArmBodyGeometry
    {file : WorkspaceFile} {tokens : List Token}
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement) (armSpan : SourceSpan) : Prop where
  bodyValid : (RuleReduction.armBody fatArrow statements).span.ValidFor file
  statementsContained :
    (LocationFragment.ofStatementList statements).RootsContainedBy
      (RuleReduction.armBody fatArrow statements).span
  bodyContained : armSpan.Contains
    (RuleReduction.armBody fatArrow statements).span

/-- Grammar-ordered semantic anchors for the repeated arm statements. -/
def MatchArmStatementLayout
    {file : WorkspaceFile} {tokens : List Token}
    (statements : List Statement)
    (origin finish : Boundary tokens) : Prop :=
  ∃ anchors : SourceAnchorTrace file tokens,
    anchors.spans = statements.map (fun statement => statement.span) ∧
      anchors.Within origin finish ∧ anchors.Ordered

theorem matchArm_bodyGeometry_of_statementLayout
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) trace)
    (layout : MatchArmStatementLayout (file := file) statements
      origin finish) :
    MatchArmBodyGeometry fatArrow statements witness.span := by
  have arrowEvidence := IntervalLocationEvidence.restrict
    (matchArm_fatArrow_subfragment origin finish pipe patterns fatArrow
      statements witness) inputEvidence
  have arrowValid : fatArrow.span.ValidFor file :=
    arrowEvidence.validFor_and_nested.1 fatArrow.span (by simp)
  have arrowContained : witness.span.Contains fatArrow.span := by
    have allRoots := IntervalLocationEvidence.rootsContainedBy tokensOrdered
      witness.consumed arrowEvidence
    exact allRoots fatArrow.span (by simp)
  cases statements with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · unfold RuleReduction.armBody RuleReduction.emptyAt
        exact ⟨rfl, Nat.le_refl _, arrowValid.2.2.1,
          arrowValid.2.2.2.2, arrowValid.2.2.2.2⟩
      · simp [RuleReduction.armBody, LocationFragment.ofStatementList,
          LocationFragment.RootsContainedBy]
      · unfold RuleReduction.armBody RuleReduction.emptyAt
        exact ⟨arrowContained.1.trans arrowValid.1,
          Nat.le_trans arrowContained.2.1 arrowContained.2.2.1,
          Nat.le_refl _, arrowContained.2.2.2⟩
  | cons first rest =>
      rcases layout with ⟨anchors, anchorSpans, anchorsWithin,
        anchorsOrdered⟩
      cases anchors with
      | nil => simp at anchorSpans
      | cons firstAnchor restAnchors =>
          have spanShape : firstAnchor.span ::
              SourceAnchorTrace.spans restAnchors =
              first.span :: rest.map (fun statement => statement.span) := by
            exact anchorSpans
          have firstSpan : firstAnchor.span = first.span :=
            (List.cons.inj spanShape).1
          have restSpans : SourceAnchorTrace.spans restAnchors =
              rest.map (fun statement => statement.span) :=
            (List.cons.inj spanShape).2
          let lastAnchor := restAnchors.getLastD firstAnchor
          let lastStatement := rest.getLastD first
          have lastSpan : lastAnchor.span = lastStatement.span := by
            calc
              lastAnchor.span =
                  (restAnchors.map (fun anchor => anchor.span)).getLastD
                    firstAnchor.span := by
                exact List.getLastD_map.symm
              _ = (rest.map (fun statement => statement.span)).getLastD
                    first.span := by
                rw [firstSpan]
                exact congrArg (fun spans => spans.getLastD first.span)
                  restSpans
              _ = lastStatement.span := by
                exact List.getLastD_map
          have lastMember : lastAnchor ∈ firstAnchor :: restAnchors :=
            getLastD_mem_cons firstAnchor restAnchors
          have originsOrdered : firstAnchor.origin.val ≤
              lastAnchor.origin.val :=
            ordered_head_origin_le firstAnchor restAnchors anchorsOrdered
              lastAnchor lastMember
          let bodyAnchor := SourceAnchor.between firstAnchor lastAnchor
            originsOrdered
          have bodySpan : bodyAnchor.span =
              (RuleReduction.armBody fatArrow (first :: rest)).span := by
            simp only [RuleReduction.armBody, bodyAnchor,
              SourceAnchor.between_span]
            rw [firstSpan, lastSpan]
            unfold lastStatement RuleReduction.between
            rfl
          refine ⟨?_, ?_, ?_⟩
          · rw [← bodySpan]
            exact bodyAnchor.span_validFor tokensOrdered
          · unfold LocationFragment.RootsContainedBy
            rw [ofStatementList_roots]
            intro root rootMember
            have available : root ∈
                SourceAnchorTrace.spans (firstAnchor :: restAnchors) := by
              rw [anchorSpans]
              exact rootMember
            rw [SourceAnchorTrace.spans, List.mem_map] at available
            rcases available with ⟨anchor, anchorMember, rfl⟩
            have inside : anchor.Within firstAnchor.origin lastAnchor.finish :=
              ⟨ordered_head_origin_le firstAnchor restAnchors
                  anchorsOrdered anchor anchorMember,
                ordered_finish_le_getLastD_finish firstAnchor restAnchors
                  anchorsOrdered anchor anchorMember⟩
            rw [← bodySpan]
            exact anchor.containedBy tokensOrdered bodyAnchor.occupied.1 inside
          · have firstInside := anchorsWithin firstAnchor (by simp)
            have lastInside := anchorsWithin lastAnchor lastMember
            have bodyInside : bodyAnchor.Within origin finish :=
              ⟨firstInside.1, lastInside.2⟩
            rw [← bodySpan]
            exact bodyAnchor.containedBy tokensOrdered witness.consumed
              bodyInside

theorem matchArm_locationSound_of_bodyGeometry
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) trace)
    (bodyGeometry : MatchArmBodyGeometry fatArrow statements witness.span) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .matchArm
        (sourceLoc witness {
          patterns := patterns
          body := RuleReduction.armBody fatArrow statements
        })) trace := by
  let patternFragment := LocationFragment.ofPatternNonempty patterns
  let statementFragment := LocationFragment.ofStatementList statements
  let body := RuleReduction.armBody fatArrow statements
  let bodyFragment := LocationFragment.locatedWithPromotedRoots body.span
    [fatArrow.span] [statementFragment]
  have patternsEvidence := IntervalLocationEvidence.restrict
    (matchArm_patterns_subfragment origin finish pipe patterns fatArrow
      statements witness) inputEvidence
  have statementsEvidence := IntervalLocationEvidence.restrict
    (matchArm_statements_subfragment origin finish pipe patterns fatArrow
      statements witness) inputEvidence
  have arrowEvidence := IntervalLocationEvidence.restrict
    (matchArm_fatArrow_subfragment origin finish pipe patterns fatArrow
      statements witness) inputEvidence
  have patternProperties := patternsEvidence.validFor_and_nested
  have statementProperties := statementsEvidence.validFor_and_nested
  have arrowProperties := arrowEvidence.validFor_and_nested
  have patternsContained : patternFragment.RootsContainedBy witness.span :=
    IntervalLocationEvidence.rootsContainedBy tokensOrdered witness.consumed
      patternsEvidence
  have arrowContained : witness.span.Contains fatArrow.span := by
    have allRoots := IntervalLocationEvidence.rootsContainedBy tokensOrdered
      witness.consumed arrowEvidence
    exact allRoots fatArrow.span (by simp)
  have arrowValid : fatArrow.span.ValidFor file :=
    arrowProperties.1 fatArrow.span (by simp)
  have bodyValid : bodyFragment.ValidFor file := by
    apply matchArmBody_validFor
    · exact bodyGeometry.bodyValid
    · exact arrowValid
    · exact statementProperties.1
  have bodyNested : bodyFragment.Nested := by
    apply matchArmBody_nested
    · exact bodyGeometry.statementsContained
    · exact statementProperties.2
  have bodyContained : bodyFragment.RootsContainedBy witness.span := by
    intro root member
    rw [show bodyFragment = LocationFragment.locatedWithPromotedRoots
      body.span [fatArrow.span] [statementFragment] by rfl,
      LocationFragment.locatedWithPromotedRoots_roots] at member
    rcases List.mem_cons.mp member with bodyRoot | arrowRoot
    · subst root
      exact bodyGeometry.bodyContained
    · have : root = fatArrow.span := List.mem_singleton.mp arrowRoot
      subst root
      exact arrowContained
  have outputValid :
      (LocationFragment.located witness.span
        [LocationFragment.merge [patternFragment, bodyFragment]]).ValidFor
          file := by
    apply matchArmOutput_validFor
    · exact witness.consumed.validFor tokensOrdered
    · exact patternProperties.1
    · exact bodyValid
  have outputNested :
      (LocationFragment.located witness.span
        [LocationFragment.merge [patternFragment, bodyFragment]]).Nested := by
    apply matchArmOutput_nested
    · exact patternsContained
    · exact bodyContained
    · exact patternProperties.2
    · exact bodyNested
  have inputHasRoot :
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)).roots ≠ [] := by
    exact (matchArm_fatArrow_subfragment origin finish pipe patterns fatArrow
      statements witness).roots_ne_nil (by simp)
  let armAnchor : SourceAnchor file tokens := {
    origin := origin
    finish := finish
    span := witness.span
    occupied := ⟨witness.consumed,
      IntervalLocationEvidence.occupied_of_roots_ne_nil inputEvidence
        inputHasRoot⟩
  }
  have traceProperties := inputEvidence.trace_within_and_ordered
  have reconstructed : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.located witness.span
        [LocationFragment.merge [patternFragment, bodyFragment]]) trace := by
    refine ⟨[armAnchor], rfl, ?_, traceProperties.1, traceProperties.2,
      outputValid, outputNested⟩
    intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  apply IntervalLocationEvidence.replaceFragment _ reconstructed
  simp only [RuleLocationView.ofRuleValue, sourceLoc,
    LocationFragment.ofMatchArm_mk, LocationFragment.ofMatchArmPayload]
  rw [ofBody_armBody]

theorem matchArm_locationSound_of_statementLayout
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) trace)
    (layout : MatchArmStatementLayout (file := file) statements
      origin finish) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .matchArm
        (sourceLoc witness {
          patterns := patterns
          body := RuleReduction.armBody fatArrow statements
        })) trace := by
  exact matchArm_locationSound_of_bodyGeometry tokensOrdered origin finish
    pipe patterns fatArrow statements witness trace inputEvidence
      (matchArm_bodyGeometry_of_statementLayout tokensOrdered origin finish
        pipe patterns fatArrow statements witness trace inputEvidence layout)

theorem matchArm_coherentRootLocationSound_of_statementLayout
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .matchArm origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .matchArm origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .matchArm origin finish context)
        priorValues}
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (inputEq : inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness) =
      RootAction.unpack .matchArm
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .matchArm origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace}
    (layout : MatchArmStatementLayout (file := file) statements
      origin finish) :
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root .matchArm origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .matchArm origin finish context)
          complete priorValues)
        (sourceLoc witness {
          patterns := patterns
          body := RuleReduction.armBody fatArrow statements
        })
        (inputEq ▸ RuleReduction.matchArm origin finish pipe patterns
          fatArrow statements witness)) trace carries := by
  intro inputEvidence
  have unpackEvidence := IntervalLocationEvidence.replaceFragment
    (RootAction.unpack_locationFragment .matchArm
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens .matchArm origin finish context)
        complete priorValues)).symm inputEvidence
  rw [← inputEq] at unpackEvidence
  exact matchArm_locationSound_of_statementLayout tokensOrdered origin finish
    pipe patterns fatArrow statements witness trace unpackEvidence layout

end RuleReduction

end Solcore.Surface.Multi
