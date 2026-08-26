import Solcore.Surface.Multi.LocationProperties
import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- A leaf location fragment retains exactly one physical source anchor. -/
def SingleAnchorLocationEvidence
    (file : WorkspaceFile)
    (tokens : List Token)
    (fragment : LocationFragment) : Prop :=
  ∃ anchor : SourceAnchor file tokens,
    fragment.roots = [anchor.span] ∧
      fragment.inventory.spans = [anchor.span] ∧
      fragment.inventory.containments = [] ∧
      fragment.ValidFor file ∧ fragment.Nested

namespace SingleAnchorLocationEvidence

/-- The sole root of a single-anchor fragment is contained by its own span. -/
theorem rootsContainedBy
    {file : WorkspaceFile}
    {tokens : List Token}
    {fragment : LocationFragment}
    (evidence : SingleAnchorLocationEvidence file tokens fragment) :
    ∃ anchor : SourceAnchor file tokens,
      fragment.RootsContainedBy anchor.span := by
  rcases evidence with
    ⟨anchor, rootsEq, spansEq, _containmentsEq, valid, _nested⟩
  refine ⟨anchor, ?_⟩
  intro root member
  rw [rootsEq] at member
  simp only [List.mem_singleton] at member
  subst root
  have anchorValid : anchor.span.ValidFor file :=
    valid anchor.span (by
      rw [spansEq]
      simp)
  exact SourceSpan.Contains.refl anchorValid.2.1

end SingleAnchorLocationEvidence

namespace RuleReduction

/-- A terminal-only assignment-operator reduction retains exactly one physical
source anchor and no internal containment edge. -/
theorem assignmentOperator_location
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assignmentOperator)}
    {output : RuleValue .assignmentOperator}
    (owned : TokensOwnedBy file tokens)
    (reduces : RuleReduction file tokens .assignmentOperator origin finish
      input output) :
    SingleAnchorLocationEvidence file tokens
      (LocationFragment.ofAssignmentOperator output) := by
  cases reduces with
  | assignmentOperatorEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorAddEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorSubtractEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorBitXorEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorBitAndEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorBitOrEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]
  | assignmentOperatorModuloEqual _ _ terminal =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.assignmentOperator, RuleReduction.terminalLoc,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        LocationFragment.Nested, LocationInventory.Nested,
        MatchedTerminal.span_validFor]

/-- A terminal-only literal reduction retains exactly one physical source
anchor and no internal containment edge. -/
theorem literal_location
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .literal)}
    {output : RuleValue .literal}
    (owned : TokensOwnedBy file tokens)
    (reduces : RuleReduction file tokens .literal origin finish input output) :
    SingleAnchorLocationEvidence file tokens
      (LocationFragment.ofLiteral output) := by
  cases reduces with
  | literalDecimal _ _ terminal payload projects =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.terminalLoc, LocationFragment.ValidFor,
        LocationInventory.ValidFor, LocationFragment.Nested,
        LocationInventory.Nested, MatchedTerminal.span_validFor]
  | literalHexadecimal _ _ terminal payload projects =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.terminalLoc, LocationFragment.ValidFor,
        LocationInventory.ValidFor, LocationFragment.Nested,
        LocationInventory.Nested, MatchedTerminal.span_validFor]
  | literalString _ _ terminal payload projects =>
      refine ⟨terminal.sourceAnchor owned (by simp), ?_⟩
      simp [RuleReduction.terminalLoc, LocationFragment.ValidFor,
        LocationInventory.ValidFor, LocationFragment.Nested,
        LocationInventory.Nested, MatchedTerminal.span_validFor]

end RuleReduction

end Solcore.Surface.Multi
