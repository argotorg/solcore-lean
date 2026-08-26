import Solcore.Surface.Multi.RuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Location evidence for the complete source file.  Unlike an ordinary
parser interval, its root may be empty and therefore does not require an
occupied token anchor. -/
def WholeFileLocationEvidence
    (file : WorkspaceFile) (tokens : List Token)
    (fragment : LocationFragment)
    (trace : SourceAnchorTrace file tokens) : Prop :=
  fragment.roots = [SourceSpan.fullFile file] ∧
    trace.Within (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) ∧
    trace.Ordered ∧ fragment.ValidFor file ∧ fragment.Nested

namespace WholeFileLocationEvidence

/-- Whole-file evidence exposes the executable specification's public
location invariant. -/
theorem everyLocationValid
    {file : WorkspaceFile} {tokens : List Token}
    {module : ParsedModuleV1}
    {trace : SourceAnchorTrace file tokens}
    (evidence : WholeFileLocationEvidence file tokens
      (LocationFragment.ofParsedModule module) trace) :
    EveryLocationValid file module := by
  exact ⟨evidence.2.2.2.1, evidence.2.2.2.2⟩

/-- Install the full-file root around evidence accumulated by the complete
module prefix, including the empty-file case. -/
theorem wrap
    {file : WorkspaceFile} {tokens : List Token}
    {children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (evidence : IntervalLocationEvidence file tokens
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
      children trace) :
    WholeFileLocationEvidence file tokens
      (LocationFragment.located (SourceSpan.fullFile file) [children])
      trace := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, _rootsWithin, traceWithin, traceOrdered,
      childrenValid, childrenNested⟩
  refine ⟨rfl, traceWithin, traceOrdered, ?_, ?_⟩
  · intro span member
    rw [LocationFragment.located_spans] at member
    rcases List.mem_cons.mp member with outer | childMember
    · subst span
      exact SourceSpan.fullFile_validFor file
    · exact childrenValid span (by simpa using childMember)
  · intro containment member
    rw [LocationFragment.located_containments] at member
    rcases List.mem_append.mp member with direct | nestedMember
    · rw [List.mem_map] at direct
      rcases direct with ⟨child, childMember, rfl⟩
      apply SourceSpan.fullFile_contains_of_validFor
      have anchorMember : child ∈ rootAnchors.spans := by
        rw [rootSpans]
        simpa using childMember
      rw [SourceAnchorTrace.spans, List.mem_map] at anchorMember
      rcases anchorMember with ⟨anchor, _member, rfl⟩
      exact anchor.span_validFor tokensOrdered
    · exact childrenNested containment (by simpa using nestedMember)

end WholeFileLocationEvidence

namespace RuleReduction

/-- The module reduction preserves the complete trace while introducing the
possibly empty full-file root. -/
def ModuleLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .module)}
    {output : RuleValue .module}
    (_reduces : RuleReduction file tokens .module origin finish input output) :
    Prop :=
  ∀ trace : SourceAnchorTrace file tokens,
    IntervalLocationEvidence file tokens origin finish
        input.locationFragment trace →
      WholeFileLocationEvidence file tokens
        (RuleLocationView.ofRuleValue .module output) trace

/-- Every module reduction satisfies the dedicated whole-file location
contract, including empty and trivia-only sources. -/
theorem module_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .module)}
    {output : RuleValue .module}
    (reduces : RuleReduction file tokens .module origin finish input output) :
    RuleReduction.ModuleLocationSound reduces := by
  cases reduces with
  | module origin finish items eof originEq finishEq eofValue =>
      subst origin
      subst finish
      intro trace evidence
      simp only [m2cV1, m2cV1Rhs, sequence, star, nonterminal,
        terminal] at evidence
      rw [EbnfValue.transport_self] at evidence
      rw [EbnfValue.locationFragment_sequence] at evidence
      rw [EbnfValues.locationFragment_cons] at evidence
      rw [EbnfValue.locationFragment_star] at evidence
      rw [EbnfValues.locationFragment_cons] at evidence
      rw [EbnfValue.locationFragment_terminalAtom] at evidence
      rw [EbnfValues.locationFragment_nil] at evidence
      have mappedItems :
          (List.map (fun value => value.locationFragment)
            (items.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
              .topItem))) =
            items.map LocationFragment.ofTopItem := by
        rw [List.map_map]
        apply List.map_congr_left
        intro item _member
        simp [RuleLocationView.ofRuleValue]
      rw [mappedItems] at evidence
      have itemsEvidence : IntervalLocationEvidence file tokens
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
          (LocationFragment.merge
            (items.map LocationFragment.ofTopItem)) trace := by
        simpa [MatchedTerminal.locationFragment] using evidence
      simpa [RuleLocationView.ofRuleValue, RuleReduction.moduleLoc,
        SourceSpan.fullFile] using
          WholeFileLocationEvidence.wrap tokensOrdered itemsEvidence

end RuleReduction

end Solcore.Surface.Multi
