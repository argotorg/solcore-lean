import Solcore.Surface.Multi.RuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace IntervalLocationEvidence

/-- Expand the location inventory hidden by one opaque assembly token.  The
token's source anchor remains the semantic root and the physical trace is
unchanged. -/
theorem enrichAssemblySlice
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {slice : AssemblySlice}
    {trace : SourceAnchorTrace file tokens}
    (facts : AssemblySliceLocationFacts file slice)
    (evidence : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.raw slice.span) trace) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofAssemblySlice slice) trace := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, traceWithin,
      traceOrdered, _rawValid, _rawNested⟩
  refine ⟨rootAnchors, ?_, rootsWithin, traceWithin, traceOrdered, ?_, ?_⟩
  · simpa using rootSpans
  · intro span member
    rw [LocationFragment.ofAssemblySlice_spans] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact facts.sliceValid
    · exact facts.openBraceValid
    · exact facts.contentsValid
    · exact facts.closeBraceValid
  · intro containment member
    rw [LocationFragment.ofAssemblySlice_containments] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact facts.containsOpenBrace
    · exact facts.containsContents
    · exact facts.containsCloseBrace

end IntervalLocationEvidence

namespace RuleReduction

/-- The assembly rule expands the opaque lexical payload into its exact slice
inventory and then installs the statement's checked outer span. -/
theorem assemblyStatement_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments)
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)}
    {output : RuleValue .assemblyStatement}
    (reduces : RuleReduction file tokens .assemblyStatement
      origin finish input output) :
    RuleReduction.LocationSound reduces := by
  cases reduces with
  | assemblyStatement origin finish assemblyKeyword assemblyToken slice
      projects witness =>
      intro trace evidence
      rcases lexical.assemblySlice_locations_of_projects
          assemblyToken projects with
        ⟨tokenSpan, facts⟩
      have tokenEvidence : IntervalLocationEvidence file tokens origin finish
          (LocationFragment.raw assemblyToken.span) trace := by
        exact IntervalLocationEvidence.restrict (evidence := evidence) (by
          simp only [m2cV1, m2cV1Rhs, sequence, hardKeyword, category,
            terminal, EbnfExpr.children]
          simp only [EbnfValue.locationFragment_sequence,
            EbnfValues.locationFragment_cons,
            EbnfValue.locationFragment_terminalAtom,
            EbnfValues.locationFragment_nil]
          simp [LocationFragment.IsSubfragmentOf,
            MatchedTerminal.locationFragment])
      have sliceEvidence : IntervalLocationEvidence file tokens origin finish
          (LocationFragment.ofAssemblySlice slice) trace := by
        apply IntervalLocationEvidence.enrichAssemblySlice facts
        exact IntervalLocationEvidence.replaceFragment
          (congrArg LocationFragment.raw tokenSpan) tokenEvidence
      have wrapped := IntervalLocationEvidence.locatedByWitness
        lexical.tokenSpansOrdered witness sliceEvidence (by simp)
      simpa [RuleLocationView.ofRuleValue, sourceLoc,
        LocationFragment.ofStatementPayload] using wrapped

end RuleReduction

end Solcore.Surface.Multi
