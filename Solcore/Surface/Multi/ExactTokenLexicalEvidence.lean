import Solcore.Surface.Multi.ExactTokenInterval
import Solcore.Surface.Multi.LocationProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A lexically exact assembly token and its parser projection use the same
outer span, so the physical scan plan is the slice plan stored in the AST. -/
theorem MatchedTerminal.physicalTokenPlan_assemblyBlock
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (sourceExact : TokensSourceExact file tokens)
    (matched : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice)
    (projects : AssemblySliceProjects matched slice) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.assemblyBlock slice) slice.span := by
  rcases projects with ⟨token, valueEq, payloadEq⟩
  rcases matched.retained_member_and_span valueEq with
    ⟨member, matchedSpanEq⟩
  have tokenExact := sourceExact token member
  unfold TokenSourceExact at tokenExact
  rw [payloadEq] at tokenExact
  rcases tokenExact with
    ⟨_open, closeCursor, _run, _close, _endEq, _range, sliceEq⟩
  have sourceEq := (owned token member).1
  have tokenSpanEq : token.span = LexicalJudgment.sourceSpan file
      token.span.startByte token.span.endByte := by
    rcases token with ⟨⟨source, startByte, endByte⟩, payload⟩
    simp only at sourceEq ⊢
    subst source
    rfl
  have sliceSpanEq : slice.span = LexicalJudgment.sourceSpan file
      token.span.startByte token.span.endByte := by
    exact congrArg Located.span sliceEq
  have spanEq : matched.span = slice.span :=
    matchedSpanEq.trans (tokenSpanEq.trans sliceSpanEq.symm)
  simp [MatchedTerminal.physicalTokenPlan, valueEq, payloadEq, spanEq]

end Solcore.Surface.Multi
