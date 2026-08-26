import Solcore.Surface.Multi.Location
import Solcore.Surface.Multi.Properties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace TokenSpansOrdered

/-- Earlier retained tokens end no later than a later token starts. -/
theorem getElem_end_le_start
    {tokens : List Token}
    (ordered : TokenSpansOrdered tokens)
    {earlier later : Nat}
    (earlierBound : earlier < tokens.length)
    (laterBound : later < tokens.length)
    (before : earlier < later) :
    tokens[earlier].span.endByte ≤ tokens[later].span.startByte := by
  rw [TokenSpansOrdered, List.pairwise_iff_getElem] at ordered
  exact ordered earlier later earlierBound laterBound before

end TokenSpansOrdered

namespace TokensOwnedBy

/-- Every indexed retained token has a source-valid span. -/
theorem getElem_valid
    {file : WorkspaceFile}
    {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (index : Nat)
    (bound : index < tokens.length) :
    tokens[index].span.ValidFor file := by
  exact owned tokens[index] (List.getElem_mem bound)

end TokensOwnedBy

namespace ConsumedSpan

/-- A consumed chart interval is source-valid when its retained token stream is
physically ordered. -/
theorem validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {span : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (consumed : ConsumedSpan file tokens origin finish span) :
    span.ValidFor file := by
  unfold ConsumedSpan at consumed
  rcases consumed with ⟨owned, intervalOrdered, shape⟩
  split at shape
  · rename_i occupied
    subst span
    have firstBound : origin.val < tokens.length :=
      Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.zero_lt_of_lt occupied
    have lastBound : Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    have firstValid := owned.getElem_valid origin.val firstBound
    have lastValid := owned.getElem_valid
      (Nat.min finish.val tokens.length - 1) lastBound
    have firstIndexLeLast :
        origin.val ≤ Nat.min finish.val tokens.length - 1 := by
      omega
    have endpointsOrdered :
        tokens[origin.val].span.startByte ≤
          tokens[Nat.min finish.val tokens.length - 1].span.endByte := by
      by_cases same :
          origin.val = Nat.min finish.val tokens.length - 1
      · simpa only [same] using lastValid.2.1
      · have before :
            origin.val < Nat.min finish.val tokens.length - 1 := by
          omega
        exact Nat.le_trans firstValid.2.1
          (Nat.le_trans
            (tokensOrdered.getElem_end_le_start
              firstBound lastBound before)
            lastValid.2.1)
    exact ⟨rfl, endpointsOrdered, lastValid.2.2.1,
      firstValid.2.2.2.1, lastValid.2.2.2.2⟩
  · rename_i vacant
    rcases shape with ⟨byte, boundary, rfl⟩
    unfold BoundaryByte at boundary
    rcases boundary with ⟨_boundaryOwned, byteEq⟩
    split at byteEq
    · rename_i inRange
      subst byte
      have valid := owned.getElem_valid origin.val inRange
      exact ⟨rfl, Nat.le_refl _,
        Nat.le_trans valid.2.1 valid.2.2.1,
        valid.2.2.2.1, valid.2.2.2.1⟩
    · subst byte
      exact ⟨rfl, Nat.le_refl _, Nat.le_refl _,
        isUtf8Boundary_end file.content,
        isUtf8Boundary_end file.content⟩

end ConsumedSpan

namespace ConsumedSpanWitness

/-- Every checked chart-span witness is valid for its source file when the
retained tokens are physically ordered. -/
theorem span_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    witness.span.ValidFor file :=
  ConsumedSpan.validFor tokensOrdered witness.consumed

end ConsumedSpanWitness

namespace SourceLocates

/-- A value located by a checked chart interval has a source-valid wrapper. -/
theorem span_validFor
    {alpha : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {payload : alpha}
    {located : Located alpha}
    (tokensOrdered : TokenSpansOrdered tokens)
    (locates : SourceLocates file tokens origin finish payload located) :
    located.span.ValidFor file := by
  rcases locates with ⟨witness, rfl⟩
  exact witness.span_validFor tokensOrdered

end SourceLocates

namespace Lexes

/-- Successful lexing makes every consumed chart interval source-valid. -/
theorem consumedSpan_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    {origin finish : Boundary tokens}
    {span : SourceSpan}
    (lexical : Lexes file tokens comments)
    (consumed : ConsumedSpan file tokens origin finish span) :
    span.ValidFor file :=
  ConsumedSpan.validFor lexical.tokenSpansOrdered consumed

/-- Successful lexing makes every checked source-located wrapper valid. -/
theorem sourceLocates_span_validFor
    {alpha : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    {origin finish : Boundary tokens}
    {payload : alpha}
    {located : Located alpha}
    (lexical : Lexes file tokens comments)
    (locates : SourceLocates file tokens origin finish payload located) :
    located.span.ValidFor file :=
  SourceLocates.span_validFor lexical.tokenSpansOrdered locates

end Lexes

end Solcore.Surface.Multi
