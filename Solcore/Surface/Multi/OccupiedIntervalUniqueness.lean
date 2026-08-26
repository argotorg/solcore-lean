import Solcore.Surface.Multi.LocationProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Every retained lexical token occupies a nonempty source interval. -/
theorem Lexes.tokenSpansPositive
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    ∀ token ∈ tokens, token.span.startByte < token.span.endByte := by
  intro token member
  rcases (Lexes.retainedTransitions lexical).1 token member with
    normal | assembly
  · rcases normal with ⟨pendingAssembly, candidateClass, winner⟩
    exact (lexer_progress file).2.1 winner.1
  · rcases assembly with ⟨endByte, recognized⟩
    have progress := (lexer_progress file).2.2 recognized
    rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
    have tokenEnd : token.span.endByte = endByte :=
      congrArg (fun value : Token => value.span.endByte) tokenEquation
    rw [tokenEnd]
    exact progress

namespace OccupiedConsumedSpan

/-- On an exact lexical token stream, an occupied source span determines its
chart origin and finish boundaries. -/
theorem interval_eq_of_span_eq
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    (lexical : Lexes file tokens comments)
    {leftOrigin leftFinish rightOrigin rightFinish : Boundary tokens}
    {leftSpan rightSpan : SourceSpan}
    (left : OccupiedConsumedSpan file tokens leftOrigin leftFinish leftSpan)
    (right : OccupiedConsumedSpan file tokens rightOrigin rightFinish rightSpan)
    (spanEq : leftSpan = rightSpan)
    (leftFinishBound : leftFinish.val ≤ tokens.length)
    (rightFinishBound : rightFinish.val ≤ tokens.length) :
    leftOrigin = rightOrigin ∧ leftFinish = rightFinish := by
  rcases left with ⟨leftConsumed, leftOccupied⟩
  rcases right with ⟨rightConsumed, rightOccupied⟩
  unfold ConsumedSpan at leftConsumed rightConsumed
  rcases leftConsumed with ⟨_leftOwned, _leftOrdered, leftShape⟩
  rcases rightConsumed with ⟨_rightOwned, _rightOrdered, rightShape⟩
  simp only [leftOccupied, ↓reduceDIte] at leftShape
  simp only [rightOccupied, ↓reduceDIte] at rightShape
  have leftOriginBound : leftOrigin.val < tokens.length :=
    Nat.lt_of_lt_of_le leftOccupied (Nat.min_le_right _ _)
  have rightOriginBound : rightOrigin.val < tokens.length :=
    Nat.lt_of_lt_of_le rightOccupied (Nat.min_le_right _ _)
  have leftCapPositive : 0 < Nat.min leftFinish.val tokens.length :=
    Nat.zero_lt_of_lt leftOccupied
  have rightCapPositive : 0 < Nat.min rightFinish.val tokens.length :=
    Nat.zero_lt_of_lt rightOccupied
  have leftLastBound : Nat.min leftFinish.val tokens.length - 1 <
      tokens.length :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt leftCapPositive Nat.zero_lt_one)
      (Nat.min_le_right _ _)
  have rightLastBound : Nat.min rightFinish.val tokens.length - 1 <
      tokens.length :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt rightCapPositive Nat.zero_lt_one)
      (Nat.min_le_right _ _)
  have shapedEq := leftShape.symm.trans (spanEq.trans rightShape)
  let sourceStart : SourceSpan → Nat := fun span => span.startByte
  let sourceEnd : SourceSpan → Nat := fun span => span.endByte
  have rawStartEq := congrArg sourceStart shapedEq
  have rawEndEq := congrArg sourceEnd shapedEq
  have startEq : tokens[leftOrigin.val].span.startByte =
      tokens[rightOrigin.val].span.startByte := by
    exact rawStartEq
  have endEq :
      tokens[Nat.min leftFinish.val tokens.length - 1].span.endByte =
        tokens[Nat.min rightFinish.val tokens.length - 1].span.endByte := by
    exact rawEndEq
  have ordered := lexical.tokenSpansOrdered
  have positive := lexical.tokenSpansPositive
  have originValEq : leftOrigin.val = rightOrigin.val := by
    by_cases before : leftOrigin.val < rightOrigin.val
    · have separated := ordered.getElem_end_le_start leftOriginBound
        rightOriginBound before
      have leftPositive := positive tokens[leftOrigin.val]
        (List.getElem_mem leftOriginBound)
      omega
    · by_cases after : rightOrigin.val < leftOrigin.val
      · have separated := ordered.getElem_end_le_start rightOriginBound
          leftOriginBound after
        have rightPositive := positive tokens[rightOrigin.val]
          (List.getElem_mem rightOriginBound)
        omega
      · omega
  have lastValEq : Nat.min leftFinish.val tokens.length - 1 =
      Nat.min rightFinish.val tokens.length - 1 := by
    by_cases before : Nat.min leftFinish.val tokens.length - 1 <
        Nat.min rightFinish.val tokens.length - 1
    · have separated := ordered.getElem_end_le_start leftLastBound
        rightLastBound before
      have rightPositive := positive
        tokens[Nat.min rightFinish.val tokens.length - 1]
        (List.getElem_mem rightLastBound)
      omega
    · by_cases after : Nat.min rightFinish.val tokens.length - 1 <
          Nat.min leftFinish.val tokens.length - 1
      · have separated := ordered.getElem_end_le_start rightLastBound
          leftLastBound after
        have leftPositive := positive
          tokens[Nat.min leftFinish.val tokens.length - 1]
          (List.getElem_mem leftLastBound)
        omega
      · omega
  have finishValEq : leftFinish.val = rightFinish.val := by
    have leftMin : Nat.min leftFinish.val tokens.length = leftFinish.val :=
      Nat.min_eq_left leftFinishBound
    have rightMin : Nat.min rightFinish.val tokens.length = rightFinish.val :=
      Nat.min_eq_left rightFinishBound
    have leftFinishPositive : 0 < leftFinish.val := by
      omega
    have rightFinishPositive : 0 < rightFinish.val := by
      omega
    have lastValEq' : leftFinish.val - 1 = rightFinish.val - 1 := by
      simpa only [leftMin, rightMin] using lastValEq
    omega
  exact ⟨Fin.ext originValEq, Fin.ext finishValEq⟩

end OccupiedConsumedSpan

end Solcore.Surface.Multi
