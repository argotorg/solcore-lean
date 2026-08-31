import Solcore.Syntax.Lexer.Invariant

/-! Exact-prefix progress laws for the canonical lexer's pure scanners. -/

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Every successfully closed nested block-comment scan advances exactly. -/
theorem scanBlockComment_closed_advances
    (cursor depth : Nat) (characters bodyRev : List Char)
    (endByte : Nat) (body remaining : List Char)
    (result : scanBlockComment cursor depth characters bodyRev =
      .closed endByte body remaining) :
    Advances cursor characters endByte remaining := by
  fun_induction scanBlockComment cursor depth characters bodyRev with
  | case1 => contradiction
  | case2 cursor depth rest bodyRev inductionHypothesis =>
      have inner := inductionHypothesis result
      have afterStar :
          Advances (cursor + 1) ('*' :: rest) endByte remaining := by
        apply Advances.prepend '*'
        simpa [show '*'.utf8Size = 1 by decide] using inner
      apply Advances.prepend '/'
      simpa [show '/'.utf8Size = 1 by decide] using afterStar
  | case3 cursor rest bodyRev =>
      simp only [BlockCommentScan.closed.injEq] at result
      rcases result with ⟨endEq, _, remainingEq⟩
      subst endByte
      subst remaining
      refine ⟨['*', '/'], by simp, ?_⟩
      simp [byteSize_cons, show '*'.utf8Size = 1 by decide,
        show '/'.utf8Size = 1 by decide]
  | case4 cursor depth rest bodyRev inductionHypothesis =>
      have inner := inductionHypothesis result
      have afterSlash :
          Advances (cursor + 1) ('/' :: rest) endByte remaining := by
        apply Advances.prepend '/'
        simpa [show '/'.utf8Size = 1 by decide] using inner
      apply Advances.prepend '*'
      simpa [show '*'.utf8Size = 1 by decide] using afterSlash
  | case5 cursor depth character rest bodyRev _ _ _ inductionHypothesis =>
      exact (inductionHypothesis result).prepend character

/-- Every successful delimited-meta scan advances through its closing marker. -/
theorem scanDelimitedMeta_some_advances (closing : Char) (cursor : Nat)
    (characters spellingRev : List Char) (scan : MetaScan)
    (result : scanDelimitedMeta closing cursor characters spellingRev =
      some scan) :
    Advances cursor characters scan.endByte scan.remaining := by
  fun_induction scanDelimitedMeta closing cursor characters spellingRev with
  | case1 => contradiction
  | case2 closing cursor character rest spellingRev nextRev nextByte _equal =>
      simp only [Option.some.injEq] at result
      subst scan
      refine ⟨[character], by simp, ?_⟩
      simp [nextByte, byteSize_cons]
  | case3 closing cursor character rest spellingRev nextRev nextByte
      _notEqual inductionHypothesis =>
      exact (inductionHypothesis result).prepend character

namespace StringScan

/-- Exact progress for every non-unterminated quoted-string outcome. -/
def Progress (startByte : Nat) (input : List Char) : StringScan → Prop
  | .closed endByte _ _ remaining =>
      Advances startByte input endByte remaining
  | .invalidEscape _ _ _ tokenEndByte remaining =>
      Advances startByte input tokenEndByte remaining
  | .invalidPrefix endByte remaining =>
      Advances startByte input endByte remaining
  | .unterminated => True

private theorem Progress.prepend (scan : StringScan)
    (character : Char) {startByte : Nat} {input : List Char}
    (progress : scan.Progress (startByte + character.utf8Size) input) :
    scan.Progress startByte (character :: input) := by
  cases scan with
  | closed => exact Advances.prepend character progress
  | invalidEscape => exact Advances.prepend character progress
  | invalidPrefix => exact Advances.prepend character progress
  | unterminated => trivial

end StringScan

/-- The general string scanner advances exactly for every ordinary outcome. -/
theorem scanString_progress (cursor : Nat)
    (characters spellingRev decodedRev : List Char)
    (invalid : Option (Nat × Nat × Option Char)) :
    (scanString cursor characters spellingRev decodedRev invalid).Progress
      cursor characters := by
  fun_induction scanString cursor characters spellingRev decodedRev invalid with
  | case1 => trivial
  | case2 cursor rest spellingRev decodedRev startByte endByte escape =>
      exact Advances.single '"' cursor rest
  | case3 cursor rest spellingRev decodedRev =>
      exact Advances.single '"' cursor rest
  | case4 => trivial
  | case5 cursor tail _ _ _ =>
      exact Advances.single '\\' cursor ('\n' :: tail)
  | case6 cursor escaped rest spellingRev decodedRev invalid decoded?
      nextInvalid nextDecodedRev _notLineFeed inductionHypothesis =>
      have afterEscaped :=
        StringScan.Progress.prepend _ escaped inductionHypothesis
      apply StringScan.Progress.prepend _ '\\'
      simpa [show '\\'.utf8Size = 1 by decide] using afterEscaped
  | case7 cursor character rest spellingRev decodedRev invalid _ _ _ _
      inductionHypothesis =>
      exact StringScan.Progress.prepend _ character inductionHypothesis

/-- A quoted-string scan includes its opening quote in exact progress. -/
theorem scanQuotedString_progress (startByte : Nat)
    (remaining : List Char) :
    (scanQuotedString startByte remaining).Progress
      startByte ('"' :: remaining) := by
  unfold scanQuotedString
  have inner := scanString_progress (startByte + 1) remaining ['"'] [] none
  apply StringScan.Progress.prepend _ '"'
  simpa [show '"'.utf8Size = 1 by decide] using inner

/-- A successfully closed quoted string produces an exact scanner transition. -/
theorem scanQuotedString_closed_advances (startByte : Nat)
    (input : List Char) (endByte : Nat) (spelling decoded : String)
    (remaining : List Char)
    (result : scanQuotedString startByte input =
      .closed endByte spelling decoded remaining) :
    Advances startByte ('"' :: input) endByte remaining := by
  have progress := scanQuotedString_progress startByte input
  rw [result] at progress
  exact progress

/-- An invalid escape still consumes one exact quoted-token prefix. -/
theorem scanQuotedString_invalidEscape_advances (startByte : Nat)
    (input : List Char) (escapeStart escapeEnd : Nat)
    (escape : Option Char) (tokenEndByte : Nat) (remaining : List Char)
    (result : scanQuotedString startByte input =
      .invalidEscape escapeStart escapeEnd escape tokenEndByte remaining) :
    Advances startByte ('"' :: input) tokenEndByte remaining := by
  have progress := scanQuotedString_progress startByte input
  rw [result] at progress
  exact progress

/-- An invalid string prefix advances exactly to its recovery boundary. -/
theorem scanQuotedString_invalidPrefix_advances (startByte : Nat)
    (input : List Char) (endByte : Nat) (remaining : List Char)
    (result : scanQuotedString startByte input =
      .invalidPrefix endByte remaining) :
    Advances startByte ('"' :: input) endByte remaining := by
  have progress := scanQuotedString_progress startByte input
  rw [result] at progress
  exact progress

end Solcore.Syntax.Lexer
