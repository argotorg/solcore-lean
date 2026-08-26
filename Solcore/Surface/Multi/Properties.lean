import Solcore.Surface.Multi.DiagnosticExhaustiveness
import Solcore.Surface.Multi.LexicalJudgment
import Solcore.Surface.Multi.Lexer
import Solcore.Surface.Multi.Measure
import Solcore.Surface.Multi.NonAssociativeCompletionAlignment
import Solcore.Surface.Multi.NonAssociativeInvariantBridge
import Solcore.Surface.Multi.NonAssociativeOptionalStrict
import Solcore.Surface.Multi.NonAssociativePassThroughCoherence
import Solcore.Surface.Multi.NonAssociativePresentEdgeReflection
import Solcore.Surface.Multi.NonAssociativeOperandPrefixExclusive
import Solcore.Surface.Multi.ParseOutcomeTotality
import Solcore.Surface.Multi.RootlessNormalizationGrammarRank
import Solcore.Surface.Multi.RootlessNormalizationRank
import Solcore.Surface.Multi.StructureProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The judgmental range predicate is exactly validity of its owned span. -/
theorem sourceSpan_valid_iff
    (file : WorkspaceFile)
    (startByte endByte : Nat) :
    (LexicalJudgment.sourceSpan file startByte endByte).ValidFor file ↔
      LexicalJudgment.SourceRange file startByte endByte := by
  simp [LexicalJudgment.sourceSpan, SourceSpan.ValidFor,
    LexicalJudgment.SourceRange]

/-- A valid located value has the unique source identity of its owning file. -/
theorem located_source_unique
    {α : Type}
    (file : WorkspaceFile)
    (located : Located α)
    (valid : located.span.ValidFor file) :
    located.span.source = file.id :=
  valid.1

/-- The maximality component carried by an independently winning candidate. -/
private theorem candidateWinner_maximal
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {startByte : Nat}
    {candidate : LexicalJudgment.Candidate}
    (winner : LexicalJudgment.CandidateWinsAt file pendingAssembly
      startByte candidate) :
    ∀ other,
      LexicalJudgment.CandidateAt file pendingAssembly startByte other →
        other = candidate ∨
          LexicalJudgment.CandidateOutranks candidate other :=
  winner.2

private theorem byteSize_cons
    (character : Char)
    (characters : List Char) :
    Lexer.byteSize (character :: characters) =
      character.utf8Size + Lexer.byteSize characters := by
  simp only [Lexer.byteSize, String.ofList_cons,
    String.utf8ByteSize_append, String.utf8ByteSize_singleton]

private theorem byteSize_append
    (leading trailing : List Char) :
    Lexer.byteSize (leading ++ trailing) =
      Lexer.byteSize leading + Lexer.byteSize trailing := by
  simp only [Lexer.byteSize, String.ofList_append,
    String.utf8ByteSize_append]

private theorem stringByteSize_eq_byteSize (text : String) :
    text.utf8ByteSize = Lexer.byteSize text.toList := by
  rw [Lexer.byteSize, String.ofList_toList]

private theorem byteSize_pos_of_ne_nil
    {characters : List Char}
    (nonempty : characters ≠ []) :
    0 < Lexer.byteSize characters := by
  cases characters with
  | nil => contradiction
  | cons character rest =>
      rw [byteSize_cons]
      exact Nat.add_pos_left character.utf8Size_pos _

private theorem takeWhile_decomposition
    (predicate : Char → Bool)
    (characters : List Char) :
    ∃ remaining,
      characters = Lexer.takeWhile predicate characters ++ remaining := by
  induction characters with
  | nil => exact ⟨[], by simp [Lexer.takeWhile]⟩
  | cons character rest inductionHypothesis =>
      by_cases accepted : predicate character = true
      · rcases inductionHypothesis with ⟨remaining, decomposition⟩
        refine ⟨remaining, ?_⟩
        simp only [Lexer.takeWhile, accepted, if_true]
        exact congrArg (List.cons character) decomposition
      · exact ⟨character :: rest, by
          simp only [Lexer.takeWhile, accepted]
          rfl⟩

private theorem takeWhile_all
    (predicate : Char → Bool)
    (characters : List Char) :
    ∀ character ∈ Lexer.takeWhile predicate characters,
      predicate character = true := by
  induction characters with
  | nil => simp [Lexer.takeWhile]
  | cons character rest inductionHypothesis =>
      by_cases accepted : predicate character = true
      · simp only [Lexer.takeWhile, accepted, if_true, List.mem_cons]
        intro next member
        rcases member with rfl | member
        · exact accepted
        · exact inductionHypothesis next member
      · simp [Lexer.takeWhile, accepted]

private theorem takeWhile_length_le
    (predicate : Char → Bool)
    (characters : List Char) :
    (Lexer.takeWhile predicate characters).length ≤ characters.length := by
  rcases takeWhile_decomposition predicate characters with
    ⟨remaining, decomposition⟩
  have lengths := congrArg List.length decomposition
  simp only [List.length_append] at lengths
  omega

private theorem prefix_length_le_takeWhile
    (predicate : Char → Bool)
    (characters leading remaining : List Char)
    (decomposition : characters = leading ++ remaining)
    (accepted : ∀ character ∈ leading, predicate character = true) :
    leading.length ≤ (Lexer.takeWhile predicate characters).length := by
  subst characters
  induction leading with
  | nil => simp
  | cons character rest inductionHypothesis =>
      have headAccepted := accepted character (by simp)
      have tailAccepted : ∀ next ∈ rest, predicate next = true := by
        intro next member
        exact accepted next (by simp [member])
      change (character :: rest).length ≤
        (if predicate character = true then
          character :: Lexer.takeWhile predicate (rest ++ remaining)
        else []).length
      rw [if_pos headAccepted]
      simp only [List.length_cons]
      exact Nat.succ_le_succ
        (inductionHypothesis tailAccepted)

private def utf8FirstByte (character : Char) : UInt8 :=
  let value := character.val.toNat
  if value ≤ 127 then
    UInt8.ofNat value
  else if value ≤ 2047 then
    UInt8.ofNat (value / 64 % 32 + 192)
  else if value ≤ 65535 then
    UInt8.ofNat (value / 4096 % 16 + 224)
  else
    UInt8.ofNat (value / 262144 % 8 + 240)

private theorem utf8FirstByte_toNat_of_ascii
    (character : Char)
    (ascii : character.toNat ≤ 127) :
    (utf8FirstByte character).toNat = character.toNat := by
  change character.val.toNat ≤ 127 at ascii
  simp only [utf8FirstByte]
  rw [if_pos ascii]
  change character.val.toNat % 2 ^ 8 = character.val.toNat
  rw [show 2 ^ 8 = 256 by decide]
  exact Nat.mod_eq_of_lt (by omega)

private theorem utf8FirstByte_toNat_ge_192
    (character : Char)
    (notAscii : ¬ character.toNat ≤ 127) :
    192 ≤ (utf8FirstByte character).toNat := by
  change ¬ character.val.toNat ≤ 127 at notAscii
  simp only [utf8FirstByte]
  rw [if_neg notAscii]
  split
  · have modulusBound : character.val.toNat / 64 % 32 < 32 :=
      Nat.mod_lt _ (by omega)
    have encodedBound :
        character.val.toNat / 64 % 32 + 192 < 256 := by
      omega
    change 192 ≤ (character.val.toNat / 64 % 32 + 192) % 2 ^ 8
    rw [show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt encodedBound]
    omega
  · split
    · have modulusBound : character.val.toNat / 4096 % 16 < 16 :=
        Nat.mod_lt _ (by omega)
      have encodedBound :
          character.val.toNat / 4096 % 16 + 224 < 256 := by
        omega
      change 192 ≤
        (character.val.toNat / 4096 % 16 + 224) % 2 ^ 8
      rw [show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt encodedBound]
      omega
    · have modulusBound : character.val.toNat / 262144 % 8 < 8 :=
        Nat.mod_lt _ (by omega)
      have encodedBound :
          character.val.toNat / 262144 % 8 + 240 < 256 := by
        omega
      change 192 ≤
        (character.val.toNat / 262144 % 8 + 240) % 2 ^ 8
      rw [show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt encodedBound]
      omega

private theorem utf8FirstByte_eq_ascii_iff
    (character : Char)
    (ascii : UInt8)
    (asciiBound : ascii.toNat ≤ 127) :
    utf8FirstByte character = ascii ↔
      character.toNat = ascii.toNat := by
  constructor
  · intro byteEquation
    by_cases characterAscii : character.toNat ≤ 127
    · calc
        character.toNat = (utf8FirstByte character).toNat :=
          (utf8FirstByte_toNat_of_ascii character characterAscii).symm
        _ = ascii.toNat := congrArg UInt8.toNat byteEquation
    · have encodedLarge :=
        utf8FirstByte_toNat_ge_192 character characterAscii
      rw [byteEquation] at encodedLarge
      omega
  · intro valueEquation
    have characterAscii : character.toNat ≤ 127 := by
      omega
    apply UInt8.toNat_inj.mp
    rw [utf8FirstByte_toNat_of_ascii character characterAscii,
      valueEquation]

private theorem utf8FirstByte_not_continuation (character : Char) :
    isUtf8ContinuationByte (utf8FirstByte character) = false := by
  apply Bool.eq_false_iff.mpr
  intro continuation
  simp only [isUtf8ContinuationByte, Bool.and_eq_true] at continuation
  by_cases ascii : character.toNat ≤ 127
  · have value := utf8FirstByte_toNat_of_ascii character ascii
    have lower : (0x80 : UInt8) ≤ utf8FirstByte character := by
      simpa using continuation.1
    change 128 ≤ (utf8FirstByte character).toNat at lower
    omega
  · have value := utf8FirstByte_toNat_ge_192 character ascii
    have upper : utf8FirstByte character ≤ (0xbf : UInt8) := by
      simpa using continuation.2
    change (utf8FirstByte character).toNat ≤ 191 at upper
    omega

private theorem utf8EncodeChar_firstByte
    (character : Char) :
    ∃ trailing,
      String.utf8EncodeChar character =
        utf8FirstByte character :: trailing := by
  simp only [String.utf8EncodeChar, utf8FirstByte]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩
    · split
      · exact ⟨[
          UInt8.ofNat (character.val.toNat / 64 % 64 + 128),
          UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩
      · exact ⟨[
          UInt8.ofNat (character.val.toNat / 4096 % 64 + 128),
          UInt8.ofNat (character.val.toNat / 64 % 64 + 128),
          UInt8.ofNat (character.val.toNat % 64 + 128)], rfl⟩

private theorem stringOfList_getElem?_zero
    (character : Char)
    (remaining : List Char) :
    (String.ofList (character :: remaining)).toByteArray.data[0]? =
      some (utf8FirstByte character) := by
  change (List.utf8Encode (character :: remaining)).data[0]? = _
  rw [List.utf8Encode_cons, ByteArray.data_append,
    Array.getElem?_append]
  have encodedNonempty : 0 < (List.utf8Encode [character]).size := by
    simp [List.utf8Encode, String.length_utf8EncodeChar,
      character.utf8Size_pos]
  rw [if_pos (by simpa using encodedNonempty)]
  obtain ⟨trailing, encoding⟩ := utf8EncodeChar_firstByte character
  simp [List.utf8Encode, encoding]

private theorem sourceTextAt_firstByte
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {text : String}
    {first : Char}
    {rest : List Char}
    (recognized : LexicalJudgment.SourceTextAt file startByte endByte text)
    (characters : text.toList = first :: rest) :
    LexicalJudgment.ByteAt file startByte (utf8FirstByte first) := by
  have byteEquation := recognized.2
  have sizeEquation := congrArg ByteArray.size byteEquation
  have textPositive : 0 < text.utf8ByteSize := by
    rw [stringByteSize_eq_byteSize, characters]
    exact byteSize_pos_of_ne_nil (by simp)
  have extractedPositive :
      0 < min endByte file.content.toByteArray.size - startByte := by
    have fileSize : file.content.toByteArray.size =
        file.content.utf8ByteSize := String.size_toByteArray
    rw [ByteArray.size_extract, fileSize,
      String.size_toByteArray] at sizeEquation
    have endBound := recognized.1.2.1
    rw [Nat.min_eq_left endBound] at sizeEquation
    rw [fileSize]
    omega
  have extractedPositiveData :
      0 < min endByte file.content.toByteArray.data.size - startByte := by
    simpa using extractedPositive
  have lookupEquation := congrArg (fun bytes : ByteArray => bytes.data[0]?)
    byteEquation
  rw [ByteArray.data_extract, Array.getElem?_extract,
    if_pos extractedPositiveData] at lookupEquation
  have textEquation : text = String.ofList (first :: rest) := by
    rw [← characters, String.ofList_toList]
  have firstLookup : text.toByteArray.data[0]? =
      some (utf8FirstByte first) := by
    rw [textEquation]
    exact stringOfList_getElem?_zero first rest
  rw [firstLookup] at lookupEquation
  exact (by
    unfold LexicalJudgment.ByteAt LexicalJudgment.byteAt
    simpa using lookupEquation)

private theorem sourceTextAt_endByte
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {text : String}
    (recognized : LexicalJudgment.SourceTextAt file startByte endByte text) :
    endByte = startByte + text.utf8ByteSize := by
  have sizeEquation := congrArg ByteArray.size recognized.2
  have ordered := recognized.1.1
  have endBound := recognized.1.2.1
  rw [ByteArray.size_extract, String.size_toByteArray,
    Nat.min_eq_left endBound, String.size_toByteArray] at sizeEquation
  omega

private theorem stringContents_progress
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {decoded : String}
    (contents :
      LexicalJudgment.StringContents file cursor endByte decoded) :
    cursor < endByte := by
  induction contents with
  | close => omega
  | scalar _ _ _ _ _ scalar _ _ _ inductionHypothesis =>
      exact Nat.lt_trans scalar.1 inductionHypothesis
  | escapedNewline _ _ _ _ _ inductionHypothesis
  | escapedTab _ _ _ _ _ inductionHypothesis
  | escapedQuote _ _ _ _ _ inductionHypothesis
  | escapedBackslash _ _ _ _ _ inductionHypothesis => omega

private theorem blockCommentRun_cursor_le
    {file : WorkspaceFile}
    {depth cursor finalDepth endByte : Nat}
    (run :
      LexicalJudgment.BlockCommentRun file depth cursor finalDepth endByte) :
    cursor ≤ endByte := by
  induction run with
  | refl => exact Nat.le_refl _
  | nestedOpen _ _ _ _ _ _ _ inductionHypothesis
  | nestedClose _ _ _ _ _ _ _ inductionHypothesis => omega
  | scalar _ _ _ _ _ _ _ _ _ scalar _ inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt scalar.1) inductionHypothesis

/-- Every recognized normal lexical candidate consumes a nonempty byte slice. -/
private theorem candidate_progress
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {startByte : Nat}
    {candidate : LexicalJudgment.Candidate}
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly startByte candidate) :
    startByte < candidate.span.endByte := by
  cases recognized with
  | lineComment endByte comment recognized =>
      rcases recognized with ⟨span, rfl⟩
      have progress : startByte < endByte := by
        have consumed := span.2.2.1
        omega
      simpa [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan] using progress
  | blockComment endByte comment recognized =>
      rcases recognized with ⟨span, rfl⟩
      rcases span with ⟨_, closeByte, run, _, rfl, _⟩
      have reached := blockCommentRun_cursor_le run
      simp [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega

  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, _, contents, _, rfl⟩
      have progress := stringContents_progress contents
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega

  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, ⟨spelling, _⟩, rfl⟩
      have endEquation := sourceTextAt_endByte spelling
      have positive : 0 < kind.spelling.utf8ByteSize := by
        cases kind <;> decide
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega
  | identifier endByte token recognized =>
      rcases recognized with
        ⟨text, kind, valid, spelling, _, rfl⟩
      have endEquation := sourceTextAt_endByte spelling
      have nonempty : text.toList ≠ [] := by
        intro empty
        simp [pathSegmentTextValid, empty] at valid
      have positive := byteSize_pos_of_ne_nil nonempty
      rw [← stringByteSize_eq_byteSize] at positive
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega
  | decimal endByte token recognized =>
      rcases recognized with
        ⟨digits, ⟨nonempty, _⟩, spelling, rfl⟩
      have endEquation := sourceTextAt_endByte spelling
      have positive := byteSize_pos_of_ne_nil nonempty
      rw [← stringByteSize_eq_byteSize] at positive
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega
  | hexadecimal endByte token recognized =>
      rcases recognized with
        ⟨digits, _, spelling, rfl⟩
      have endEquation := sourceTextAt_endByte spelling
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      have positive : 0 < ("0x" ++ digits).utf8ByteSize := by
        rw [String.utf8ByteSize_append]
        have prefixPositive : 0 < "0x".utf8ByteSize := by decide
        omega
      omega
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨writtenSymbol, spelling, _, _, rfl⟩
      simp only at kind
      cases kind
      have endEquation := sourceTextAt_endByte spelling
      have positive : 0 < symbol.spelling.utf8ByteSize := by
        cases symbol <;> decide
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      omega

private theorem assemblyRun_cursor_le
    {file : WorkspaceFile}
    {initialState finalState : LexicalJudgment.AssemblyScannerState}
    {cursor endByte : Nat}
    (run : LexicalJudgment.AssemblyRun file initialState cursor
      finalState endByte) :
    cursor ≤ endByte := by
  induction run with
  | refl => exact Nat.le_refl _
  | step _ _ _ _ next _ transition _ inductionHypothesis =>
      cases transition <;> try omega
      all_goals
        unfold LexicalJudgment.ScalarAt at *
        omega

/-- Every executor transition advances its UTF-8 byte cursor. -/
theorem lexer_progress (file : WorkspaceFile) :
    (∀ {startByte endByte},
      LexicalJudgment.WhitespaceAt file startByte endByte →
        startByte < endByte) ∧
    (∀ {pendingAssembly startByte candidate},
      LexicalJudgment.CandidateAt file pendingAssembly startByte candidate →
        startByte < candidate.span.endByte) ∧
    (∀ {startByte endByte token},
      LexicalJudgment.AssemblyTokenAt file startByte endByte token →
        startByte < endByte) := by
  refine ⟨?_, candidate_progress, ?_⟩
  · rintro startByte endByte ⟨character, scalar, whitespace⟩
    exact scalar.1
  · rintro startByte endByte token ⟨slice, recognized, tokenEquation⟩
    rcases recognized with ⟨openBrace, closeByte, run, closeBrace,
      endEquation, range, sliceEquation⟩
    have reached := assemblyRun_cursor_le run
    omega

private theorem candidateOutranks_asymmetric
    {preferred other : LexicalJudgment.Candidate}
    (forward : LexicalJudgment.CandidateOutranks preferred other)
    (backward : LexicalJudgment.CandidateOutranks other preferred) : False := by
  unfold LexicalJudgment.CandidateOutranks at forward backward
  rcases forward with forward | forward <;>
    rcases backward with backward | backward <;> omega

private theorem candidateWinner_unique
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {first second : LexicalJudgment.Candidate}
    (firstWins :
      LexicalJudgment.CandidateWinsAt file pendingAssembly cursor first)
    (secondWins :
      LexicalJudgment.CandidateWinsAt file pendingAssembly cursor second) :
    first = second := by
  rcases firstWins.2 second secondWins.1 with equality | forward
  · exact equality.symm
  rcases secondWins.2 first firstWins.1 with equality | backward
  · exact equality
  exact False.elim (candidateOutranks_asymmetric forward backward)

private theorem candidateAt_startByte
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {candidate : LexicalJudgment.Candidate}
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    candidate.span.startByte = cursor := by
  cases recognized with
  | lineComment endByte comment recognized =>
      rcases recognized with ⟨span, tokenEquation⟩
      subst comment
      rfl
  | blockComment endByte comment recognized =>
      rcases recognized with ⟨span, tokenEquation⟩
      subst comment
      rfl
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quote, contents, sourceText, tokenEquation⟩
      subst token
      rfl
  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, spelling, tokenEquation⟩
      subst token
      rfl
  | identifier endByte token recognized =>
      rcases recognized with
        ⟨text, kind, valid, sourceText, classification, tokenEquation⟩
      subst token
      rfl
  | decimal endByte token recognized =>
      rcases recognized with ⟨digits, valid, sourceText, tokenEquation⟩
      subst token
      rfl
  | hexadecimal endByte token recognized =>
      rcases recognized with ⟨digits, valid, sourceText, tokenEquation⟩
      subst token
      rfl
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨written, sourceText, slashGuard, assemblyGuard, tokenEquation⟩
      subst token
      rfl

/-- Every normal lexical candidate carries a span owned by its source file. -/
private theorem candidateAt_span_valid
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {candidate : LexicalJudgment.Candidate}
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    candidate.span.ValidFor file := by
  cases recognized with
  | lineComment endByte comment recognized =>
      rcases recognized with ⟨span, tokenEquation⟩
      subst comment
      exact (sourceSpan_valid_iff file cursor endByte).mpr span.2.1
  | blockComment endByte comment recognized =>
      rcases recognized with ⟨span, tokenEquation⟩
      subst comment
      rcases span with
        ⟨_open, closeCursor, _run, _close, _endEquation, range⟩
      exact (sourceSpan_valid_iff file cursor endByte).mpr range
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, _quote, _contents, sourceText, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr sourceText.1
  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, spelling, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr spelling.1.1
  | identifier endByte token recognized =>
      rcases recognized with
        ⟨text, kind, _valid, sourceText, _classification, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr sourceText.1
  | decimal endByte token recognized =>
      rcases recognized with ⟨digits, _valid, sourceText, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr sourceText.1
  | hexadecimal endByte token recognized =>
      rcases recognized with ⟨digits, _valid, sourceText, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr sourceText.1
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨written, sourceText, _slashGuard, _assemblyGuard, tokenEquation⟩
      subst token
      exact (sourceSpan_valid_iff file cursor endByte).mpr sourceText.1

/-- Every opaque assembly token carries the exact owned source span. -/
private theorem assemblyTokenAt_span_valid
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {token : Token}
    (recognized :
      LexicalJudgment.AssemblyTokenAt file startByte endByte token) :
    token.span.ValidFor file := by
  rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
  subst token
  rcases sliceAt with
    ⟨_open, closeCursor, _run, _close, _endEquation, range, _slice⟩
  exact (sourceSpan_valid_iff file startByte endByte).mpr range

/-- A character suffix paired with its exact starting UTF-8 byte cursor. -/
private inductive SuffixAt
    (file : WorkspaceFile)
    (cursor : Nat)
    (characters : List Char) : Prop where
  | intro
      (leading : List Char)
      (decomposition : file.content.toList = leading ++ characters)
      (cursor_eq : cursor = Lexer.byteSize leading) :
      SuffixAt file cursor characters

namespace SuffixAt

private theorem initial (file : WorkspaceFile) :
    SuffixAt file 0 file.content.toList := by
  refine ⟨[], by simp, ?_⟩
  simp [Lexer.byteSize]

private theorem remainingByteSize
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters) :
    file.content.utf8ByteSize = cursor + Lexer.byteSize characters := by
  rcases suffix with ⟨leading, decomposition, cursorEquation⟩
  rw [stringByteSize_eq_byteSize, decomposition, byteSize_append,
    cursorEquation]

private theorem cursor_unique
    {file : WorkspaceFile}
    {firstCursor secondCursor : Nat}
    {characters : List Char}
    (first : SuffixAt file firstCursor characters)
    (second : SuffixAt file secondCursor characters) :
    firstCursor = secondCursor := by
  have firstSize := first.remainingByteSize
  have secondSize := second.remainingByteSize
  omega

private theorem advance
    {file : WorkspaceFile}
    {cursor nextCursor : Nat}
    {characters consumed remaining : List Char}
    (suffix : SuffixAt file cursor characters)
    (decomposition : characters = consumed ++ remaining)
    (nextCursorEquation :
      nextCursor = cursor + Lexer.byteSize consumed) :
    SuffixAt file nextCursor remaining := by
  rcases suffix with ⟨leading, sourceEquation, cursorEquation⟩
  refine ⟨leading ++ consumed, ?_, ?_⟩
  · rw [sourceEquation, decomposition, List.append_assoc]
  · rw [nextCursorEquation, cursorEquation, byteSize_append]

private theorem byteArray_extract_middle
    (leading payload trailing : ByteArray) :
    (leading ++ payload ++ trailing).extract leading.size
        (leading.size + payload.size) = payload := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract, Array.toList_extract]
  simp

private theorem sourceSlice
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters consumed remaining : List Char}
    (suffix : SuffixAt file cursor characters)
    (decomposition : characters = consumed ++ remaining) :
    file.content.toByteArray.extract cursor
        (cursor + Lexer.byteSize consumed) =
      (String.ofList consumed).toByteArray := by
  rcases suffix with ⟨leading, sourceEquation, cursorEquation⟩
  have contentEquation :
      file.content =
        String.ofList leading ++
          String.ofList consumed ++ String.ofList remaining := by
    calc
      file.content = String.ofList file.content.toList :=
        String.ofList_toList.symm
      _ = String.ofList (leading ++ consumed ++ remaining) := by
        rw [sourceEquation, decomposition, List.append_assoc]
      _ = String.ofList leading ++
          String.ofList consumed ++ String.ofList remaining := by
        rw [String.ofList_append, String.ofList_append]
  rw [contentEquation, String.toByteArray_append,
    String.toByteArray_append, cursorEquation]
  simpa only [String.size_toByteArray, Lexer.byteSize] using
    byteArray_extract_middle
      (String.ofList leading).toByteArray
      (String.ofList consumed).toByteArray
      (String.ofList remaining).toByteArray

private theorem byteArray_getElem?_after_prefix
    (leading trailing : ByteArray) :
    (leading ++ trailing).data[leading.size]? = trailing.data[0]? := by
  rw [ByteArray.data_append, Array.getElem?_append,
    ByteArray.size_data]
  rw [if_neg (by omega)]
  simp

private theorem sourceByteAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters) :
    LexicalJudgment.byteAt file cursor =
      match characters with
      | [] => none
      | character :: _ => some (utf8FirstByte character) := by
  rcases suffix with ⟨leading, sourceEquation, cursorEquation⟩
  have contentEquation :
      file.content = String.ofList leading ++ String.ofList characters := by
    calc
      file.content = String.ofList file.content.toList :=
        String.ofList_toList.symm
      _ = String.ofList (leading ++ characters) := by rw [sourceEquation]
      _ = _ := by rw [String.ofList_append]
  subst cursor
  have lookup := byteArray_getElem?_after_prefix
    (String.ofList leading).toByteArray
    (String.ofList characters).toByteArray
  rw [String.size_toByteArray] at lookup
  unfold LexicalJudgment.byteAt
  simp only [Lexer.byteSize]
  rw [contentEquation, String.toByteArray_append, lookup]
  cases characters with
  | nil => rfl
  | cons character remaining =>
      exact stringOfList_getElem?_zero character remaining

private theorem boundary
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters) :
    isUtf8Boundary file.content cursor = true := by
  by_cases atStart : cursor = 0
  · subst cursor
    exact isUtf8Boundary_zero file.content
  cases characters with
  | nil =>
      have atEnd : cursor = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        simpa [Lexer.byteSize] using size.symm
      subst cursor
      exact isUtf8Boundary_end file.content
  | cons character remaining =>
      have lookup := suffix.sourceByteAt
      have rawLookup :
          file.content.toByteArray.data[cursor]? =
            some (utf8FirstByte character) := by
        simpa [LexicalJudgment.byteAt] using lookup
      simp [isUtf8Boundary, rawLookup,
        utf8FirstByte_not_continuation]

private theorem sourceRange
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters consumed remaining : List Char}
    (suffix : SuffixAt file cursor characters)
    (decomposition : characters = consumed ++ remaining) :
    LexicalJudgment.SourceRange file cursor
      (cursor + Lexer.byteSize consumed) := by
  have endSuffix := suffix.advance decomposition rfl
  have totalSize := suffix.remainingByteSize
  constructor
  · omega
  constructor
  · rw [decomposition, byteSize_append] at totalSize
    rw [totalSize]
    omega
  exact ⟨suffix.boundary, endSuffix.boundary⟩

private theorem rangeToEnd
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters) :
    LexicalJudgment.SourceRange file cursor file.content.utf8ByteSize := by
  have range := suffix.sourceRange
    (consumed := characters) (remaining := []) (by simp)
  have size := suffix.remainingByteSize
  rw [← size] at range
  exact range

private theorem sourceRange_trans
    {file : WorkspaceFile}
    {startByte middleByte endByte : Nat}
    (first :
      LexicalJudgment.SourceRange file startByte middleByte)
    (second :
      LexicalJudgment.SourceRange file middleByte endByte) :
    LexicalJudgment.SourceRange file startByte endByte := by
  exact ⟨Nat.le_trans first.1 second.1,
    second.2.1, first.2.2.1, second.2.2.2⟩

private theorem sourceTextAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters consumed remaining : List Char}
    (suffix : SuffixAt file cursor characters)
    (decomposition : characters = consumed ++ remaining) :
    LexicalJudgment.SourceTextAt file cursor
      (cursor + Lexer.byteSize consumed) (String.ofList consumed) := by
  exact ⟨suffix.sourceRange decomposition,
    suffix.sourceSlice decomposition⟩

private theorem sourceTextDecomposition
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {text : String}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.SourceTextAt file cursor endByte text) :
    ∃ remaining,
      characters = text.toList ++ remaining ∧
      endByte = cursor + text.utf8ByteSize := by
  rcases suffix with ⟨leading, sourceEquation, cursorEquation⟩
  have contentEquation :
      file.content = String.ofList leading ++ String.ofList characters := by
    calc
      file.content = String.ofList file.content.toList :=
        String.ofList_toList.symm
      _ = String.ofList (leading ++ characters) := by rw [sourceEquation]
      _ = _ := by rw [String.ofList_append]
  have ordered := recognized.1.1
  have endBound := recognized.1.2.1
  have sizeEquation := congrArg ByteArray.size recognized.2
  have fileSize : file.content.toByteArray.size =
      file.content.utf8ByteSize := String.size_toByteArray
  rw [ByteArray.size_extract, fileSize,
    Nat.min_eq_left endBound, String.size_toByteArray] at sizeEquation
  have endEquation : endByte = cursor + text.utf8ByteSize := by
    omega
  by_cases textEmpty : text = ""
  · subst text
    refine ⟨characters, by simp, ?_⟩
    simpa using endEquation
  let startPosition : String.Pos.Raw := ⟨cursor⟩
  let endPosition : String.Pos.Raw := ⟨endByte⟩
  have positionOrdered : startPosition ≤ endPosition := by
    simpa [String.Pos.Raw.le_iff, startPosition, endPosition] using ordered
  have positionBound : endPosition ≤ file.content.rawEndPos := by
    simpa [String.Pos.Raw.le_iff, String.byteIdx_rawEndPos,
      endPosition] using endBound
  have extractValid :
      (file.content.toByteArray.extract cursor endByte).IsValidUTF8 := by
    rw [recognized.2]
    exact text.isValidUTF8
  have positionsValid :=
    (String.Pos.Raw.isValidUTF8_extract_iff startPosition endPosition
      positionOrdered positionBound).mp extractValid
  have positionsDistinct : startPosition ≠ endPosition := by
    intro equals
    have cursorEquation' : cursor = endByte := by
      exact congrArg String.Pos.Raw.byteIdx equals
    have textSizeZero : text.utf8ByteSize = 0 := by omega
    exact textEmpty (String.utf8ByteSize_eq_zero_iff.mp textSizeZero)
  rcases positionsValid.resolve_left positionsDistinct with
    ⟨_, endValid⟩
  let trailing : String :=
    ⟨file.content.toByteArray.extract endByte file.content.utf8ByteSize,
      endValid.isValidUTF8_extract_utf8ByteSize⟩
  have suffixBytes :
      file.content.toByteArray.extract cursor
          file.content.utf8ByteSize =
        (String.ofList characters).toByteArray := by
    rw [contentEquation, String.toByteArray_append, cursorEquation,
      String.utf8ByteSize_append]
    simpa only [String.size_toByteArray, Lexer.byteSize] using
      (ByteArray.extract_append_eq_right
        (a := (String.ofList leading).toByteArray)
        (b := (String.ofList characters).toByteArray)
        (i := (String.ofList leading).toByteArray.size)
        (j := (String.ofList leading).toByteArray.size +
          (String.ofList characters).toByteArray.size) rfl rfl)
  have splitBytes := ByteArray.extract_eq_extract_append_extract
    (a := file.content.toByteArray) endByte ordered endBound
  rw [splitBytes, recognized.2] at suffixBytes
  have suffixString :
      String.ofList characters = text ++ trailing := by
    apply String.toByteArray_inj.mp
    simpa [trailing, String.toByteArray_append] using suffixBytes.symm
  have listEquation := congrArg String.toList suffixString
  simp only [String.toList_ofList, String.toList_append] at listEquation
  exact ⟨trailing.toList, listEquation, endEquation⟩

private theorem scalarAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining)) :
    LexicalJudgment.ScalarAt file cursor character
      (cursor + character.utf8Size) := by
  have text := suffix.sourceTextAt
    (consumed := [character]) (remaining := remaining) (by simp)
  rw [show Lexer.byteSize [character] = character.utf8Size by
    simp [Lexer.byteSize]] at text
  exact ⟨by exact Nat.lt_add_of_pos_right character.utf8Size_pos, by
    simpa using text⟩

private theorem advanceOne
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining)) :
    SuffixAt file (cursor + character.utf8Size) remaining := by
  apply suffix.advance (consumed := [character]) (by simp)
  simp [Lexer.byteSize]

private theorem advanceTwoAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {first second : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (first :: second :: remaining))
    (firstSize : first.utf8Size = 1)
    (secondSize : second.utf8Size = 1) :
    SuffixAt file (cursor + 2) remaining := by
  apply suffix.advance (consumed := [first, second]) (by simp)
  simp [Lexer.byteSize, firstSize, secondSize]

private theorem advancePrefixDrop
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters consumed remaining : List Char}
    (suffix : SuffixAt file cursor characters)
    (decomposition : characters = consumed ++ remaining) :
    SuffixAt file (cursor + Lexer.byteSize consumed)
      (characters.drop consumed.length) := by
  have advanced := suffix.advance decomposition rfl
  have dropEquation : characters.drop consumed.length = remaining := by
    rw [decomposition]
    simp
  rw [dropEquation]
  exact advanced

private theorem byteAtFirst
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining)) :
    LexicalJudgment.ByteAt file cursor (utf8FirstByte character) := by
  simpa [LexicalJudgment.ByteAt] using suffix.sourceByteAt

private theorem bytePairAtAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {first second : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (first :: second :: remaining))
    (firstByte : utf8FirstByte first = UInt8.ofNat first.toNat)
    (secondByte : utf8FirstByte second = UInt8.ofNat second.toNat)
    (firstSize : first.utf8Size = 1) :
    LexicalJudgment.BytePairAt file cursor
      (UInt8.ofNat first.toNat) (UInt8.ofNat second.toNat) := by
  constructor
  · rw [← firstByte]
    exact suffix.byteAtFirst
  · have next := suffix.advanceOne
    rw [firstSize] at next
    rw [← secondByte]
    exact next.byteAtFirst

private theorem character_eq_of_byteAtAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {character expected : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining))
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat expected.toNat))
    (expectedAscii : expected.toNat ≤ 127) :
    character = expected := by
  have actual := suffix.byteAtFirst
  unfold LexicalJudgment.ByteAt at actual byte
  rw [actual] at byte
  have firstByte := Option.some.inj byte
  apply Char.toNat_inj.mp
  have value := (utf8FirstByte_eq_ascii_iff character
    (UInt8.ofNat expected.toNat) (by
      change expected.toNat % 256 ≤ 127
      rw [Nat.mod_eq_of_lt (by omega)]
      exact expectedAscii)).mp firstByte
  simpa [Nat.mod_eq_of_lt (by omega : expected.toNat < 256)] using value

private theorem pair_eq_of_bytePairAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {character first second : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining))
    (pair : LexicalJudgment.BytePairAt file cursor
      (UInt8.ofNat first.toNat) (UInt8.ofNat second.toNat))
    (firstAscii : first.toNat ≤ 127)
    (secondAscii : second.toNat ≤ 127)
    (firstSize : first.utf8Size = 1) :
    ∃ tail, character = first ∧ remaining = second :: tail := by
  have characterEquation :=
    suffix.character_eq_of_byteAtAscii pair.1 firstAscii
  subst character
  cases remaining with
  | nil =>
      have afterFirst := suffix.advanceOne
      rw [firstSize] at afterFirst
      have atEnd := afterFirst.sourceByteAt
      have secondByte := pair.2
      unfold LexicalJudgment.ByteAt at secondByte
      rw [atEnd] at secondByte
      simp at secondByte
  | cons nextCharacter tail =>
      have afterFirst := suffix.advanceOne
      rw [firstSize] at afterFirst
      have nextEquation := afterFirst.character_eq_of_byteAtAscii
        pair.2 secondAscii
      subst nextCharacter
      exact ⟨tail, rfl, rfl⟩

private theorem characters_eq_pair_of_bytePairAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {first second : Char}
    (suffix : SuffixAt file cursor characters)
    (pair : LexicalJudgment.BytePairAt file cursor
      (UInt8.ofNat first.toNat) (UInt8.ofNat second.toNat))
    (firstAscii : first.toNat ≤ 127)
    (secondAscii : second.toNat ≤ 127)
    (firstSize : first.utf8Size = 1) :
    ∃ tail, characters = first :: second :: tail := by
  cases characters with
  | nil =>
      have atEnd := suffix.sourceByteAt
      have firstByte := pair.1
      unfold LexicalJudgment.ByteAt at firstByte
      rw [atEnd] at firstByte
      simp at firstByte
  | cons character remaining =>
      rcases suffix.pair_eq_of_bytePairAscii pair firstAscii secondAscii
          firstSize with ⟨tail, characterEquation, remainingEquation⟩
      subst character
      subst remaining
      exact ⟨tail, rfl⟩

private theorem characters_eq_cons_of_byteAtAscii
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {expected : Char}
    (suffix : SuffixAt file cursor characters)
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat expected.toNat))
    (expectedAscii : expected.toNat ≤ 127) :
    ∃ remaining, characters = expected :: remaining := by
  cases characters with
  | nil =>
      have atEnd := suffix.sourceByteAt
      unfold LexicalJudgment.ByteAt at byte
      rw [atEnd] at byte
      simp at byte
  | cons character remaining =>
      have equation := suffix.character_eq_of_byteAtAscii
        byte expectedAscii
      subst character
      exact ⟨remaining, rfl⟩

private theorem scalarAt_decomposition
    {file : WorkspaceFile}
    {cursor next : Nat}
    {characters : List Char}
    {character : Char}
    (suffix : SuffixAt file cursor characters)
    (scalar :
      LexicalJudgment.ScalarAt file cursor character next) :
    ∃ remaining,
      characters = character :: remaining ∧
      next = cursor + character.utf8Size ∧
      SuffixAt file next remaining := by
  rcases suffix.sourceTextDecomposition scalar.2 with
    ⟨remaining, decomposition, endEquation⟩
  have singletonBytes :
      (String.singleton character).utf8ByteSize = character.utf8Size := by
    simp
  rw [singletonBytes] at endEquation
  refine ⟨remaining, by simpa using decomposition, endEquation, ?_⟩
  apply suffix.advance (consumed := [character]) (by simpa using decomposition)
  simp [Lexer.byteSize, endEquation]

private theorem slashStar_of_bytePair
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining))
    (pair : LexicalJudgment.BytePairAt file cursor 47 42) :
    ∃ tail, character = '/' ∧ remaining = '*' :: tail := by
  rcases pair with ⟨pairFirst, pairSecond⟩
  unfold LexicalJudgment.ByteAt at pairFirst pairSecond
  have actualFirst := suffix.byteAtFirst
  have firstByte : utf8FirstByte character = 47 := by
    unfold LexicalJudgment.ByteAt at actualFirst
    rw [actualFirst] at pairFirst
    exact Option.some.inj pairFirst
  have firstCharacter : character = '/' := by
    apply Char.toNat_inj.mp
    exact (utf8FirstByte_eq_ascii_iff character 47 (by decide)).mp
      firstByte
  subst character
  have slashSize : '/'.utf8Size = 1 := by decide
  cases remaining with
  | nil =>
      have next := suffix.advanceOne
      rw [slashSize] at next
      have atEnd := next.sourceByteAt
      have atEnd' :
          LexicalJudgment.byteAt file (cursor + 1) = none := by
        simpa using atEnd
      rw [atEnd'] at pairSecond
      simp at pairSecond
  | cons nextCharacter tail =>
      have next := suffix.advanceOne
      rw [slashSize] at next
      have actualSecond := next.byteAtFirst
      have secondByte : utf8FirstByte nextCharacter = 42 := by
        have actualSecond' :
            LexicalJudgment.byteAt file (cursor + 1) =
              some (utf8FirstByte nextCharacter) := by
          simpa [LexicalJudgment.ByteAt] using actualSecond
        rw [actualSecond'] at pairSecond
        exact Option.some.inj pairSecond
      have secondCharacter : nextCharacter = '*' := by
        apply Char.toNat_inj.mp
        exact (utf8FirstByte_eq_ascii_iff nextCharacter 42 (by decide)).mp
          secondByte
      subst nextCharacter
      exact ⟨tail, rfl, rfl⟩

private theorem starSlash_of_bytePair
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {remaining : List Char}
    (suffix : SuffixAt file cursor (character :: remaining))
    (pair : LexicalJudgment.BytePairAt file cursor 42 47) :
    ∃ tail, character = '*' ∧ remaining = '/' :: tail := by
  rcases pair with ⟨pairFirst, pairSecond⟩
  unfold LexicalJudgment.ByteAt at pairFirst pairSecond
  have actualFirst := suffix.byteAtFirst
  have firstByte : utf8FirstByte character = 42 := by
    unfold LexicalJudgment.ByteAt at actualFirst
    rw [actualFirst] at pairFirst
    exact Option.some.inj pairFirst
  have firstCharacter : character = '*' := by
    apply Char.toNat_inj.mp
    exact (utf8FirstByte_eq_ascii_iff character 42 (by decide)).mp
      firstByte
  subst character
  have starSize : '*'.utf8Size = 1 := by decide
  cases remaining with
  | nil =>
      have next := suffix.advanceOne
      rw [starSize] at next
      have atEnd := next.sourceByteAt
      have atEnd' :
          LexicalJudgment.byteAt file (cursor + 1) = none := by
        simpa using atEnd
      rw [atEnd'] at pairSecond
      simp at pairSecond
  | cons nextCharacter tail =>
      have next := suffix.advanceOne
      rw [starSize] at next
      have actualSecond := next.byteAtFirst
      have secondByte : utf8FirstByte nextCharacter = 47 := by
        have actualSecond' :
            LexicalJudgment.byteAt file (cursor + 1) =
              some (utf8FirstByte nextCharacter) := by
          simpa [LexicalJudgment.ByteAt] using actualSecond
        rw [actualSecond'] at pairSecond
        exact Option.some.inj pairSecond
      have secondCharacter : nextCharacter = '/' := by
        apply Char.toNat_inj.mp
        exact (utf8FirstByte_eq_ascii_iff nextCharacter 47 (by decide)).mp
          secondByte
      subst nextCharacter
      exact ⟨tail, rfl, rfl⟩

end SuffixAt

private theorem isAsciiLetter_eq_true_iff (character : Char) :
    Lexer.isAsciiLetter character = true ↔
      LexicalJudgment.AsciiLetter character := by
  simp [Lexer.isAsciiLetter, Lexer.isAsciiLower, Lexer.isAsciiUpper,
    LexicalJudgment.AsciiLetter, or_comm]

private theorem isAsciiDigit_eq_true_iff (character : Char) :
    Lexer.isAsciiDigit character = true ↔
      LexicalJudgment.AsciiDigit character := by
  simp [Lexer.isAsciiDigit, LexicalJudgment.AsciiDigit]

private theorem isAsciiHexDigit_eq_true_iff (character : Char) :
    Lexer.isAsciiHexDigit character = true ↔
      LexicalJudgment.AsciiHexDigit character := by
  simp [Lexer.isAsciiHexDigit, Lexer.isAsciiDigit,
    LexicalJudgment.AsciiHexDigit, LexicalJudgment.AsciiDigit,
    or_comm, or_left_comm]

private theorem isIdentifierContinue_eq_true_iff (character : Char) :
    Lexer.isIdentifierContinue character = true ↔
      LexicalJudgment.IdentifierContinue character := by
  simp [Lexer.isIdentifierContinue, Lexer.isAsciiLetter,
    Lexer.isAsciiLower, Lexer.isAsciiUpper, Lexer.isAsciiDigit,
    LexicalJudgment.IdentifierContinue, LexicalJudgment.AsciiLetter,
    LexicalJudgment.AsciiDigit, or_comm, or_assoc]

private theorem isPragmaContinuation_eq_true_iff (character : Char) :
    Lexer.isPragmaContinuation character = true ↔
      LexicalJudgment.PragmaContinuation character := by
  simp [Lexer.isPragmaContinuation, Lexer.isIdentifierContinue,
    Lexer.isAsciiLetter, Lexer.isAsciiLower, Lexer.isAsciiUpper,
    Lexer.isAsciiDigit, LexicalJudgment.PragmaContinuation,
    LexicalJudgment.IdentifierContinue, LexicalJudgment.AsciiLetter,
    LexicalJudgment.AsciiDigit, or_comm, or_assoc]

private theorem isWhitespace_eq_true_iff (character : Char) :
    Lexer.isWhitespace character = true ↔
      LexicalJudgment.WhitespaceCharacter character := by
  simp [Lexer.isWhitespace, LexicalJudgment.WhitespaceCharacter,
    or_comm, or_left_comm, or_assoc]

private theorem invalidLexemeStart
    {character : Char}
    (notWhitespace : Lexer.isWhitespace character ≠ true)
    (notLetter : Lexer.isAsciiLetter character ≠ true)
    (notDigit : Lexer.isAsciiDigit character ≠ true)
    (notQuote : character ≠ '"')
    (noSingleSymbol : Lexer.singleSymbol? character = none) :
    ¬ LexicalJudgment.LexemeStartCharacter character := by
  intro starts
  rcases starts with
    whitespace | letter | digit | quote | ⟨symbol, tail, spelling⟩
  · exact notWhitespace
      ((isWhitespace_eq_true_iff character).mpr whitespace)
  · exact notLetter ((isAsciiLetter_eq_true_iff character).mpr letter)
  · exact notDigit ((isAsciiDigit_eq_true_iff character).mpr digit)
  · exact notQuote quote
  · cases symbol <;>
      simp [Symbol.spelling] at spelling <;>
      rcases spelling with ⟨characterEquation, tailEquation⟩ <;>
      cases characterEquation <;>
      simp [Lexer.singleSymbol?] at noSingleSymbol

private theorem pathSegmentTextValid_of_cons
    (first : Char)
    (rest : List Char)
    (letter : LexicalJudgment.AsciiLetter first)
    (continuations :
      ∀ character ∈ rest,
        LexicalJudgment.IdentifierContinue character) :
    pathSegmentTextValid (String.ofList (first :: rest)) = true := by
  simp only [pathSegmentTextValid, String.toList_ofList]
  change (Lexer.isAsciiLetter first &&
      rest.all Lexer.isIdentifierContinue) = true
  rw [Bool.and_eq_true, isAsciiLetter_eq_true_iff,
    List.all_eq_true]
  exact ⟨letter, fun character member =>
    (isIdentifierContinue_eq_true_iff character).mpr
      (continuations character member)⟩

private theorem hardKeyword_text_eq
    {text : String}
    {keyword : HardKeyword}
    (recognized : HardKeyword.ofString? text = some keyword) :
    text = keyword.spelling := by
  cases keyword <;>
    unfold HardKeyword.ofString? at recognized <;>
    split at recognized <;>
    simp_all [HardKeyword.spelling]

private theorem classifyIdentifier_spec (text : String) :
    LexicalJudgment.IdentifierClassifies text
      (Lexer.classifyIdentifier text) := by
  rw [Lexer.classifyIdentifier_equation]
  cases recognized : HardKeyword.ofString? text with
  | none => exact .identifier text recognized
  | some keyword =>
      have equality := hardKeyword_text_eq recognized
      subst text
      exact .hardKeyword keyword

private theorem identifierContinue_utf8Size
    {character : Char}
    (accepted : LexicalJudgment.IdentifierContinue character) :
    character.utf8Size = 1 := by
  unfold LexicalJudgment.IdentifierContinue at accepted
  unfold LexicalJudgment.AsciiLetter LexicalJudgment.AsciiDigit at accepted
  rw [Char.utf8Size_eq_one_iff]
  rcases accepted with (letter | digit | rfl)
  · rcases letter with upper | lower
    · change 'A'.val ≤ character.val ∧
        character.val ≤ 'Z'.val at upper
      exact Nat.le_trans upper.2 (by decide)
    · change 'a'.val ≤ character.val ∧
        character.val ≤ 'z'.val at lower
      exact Nat.le_trans lower.2 (by decide)
  · change '0'.val ≤ character.val ∧
      character.val ≤ '9'.val at digit
    exact Nat.le_trans digit.2 (by decide)
  · decide

private theorem asciiLetter_not_digit
    {character : Char}
    (letter : LexicalJudgment.AsciiLetter character)
    (digit : LexicalJudgment.AsciiDigit character) : False := by
  unfold LexicalJudgment.AsciiLetter at letter
  unfold LexicalJudgment.AsciiDigit at digit
  rcases letter with upper | lower
  · change 'A'.val ≤ character.val ∧
      character.val ≤ 'Z'.val at upper
    change '0'.val ≤ character.val ∧
      character.val ≤ '9'.val at digit
    exact (show ¬ 'A'.val ≤ '9'.val by decide)
      (Nat.le_trans upper.1 digit.2)
  · change 'a'.val ≤ character.val ∧
      character.val ≤ 'z'.val at lower
    change '0'.val ≤ character.val ∧
      character.val ≤ '9'.val at digit
    exact (show ¬ 'a'.val ≤ '9'.val by decide)
      (Nat.le_trans lower.1 digit.2)

private theorem byteSize_eq_length_of_identifierContinue
    (characters : List Char)
    (accepted :
      ∀ character ∈ characters,
        LexicalJudgment.IdentifierContinue character) :
    Lexer.byteSize characters = characters.length := by
  induction characters with
  | nil => simp [Lexer.byteSize]
  | cons character rest inductionHypothesis =>
      rw [byteSize_cons, identifierContinue_utf8Size
        (accepted character (by simp)),
        inductionHypothesis (by
          intro next member
          exact accepted next (by simp [member]))]
      simp only [List.length_cons]
      omega

private theorem identifierToken_prefix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.IdentifierTokenAt file cursor endByte token) :
    ∃ text kind remaining,
      characters = text.toList ++ remaining ∧
      endByte = cursor + text.utf8ByteSize ∧
      pathSegmentTextValid text = true ∧
      LexicalJudgment.IdentifierClassifies text kind ∧
      token = {
        span := LexicalJudgment.sourceSpan file cursor endByte
        payload := kind
      } := by
  rcases recognized with
    ⟨text, kind, valid, spelling, classified, rfl⟩
  rcases suffix.sourceTextDecomposition spelling with
    ⟨remaining, decomposition, endEquation⟩
  exact ⟨text, kind, remaining, decomposition, endEquation,
    valid, classified, rfl⟩

private theorem identifierToken_end_le
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.IdentifierTokenAt file cursor endByte token) :
    endByte ≤ cursor + Lexer.byteSize
      (Lexer.takeWhile Lexer.isIdentifierContinue characters) := by
  rcases identifierToken_prefix suffix recognized with
    ⟨text, kind, remaining, decomposition, endEquation,
      valid, _, _⟩
  cases textEquation : text.toList with
  | nil => simp [pathSegmentTextValid, textEquation] at valid
  | cons first rest =>
      rw [pathSegmentTextValid, textEquation] at valid
      change (Lexer.isAsciiLetter first &&
        rest.all Lexer.isIdentifierContinue) = true at valid
      rw [Bool.and_eq_true, List.all_eq_true] at valid
      have allAccepted :
          ∀ character ∈ first :: rest,
            Lexer.isIdentifierContinue character = true := by
        intro character member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp [Lexer.isIdentifierContinue, valid.1]
        · exact valid.2 character member
      have lengthBound := prefix_length_le_takeWhile
        Lexer.isIdentifierContinue characters (first :: rest) remaining
        (by simpa [textEquation] using decomposition)
        allAccepted
      have relationalAccepted :
          ∀ character ∈ first :: rest,
            LexicalJudgment.IdentifierContinue character := by
        intro character member
        exact (isIdentifierContinue_eq_true_iff character).mp
          (allAccepted character member)
      have executorAccepted :
          ∀ character ∈
              Lexer.takeWhile Lexer.isIdentifierContinue characters,
            LexicalJudgment.IdentifierContinue character := by
        intro character member
        exact (isIdentifierContinue_eq_true_iff character).mp
          (takeWhile_all Lexer.isIdentifierContinue characters
            character member)
      have prefixBytes :=
        byteSize_eq_length_of_identifierContinue
          (first :: rest) relationalAccepted
      have executorBytes :=
        byteSize_eq_length_of_identifierContinue
          (Lexer.takeWhile Lexer.isIdentifierContinue characters)
          executorAccepted
      rw [stringByteSize_eq_byteSize, textEquation,
        prefixBytes] at endEquation
      omega

private theorem identifierClassifies_executor
    {text : String}
    {kind : TokenKind}
    (classified : LexicalJudgment.IdentifierClassifies text kind) :
    kind = Lexer.classifyIdentifier text := by
  cases classified with
  | hardKeyword keyword =>
      simp [Lexer.classifyIdentifier, HardKeyword.ofString?_spelling]
  | identifier text notKeyword =>
      simp [Lexer.classifyIdentifier, notKeyword]

private theorem identifierToken_eq_executor
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.IdentifierTokenAt file cursor endByte token)
    (sameEnd : endByte = cursor + Lexer.byteSize
      (Lexer.takeWhile Lexer.isIdentifierContinue characters)) :
    token = Lexer.tokenAt file cursor
      (cursor + Lexer.byteSize
        (Lexer.takeWhile Lexer.isIdentifierContinue characters))
      (Lexer.classifyIdentifier
        (String.ofList
          (Lexer.takeWhile Lexer.isIdentifierContinue characters))) := by
  rcases identifierToken_prefix suffix recognized with
    ⟨text, kind, remaining, decomposition, endEquation,
      valid, classified, tokenEquation⟩
  cases textEquation : text.toList with
  | nil => simp [pathSegmentTextValid, textEquation] at valid
  | cons first rest =>
      rw [pathSegmentTextValid, textEquation] at valid
      change (Lexer.isAsciiLetter first &&
        rest.all Lexer.isIdentifierContinue) = true at valid
      rw [Bool.and_eq_true, List.all_eq_true] at valid
      have allAccepted :
          ∀ character ∈ first :: rest,
            Lexer.isIdentifierContinue character = true := by
        intro character member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp [Lexer.isIdentifierContinue, valid.1]
        · exact valid.2 character member
      have relationalAccepted :
          ∀ character ∈ first :: rest,
            LexicalJudgment.IdentifierContinue character := by
        intro character member
        exact (isIdentifierContinue_eq_true_iff character).mp
          (allAccepted character member)
      have executorAccepted :
          ∀ character ∈
              Lexer.takeWhile Lexer.isIdentifierContinue characters,
            LexicalJudgment.IdentifierContinue character := by
        intro character member
        exact (isIdentifierContinue_eq_true_iff character).mp
          (takeWhile_all Lexer.isIdentifierContinue characters
            character member)
      have prefixBytes :=
        byteSize_eq_length_of_identifierContinue
          (first :: rest) relationalAccepted
      have executorBytes :=
        byteSize_eq_length_of_identifierContinue
          (Lexer.takeWhile Lexer.isIdentifierContinue characters)
          executorAccepted
      have lengthEquation :
          (first :: rest).length =
            (Lexer.takeWhile Lexer.isIdentifierContinue characters).length := by
        rw [stringByteSize_eq_byteSize, textEquation,
          prefixBytes] at endEquation
        omega
      rcases takeWhile_decomposition Lexer.isIdentifierContinue characters with
        ⟨executorRemaining, executorDecomposition⟩
      have relationalPrefix : first :: rest <+: characters :=
        ⟨remaining, by simpa [textEquation] using decomposition.symm⟩
      have executorPrefix :
          Lexer.takeWhile Lexer.isIdentifierContinue characters <+:
            characters :=
        ⟨executorRemaining, executorDecomposition.symm⟩
      have listEquation :
          first :: rest =
            Lexer.takeWhile Lexer.isIdentifierContinue characters := by
        rw [List.prefix_iff_eq_take] at relationalPrefix executorPrefix
        calc
          first :: rest = characters.take (first :: rest).length :=
            relationalPrefix
          _ = characters.take
              (Lexer.takeWhile Lexer.isIdentifierContinue characters).length :=
            congrArg (fun length => characters.take length) lengthEquation
          _ = Lexer.takeWhile Lexer.isIdentifierContinue characters :=
            executorPrefix.symm
      have textEquality :
          text = String.ofList
            (Lexer.takeWhile Lexer.isIdentifierContinue characters) := by
        apply String.toList_inj.mp
        simp [textEquation, listEquation]
      have kindEquation := identifierClassifies_executor classified
      rw [textEquality] at kindEquation
      rw [tokenEquation, sameEnd, kindEquation]
      rfl

private theorem identifierCandidateAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor (character :: rest))
    (letter : Lexer.isAsciiLetter character = true) :
    let spellingCharacters :=
      Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest)
    let text := String.ofList spellingCharacters
    let endByte := cursor + Lexer.byteSize spellingCharacters
    let kind := Lexer.classifyIdentifier text
    LexicalJudgment.CandidateAt file pendingAssembly cursor
      (.token .identifier (Lexer.tokenAt file cursor endByte kind)) := by
  dsimp only
  have headContinuation :
      Lexer.isIdentifierContinue character = true := by
    simp [Lexer.isIdentifierContinue, letter]
  have takeEquation :
      Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest) =
        character :: Lexer.takeWhile Lexer.isIdentifierContinue rest := by
    simp [Lexer.takeWhile, headContinuation]
  have valid :
      pathSegmentTextValid
        (String.ofList
          (Lexer.takeWhile Lexer.isIdentifierContinue
            (character :: rest))) = true := by
    rw [takeEquation]
    apply pathSegmentTextValid_of_cons
    · exact (isAsciiLetter_eq_true_iff character).mp letter
    · intro next member
      exact (isIdentifierContinue_eq_true_iff next).mp
        (takeWhile_all Lexer.isIdentifierContinue rest next member)
  rcases takeWhile_decomposition Lexer.isIdentifierContinue
      (character :: rest) with ⟨remaining, decomposition⟩
  have spelling := suffix.sourceTextAt decomposition
  apply LexicalJudgment.CandidateAt.identifier
  refine ⟨String.ofList
      (Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest)),
    Lexer.classifyIdentifier
      (String.ofList
        (Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest))),
    valid, ?_, classifyIdentifier_spec _, ?_⟩
  · simpa using spelling
  · rfl

private theorem hasPragmaBoundary_complete
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (boundary : LexicalJudgment.PragmaBoundaryAt file cursor) :
    Lexer.hasPragmaBoundary characters = true := by
  cases characters with
  | nil => rfl
  | cons character rest =>
      have scalar := suffix.scalarAt
      have rejected := boundary character
        (cursor + character.utf8Size) scalar
      have executable : Lexer.isPragmaContinuation character = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        exact rejected
          ((isPragmaContinuation_eq_true_iff character).mp accepted)
      simp [Lexer.hasPragmaBoundary, executable]

private theorem startsWith_sound
    {expected actual : List Char}
    (recognized : Lexer.startsWith expected actual = true) :
    ∃ remaining, actual = expected ++ remaining := by
  induction expected generalizing actual with
  | nil => exact ⟨actual, by simp⟩
  | cons expectedCharacter expectedRest inductionHypothesis =>
      cases actual with
      | nil => simp [Lexer.startsWith] at recognized
      | cons actualCharacter actualRest =>
          simp only [Lexer.startsWith, Bool.and_eq_true] at recognized
          have characterEquation : expectedCharacter = actualCharacter := by
            exact eq_of_beq recognized.1
          subst actualCharacter
          rcases inductionHypothesis recognized.2 with
            ⟨remaining, decomposition⟩
          exact ⟨remaining, by simp [decomposition]⟩

private theorem hasPragmaBoundary_sound
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (recognized : Lexer.hasPragmaBoundary characters = true) :
    LexicalJudgment.PragmaBoundaryAt file cursor := by
  intro candidate next scalar
  cases characters with
  | nil =>
      have atEnd := suffix.remainingByteSize
      simp [Lexer.byteSize] at atEnd
      have progress := scalar.1
      have nextBound := scalar.2.1.2.1
      omega
  | cons character rest =>
      have executable : Lexer.isPragmaContinuation character = false := by
        simpa [Lexer.hasPragmaBoundary] using recognized
      rcases suffix.sourceTextDecomposition scalar.2 with
        ⟨remaining, decomposition, _⟩
      have characterEquation : candidate = character := by
        have heads := congrArg List.head? decomposition
        simpa using heads.symm
      subst candidate
      intro continuation
      have accepted :=
        (isPragmaContinuation_eq_true_iff character).mpr continuation
      rw [executable] at accepted
      contradiction

private def samePragmaKind : PragmaKind → PragmaKind → Bool
  | .noCoverageCondition, .noCoverageCondition
  | .noPattersonCondition, .noPattersonCondition
  | .noBoundedVariableCondition, .noBoundedVariableCondition
  | .noGenericInstanceFor, .noGenericInstanceFor => true
  | _, _ => false

private theorem pragma_startsWith
    (expected actual : PragmaKind)
    (remaining : List Char) :
    Lexer.startsWith expected.spelling.toList
      (actual.spelling.toList ++ remaining) =
        samePragmaKind expected actual := by
  cases expected <;> cases actual <;> rfl

private theorem pragma_match_condition
    (expected actual : PragmaKind)
    (remaining : List Char)
    (boundary : Lexer.hasPragmaBoundary remaining = true) :
    (Lexer.startsWith expected.spelling.toList
          (actual.spelling.toList ++ remaining) &&
        Lexer.hasPragmaBoundary
          ((actual.spelling.toList ++ remaining).drop
            expected.spelling.toList.length)) =
      samePragmaKind expected actual := by
  cases expected <;> cases actual <;>
    simp [pragma_startsWith, samePragmaKind, boundary]

private theorem pragmaSpelling_of_matchCondition
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (kind : PragmaKind)
    (suffix : SuffixAt file cursor characters)
    (recognized :
      (Lexer.startsWith kind.spelling.toList characters &&
        Lexer.hasPragmaBoundary
          (characters.drop kind.spelling.toList.length)) = true) :
    LexicalJudgment.PragmaSpellingAt file cursor
      (cursor + kind.spelling.utf8ByteSize) kind := by
  rw [Bool.and_eq_true] at recognized
  rcases recognized with ⟨starts, boundary⟩
  rcases startsWith_sound starts with ⟨remaining, decomposition⟩
  rw [decomposition, List.drop_left] at boundary
  have spelling := suffix.sourceTextAt decomposition
  have byteEquation :
      Lexer.byteSize kind.spelling.toList = kind.spelling.utf8ByteSize := by
    rw [← stringByteSize_eq_byteSize]
  have after :
      SuffixAt file (cursor + kind.spelling.utf8ByteSize) remaining :=
    suffix.advance decomposition (by rw [byteEquation])
  constructor
  · simpa [byteEquation] using spelling
  · exact hasPragmaBoundary_sound after boundary

private theorem pragmaMatch_sound
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {kind : PragmaKind}
    (suffix : SuffixAt file cursor characters)
    (matched : Lexer.pragmaMatch? characters = some kind) :
    LexicalJudgment.PragmaSpellingAt file cursor
      (cursor + kind.spelling.utf8ByteSize) kind := by
  unfold Lexer.pragmaMatch? at matched
  dsimp only at matched
  split at matched
  · have kindEquation : kind = .noCoverageCondition := by
      exact Option.some.inj matched.symm
    subst kind
    exact pragmaSpelling_of_matchCondition .noCoverageCondition suffix
      (by assumption)
  · split at matched
    · have kindEquation : kind = .noPattersonCondition := by
        exact Option.some.inj matched.symm
      subst kind
      exact pragmaSpelling_of_matchCondition .noPattersonCondition suffix
        (by assumption)
    · split at matched
      · have kindEquation : kind = .noBoundedVariableCondition := by
          exact Option.some.inj matched.symm
        subst kind
        exact pragmaSpelling_of_matchCondition .noBoundedVariableCondition
          suffix (by assumption)
      · split at matched
        · have kindEquation : kind = .noGenericInstanceFor := by
            exact Option.some.inj matched.symm
          subst kind
          exact pragmaSpelling_of_matchCondition .noGenericInstanceFor
            suffix (by assumption)
        · simp at matched

private theorem pragmaMatch_decomposition
    {characters : List Char}
    {kind : PragmaKind}
    (matched : Lexer.pragmaMatch? characters = some kind) :
    ∃ remaining, characters = kind.spelling.toList ++ remaining := by
  unfold Lexer.pragmaMatch? at matched
  dsimp only at matched
  split at matched
  · have kindEquation : kind = .noCoverageCondition := by
      exact Option.some.inj matched.symm
    subst kind
    apply startsWith_sound
    simp_all only [Bool.and_eq_true]
  · split at matched
    · have kindEquation : kind = .noPattersonCondition := by
        exact Option.some.inj matched.symm
      subst kind
      apply startsWith_sound
      simp_all only [Bool.and_eq_true]
    · split at matched
      · have kindEquation : kind = .noBoundedVariableCondition := by
          exact Option.some.inj matched.symm
        subst kind
        apply startsWith_sound
        simp_all only [Bool.and_eq_true]
      · split at matched
        · have kindEquation : kind = .noGenericInstanceFor := by
            exact Option.some.inj matched.symm
          subst kind
          apply startsWith_sound
          simp_all only [Bool.and_eq_true]
        · simp at matched

private theorem pragmaMatch_complete
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {kind : PragmaKind}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.PragmaSpellingAt file cursor endByte kind) :
    Lexer.pragmaMatch? characters = some kind := by
  rcases suffix.sourceTextDecomposition recognized.1 with
    ⟨remaining, decomposition, endEquation⟩
  have spellingBytes :
      Lexer.byteSize kind.spelling.toList = kind.spelling.utf8ByteSize := by
    rw [← stringByteSize_eq_byteSize]
  have after : SuffixAt file endByte remaining :=
    suffix.advance decomposition (by
    rw [endEquation, spellingBytes])
  have boundary := hasPragmaBoundary_complete after recognized.2
  unfold Lexer.pragmaMatch?
  simp only [decomposition]
  rw [pragma_match_condition .noCoverageCondition kind remaining boundary,
    pragma_match_condition .noPattersonCondition kind remaining boundary,
    pragma_match_condition .noBoundedVariableCondition kind remaining boundary,
    pragma_match_condition .noGenericInstanceFor kind remaining boundary]
  cases kind <;> rfl

private theorem candidateAt_of_letter
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor (character :: rest))
    (letter : Lexer.isAsciiLetter character = true)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    (∃ endByte token,
      candidate = .token .pragmaName token ∧
        LexicalJudgment.PragmaTokenAt file cursor endByte token) ∨
    (∃ endByte token,
      candidate = .token .identifier token ∧
        LexicalJudgment.IdentifierTokenAt file cursor endByte token) := by
  cases recognized with
  | lineComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | blockComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      have quote := suffix.character_eq_of_byteAtAscii
        quoteAt (expected := '"') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | pragmaName endByte token recognized =>
      exact Or.inl ⟨endByte, token, rfl, recognized⟩
  | identifier endByte token recognized =>
      exact Or.inr ⟨endByte, token, rfl, recognized⟩
  | decimal endByte token recognized =>
      rcases recognized with
        ⟨digits, ⟨nonempty, allDigits⟩, spelling, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      cases digitsEquation : digits.toList with
      | nil => contradiction
      | cons first tail =>
          have firstEquation : character = first := by
            have heads := congrArg List.head? decomposition
            simpa [digitsEquation] using heads
          subst first
          have digit := allDigits character (by simp [digitsEquation])
          have asciiLetter :=
            (isAsciiLetter_eq_true_iff character).mp letter
          unfold LexicalJudgment.AsciiDigit at digit
          unfold LexicalJudgment.AsciiLetter at asciiLetter
          rcases asciiLetter with upper | lower
          · change '0'.val ≤ character.val ∧
              character.val ≤ '9'.val at digit
            change 'A'.val ≤ character.val ∧
              character.val ≤ 'Z'.val at upper
            exact False.elim ((show ¬ 'A'.val ≤ '9'.val by decide)
              (Nat.le_trans upper.1 digit.2))
          · change '0'.val ≤ character.val ∧
              character.val ≤ '9'.val at digit
            change 'a'.val ≤ character.val ∧
              character.val ≤ 'z'.val at lower
            exact False.elim ((show ¬ 'a'.val ≤ '9'.val by decide)
              (Nat.le_trans lower.1 digit.2))
  | hexadecimal endByte token recognized =>
      rcases recognized with ⟨digits, _, spelling, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      have zero : character = '0' := by
        simpa using congrArg List.head? decomposition
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨writtenSymbol, spelling, _, _, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      cases writtenSymbol <;>
        simp [Symbol.spelling] at decomposition <;>
        rcases decomposition with ⟨rfl, _⟩ <;>
        simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
          Lexer.isAsciiUpper] at letter

private theorem candidateAt_of_digit
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor (character :: rest))
    (digitStart : Lexer.isAsciiDigit character = true)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    (∃ endByte token,
      candidate = .token .numericLiteral token ∧
        LexicalJudgment.DecimalTokenAt file cursor endByte token) ∨
    (∃ endByte token,
      candidate = .token .numericLiteral token ∧
        LexicalJudgment.HexadecimalTokenAt file cursor endByte token) := by
  have actualDigit :=
    (isAsciiDigit_eq_true_iff character).mp digitStart
  cases recognized with
  | lineComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiDigit] at digitStart
  | blockComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiDigit] at digitStart
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      have quote := suffix.character_eq_of_byteAtAscii
        quoteAt (expected := '"') (by decide)
      subst character
      simp [Lexer.isAsciiDigit] at digitStart
  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, spelling, tokenEquation⟩
      rcases suffix.sourceTextDecomposition spelling.1 with
        ⟨remaining, decomposition, _⟩
      cases kind <;>
        simp [PragmaKind.spelling] at decomposition <;>
        rcases decomposition with ⟨rfl, _⟩ <;>
        simp [Lexer.isAsciiDigit] at digitStart
  | identifier endByte token recognized =>
      rcases identifierToken_prefix suffix recognized with
        ⟨text, kind, remaining, decomposition, endEquation,
          valid, classified, tokenEquation⟩
      cases textEquation : text.toList with
      | nil => simp [pathSegmentTextValid, textEquation] at valid
      | cons first tail =>
          rw [pathSegmentTextValid, textEquation] at valid
          change (Lexer.isAsciiLetter first &&
            tail.all Lexer.isIdentifierContinue) = true at valid
          rw [Bool.and_eq_true] at valid
          have firstEquation : character = first := by
            have heads := congrArg List.head? decomposition
            simpa [textEquation] using heads
          subst first
          exact False.elim (asciiLetter_not_digit
            ((isAsciiLetter_eq_true_iff character).mp valid.1)
            actualDigit)
  | decimal endByte token recognized =>
      exact Or.inl ⟨endByte, token, rfl, recognized⟩
  | hexadecimal endByte token recognized =>
      exact Or.inr ⟨endByte, token, rfl, recognized⟩
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨writtenSymbol, spelling, _, _, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      cases writtenSymbol <;>
        simp [Symbol.spelling] at decomposition <;>
        rcases decomposition with ⟨rfl, _⟩ <;>
        simp [Lexer.isAsciiDigit] at digitStart

private theorem asciiDigit_identifierContinue
    {character : Char}
    (digit : LexicalJudgment.AsciiDigit character) :
    LexicalJudgment.IdentifierContinue character :=
  Or.inr (Or.inl digit)

private theorem byteSize_eq_length_of_asciiDigits
    (characters : List Char)
    (digits :
      ∀ character ∈ characters, LexicalJudgment.AsciiDigit character) :
    Lexer.byteSize characters = characters.length :=
  byteSize_eq_length_of_identifierContinue characters
    (fun character member =>
      asciiDigit_identifierContinue (digits character member))

private theorem decimalCandidateAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor (character :: rest))
    (digitStart : Lexer.isAsciiDigit character = true) :
    let digitsCharacters :=
      Lexer.takeWhile Lexer.isAsciiDigit (character :: rest)
    let digits := String.ofList digitsCharacters
    let endByte := cursor + digits.utf8ByteSize
    LexicalJudgment.CandidateAt file pendingAssembly cursor
      (.token .numericLiteral
        (Lexer.tokenAt file cursor endByte
          (.decimalLiteral digits digits))) := by
  dsimp only
  have takeEquation :
      Lexer.takeWhile Lexer.isAsciiDigit (character :: rest) =
        character :: Lexer.takeWhile Lexer.isAsciiDigit rest := by
    simp [Lexer.takeWhile, digitStart]
  have decimalText :
      LexicalJudgment.DecimalText
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiDigit (character :: rest))) := by
    constructor
    · rw [String.toList_ofList, takeEquation]
      simp
    · intro next member
      rw [String.toList_ofList] at member
      exact (isAsciiDigit_eq_true_iff next).mp
        (takeWhile_all Lexer.isAsciiDigit (character :: rest) next member)
  rcases takeWhile_decomposition Lexer.isAsciiDigit
      (character :: rest) with ⟨remaining, decomposition⟩
  have spelling := suffix.sourceTextAt decomposition
  apply LexicalJudgment.CandidateAt.decimal
  refine ⟨String.ofList
      (Lexer.takeWhile Lexer.isAsciiDigit (character :: rest)),
    decimalText, ?_, rfl⟩
  simpa [stringByteSize_eq_byteSize] using spelling

private theorem decimalToken_prefix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.DecimalTokenAt file cursor endByte token) :
    ∃ digits remaining,
      characters = digits.toList ++ remaining ∧
      endByte = cursor + digits.utf8ByteSize ∧
      LexicalJudgment.DecimalText digits ∧
      token = {
        span := LexicalJudgment.sourceSpan file cursor endByte
        payload := .decimalLiteral digits digits
      } := by
  rcases recognized with ⟨digits, decimal, spelling, rfl⟩
  rcases suffix.sourceTextDecomposition spelling with
    ⟨remaining, decomposition, endEquation⟩
  exact ⟨digits, remaining, decomposition, endEquation,
    decimal, rfl⟩

private theorem decimalToken_end_le
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.DecimalTokenAt file cursor endByte token) :
    endByte ≤ cursor + Lexer.byteSize
      (Lexer.takeWhile Lexer.isAsciiDigit characters) := by
  rcases decimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      decimal, tokenEquation⟩
  have accepted :
      ∀ character ∈ digits.toList,
        Lexer.isAsciiDigit character = true := by
    intro character member
    exact (isAsciiDigit_eq_true_iff character).mpr
      (decimal.2 character member)
  have lengthBound := prefix_length_le_takeWhile
    Lexer.isAsciiDigit characters digits.toList remaining decomposition
    accepted
  have prefixBytes := byteSize_eq_length_of_asciiDigits
    digits.toList decimal.2
  have executorDigits :
      ∀ character ∈ Lexer.takeWhile Lexer.isAsciiDigit characters,
        LexicalJudgment.AsciiDigit character := by
    intro character member
    exact (isAsciiDigit_eq_true_iff character).mp
      (takeWhile_all Lexer.isAsciiDigit characters character member)
  have executorBytes := byteSize_eq_length_of_asciiDigits
    (Lexer.takeWhile Lexer.isAsciiDigit characters) executorDigits
  rw [stringByteSize_eq_byteSize, prefixBytes] at endEquation
  omega

private theorem decimalToken_eq_executor
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.DecimalTokenAt file cursor endByte token)
    (sameEnd : endByte = cursor + Lexer.byteSize
      (Lexer.takeWhile Lexer.isAsciiDigit characters)) :
    token = Lexer.tokenAt file cursor
      (cursor + Lexer.byteSize
        (Lexer.takeWhile Lexer.isAsciiDigit characters))
      (.decimalLiteral
        (String.ofList (Lexer.takeWhile Lexer.isAsciiDigit characters))
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiDigit characters))) := by
  rcases decimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      decimal, tokenEquation⟩
  have accepted :
      ∀ character ∈ digits.toList,
        Lexer.isAsciiDigit character = true := by
    intro character member
    exact (isAsciiDigit_eq_true_iff character).mpr
      (decimal.2 character member)
  have prefixBytes := byteSize_eq_length_of_asciiDigits
    digits.toList decimal.2
  have executorDigits :
      ∀ character ∈ Lexer.takeWhile Lexer.isAsciiDigit characters,
        LexicalJudgment.AsciiDigit character := by
    intro character member
    exact (isAsciiDigit_eq_true_iff character).mp
      (takeWhile_all Lexer.isAsciiDigit characters character member)
  have executorBytes := byteSize_eq_length_of_asciiDigits
    (Lexer.takeWhile Lexer.isAsciiDigit characters) executorDigits
  have lengthEquation :
      digits.toList.length =
        (Lexer.takeWhile Lexer.isAsciiDigit characters).length := by
    rw [stringByteSize_eq_byteSize, prefixBytes] at endEquation
    omega
  rcases takeWhile_decomposition Lexer.isAsciiDigit characters with
    ⟨executorRemaining, executorDecomposition⟩
  have relationalPrefix : digits.toList <+: characters :=
    ⟨remaining, decomposition.symm⟩
  have executorPrefix :
      Lexer.takeWhile Lexer.isAsciiDigit characters <+: characters :=
    ⟨executorRemaining, executorDecomposition.symm⟩
  rw [List.prefix_iff_eq_take] at relationalPrefix executorPrefix
  have listEquation :
      digits.toList = Lexer.takeWhile Lexer.isAsciiDigit characters := by
    calc
      digits.toList = characters.take digits.toList.length :=
        relationalPrefix
      _ = characters.take
          (Lexer.takeWhile Lexer.isAsciiDigit characters).length :=
        congrArg (fun length => characters.take length) lengthEquation
      _ = Lexer.takeWhile Lexer.isAsciiDigit characters :=
        executorPrefix.symm
  have digitsEquation :
      digits = String.ofList
        (Lexer.takeWhile Lexer.isAsciiDigit characters) := by
    apply String.toList_inj.mp
    simp [listEquation]
  rw [tokenEquation, sameEnd, digitsEquation]
  rfl

private theorem asciiHexDigit_identifierContinue
    {character : Char}
    (digit : LexicalJudgment.AsciiHexDigit character) :
    LexicalJudgment.IdentifierContinue character := by
  rcases digit with decimal | lower | upper
  · exact asciiDigit_identifierContinue decimal
  · exact Or.inl (Or.inr ⟨lower.1,
      Nat.le_trans lower.2 (by decide)⟩)
  · exact Or.inl (Or.inl ⟨upper.1,
      Nat.le_trans upper.2 (by decide)⟩)

private theorem byteSize_eq_length_of_asciiHexDigits
    (characters : List Char)
    (digits :
      ∀ character ∈ characters,
        LexicalJudgment.AsciiHexDigit character) :
    Lexer.byteSize characters = characters.length :=
  byteSize_eq_length_of_identifierContinue characters
    (fun character member =>
      asciiHexDigit_identifierContinue (digits character member))

private theorem hexadecimalCandidateAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {digit : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor ('0' :: 'x' :: digit :: rest))
    (hexStart : Lexer.isAsciiHexDigit digit = true) :
    let digitsCharacters :=
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)
    let digits := String.ofList digitsCharacters
    let spelling := "0x" ++ digits
    let endByte := cursor + spelling.utf8ByteSize
    LexicalJudgment.CandidateAt file pendingAssembly cursor
      (.token .numericLiteral
        (Lexer.tokenAt file cursor endByte
          (.hexadecimalLiteral spelling digits))) := by
  dsimp only
  have takeEquation :
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest) =
        digit :: Lexer.takeWhile Lexer.isAsciiHexDigit rest := by
    simp [Lexer.takeWhile, hexStart]
  have hexadecimalDigits :
      LexicalJudgment.HexadecimalDigits
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))) := by
    constructor
    · rw [String.toList_ofList, takeEquation]
      simp
    · intro next member
      rw [String.toList_ofList] at member
      exact (isAsciiHexDigit_eq_true_iff next).mp
        (takeWhile_all Lexer.isAsciiHexDigit (digit :: rest) next member)
  rcases takeWhile_decomposition Lexer.isAsciiHexDigit
      (digit :: rest) with ⟨remaining, decomposition⟩
  have fullDecomposition :
      '0' :: 'x' :: digit :: rest =
        ('0' :: 'x' ::
          Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) ++
          remaining := by
    simp only [List.cons_append, List.cons.injEq, true_and]
    exact decomposition
  have source := suffix.sourceTextAt fullDecomposition
  have consumedByteEquation :
      Lexer.byteSize ('0' :: 'x' ::
        Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) =
      ("0x" ++ String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit
          (digit :: rest))).utf8ByteSize := by
    rw [show ('0' :: 'x' ::
        Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) =
      ['0', 'x'] ++
        Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest) by rfl,
      byteSize_append, String.utf8ByteSize_append,
      stringByteSize_eq_byteSize
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))),
      String.toList_ofList]
    have prefixBytes : Lexer.byteSize ['0', 'x'] = "0x".utf8ByteSize :=
      by decide
    rw [prefixBytes]
  have consumedTextEquation :
      String.ofList ('0' :: 'x' ::
        Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) =
      "0x" ++ String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) := by
    apply String.toList_inj.mp
    simp
  rw [consumedByteEquation, consumedTextEquation] at source
  apply LexicalJudgment.CandidateAt.hexadecimal
  refine ⟨String.ofList
      (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)),
    hexadecimalDigits, ?_, rfl⟩
  simpa [Lexer.byteSize, String.utf8ByteSize_append] using source

private theorem hexadecimalToken_prefix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.HexadecimalTokenAt file cursor endByte token) :
    ∃ digits remaining,
      characters = ('0' :: 'x' :: digits.toList) ++ remaining ∧
      endByte = cursor + ("0x" ++ digits).utf8ByteSize ∧
      LexicalJudgment.HexadecimalDigits digits ∧
      token = {
        span := LexicalJudgment.sourceSpan file cursor endByte
        payload := .hexadecimalLiteral ("0x" ++ digits) digits
      } := by
  rcases recognized with ⟨digits, hexadecimal, spelling, rfl⟩
  rcases suffix.sourceTextDecomposition spelling with
    ⟨remaining, decomposition, endEquation⟩
  refine ⟨digits, remaining, ?_, endEquation, hexadecimal, rfl⟩
  simpa using decomposition

private theorem hexadecimalToken_end_le
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {digit : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor ('0' :: 'x' :: digit :: rest))
    (recognized :
      LexicalJudgment.HexadecimalTokenAt file cursor endByte token) :
    endByte ≤ cursor + ("0x" ++
      String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))).utf8ByteSize := by
  rcases hexadecimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      hexadecimal, tokenEquation⟩
  have digitDecomposition :
      digit :: rest = digits.toList ++ remaining := by
    simpa only [List.cons_append, List.cons.injEq, true_and]
      using decomposition
  have accepted :
      ∀ character ∈ digits.toList,
        Lexer.isAsciiHexDigit character = true := by
    intro character member
    exact (isAsciiHexDigit_eq_true_iff character).mpr
      (hexadecimal.2 character member)
  have lengthBound := prefix_length_le_takeWhile
    Lexer.isAsciiHexDigit (digit :: rest) digits.toList remaining
    digitDecomposition accepted
  have prefixBytes := byteSize_eq_length_of_asciiHexDigits
    digits.toList hexadecimal.2
  have executorDigits :
      ∀ character ∈ Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest),
        LexicalJudgment.AsciiHexDigit character := by
    intro character member
    exact (isAsciiHexDigit_eq_true_iff character).mp
      (takeWhile_all Lexer.isAsciiHexDigit (digit :: rest)
        character member)
  have executorBytes := byteSize_eq_length_of_asciiHexDigits
    (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) executorDigits
  have prefixLiteral : "0x".utf8ByteSize = 2 := by decide
  rw [String.utf8ByteSize_append, prefixLiteral,
    stringByteSize_eq_byteSize digits, prefixBytes] at endEquation
  rw [String.utf8ByteSize_append, prefixLiteral,
    stringByteSize_eq_byteSize
      (String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))),
    String.toList_ofList, executorBytes]
  omega

private theorem hexadecimalToken_eq_executor
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {digit : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor ('0' :: 'x' :: digit :: rest))
    (recognized :
      LexicalJudgment.HexadecimalTokenAt file cursor endByte token)
    (sameEnd : endByte = cursor + ("0x" ++
      String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))).utf8ByteSize) :
    token = Lexer.tokenAt file cursor endByte
      (.hexadecimalLiteral
        ("0x" ++ String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)))
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)))) := by
  rcases hexadecimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      hexadecimal, tokenEquation⟩
  have digitDecomposition :
      digit :: rest = digits.toList ++ remaining := by
    simpa only [List.cons_append, List.cons.injEq, true_and]
      using decomposition
  have prefixBytes := byteSize_eq_length_of_asciiHexDigits
    digits.toList hexadecimal.2
  have executorDigits :
      ∀ character ∈ Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest),
        LexicalJudgment.AsciiHexDigit character := by
    intro character member
    exact (isAsciiHexDigit_eq_true_iff character).mp
      (takeWhile_all Lexer.isAsciiHexDigit (digit :: rest)
        character member)
  have executorBytes := byteSize_eq_length_of_asciiHexDigits
    (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) executorDigits
  have lengthEquation : digits.toList.length =
      (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)).length := by
    have prefixLiteral : "0x".utf8ByteSize = 2 := by decide
    rw [String.utf8ByteSize_append, prefixLiteral,
      stringByteSize_eq_byteSize digits, prefixBytes] at endEquation
    rw [String.utf8ByteSize_append, prefixLiteral,
      stringByteSize_eq_byteSize
        (String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))),
      String.toList_ofList, executorBytes] at sameEnd
    omega
  rcases takeWhile_decomposition Lexer.isAsciiHexDigit (digit :: rest) with
    ⟨executorRemaining, executorDecomposition⟩
  have relationalPrefix : digits.toList <+: digit :: rest :=
    ⟨remaining, digitDecomposition.symm⟩
  have executorPrefix :
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest) <+:
        digit :: rest :=
    ⟨executorRemaining, executorDecomposition.symm⟩
  rw [List.prefix_iff_eq_take] at relationalPrefix executorPrefix
  have listEquation : digits.toList =
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest) := by
    calc
      digits.toList = (digit :: rest).take digits.toList.length :=
        relationalPrefix
      _ = (digit :: rest).take
          (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)).length :=
        congrArg (fun length => (digit :: rest).take length) lengthEquation
      _ = Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest) :=
        executorPrefix.symm
  have digitsEquation : digits = String.ofList
      (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) := by
    apply String.toList_inj.mp
    simp [listEquation]
  rw [tokenEquation, digitsEquation]
  rfl

private theorem decimalCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor (character :: rest))
    (digitStart : Lexer.isAsciiDigit character = true)
    (noHexadecimal :
      ¬ ∃ digit tail,
        character :: rest = '0' :: 'x' :: digit :: tail ∧
          Lexer.isAsciiHexDigit digit = true) :
    let digitsCharacters :=
      Lexer.takeWhile Lexer.isAsciiDigit (character :: rest)
    let digits := String.ofList digitsCharacters
    let endByte := cursor + digits.utf8ByteSize
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .numericLiteral
        (Lexer.tokenAt file cursor endByte
          (.decimalLiteral digits digits))) := by
  dsimp only
  have self := decimalCandidateAt
    (pendingAssembly := pendingAssembly) suffix digitStart
  refine ⟨self, ?_⟩
  intro other recognized
  rcases candidateAt_of_digit suffix digitStart recognized with
    decimal | hexadecimal
  · rcases decimal with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    have bound := decimalToken_end_le suffix otherRecognized
    have executorEnd :
        cursor +
            (String.ofList
              (Lexer.takeWhile Lexer.isAsciiDigit
                (character :: rest))).utf8ByteSize =
          cursor + Lexer.byteSize
            (Lexer.takeWhile Lexer.isAsciiDigit (character :: rest)) := by
      rw [stringByteSize_eq_byteSize, String.toList_ofList]
    by_cases sameEnd : otherEnd = cursor + Lexer.byteSize
        (Lexer.takeWhile Lexer.isAsciiDigit (character :: rest))
    · have tokenEquation := decimalToken_eq_executor
        suffix otherRecognized sameEnd
      left
      rw [tokenEquation, executorEnd]
    · rcases decimalToken_prefix suffix otherRecognized with
        ⟨otherDigits, remaining, decomposition, endEquation,
          decimalText, tokenEquation⟩
      right
      left
      rw [tokenEquation]
      simp only [LexicalJudgment.Candidate.span,
        Lexer.tokenAt, Lexer.sourceSpan,
        LexicalJudgment.sourceSpan]
      omega
  · rcases hexadecimal with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    rcases hexadecimalToken_prefix suffix otherRecognized with
      ⟨digits, remaining, decomposition, endEquation,
        hexadecimalDigits, tokenEquation⟩
    cases digitsEquation : digits.toList with
    | nil => exact False.elim (hexadecimalDigits.1 digitsEquation)
    | cons first tail =>
        apply False.elim
        apply noHexadecimal
        refine ⟨first, tail ++ remaining, ?_, ?_⟩
        · simpa [digitsEquation] using decomposition
        · exact (isAsciiHexDigit_eq_true_iff first).mpr
            (hexadecimalDigits.2 first (by simp [digitsEquation]))

private theorem identifierToken_firstLetter
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {character : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor (character :: rest))
    (recognized :
      LexicalJudgment.IdentifierTokenAt file cursor endByte token) :
    LexicalJudgment.AsciiLetter character := by
  rcases identifierToken_prefix suffix recognized with
    ⟨text, kind, remaining, decomposition, endEquation,
      valid, classified, tokenEquation⟩
  cases textEquation : text.toList with
  | nil => simp [pathSegmentTextValid, textEquation] at valid
  | cons first tail =>
      rw [pathSegmentTextValid, textEquation] at valid
      change (Lexer.isAsciiLetter first &&
        tail.all Lexer.isIdentifierContinue) = true at valid
      rw [Bool.and_eq_true] at valid
      have firstEquation : character = first := by
        have heads := congrArg List.head? decomposition
        simpa [textEquation] using heads
      subst first
      exact (isAsciiLetter_eq_true_iff character).mp valid.1

private theorem pragmaToken_first_n
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {character : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor (character :: rest))
    (recognized :
      LexicalJudgment.PragmaTokenAt file cursor endByte token) :
    character = 'n' := by
  rcases recognized with ⟨kind, spelling, tokenEquation⟩
  rcases suffix.sourceTextDecomposition spelling.1 with
    ⟨remaining, decomposition, endEquation⟩
  cases kind <;>
    simpa [PragmaKind.spelling] using congrArg List.head? decomposition

private theorem decimalToken_firstDigit
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {character : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor (character :: rest))
    (recognized :
      LexicalJudgment.DecimalTokenAt file cursor endByte token) :
    LexicalJudgment.AsciiDigit character := by
  rcases decimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      decimal, tokenEquation⟩
  cases digitsEquation : digits.toList with
  | nil => exact False.elim (decimal.1 digitsEquation)
  | cons first tail =>
      have firstEquation : character = first := by
        have heads := congrArg List.head? decomposition
        simpa [digitsEquation] using heads
      subst first
      exact decimal.2 character (by simp [digitsEquation])

private theorem hexadecimalToken_first_zero
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {character : Char}
    {rest : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor (character :: rest))
    (recognized :
      LexicalJudgment.HexadecimalTokenAt file cursor endByte token) :
    character = '0' := by
  rcases hexadecimalToken_prefix suffix recognized with
    ⟨digits, remaining, decomposition, endEquation,
      hexadecimal, tokenEquation⟩
  simpa using congrArg List.head? decomposition

private theorem candidateAt_of_symbolStart
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor (character :: rest))
    (notLetter : Lexer.isAsciiLetter character = false)
    (notDigit : Lexer.isAsciiDigit character = false)
    (notQuote : character ≠ '"')
    (notLineComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 47)
    (notBlockComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 42)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    ∃ endByte symbol token,
      candidate =
        .token (LexicalJudgment.symbolCandidateClass symbol) token ∧
      LexicalJudgment.SymbolTokenAt file pendingAssembly
        cursor endByte token ∧
      token.payload = .symbol symbol := by
  cases recognized with
  | lineComment endByte comment recognized =>
      exact False.elim (notLineComment recognized.1.1)
  | blockComment endByte comment recognized =>
      exact False.elim (notBlockComment recognized.1.1)
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      exact False.elim (notQuote
        (suffix.character_eq_of_byteAtAscii quoteAt
          (expected := '"') (by decide)))
  | pragmaName endByte token recognized =>
      have first := pragmaToken_first_n suffix recognized
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at notLetter
  | identifier endByte token recognized =>
      have letter := identifierToken_firstLetter suffix recognized
      have executable := (isAsciiLetter_eq_true_iff character).mpr letter
      rw [notLetter] at executable
      contradiction
  | decimal endByte token recognized =>
      have digit := decimalToken_firstDigit suffix recognized
      have executable := (isAsciiDigit_eq_true_iff character).mpr digit
      rw [notDigit] at executable
      contradiction
  | hexadecimal endByte token recognized =>
      have zero := hexadecimalToken_first_zero suffix recognized
      subst character
      simp [Lexer.isAsciiDigit] at notDigit
  | symbol endByte symbol token recognized kind =>
      exact ⟨endByte, symbol, token, rfl, recognized, kind⟩

private theorem multiSymbol_sound
    {first second : Char}
    {symbol : Symbol}
    (matched : Lexer.multiSymbol? first second = some symbol) :
    symbol.spelling.toList = [first, second] ∧
      LexicalJudgment.symbolCandidateClass symbol = .multiCharacterSymbol := by
  unfold Lexer.multiSymbol? at matched
  split at matched <;>
    simp_all [Symbol.spelling, LexicalJudgment.symbolCandidateClass] <;>
    subst symbol <;> decide

private theorem singleSymbol_sound
    {character : Char}
    {symbol : Symbol}
    (matched : Lexer.singleSymbol? character = some symbol) :
    symbol.spelling.toList = [character] ∧
      LexicalJudgment.symbolCandidateClass symbol = .singleCharacterSymbol := by
  unfold Lexer.singleSymbol? at matched
  split at matched <;>
    simp_all [Symbol.spelling, LexicalJudgment.symbolCandidateClass] <;>
    subst symbol <;> decide

private theorem multiSymbol_nextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {first second : Char}
    {tail : List Char}
    {symbol : Symbol}
    (suffix : SuffixAt file cursor (first :: second :: tail))
    (matched : Lexer.multiSymbol? first second = some symbol) :
    SuffixAt file (cursor + 2) tail := by
  unfold Lexer.multiSymbol? at matched
  split at matched <;> simp_all <;>
    exact suffix.advanceTwoAscii (by decide) (by decide)

private theorem multiSymbol_complete_of_class
    (symbol : Symbol)
    (first second : Char)
    (spelling : symbol.spelling.toList = [first, second])
    (candidateClass :
      LexicalJudgment.symbolCandidateClass symbol =
        .multiCharacterSymbol) :
    Lexer.multiSymbol? first second = some symbol := by
  cases symbol <;>
    simp [LexicalJudgment.symbolCandidateClass] at candidateClass
  all_goals
    simp [Symbol.spelling] at spelling
    rcases spelling with ⟨firstEquation, secondEquation⟩
    cases firstEquation
    cases secondEquation
    rfl

private theorem singleSymbol_complete_of_class
    (symbol : Symbol)
    (character : Char)
    (spelling : symbol.spelling.toList = [character])
    (candidateClass :
      LexicalJudgment.symbolCandidateClass symbol =
        .singleCharacterSymbol) :
    Lexer.singleSymbol? character = some symbol := by
  cases symbol <;>
    simp [LexicalJudgment.symbolCandidateClass] at candidateClass
  all_goals
    simp [Symbol.spelling] at spelling
    cases spelling
    rfl

private theorem symbol_eq_of_spelling_eq
    {first second : Symbol}
    (spelling : first.spelling = second.spelling) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [Symbol.spelling]

private theorem symbolCandidateClass_cases (symbol : Symbol) :
    LexicalJudgment.symbolCandidateClass symbol =
        .multiCharacterSymbol ∨
      LexicalJudgment.symbolCandidateClass symbol =
        .singleCharacterSymbol := by
  cases symbol <;>
    simp [LexicalJudgment.symbolCandidateClass]

private theorem symbolSpelling_size_of_multi
    (symbol : Symbol)
    (candidateClass :
      LexicalJudgment.symbolCandidateClass symbol =
        .multiCharacterSymbol) :
    symbol.spelling.utf8ByteSize = 2 := by
  cases symbol <;>
    simp_all [Symbol.spelling, LexicalJudgment.symbolCandidateClass] <;>
    decide

private theorem symbolSpelling_size_of_single
    (symbol : Symbol)
    (candidateClass :
      LexicalJudgment.symbolCandidateClass symbol =
        .singleCharacterSymbol) :
    symbol.spelling.utf8ByteSize = 1 := by
  cases symbol <;>
    simp_all [Symbol.spelling, LexicalJudgment.symbolCandidateClass] <;>
    decide

private theorem singleSymbol_nextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {character : Char}
    {rest : List Char}
    {symbol : Symbol}
    (suffix : SuffixAt file cursor (character :: rest))
    (matched : Lexer.singleSymbol? character = some symbol) :
    SuffixAt file (cursor + 1) rest := by
  have sound := singleSymbol_sound matched
  have spellingSize := symbolSpelling_size_of_single symbol sound.2
  have characterSize : character.utf8Size = 1 := by
    calc
      character.utf8Size = Lexer.byteSize [character] := by
        simp [Lexer.byteSize]
      _ = Lexer.byteSize symbol.spelling.toList :=
        congrArg Lexer.byteSize sound.1 |>.symm
      _ = symbol.spelling.utf8ByteSize :=
        (stringByteSize_eq_byteSize symbol.spelling).symm
      _ = 1 := spellingSize
  simpa [characterSize] using suffix.advanceOne

private theorem symbolSpelling_length_of_multi
    (symbol : Symbol)
    (candidateClass :
      LexicalJudgment.symbolCandidateClass symbol =
        .multiCharacterSymbol) :
    symbol.spelling.toList.length = 2 := by
  cases symbol <;>
    simp_all [Symbol.spelling, LexicalJudgment.symbolCandidateClass]

private theorem multiSymbol_first_facts
    {first second : Char}
    {symbol : Symbol}
    (matched : Lexer.multiSymbol? first second = some symbol) :
    Lexer.isAsciiLetter first = false ∧
      Lexer.isAsciiDigit first = false ∧
      first ≠ '"' ∧ first ≠ '/' := by
  unfold Lexer.multiSymbol? at matched
  split at matched <;>
    simp_all [Lexer.isAsciiLetter, Lexer.isAsciiLower,
      Lexer.isAsciiUpper, Lexer.isAsciiDigit]

private theorem singleSymbol_not_quote
    {character : Char}
    {symbol : Symbol}
    (matched : Lexer.singleSymbol? character = some symbol) :
    character ≠ '"' := by
  unfold Lexer.singleSymbol? at matched
  split at matched <;> simp_all

private theorem symbolToken_data
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {pendingAssembly : Bool}
    {characters : List Char}
    {symbol : Symbol}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.SymbolTokenAt file pendingAssembly cursor endByte token)
    (kind : token.payload = .symbol symbol) :
    ∃ remaining,
      characters = symbol.spelling.toList ++ remaining ∧
      LexicalJudgment.SourceTextAt file cursor endByte symbol.spelling ∧
      endByte = cursor + symbol.spelling.utf8ByteSize ∧
      (symbol = .slash →
        ¬ LexicalJudgment.BytePairAt file cursor 47 47 ∧
          ¬ LexicalJudgment.BytePairAt file cursor 47 42) ∧
      (pendingAssembly = true → symbol ≠ .leftBrace) ∧
      token = {
        span := LexicalJudgment.sourceSpan file cursor endByte
        payload := .symbol symbol
      } := by
  rcases recognized with
    ⟨writtenSymbol, spelling, slashGuard, assemblyGuard, tokenEquation⟩
  rw [tokenEquation] at kind
  simp only at kind
  have symbolEquation : writtenSymbol = symbol := by
    cases kind
    rfl
  subst symbol
  rcases suffix.sourceTextDecomposition spelling with
    ⟨remaining, decomposition, endEquation⟩
  exact ⟨remaining, decomposition, spelling, endEquation,
    slashGuard, assemblyGuard, tokenEquation⟩

private theorem multiSymbolCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {first second : Char}
    {tail : List Char}
    {symbol : Symbol}
    (suffix : SuffixAt file cursor (first :: second :: tail))
    (matched : Lexer.multiSymbol? first second = some symbol) :
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .multiCharacterSymbol
        (Lexer.tokenAt file cursor (cursor + 2) (.symbol symbol))) := by
  have sound := multiSymbol_sound matched
  have spellingSize := symbolSpelling_size_of_multi symbol sound.2
  have decomposition :
      first :: second :: tail = symbol.spelling.toList ++ tail := by
    rw [sound.1]
    rfl
  have sourceTextRaw := suffix.sourceTextAt decomposition
  have sourceText :
      LexicalJudgment.SourceTextAt file cursor (cursor + 2)
        symbol.spelling := by
    simpa [Lexer.byteSize, spellingSize] using sourceTextRaw
  have notSlash : symbol ≠ .slash := by
    intro equation
    subst symbol
    simp [LexicalJudgment.symbolCandidateClass] at sound
  have notLeftBrace : symbol ≠ .leftBrace := by
    intro equation
    subst symbol
    simp [LexicalJudgment.symbolCandidateClass] at sound
  have symbolRecognized :
      LexicalJudgment.SymbolTokenAt file pendingAssembly cursor
        (cursor + 2)
        (Lexer.tokenAt file cursor (cursor + 2) (.symbol symbol)) := by
    refine ⟨symbol, sourceText, ?_, ?_, ?_⟩
    · intro equation
      exact False.elim (notSlash equation)
    · intro _
      exact notLeftBrace
    · rfl
  have self :
      LexicalJudgment.CandidateAt file pendingAssembly cursor
        (.token .multiCharacterSymbol
          (Lexer.tokenAt file cursor (cursor + 2) (.symbol symbol))) := by
    simpa [sound.2] using
      (LexicalJudgment.CandidateAt.symbol
        (cursor + 2) symbol
        (Lexer.tokenAt file cursor (cursor + 2) (.symbol symbol))
        symbolRecognized rfl)
  rcases multiSymbol_first_facts matched with
    ⟨notLetter, notDigit, notQuote, firstNotSlash⟩
  have notLineComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
    intro pair
    rcases suffix.pair_eq_of_bytePairAscii
        (first := '/') (second := '/') pair
        (by decide) (by decide) (by decide) with
      ⟨remaining, firstEquation, restEquation⟩
    exact firstNotSlash firstEquation
  have notBlockComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
    intro pair
    rcases suffix.pair_eq_of_bytePairAscii
        (first := '/') (second := '*') pair
        (by decide) (by decide) (by decide) with
      ⟨remaining, firstEquation, restEquation⟩
    exact firstNotSlash firstEquation
  refine ⟨self, ?_⟩
  intro other recognized
  rcases candidateAt_of_symbolStart suffix notLetter notDigit notQuote
      notLineComment notBlockComment recognized with
    ⟨otherEnd, otherSymbol, otherToken, rfl,
      otherRecognized, otherKind⟩
  rcases symbolToken_data suffix otherRecognized otherKind with
    ⟨remaining, otherDecomposition, otherSourceText,
      otherEndEquation, otherSlashGuard, otherAssemblyGuard,
      otherTokenEquation⟩
  rcases symbolCandidateClass_cases otherSymbol with
    otherMulti | otherSingle
  · have otherSpellingSize :=
      symbolSpelling_size_of_multi otherSymbol otherMulti
    have sameEnd : otherEnd = cursor + 2 := by
      omega
    rw [sameEnd] at otherSourceText otherTokenEquation
    have spellingBytes :
        otherSymbol.spelling.toByteArray = symbol.spelling.toByteArray :=
      otherSourceText.2.symm.trans sourceText.2
    have symbolEquation : otherSymbol = symbol :=
      symbol_eq_of_spelling_eq (String.toByteArray_inj.mp spellingBytes)
    subst otherSymbol
    left
    simp [otherTokenEquation, otherMulti, Lexer.tokenAt,
      Lexer.sourceSpan, LexicalJudgment.sourceSpan]
  · right
    unfold LexicalJudgment.CandidateOutranks
    left
    have otherSpellingSize :=
      symbolSpelling_size_of_single otherSymbol otherSingle
    rw [otherTokenEquation]
    simp only [LexicalJudgment.Candidate.span,
      LexicalJudgment.sourceSpan, Lexer.tokenAt, Lexer.sourceSpan]
    omega

private theorem singleSymbolCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    {symbol : Symbol}
    (suffix : SuffixAt file cursor (character :: rest))
    (notLetter : Lexer.isAsciiLetter character = false)
    (notDigit : Lexer.isAsciiDigit character = false)
    (notLineComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 47)
    (notBlockComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 42)
    (noMulti :
      ∀ next tail,
        rest = next :: tail →
          Lexer.multiSymbol? character next = none)
    (matched : Lexer.singleSymbol? character = some symbol)
    (assemblyGuard : pendingAssembly = true → symbol ≠ .leftBrace) :
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .singleCharacterSymbol
        (Lexer.tokenAt file cursor (cursor + 1) (.symbol symbol))) := by
  have sound := singleSymbol_sound matched
  have spellingSize := symbolSpelling_size_of_single symbol sound.2
  have decomposition :
      character :: rest = symbol.spelling.toList ++ rest := by
    rw [sound.1]
    rfl
  have sourceTextRaw := suffix.sourceTextAt decomposition
  have sourceText :
      LexicalJudgment.SourceTextAt file cursor (cursor + 1)
        symbol.spelling := by
    simpa [Lexer.byteSize, spellingSize] using sourceTextRaw
  have symbolRecognized :
      LexicalJudgment.SymbolTokenAt file pendingAssembly cursor
        (cursor + 1)
        (Lexer.tokenAt file cursor (cursor + 1) (.symbol symbol)) := by
    refine ⟨symbol, sourceText, ?_, assemblyGuard, ?_⟩
    · intro equation
      subst symbol
      exact ⟨notLineComment, notBlockComment⟩
    · rfl
  have self :
      LexicalJudgment.CandidateAt file pendingAssembly cursor
        (.token .singleCharacterSymbol
          (Lexer.tokenAt file cursor (cursor + 1) (.symbol symbol))) := by
    simpa [sound.2] using
      (LexicalJudgment.CandidateAt.symbol
        (cursor + 1) symbol
        (Lexer.tokenAt file cursor (cursor + 1) (.symbol symbol))
        symbolRecognized rfl)
  refine ⟨self, ?_⟩
  intro other recognized
  rcases candidateAt_of_symbolStart suffix notLetter notDigit
      (singleSymbol_not_quote matched) notLineComment notBlockComment
      recognized with
    ⟨otherEnd, otherSymbol, otherToken, rfl,
      otherRecognized, otherKind⟩
  rcases symbolToken_data suffix otherRecognized otherKind with
    ⟨remaining, otherDecomposition, otherSourceText,
      otherEndEquation, otherSlashGuard, otherAssemblyGuard,
      otherTokenEquation⟩
  rcases symbolCandidateClass_cases otherSymbol with
    otherMulti | otherSingle
  · have spellingLength :=
      symbolSpelling_length_of_multi otherSymbol otherMulti
    cases rest with
    | nil =>
        have lengthEquation := congrArg List.length otherDecomposition
        simp [spellingLength] at lengthEquation
        omega
    | cons next tail =>
        have prefixEvidence :
            otherSymbol.spelling.toList <+: character :: next :: tail :=
          ⟨remaining, otherDecomposition.symm⟩
        rw [List.prefix_iff_eq_take] at prefixEvidence
        rw [spellingLength] at prefixEvidence
        have otherMatched := multiSymbol_complete_of_class otherSymbol
          character next (by simpa using prefixEvidence) otherMulti
        have blocked := noMulti next tail rfl
        rw [blocked] at otherMatched
        contradiction
  · have otherSpellingSize :=
      symbolSpelling_size_of_single otherSymbol otherSingle
    have sameEnd : otherEnd = cursor + 1 := by
      omega
    rw [sameEnd] at otherSourceText otherTokenEquation
    have spellingBytes :
        otherSymbol.spelling.toByteArray = symbol.spelling.toByteArray :=
      otherSourceText.2.symm.trans sourceText.2
    have symbolEquation : otherSymbol = symbol :=
      symbol_eq_of_spelling_eq (String.toByteArray_inj.mp spellingBytes)
    subst otherSymbol
    left
    simp [otherTokenEquation, otherSingle, Lexer.tokenAt,
      Lexer.sourceSpan, LexicalJudgment.sourceSpan]

private theorem hexadecimalCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {digit : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor ('0' :: 'x' :: digit :: rest))
    (hexStart : Lexer.isAsciiHexDigit digit = true) :
    let digitsCharacters :=
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)
    let digits := String.ofList digitsCharacters
    let spelling := "0x" ++ digits
    let endByte := cursor + spelling.utf8ByteSize
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .numericLiteral
        (Lexer.tokenAt file cursor endByte
          (.hexadecimalLiteral spelling digits))) := by
  dsimp only
  have self := hexadecimalCandidateAt
    (pendingAssembly := pendingAssembly) suffix hexStart
  have digitStart : Lexer.isAsciiDigit '0' = true := by decide
  refine ⟨self, ?_⟩
  intro other recognized
  rcases candidateAt_of_digit suffix digitStart recognized with
    decimal | hexadecimal
  · rcases decimal with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    have bound := decimalToken_end_le suffix otherRecognized
    have decimalTake :
        Lexer.takeWhile Lexer.isAsciiDigit
          ('0' :: 'x' :: digit :: rest) = ['0'] := by
      rfl
    rw [decimalTake] at bound
    have oneByte : Lexer.byteSize ['0'] = 1 := by decide
    rw [oneByte] at bound
    rcases decimalToken_prefix suffix otherRecognized with
      ⟨otherDigits, remaining, decomposition, endEquation,
        decimalText, tokenEquation⟩
    have producedLong :
        1 < ("0x" ++ String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit
            (digit :: rest))).utf8ByteSize := by
      rw [String.utf8ByteSize_append]
      have prefixBytes : "0x".utf8ByteSize = 2 := by decide
      omega
    right
    left
    rw [tokenEquation]
    simp only [LexicalJudgment.Candidate.span,
      Lexer.tokenAt, Lexer.sourceSpan,
      LexicalJudgment.sourceSpan]
    omega
  · rcases hexadecimal with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    have bound := hexadecimalToken_end_le suffix otherRecognized
    by_cases sameEnd : (otherEnd = cursor + ("0x" ++
        String.ofList
          (Lexer.takeWhile Lexer.isAsciiHexDigit
            (digit :: rest))).utf8ByteSize)
    · have tokenEquation := hexadecimalToken_eq_executor
        suffix otherRecognized sameEnd
      left
      rw [tokenEquation, sameEnd]
    · rcases hexadecimalToken_prefix suffix otherRecognized with
        ⟨otherDigits, remaining, decomposition, endEquation,
          hexadecimalDigits, tokenEquation⟩
      right
      left
      rw [tokenEquation]
      simp only [LexicalJudgment.Candidate.span,
        Lexer.tokenAt, Lexer.sourceSpan,
        LexicalJudgment.sourceSpan]
      omega
private theorem pragmaCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {characters : List Char}
    {kind : PragmaKind}
    (suffix : SuffixAt file cursor characters)
    (matched : Lexer.pragmaMatch? characters = some kind) :
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .pragmaName
        (Lexer.tokenAt file cursor
          (cursor + kind.spelling.utf8ByteSize) (.pragmaName kind))) := by
  have spelling := pragmaMatch_sound suffix matched
  have self :
      LexicalJudgment.CandidateAt file pendingAssembly cursor
        (.token .pragmaName
          (Lexer.tokenAt file cursor
            (cursor + kind.spelling.utf8ByteSize) (.pragmaName kind))) := by
    apply LexicalJudgment.CandidateAt.pragmaName
    exact ⟨kind, spelling, rfl⟩
  rcases suffix.sourceTextDecomposition spelling.1 with
    ⟨remaining, decomposition, endEquation⟩
  have firstCharacter : ∃ rest, characters = 'n' :: rest := by
    cases kind <;>
      simp [PragmaKind.spelling] at decomposition <;>
      exact ⟨_, decomposition⟩
  rcases firstCharacter with ⟨rest, charactersEquation⟩
  have suffixLetter : SuffixAt file cursor ('n' :: rest) := by
    rw [← charactersEquation]
    exact suffix
  subst characters
  have matchedLetter : Lexer.pragmaMatch? ('n' :: rest) = some kind := by
    rw [← charactersEquation]
    exact matched
  have letter : Lexer.isAsciiLetter 'n' = true := by decide
  refine ⟨self, ?_⟩
  intro other recognized
  rcases candidateAt_of_letter suffixLetter letter recognized with
    pragma | identifier
  · rcases pragma with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    rcases otherRecognized with
      ⟨otherKind, otherSpelling, otherTokenEquation⟩
    have otherMatch := pragmaMatch_complete suffixLetter otherSpelling
    rw [matchedLetter] at otherMatch
    have kindEquation : otherKind = kind := (Option.some.inj otherMatch).symm
    subst otherKind
    have otherEndEquation :
        otherEnd = cursor + kind.spelling.utf8ByteSize :=
      sourceTextAt_endByte otherSpelling.1
    subst otherEnd
    rw [otherTokenEquation]
    left
    rfl
  · rcases identifier with
      ⟨otherEnd, otherToken, rfl, otherRecognized⟩
    have bound := identifierToken_end_le suffixLetter otherRecognized
    have takeEquation :
        Lexer.takeWhile Lexer.isIdentifierContinue ('n' :: rest) =
          ['n', 'o'] := by
      have restEquation := charactersEquation
      cases kind <;>
        simp [PragmaKind.spelling] at restEquation <;>
        subst rest <;> rfl
    have producedLong : 2 < kind.spelling.utf8ByteSize := by
      cases kind <;> decide
    right
    left
    rcases identifierToken_prefix suffixLetter otherRecognized with
      ⟨text, identifierKind, identifierRemaining, identifierDecomposition,
        identifierEndEquation, identifierValid, identifierClassified,
        identifierTokenEquation⟩
    rw [identifierTokenEquation]
    simp only [LexicalJudgment.Candidate.span,
      Lexer.tokenAt, Lexer.sourceSpan,
      LexicalJudgment.sourceSpan]
    rw [takeEquation] at bound
    have twoBytes : Lexer.byteSize ['n', 'o'] = 2 := by decide
    rw [twoBytes] at bound
    omega

private theorem identifierCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {character : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor (character :: rest))
    (letter : Lexer.isAsciiLetter character = true)
    (noPragma :
      Lexer.pragmaMatch? (character :: rest) = none) :
    let spellingCharacters :=
      Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest)
    let text := String.ofList spellingCharacters
    let endByte := cursor + Lexer.byteSize spellingCharacters
    let kind := Lexer.classifyIdentifier text
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .identifier (Lexer.tokenAt file cursor endByte kind)) := by
  dsimp only
  have self :
      LexicalJudgment.CandidateAt file pendingAssembly cursor
        (.token .identifier
          (Lexer.tokenAt file cursor
            (cursor + Lexer.byteSize
              (Lexer.takeWhile Lexer.isIdentifierContinue
                (character :: rest)))
            (Lexer.classifyIdentifier
              (String.ofList
                (Lexer.takeWhile Lexer.isIdentifierContinue
                  (character :: rest)))))) :=
    identifierCandidateAt suffix letter
  refine ⟨self, ?_⟩
  intro other recognized
  cases recognized with
  | lineComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | blockComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii
        recognized.1.1.1 (expected := '/') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      have quote := suffix.character_eq_of_byteAtAscii
        quoteAt (expected := '"') (by decide)
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, spelling, _⟩
      have matched := pragmaMatch_complete suffix spelling
      rw [noPragma] at matched
      contradiction
  | identifier endByte token recognized =>
      have bound := identifierToken_end_le suffix recognized
      by_cases sameEnd : endByte = cursor + Lexer.byteSize
          (Lexer.takeWhile Lexer.isIdentifierContinue (character :: rest))
      · have tokenEquation := identifierToken_eq_executor
          suffix recognized sameEnd
        left
        rw [tokenEquation]
      · right
        left
        rcases identifierToken_prefix suffix recognized with
          ⟨text, kind, remaining, decomposition, endEquation,
            valid, classified, tokenEquation⟩
        rw [tokenEquation]
        simp only [LexicalJudgment.Candidate.span,
          Lexer.tokenAt, Lexer.sourceSpan,
          LexicalJudgment.sourceSpan]
        omega
  | decimal endByte token recognized =>
      rcases recognized with
        ⟨digits, ⟨nonempty, allDigits⟩, spelling, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      cases digitsEquation : digits.toList with
      | nil => contradiction
      | cons first tail =>
          have firstEquation : character = first := by
            have heads := congrArg List.head? decomposition
            simp [digitsEquation] at heads
            exact heads
          subst first
          have digit := allDigits character (by simp [digitsEquation])
          have asciiLetter :=
            (isAsciiLetter_eq_true_iff character).mp letter
          unfold LexicalJudgment.AsciiDigit at digit
          unfold LexicalJudgment.AsciiLetter at asciiLetter
          rcases asciiLetter with upper | lower
          · change '0'.val ≤ character.val ∧
              character.val ≤ '9'.val at digit
            change 'A'.val ≤ character.val ∧
              character.val ≤ 'Z'.val at upper
            have impossible : ¬ 'A'.val ≤ '9'.val := by decide
            exact False.elim
              (impossible (Nat.le_trans upper.1 digit.2))
          · change '0'.val ≤ character.val ∧
              character.val ≤ '9'.val at digit
            change 'a'.val ≤ character.val ∧
              character.val ≤ 'z'.val at lower
            have impossible : ¬ 'a'.val ≤ '9'.val := by decide
            exact False.elim
              (impossible (Nat.le_trans lower.1 digit.2))
  | hexadecimal endByte token recognized =>
      rcases recognized with ⟨digits, _, spelling, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      have zero : character = '0' := by
        simpa using congrArg List.head? decomposition
      subst character
      simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
        Lexer.isAsciiUpper] at letter
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨writtenSymbol, spelling, _, _, _⟩
      rcases suffix.sourceTextDecomposition spelling with
        ⟨remaining, decomposition, _⟩
      cases writtenSymbol <;>
        simp [Symbol.spelling] at decomposition <;>
        rcases decomposition with ⟨rfl, _⟩ <;>
        simp [Lexer.isAsciiLetter, Lexer.isAsciiLower,
          Lexer.isAsciiUpper] at letter

private theorem uint8OfNat_ne_lineFeed_of_range
    (value : Nat)
    (lowerBound : 128 ≤ value)
    (upperBound : value < 256) :
    UInt8.ofNat value ≠ 10 := by
  intro equation
  have values := congrArg UInt8.toNat equation
  change value % 2 ^ 8 = 10 at values
  rw [show 2 ^ 8 = 256 by decide,
    Nat.mod_eq_of_lt upperBound] at values
  omega

private theorem utf8EncodeChar_contains_lineFeed_iff
    (character : Char) :
    (10 : UInt8) ∈ String.utf8EncodeChar character ↔
      character = '\n' := by
  constructor
  · intro contains
    simp only [String.utf8EncodeChar] at contains
    split at contains
    · rename_i ascii
      simp only [List.mem_singleton] at contains
      have values := congrArg UInt8.toNat contains
      change 10 = character.val.toNat % 2 ^ 8 at values
      rw [show 2 ^ 8 = 256 by decide,
        Nat.mod_eq_of_lt (by omega)] at values
      apply Char.toNat_inj.mp
      change character.val.toNat = 10
      omega
    · split at contains
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
        rcases contains with leading | continuation
        · exact False.elim
            (uint8OfNat_ne_lineFeed_of_range
              (character.val.toNat / 64 % 32 + 192)
              (by omega)
              (by
                have bound := Nat.mod_lt
                  (character.val.toNat / 64) (by omega : 0 < 32)
                omega)
              leading.symm)
        · exact False.elim
            (uint8OfNat_ne_lineFeed_of_range
              (character.val.toNat % 64 + 128)
              (by omega)
              (by
                have bound := Nat.mod_lt character.val.toNat
                  (by omega : 0 < 64)
                omega)
              continuation.symm)
      · split at contains
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
          rcases contains with leading | middle | trailing
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 4096 % 16 + 224)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 4096) (by omega : 0 < 16)
                  omega)
                leading.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 64 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 64) (by omega : 0 < 64)
                  omega)
                middle.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt character.val.toNat
                    (by omega : 0 < 64)
                  omega)
                trailing.symm)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at contains
          rcases contains with leading | second | third | trailing
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 262144 % 8 + 240)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 262144) (by omega : 0 < 8)
                  omega)
                leading.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 4096 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 4096) (by omega : 0 < 64)
                  omega)
                second.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat / 64 % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt
                    (character.val.toNat / 64) (by omega : 0 < 64)
                  omega)
                third.symm)
          · exact False.elim
              (uint8OfNat_ne_lineFeed_of_range
                (character.val.toNat % 64 + 128)
                (by omega)
                (by
                  have bound := Nat.mod_lt character.val.toNat
                    (by omega : 0 < 64)
                  omega)
                trailing.symm)
  · rintro rfl
    decide

private theorem utf8EncodedCharacters_do_not_contain_lineFeed
    (characters : List Char)
    (noLineFeed : characters.all (· != '\n') = true) :
    (10 : UInt8) ∉
      (String.ofList characters).toByteArray.data.toList := by
  induction characters with
  | nil => simp
  | cons character rest inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at noLineFeed
      have characterNotLineFeed : character ≠ '\n' := by
        simpa using noLineFeed.1
      have characterBytesDoNotContain :
          (10 : UInt8) ∉ String.utf8EncodeChar character := by
        intro contains
        exact characterNotLineFeed
          ((utf8EncodeChar_contains_lineFeed_iff character).mp contains)
      change (10 : UInt8) ∉
        (List.utf8Encode (character :: rest)).data.toList
      rw [List.utf8Encode_cons, ByteArray.data_append,
        Array.toList_append, List.mem_append, not_or]
      refine ⟨?_, inductionHypothesis noLineFeed.2⟩
      simpa [List.utf8Encode] using characterBytesDoNotContain

private theorem byteAt_not_of_sourceSlice_no_member
    {file : WorkspaceFile}
    {startByte endByte cursor : Nat}
    {characters : List Char}
    (range : LexicalJudgment.SourceRange file startByte endByte)
    (slice :
      file.content.toByteArray.extract startByte endByte =
        (String.ofList characters).toByteArray)
    (noLineFeed :
      (10 : UInt8) ∉
        (String.ofList characters).toByteArray.data.toList)
    (lower : startByte ≤ cursor)
    (upper : cursor < endByte) :
    ¬ LexicalJudgment.ByteAt file cursor 10 := by
  intro byte
  have extractedLookup :
      (file.content.toByteArray.extract startByte endByte).data[
        cursor - startByte]? = some 10 := by
    rw [ByteArray.data_extract, Array.getElem?_extract,
      ByteArray.size_data, String.size_toByteArray,
      Nat.min_eq_left range.2.1, if_pos (by omega)]
    simpa [LexicalJudgment.ByteAt, LexicalJudgment.byteAt,
      show startByte + (cursor - startByte) = cursor by omega] using byte
  rw [slice] at extractedLookup
  rcases Array.getElem?_eq_some_iff.mp extractedLookup with
    ⟨indexBound, elementEquation⟩
  apply noLineFeed
  rw [← elementEquation]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem indexBound)

private def LineScanSpec
    (cursor : Nat)
    (characters : List Char)
    (result : Lexer.LineScanResult) : Prop :=
  ∃ consumed remaining,
    characters = consumed ++ remaining ∧
      result.endByte = cursor + Lexer.byteSize consumed ∧
      result.consumedCharacters = consumed.length ∧
      consumed.all (· != '\n') = true ∧
      (remaining = [] ∨ ∃ tail, remaining = '\n' :: tail)

private theorem scanLineComment_certified
    (cursor : Nat)
    (characters : List Char) :
    LineScanSpec cursor characters
      (Lexer.scanLineComment cursor characters) := by
  induction cursor, characters using Lexer.scanLineComment.induct with
  | case1 cursor =>
      refine ⟨[], [], rfl, ?_, ?_, by simp, Or.inl rfl⟩
      · simp [Lexer.scanLineComment.eq_1, Lexer.byteSize]
      · simp [Lexer.scanLineComment.eq_1]
  | case2 cursor tail =>
      refine ⟨[], '\n' :: tail, rfl, ?_, ?_, by simp,
        Or.inr ⟨tail, rfl⟩⟩
      · simp [Lexer.scanLineComment.eq_2, Lexer.byteSize]
      · simp [Lexer.scanLineComment.eq_2]
  | case3 cursor character rest notLineFeed inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨consumed, remaining, decomposition, endEquation,
          consumedEquation, noLineFeeds, boundary⟩
      refine ⟨character :: consumed, remaining, ?_, ?_, ?_, ?_, boundary⟩
      · simp [decomposition]
      · rw [Lexer.scanLineComment.eq_3 cursor character rest notLineFeed,
          endEquation, byteSize_cons]
        omega
      · rw [Lexer.scanLineComment.eq_3 cursor character rest notLineFeed,
          consumedEquation]
        simp
      · rw [List.all_cons, Bool.and_eq_true]
        exact ⟨by simpa using notLineFeed, noLineFeeds⟩

private theorem lineCommentRecognized
    {file : WorkspaceFile}
    {cursor : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '/' :: body)) :
    let scanned := Lexer.scanLineComment (cursor + 2) body
    LexicalJudgment.LineCommentAt file cursor scanned.endByte
      (Lexer.commentAt file cursor scanned.endByte .line) := by
  dsimp only
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  rcases scanLineComment_certified (cursor + 2) body with
    ⟨consumed, remaining, decomposition, endEquation,
      consumedEquation, noLineFeeds, boundary⟩
  have fullDecomposition :
      '/' :: '/' :: body =
        ('/' :: '/' :: consumed) ++ remaining := by
    simp [decomposition]
  have prefixSize :
      Lexer.byteSize ('/' :: '/' :: consumed) =
        2 + Lexer.byteSize consumed := by
    rw [byteSize_cons, byteSize_cons]
    have slashSize : '/'.utf8Size = 1 := by decide
    omega
  have rangeRaw := suffix.sourceRange fullDecomposition
  have range :
      LexicalJudgment.SourceRange file cursor
        (Lexer.scanLineComment (cursor + 2) body).endByte := by
    rw [prefixSize] at rangeRaw
    have normalized : cursor + (2 + Lexer.byteSize consumed) =
        cursor + 2 + Lexer.byteSize consumed := by omega
    rw [normalized, ← endEquation] at rangeRaw
    exact rangeRaw
  have sliceRaw := suffix.sourceSlice fullDecomposition
  have slice :
      file.content.toByteArray.extract cursor
        (Lexer.scanLineComment (cursor + 2) body).endByte =
        (String.ofList ('/' :: '/' :: consumed)).toByteArray := by
    rw [prefixSize] at sliceRaw
    have normalized : cursor + (2 + Lexer.byteSize consumed) =
        cursor + 2 + Lexer.byteSize consumed := by omega
    rw [normalized, ← endEquation] at sliceRaw
    exact sliceRaw
  have prefixNoLineFeed :
      ('/' :: '/' :: consumed).all (· != '\n') = true := by
    simpa using noLineFeeds
  have noLineFeedBytes :=
    utf8EncodedCharacters_do_not_contain_lineFeed
      ('/' :: '/' :: consumed) prefixNoLineFeed
  have nextSuffix :
      SuffixAt file (Lexer.scanLineComment (cursor + 2) body).endByte
        remaining := by
    apply suffix.advance fullDecomposition
    rw [prefixSize, endEquation]
    omega
  have endpoint :
      (Lexer.scanLineComment (cursor + 2) body).endByte =
          file.content.utf8ByteSize ∨
        LexicalJudgment.ByteAt file
          (Lexer.scanLineComment (cursor + 2) body).endByte 10 := by
    rcases boundary with atEnd | atLineFeed
    · left
      subst remaining
      have size := nextSuffix.remainingByteSize
      simpa [Lexer.byteSize] using size.symm
    · rcases atLineFeed with ⟨tail, rfl⟩
      right
      simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
        nextSuffix.byteAtFirst
  refine ⟨?_, ?_⟩
  · refine ⟨?_, range, ?_, ?_, endpoint⟩
    · simpa using suffix.bytePairAtAscii
        (first := '/') (second := '/')
        (by decide) (by decide) (by decide)
    · rw [endEquation]
      omega
    · intro interior lower upper
      exact byteAt_not_of_sourceSlice_no_member range slice
        noLineFeedBytes (by omega) upper
  · rfl

private theorem lineCommentCandidateAt
    {file : WorkspaceFile}
    {cursor : Nat}
    {body : List Char}
    {pendingAssembly : Bool}
    (suffix : SuffixAt file cursor ('/' :: '/' :: body)) :
    let scanned := Lexer.scanLineComment (cursor + 2) body
    LexicalJudgment.CandidateAt file pendingAssembly cursor
      (.comment (Lexer.commentAt file cursor scanned.endByte .line)) := by
  dsimp only
  exact LexicalJudgment.CandidateAt.lineComment _ _
    (lineCommentRecognized suffix)

private theorem lineCommentSpan_end_unique
    {file : WorkspaceFile}
    {startByte firstEnd secondEnd : Nat}
    (first :
      LexicalJudgment.LineCommentSpanAt file startByte firstEnd)
    (second :
      LexicalJudgment.LineCommentSpanAt file startByte secondEnd) :
    firstEnd = secondEnd := by
  rcases first with
    ⟨firstOpener, firstRange, firstLower, firstInterior, firstBoundary⟩
  rcases second with
    ⟨secondOpener, secondRange, secondLower, secondInterior,
      secondBoundary⟩
  apply Nat.le_antisymm
  · by_cases ordered : firstEnd ≤ secondEnd
    · exact ordered
    · exfalso
      have secondBeforeFirst : secondEnd < firstEnd := by omega
      rcases secondBoundary with secondAtEnd | secondLineFeed
      · rw [secondAtEnd] at secondBeforeFirst
        have firstBound := firstRange.2.1
        omega
      · exact False.elim
          (firstInterior secondEnd secondLower secondBeforeFirst
            secondLineFeed)
  · by_cases ordered : secondEnd ≤ firstEnd
    · exact ordered
    · exfalso
      have firstBeforeSecond : firstEnd < secondEnd := by omega
      rcases firstBoundary with firstAtEnd | firstLineFeed
      · rw [firstAtEnd] at firstBeforeSecond
        have secondBound := secondRange.2.1
        omega
      · exact False.elim
          (secondInterior firstEnd firstLower firstBeforeSecond
            firstLineFeed)

private theorem candidateAt_of_lineStart
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor ('/' :: '/' :: body))
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    ∃ endByte comment,
      candidate = .comment comment ∧
        LexicalJudgment.LineCommentAt file cursor endByte comment := by
  cases recognized with
  | lineComment endByte comment recognized =>
      exact ⟨endByte, comment, rfl, recognized⟩
  | blockComment endByte comment recognized =>
      rcases suffix.pair_eq_of_bytePairAscii
          (first := '/') (second := '*') recognized.1.1
          (by decide) (by decide) (by decide) with
        ⟨tail, firstEquation, restEquation⟩
      simp at restEquation
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      have quote := suffix.character_eq_of_byteAtAscii quoteAt
        (expected := '"') (by decide)
      contradiction
  | pragmaName endByte token recognized =>
      have first := pragmaToken_first_n suffix recognized
      contradiction
  | identifier endByte token recognized =>
      have letter := identifierToken_firstLetter suffix recognized
      have notLetter : ¬ LexicalJudgment.AsciiLetter '/' := by
        simp [LexicalJudgment.AsciiLetter]
      contradiction
  | decimal endByte token recognized =>
      have digit := decimalToken_firstDigit suffix recognized
      have notDigit : ¬ LexicalJudgment.AsciiDigit '/' := by
        simp [LexicalJudgment.AsciiDigit]
      contradiction
  | hexadecimal endByte token recognized =>
      have zero := hexadecimalToken_first_zero suffix recognized
      contradiction
  | symbol endByte symbol token recognized kind =>
      rcases symbolToken_data suffix recognized kind with
        ⟨remaining, decomposition, sourceText, endEquation,
          slashGuard, assemblyGuard, tokenEquation⟩
      have symbolEquation : symbol = .slash := by
        cases symbol <;> simp_all [Symbol.spelling]
      subst symbol
      have linePair :
          LexicalJudgment.BytePairAt file cursor 47 47 := by
        simpa using suffix.bytePairAtAscii
          (first := '/') (second := '/')
          (by decide) (by decide) (by decide)
      exact False.elim ((slashGuard rfl).1 linePair)

private theorem lineCommentCandidateWins
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '/' :: body)) :
    let scanned := Lexer.scanLineComment (cursor + 2) body
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.comment (Lexer.commentAt file cursor scanned.endByte .line)) := by
  dsimp only
  have selfRecognized := lineCommentRecognized suffix
  refine ⟨LexicalJudgment.CandidateAt.lineComment _ _ selfRecognized, ?_⟩
  intro other recognized
  rcases candidateAt_of_lineStart suffix recognized with
    ⟨otherEnd, otherComment, rfl, otherRecognized⟩
  have endEquation := lineCommentSpan_end_unique
    selfRecognized.1 otherRecognized.1
  subst otherEnd
  rw [otherRecognized.2, selfRecognized.2]
  exact Or.inl rfl

private theorem slashStarBytePair
    {file : WorkspaceFile}
    {cursor : Nat}
    {remaining : List Char}
    (suffix : SuffixAt file cursor ('/' :: '*' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 47 42 := by
  simpa using suffix.bytePairAtAscii
    (first := '/') (second := '*')
    (by decide) (by decide) (by decide)

private theorem starSlashBytePair
    {file : WorkspaceFile}
    {cursor : Nat}
    {remaining : List Char}
    (suffix : SuffixAt file cursor ('*' :: '/' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 42 47 := by
  simpa using suffix.bytePairAtAscii
    (first := '*') (second := '/')
    (by decide) (by decide) (by decide)

private def BlockScanSpec
    (file : WorkspaceFile)
    (cursor depth : Nat)
    (characters : List Char) :
    Lexer.BlockScanResult → Prop
  | .closed endByte consumedCharacters _ =>
      ∃ beforeClose remaining closeCursor,
        characters = beforeClose ++ '*' :: '/' :: remaining ∧
          consumedCharacters = beforeClose.length + 2 ∧
          closeCursor = cursor + Lexer.byteSize beforeClose ∧
          endByte = closeCursor + 2 ∧
          LexicalJudgment.BlockCommentRun file depth cursor 1 closeCursor ∧
          LexicalJudgment.BytePairAt file closeCursor 42 47
  | .unterminated _ =>
      ∃ finalDepth,
        0 < finalDepth ∧
          LexicalJudgment.BlockCommentRun file depth cursor finalDepth
            file.content.utf8ByteSize

private theorem scanBlockComment_certified
    (file : WorkspaceFile)
    (cursor depth : Nat)
    (characters : List Char) :
    ∀ (_ : SuffixAt file cursor characters),
      0 < depth →
        BlockScanSpec file cursor depth characters
          (Lexer.scanBlockComment cursor depth characters) := by
  induction cursor, depth, characters using Lexer.scanBlockComment.induct with
  | case1 cursor depth =>
      intro suffix positive
      simp only [Lexer.scanBlockComment.eq_1, BlockScanSpec]
      have atEnd := suffix.remainingByteSize
      simp [Lexer.byteSize] at atEnd
      refine ⟨depth, positive, ?_⟩
      rw [atEnd]
      exact .refl depth cursor
  | case2 cursor depth rest endByte consumed units equation
      inductionHypothesis =>
      intro suffix positive
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis nextSuffix (by omega)
      rw [equation] at certified
      rcases certified with
        ⟨beforeClose, remaining, closeCursor, decomposition,
          consumedEquation, closeEquation, endEquation, run, closer⟩
      simp only [Lexer.scanBlockComment.eq_2, equation, BlockScanSpec]
      refine ⟨'/' :: '*' :: beforeClose, remaining, closeCursor, ?_, ?_,
        ?_, endEquation, ?_, closer⟩
      · simp [decomposition]
      · simp [consumedEquation]
      · rw [closeEquation, byteSize_cons, byteSize_cons]
        have slashSize : '/'.utf8Size = 1 := by decide
        have starSize : '*'.utf8Size = 1 := by decide
        omega
      · exact .nestedOpen depth cursor 1 closeCursor positive
          (slashStarBytePair suffix) run
  | case3 cursor depth rest units equation inductionHypothesis =>
      intro suffix positive
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis nextSuffix (by omega)
      rw [equation] at certified
      rcases certified with ⟨finalDepth, finalPositive, run⟩
      simp only [Lexer.scanBlockComment.eq_2, equation, BlockScanSpec]
      exact ⟨finalDepth, finalPositive,
        .nestedOpen depth cursor finalDepth file.content.utf8ByteSize
          positive (slashStarBytePair suffix) run⟩
  | case4 cursor tail =>
      intro suffix _
      simp only [Lexer.scanBlockComment.eq_3, BlockScanSpec]
      refine ⟨[], tail, cursor, by simp, by simp, ?_, by omega,
        .refl 1 cursor, starSlashBytePair suffix⟩
      simp [Lexer.byteSize]
  | case5 cursor depth rest endByte consumed units equation
      inductionHypothesis =>
      intro suffix _
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis nextSuffix (by omega)
      rw [equation] at certified
      rcases certified with
        ⟨beforeClose, remaining, closeCursor, decomposition,
          consumedEquation, closeEquation, endEquation, run, closer⟩
      simp only [Lexer.scanBlockComment.eq_4, equation, BlockScanSpec]
      refine ⟨'*' :: '/' :: beforeClose, remaining, closeCursor, ?_, ?_,
        ?_, endEquation, ?_, closer⟩
      · simp [decomposition]
      · simp [consumedEquation]
      · rw [closeEquation, byteSize_cons, byteSize_cons]
        have starSize : '*'.utf8Size = 1 := by decide
        have slashSize : '/'.utf8Size = 1 := by decide
        omega
      · exact .nestedClose (depth + 2) cursor 1 closeCursor (by omega)
          (starSlashBytePair suffix) run
  | case6 cursor depth rest units equation inductionHypothesis =>
      intro suffix _
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis nextSuffix (by omega)
      rw [equation] at certified
      rcases certified with ⟨finalDepth, finalPositive, run⟩
      simp only [Lexer.scanBlockComment.eq_4, equation, BlockScanSpec]
      exact ⟨finalDepth, finalPositive,
        .nestedClose (depth + 2) cursor finalDepth
          file.content.utf8ByteSize (by omega)
          (starSlashBytePair suffix) run⟩
  | case7 cursor depth character rest notOpen notOuterClose
      notNestedClose endByte consumed units equation inductionHypothesis =>
      intro suffix positive
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis nextSuffix positive
      rw [equation] at certified
      rcases certified with
        ⟨beforeClose, remaining, closeCursor, decomposition,
          consumedEquation, closeEquation, endEquation, run, closer⟩
      have notOpener :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro opener
        rcases suffix.slashStar_of_bytePair opener with
          ⟨tail, characterEquation, restEquation⟩
        exact notOpen tail characterEquation restEquation
      have notCloser :
          ¬ LexicalJudgment.BytePairAt file cursor 42 47 := by
        intro closerAtCursor
        rcases suffix.starSlash_of_bytePair closerAtCursor with
          ⟨tail, characterEquation, restEquation⟩
        cases depth with
        | zero => omega
        | succ predecessor =>
            cases predecessor with
            | zero =>
                exact notOuterClose tail rfl characterEquation restEquation
            | succ nested =>
                exact notNestedClose nested tail rfl characterEquation
                  restEquation
      simp only [Lexer.scanBlockComment.eq_5 _ _ _ _ notOpen
        notOuterClose notNestedClose, equation, BlockScanSpec]
      refine ⟨character :: beforeClose, remaining, closeCursor, ?_, ?_,
        ?_, endEquation, ?_, closer⟩
      · simp [decomposition]
      · simp [consumedEquation]
      · rw [closeEquation, byteSize_cons]
        omega
      · exact .scalar depth cursor (cursor + character.utf8Size) 1
          closeCursor character positive notOpener notCloser
          suffix.scalarAt run
  | case8 cursor depth character rest notOpen notOuterClose
      notNestedClose units equation inductionHypothesis =>
      intro suffix positive
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis nextSuffix positive
      rw [equation] at certified
      rcases certified with ⟨finalDepth, finalPositive, run⟩
      have notOpener :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro opener
        rcases suffix.slashStar_of_bytePair opener with
          ⟨tail, characterEquation, restEquation⟩
        exact notOpen tail characterEquation restEquation
      have notCloser :
          ¬ LexicalJudgment.BytePairAt file cursor 42 47 := by
        intro closerAtCursor
        rcases suffix.starSlash_of_bytePair closerAtCursor with
          ⟨tail, characterEquation, restEquation⟩
        cases depth with
        | zero => omega
        | succ predecessor =>
            cases predecessor with
            | zero =>
                exact notOuterClose tail rfl characterEquation restEquation
            | succ nested =>
                exact notNestedClose nested tail rfl characterEquation
                  restEquation
      simp only [Lexer.scanBlockComment.eq_5 _ _ _ _ notOpen
        notOuterClose notNestedClose, equation, BlockScanSpec]
      exact ⟨finalDepth, finalPositive,
        .scalar depth cursor (cursor + character.utf8Size) finalDepth
          file.content.utf8ByteSize character positive notOpener notCloser
          suffix.scalarAt run⟩

private theorem blockCommentRecognized
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '*' :: body))
    (scanned :
      Lexer.scanBlockComment (cursor + 2) 1 body =
        .closed endByte consumedCharacters units) :
    LexicalJudgment.BlockCommentAt file cursor endByte
      (Lexer.commentAt file cursor endByte .block) := by
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  have certified := scanBlockComment_certified file (cursor + 2) 1 body
    afterOpener (by omega)
  rw [scanned] at certified
  rcases certified with
    ⟨beforeClose, remaining, closeCursor, decomposition,
      consumedEquation, closeEquation, endEquation, run, closer⟩
  let consumed : List Char :=
    ('/' :: '*' :: beforeClose) ++ ['*', '/']
  have fullDecomposition :
      '/' :: '*' :: body = consumed ++ remaining := by
    dsimp [consumed]
    simp [decomposition, List.append_assoc]
  have delimiterPrefixSize :
      Lexer.byteSize ('/' :: '*' :: beforeClose) =
        2 + Lexer.byteSize beforeClose := by
    rw [byteSize_cons, byteSize_cons]
    have slashSize : '/'.utf8Size = 1 := by decide
    have starSize : '*'.utf8Size = 1 := by decide
    omega
  have closerSize : Lexer.byteSize ['*', '/'] = 2 := by decide
  have consumedSize :
      Lexer.byteSize consumed = 2 + Lexer.byteSize beforeClose + 2 := by
    dsimp [consumed]
    rw [byteSize_cons, byteSize_cons, byteSize_append, closerSize]
    have slashSize : '/'.utf8Size = 1 := by decide
    have starSize : '*'.utf8Size = 1 := by decide
    omega
  have cursorEnd : cursor + Lexer.byteSize consumed = endByte := by
    rw [consumedSize, endEquation, closeEquation]
    omega
  have rangeRaw := suffix.sourceRange fullDecomposition
  rw [cursorEnd] at rangeRaw
  refine ⟨?_, rfl⟩
  refine ⟨?_, closeCursor, run, closer, endEquation, rangeRaw⟩
  simpa using suffix.bytePairAtAscii
    (first := '/') (second := '*')
    (by decide) (by decide) (by decide)

private theorem unterminatedBlockCommentRecognized
    {file : WorkspaceFile}
    {cursor units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '*' :: body))
    (scanned :
      Lexer.scanBlockComment (cursor + 2) 1 body =
        .unterminated units) :
    LexicalJudgment.UnterminatedBlockCommentAt file cursor := by
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  have certified := scanBlockComment_certified file (cursor + 2) 1 body
    afterOpener (by omega)
  rw [scanned] at certified
  rcases certified with ⟨finalDepth, positive, run⟩
  refine ⟨?_, finalDepth, positive, run⟩
  simpa using suffix.bytePairAtAscii
    (first := '/') (second := '*')
    (by decide) (by decide) (by decide)

private theorem blockCommentRun_to_scanClosed
    {file : WorkspaceFile}
    {depth cursor finalDepth closeCursor : Nat}
    {characters : List Char}
    (run :
      LexicalJudgment.BlockCommentRun file depth cursor finalDepth closeCursor)
    (finalDepthOne : finalDepth = 1)
    (suffix : SuffixAt file cursor characters)
    (closer : LexicalJudgment.BytePairAt file closeCursor 42 47) :
    ∃ consumedCharacters units,
      Lexer.scanBlockComment cursor depth characters =
        .closed (closeCursor + 2) consumedCharacters units := by
  induction run generalizing characters with
  | refl depth cursor =>
      subst depth
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '*') (second := '/') closer
          (by decide) (by decide) (by decide) with
        ⟨tail, decomposition⟩
      subst characters
      exact ⟨2, 1, Lexer.scanBlockComment.eq_3 cursor tail⟩
  | nestedOpen depth cursor finalDepth endByte positive opener tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '/') (second := '*') opener
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis finalDepthOne nextSuffix closer with
        ⟨consumed, units, scanned⟩
      refine ⟨consumed + 2, units + 1, ?_⟩
      rw [Lexer.scanBlockComment.eq_2, scanned]
  | nestedClose depth cursor finalDepth endByte nested closerAtCursor tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '*') (second := '/') closerAtCursor
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      cases depth with
      | zero => omega
      | succ predecessor =>
          cases predecessor with
          | zero => omega
          | succ nestedDepth =>
              have nextSuffix := suffix.advanceTwoAscii
                (by decide) (by decide)
              rcases inductionHypothesis finalDepthOne nextSuffix closer with
                ⟨consumed, units, scanned⟩
              have recursiveDepth :
                  nestedDepth + 1 + 1 - 1 = nestedDepth + 1 := by omega
              rw [recursiveDepth] at scanned
              refine ⟨consumed + 2, units + 1, ?_⟩
              rw [Lexer.scanBlockComment.eq_4, scanned]
  | scalar depth cursor next finalDepth endByte character positive
      notOpener notCloser scalar tail inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      subst characters
      subst next
      have notOpenPattern :
          ∀ trailing,
            character = '/' → remaining = '*' :: trailing → False := by
        intro trailing characterEquation remainingEquation
        subst character
        subst remaining
        exact notOpener (slashStarBytePair suffix)
      have notOuterClosePattern :
          ∀ trailing,
            depth = 1 → character = '*' →
              remaining = '/' :: trailing → False := by
        intro trailing depthEquation characterEquation remainingEquation
        subst character
        subst remaining
        exact notCloser (starSlashBytePair suffix)
      have notNestedClosePattern :
          ∀ nestedDepth trailing,
            depth = nestedDepth + 2 → character = '*' →
              remaining = '/' :: trailing → False := by
        intro nestedDepth trailing depthEquation characterEquation
          remainingEquation
        subst character
        subst remaining
        exact notCloser (starSlashBytePair suffix)
      rcases inductionHypothesis finalDepthOne nextSuffix closer with
        ⟨consumed, units, scanned⟩
      refine ⟨consumed + 1, units + 1, ?_⟩
      rw [Lexer.scanBlockComment.eq_5 _ _ _ _ notOpenPattern
        notOuterClosePattern notNestedClosePattern, scanned]

private theorem blockCommentSpan_end_unique
    {file : WorkspaceFile}
    {startByte firstEnd secondEnd : Nat}
    {body : List Char}
    (suffix : SuffixAt file startByte ('/' :: '*' :: body))
    (first :
      LexicalJudgment.BlockCommentSpanAt file startByte firstEnd)
    (second :
      LexicalJudgment.BlockCommentSpanAt file startByte secondEnd) :
    firstEnd = secondEnd := by
  rcases first with
    ⟨firstOpener, firstClose, firstRun, firstCloser,
      firstEndEquation, firstRange⟩
  rcases second with
    ⟨secondOpener, secondClose, secondRun, secondCloser,
      secondEndEquation, secondRange⟩
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  rcases blockCommentRun_to_scanClosed firstRun rfl afterOpener firstCloser with
    ⟨firstConsumed, firstUnits, firstScan⟩
  rcases blockCommentRun_to_scanClosed secondRun rfl afterOpener secondCloser with
    ⟨secondConsumed, secondUnits, secondScan⟩
  rw [firstScan] at secondScan
  cases secondScan
  omega

private theorem candidateAt_of_blockStart
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor ('/' :: '*' :: body))
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    ∃ endByte comment,
      candidate = .comment comment ∧
        LexicalJudgment.BlockCommentAt file cursor endByte comment := by
  cases recognized with
  | lineComment endByte comment recognized =>
      rcases suffix.pair_eq_of_bytePairAscii
          (first := '/') (second := '/') recognized.1.1
          (by decide) (by decide) (by decide) with
        ⟨tail, firstEquation, restEquation⟩
      simp at restEquation
  | blockComment endByte comment recognized =>
      exact ⟨endByte, comment, rfl, recognized⟩
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quoteAt, contents, sourceText, tokenEquation⟩
      have quote := suffix.character_eq_of_byteAtAscii quoteAt
        (expected := '"') (by decide)
      contradiction
  | pragmaName endByte token recognized =>
      have first := pragmaToken_first_n suffix recognized
      contradiction
  | identifier endByte token recognized =>
      have letter := identifierToken_firstLetter suffix recognized
      have notLetter : ¬ LexicalJudgment.AsciiLetter '/' := by
        simp [LexicalJudgment.AsciiLetter]
      contradiction
  | decimal endByte token recognized =>
      have digit := decimalToken_firstDigit suffix recognized
      have notDigit : ¬ LexicalJudgment.AsciiDigit '/' := by
        simp [LexicalJudgment.AsciiDigit]
      contradiction
  | hexadecimal endByte token recognized =>
      have zero := hexadecimalToken_first_zero suffix recognized
      contradiction
  | symbol endByte symbol token recognized kind =>
      rcases symbolToken_data suffix recognized kind with
        ⟨remaining, decomposition, sourceText, endEquation,
          slashGuard, assemblyGuard, tokenEquation⟩
      have symbolEquation : symbol = .slash := by
        cases symbol <;> simp_all [Symbol.spelling]
      subst symbol
      have blockPair :
          LexicalJudgment.BytePairAt file cursor 47 42 := by
        simpa using suffix.bytePairAtAscii
          (first := '/') (second := '*')
          (by decide) (by decide) (by decide)
      exact False.elim ((slashGuard rfl).2 blockPair)

private theorem blockCommentCandidateWins
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '*' :: body))
    (scanned :
      Lexer.scanBlockComment (cursor + 2) 1 body =
        .closed endByte consumedCharacters units) :
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.comment (Lexer.commentAt file cursor endByte .block)) := by
  have selfRecognized := blockCommentRecognized suffix scanned
  refine ⟨LexicalJudgment.CandidateAt.blockComment _ _ selfRecognized, ?_⟩
  intro other recognized
  rcases candidateAt_of_blockStart suffix recognized with
    ⟨otherEnd, otherComment, rfl, otherRecognized⟩
  have endEquation := blockCommentSpan_end_unique suffix
    selfRecognized.1 otherRecognized.1
  subst otherEnd
  rw [otherRecognized.2, selfRecognized.2]
  exact Or.inl rfl

private theorem decodedEscape_cases
    (escaped decoded : Char)
    (equation :
      (match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none) = some decoded) :
    (escaped = 'n' ∧ decoded = '\n') ∨
      (escaped = 't' ∧ decoded = '\t') ∨
      (escaped = '"' ∧ decoded = '"') ∨
      (escaped = '\\' ∧ decoded = '\\') := by
  by_cases newline : escaped = 'n'
  · subst escaped
    simp at equation
    exact Or.inl ⟨rfl, equation.symm⟩
  by_cases tab : escaped = 't'
  · subst escaped
    simp at equation
    exact Or.inr (Or.inl ⟨rfl, equation.symm⟩)
  by_cases quote : escaped = '"'
  · subst escaped
    simp at equation
    exact Or.inr (Or.inr (Or.inl ⟨rfl, equation.symm⟩))
  by_cases backslash : escaped = '\\'
  · subst escaped
    simp at equation
    exact Or.inr (Or.inr (Or.inr ⟨rfl, equation.symm⟩))
  simp_all

private theorem invalidEscape_ne
    (escaped : Char)
    (equation :
      (match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none) = none) :
    escaped ≠ 'n' ∧ escaped ≠ 't' ∧
      escaped ≠ '"' ∧ escaped ≠ '\\' := by
  constructor
  · intro equals
    subst escaped
    simp at equation
  constructor
  · intro equals
    subst escaped
    simp at equation
  constructor
  · intro equals
    subst escaped
    simp at equation
  · intro equals
    subst escaped
    simp at equation

private theorem backslashNewlineBytePair
    {file : WorkspaceFile} {cursor : Nat} {remaining : List Char}
    (suffix : SuffixAt file cursor ('\\' :: 'n' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 92 110 := by
  simpa using suffix.bytePairAtAscii
    (first := '\\') (second := 'n')
    (by decide) (by decide) (by decide)

private theorem backslashTabBytePair
    {file : WorkspaceFile} {cursor : Nat} {remaining : List Char}
    (suffix : SuffixAt file cursor ('\\' :: 't' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 92 116 := by
  simpa using suffix.bytePairAtAscii
    (first := '\\') (second := 't')
    (by decide) (by decide) (by decide)

private theorem backslashQuoteBytePair
    {file : WorkspaceFile} {cursor : Nat} {remaining : List Char}
    (suffix : SuffixAt file cursor ('\\' :: '"' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 92 34 := by
  simpa using suffix.bytePairAtAscii
    (first := '\\') (second := '"')
    (by decide) (by decide) (by decide)

private theorem backslashBackslashBytePair
    {file : WorkspaceFile} {cursor : Nat} {remaining : List Char}
    (suffix : SuffixAt file cursor ('\\' :: '\\' :: remaining)) :
    LexicalJudgment.BytePairAt file cursor 92 92 := by
  simpa using suffix.bytePairAtAscii
    (first := '\\') (second := '\\')
    (by decide) (by decide) (by decide)

private theorem scanString_validEscape_equation
    (file : WorkspaceFile)
    (cursor : Nat)
    (escaped decoded : Char)
    (rest decodedRev : List Char)
    (decodedEquation :
      (match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none) = some decoded) :
    Lexer.scanString file cursor ('\\' :: escaped :: rest) decodedRev =
      match Lexer.scanString file (cursor + 1 + escaped.utf8Size) rest
          (decoded :: decodedRev) with
      | .closed endByte consumed value units =>
          .closed endByte (consumed + 2) value (units + 1)
      | .invalidEscape diagnostic units =>
          .invalidEscape diagnostic (units + 1)
      | .unterminated units => .unterminated (units + 1) := by
  rcases decodedEscape_cases escaped decoded decodedEquation with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Lexer.scanString.eq_4 file cursor decodedRev rest
  · exact Lexer.scanString.eq_5 file cursor decodedRev rest
  · exact Lexer.scanString.eq_6 file cursor decodedRev rest
  · exact Lexer.scanString.eq_7 file cursor decodedRev rest

private def StringScanSpec
    (file : WorkspaceFile)
    (cursor : Nat)
    (characters decodedRev : List Char) :
    Lexer.StringScanResult → Prop
  | .closed endByte consumedCharacters decoded _ =>
      ∃ rawContent remaining closeCursor decodedContent,
        characters = rawContent ++ '"' :: remaining ∧
          consumedCharacters = rawContent.length + 1 ∧
          closeCursor = cursor + Lexer.byteSize rawContent ∧
          endByte = closeCursor + 1 ∧
          LexicalJudgment.StringContents file cursor endByte decodedContent ∧
          decoded = String.ofList decodedRev.reverse ++ decodedContent
  | .invalidEscape diagnostic _ =>
      ∃ escapeStart escapeEnd character,
        LexicalJudgment.StringScanPrefix file cursor escapeStart ∧
          LexicalJudgment.InvalidStringEscapeAt file escapeStart escapeEnd
            character ∧
          diagnostic = .invalidStringEscape
            (LexicalJudgment.sourceSpan file escapeStart escapeEnd) character
  | .unterminated _ =>
      LexicalJudgment.StringScanPrefix file cursor
        file.content.utf8ByteSize

private theorem scanString_certified
    (file : WorkspaceFile)
    (cursor : Nat)
    (characters decodedRev : List Char) :
    ∀ (_ : SuffixAt file cursor characters),
      StringScanSpec file cursor characters decodedRev
        (Lexer.scanString file cursor characters decodedRev) := by
  induction cursor, characters, decodedRev using Lexer.scanString.induct file with
  | case1 cursor decodedRev =>
      intro suffix
      simp only [Lexer.scanString.eq_1, StringScanSpec]
      have atEnd := suffix.remainingByteSize
      simpa [Lexer.byteSize, atEnd] using
        (LexicalJudgment.StringScanPrefix.refl cursor)
  | case2 cursor tail decodedRev =>
      intro suffix
      simp only [Lexer.scanString.eq_2, StringScanSpec]
      refine ⟨[], tail, cursor, "", by simp, by simp, ?_, by omega,
        ?_, by simp⟩
      · simp [Lexer.byteSize]
      · exact .close cursor (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst)
  | case3 cursor decodedRev =>
      intro suffix
      simp only [Lexer.scanString.eq_3, StringScanSpec]
      refine ⟨cursor, cursor + 1, none,
        .refl cursor, ?_, ?_⟩
      · exact .endOfFile cursor (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst) (by
          have atEnd := suffix.remainingByteSize
          have backslashSize : '\\'.utf8Size = 1 := by decide
          rw [byteSize_cons, backslashSize] at atEnd
          simpa [Lexer.byteSize] using atEnd.symm)
      · simp [Lexer.sourceSpan, LexicalJudgment.sourceSpan]
  | case4 cursor escaped rest decodedRev decodedOption decodedNone =>
      intro suffix
      have nextSuffix := suffix.advanceOne
      have invalidEscape :
          LexicalJudgment.InvalidStringEscapeAt file cursor
            (cursor + 1 + escaped.utf8Size) (some escaped) := by
        apply LexicalJudgment.InvalidStringEscapeAt.unsupported
        · simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst
        · have backslashSize : '\\'.utf8Size = 1 := by decide
          rw [backslashSize] at nextSuffix
          exact nextSuffix.scalarAt
        · exact invalidEscape_ne escaped decodedNone
      rcases invalidEscape_ne escaped decodedNone with
        ⟨notNewline, notTab, notQuote, notBackslash⟩
      rw [Lexer.scanString.eq_8 file cursor decodedRev escaped rest
        notNewline notTab notQuote notBackslash]
      simp only [StringScanSpec]
      exact ⟨cursor, cursor + 1 + escaped.utf8Size, some escaped,
        .refl cursor, invalidEscape, by
          simp [Lexer.sourceSpan, LexicalJudgment.sourceSpan]⟩
  | case5 cursor escaped rest decodedRev next decodedOption decoded decodedEquation endByte
      consumed value units equation inductionHypothesis =>
      intro suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have nextSuffix := afterBackslash.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      rcases certified with
        ⟨rawContent, remaining, closeCursor, decodedTail,
          decomposition, consumedEquation, closeEquation, endEquation,
          contents, valueEquation⟩
      have decodedCase := decodedEscape_cases escaped decoded decodedEquation
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only [StringScanSpec]
      refine ⟨'\\' :: escaped :: rawContent, remaining, closeCursor,
        String.singleton decoded ++ decodedTail, ?_, ?_, ?_, endEquation,
        ?_, ?_⟩
      · simp [decomposition]
      · simp [consumedEquation]
      · rw [closeEquation, byteSize_cons, byteSize_cons]
        omega
      · rcases decodedCase with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .escapedNewline cursor endByte decodedTail
            (backslashNewlineBytePair suffix) contents
        · exact .escapedTab cursor endByte decodedTail
            (backslashTabBytePair suffix) contents
        · exact .escapedQuote cursor endByte decodedTail
            (backslashQuoteBytePair suffix) contents
        · exact .escapedBackslash cursor endByte decodedTail
            (backslashBackslashBytePair suffix) contents
      · rw [valueEquation, List.reverse_cons, String.ofList_append]
        rw [← String.singleton_eq_ofList, String.append_assoc]
  | case6 cursor escaped rest decodedRev next decodedOption decoded decodedEquation diagnostic
      units equation inductionHypothesis =>
      intro suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have nextSuffix := afterBackslash.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      rcases certified with
        ⟨escapeStart, escapeEnd, character, scanPrefix, invalid,
          diagnosticEquation⟩
      have decodedCase := decodedEscape_cases escaped decoded decodedEquation
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only [StringScanSpec]
      refine ⟨escapeStart, escapeEnd, character, ?_, invalid,
        diagnosticEquation⟩
      rcases decodedCase with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .escapedNewline cursor escapeStart
          (backslashNewlineBytePair suffix) scanPrefix
      · exact .escapedTab cursor escapeStart
          (backslashTabBytePair suffix) scanPrefix
      · exact .escapedQuote cursor escapeStart
          (backslashQuoteBytePair suffix) scanPrefix
      · exact .escapedBackslash cursor escapeStart
          (backslashBackslashBytePair suffix) scanPrefix
  | case7 cursor escaped rest decodedRev next decodedOption decoded decodedEquation units equation
      inductionHypothesis =>
      intro suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have nextSuffix := afterBackslash.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      have decodedCase := decodedEscape_cases escaped decoded decodedEquation
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only [StringScanSpec]
      rcases decodedCase with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .escapedNewline cursor file.content.utf8ByteSize
          (backslashNewlineBytePair suffix) certified
      · exact .escapedTab cursor file.content.utf8ByteSize
          (backslashTabBytePair suffix) certified
      · exact .escapedQuote cursor file.content.utf8ByteSize
          (backslashQuoteBytePair suffix) certified
      · exact .escapedBackslash cursor file.content.utf8ByteSize
          (backslashBackslashBytePair suffix) certified
  | case8 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash endByte consumed value units equation
      inductionHypothesis =>
      intro suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      rcases certified with
        ⟨rawContent, remaining, closeCursor, decodedTail,
          decomposition, consumedEquation, closeEquation, endEquation,
          contents, valueEquation⟩
      have characterNotBackslash : character ≠ '\\' := by
        intro equals
        subst character
        cases rest with
        | nil => exact notTrailingBackslash rfl rfl
        | cons escaped tail =>
            exact notEscapedBackslash escaped tail rfl rfl
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [StringScanSpec]
      refine ⟨character :: rawContent, remaining, closeCursor,
        String.singleton character ++ decodedTail, ?_, ?_, ?_, endEquation,
        ?_, ?_⟩
      · simp [decomposition]
      · simp [consumedEquation]
      · rw [closeEquation, byteSize_cons]
        omega
      · exact .scalar cursor (cursor + character.utf8Size) endByte
          character decodedTail suffix.scalarAt notQuote
          characterNotBackslash contents
      · rw [valueEquation, List.reverse_cons, String.ofList_append]
        rw [← String.singleton_eq_ofList, String.append_assoc]
  | case9 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash diagnostic units equation inductionHypothesis =>
      intro suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      rcases certified with
        ⟨escapeStart, escapeEnd, escaped, scanPrefix, invalid,
          diagnosticEquation⟩
      have characterNotBackslash : character ≠ '\\' := by
        intro equals
        subst character
        cases rest with
        | nil => exact notTrailingBackslash rfl rfl
        | cons next tail =>
            exact notEscapedBackslash next tail rfl rfl
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [StringScanSpec]
      exact ⟨escapeStart, escapeEnd, escaped,
        .scalar cursor (cursor + character.utf8Size) escapeStart character
          suffix.scalarAt notQuote characterNotBackslash scanPrefix,
        invalid, diagnosticEquation⟩
  | case10 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash units equation inductionHypothesis =>
      intro suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis nextSuffix
      rw [equation] at certified
      have characterNotBackslash : character ≠ '\\' := by
        intro equals
        subst character
        cases rest with
        | nil => exact notTrailingBackslash rfl rfl
        | cons escaped tail =>
            exact notEscapedBackslash escaped tail rfl rfl
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [StringScanSpec]
      exact .scalar cursor (cursor + character.utf8Size)
        file.content.utf8ByteSize character suffix.scalarAt notQuote
          characterNotBackslash certified

private theorem stringTokenRecognized
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {body : List Char}
    {decoded : String}
    (suffix : SuffixAt file cursor ('"' :: body))
    (scanned :
      Lexer.scanString file (cursor + 1) body [] =
        .closed endByte consumedCharacters decoded units) :
    let characters := '"' :: body
    let total := consumedCharacters + 1
    let spelling := String.ofList (characters.take total)
    LexicalJudgment.StringTokenAt file cursor endByte
      (Lexer.tokenAt file cursor endByte (.stringLiteral spelling decoded)) := by
  dsimp only
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  have certified := scanString_certified file (cursor + 1) body [] afterOpener
  rw [scanned] at certified
  rcases certified with
    ⟨rawContent, remaining, closeCursor, decodedContent,
      decomposition, consumedEquation, closeEquation, endEquation,
      contents, decodedEquation⟩
  have decodedValue : decoded = decodedContent := by
    simpa using decodedEquation
  subst decodedContent
  let consumed : List Char :=
    ('"' :: rawContent) ++ ['"']
  have fullDecomposition :
      '"' :: body = consumed ++ remaining := by
    dsimp [consumed]
    simp [decomposition, List.append_assoc]
  have consumedLength : consumed.length = consumedCharacters + 1 := by
    dsimp [consumed]
    simp [consumedEquation]
  have takeEquation :
      ('"' :: body).take (consumedCharacters + 1) = consumed := by
    rw [fullDecomposition, ← consumedLength]
    exact List.take_left
  have openerAndBodySize :
      Lexer.byteSize ('"' :: rawContent) =
        1 + Lexer.byteSize rawContent := by
    rw [byteSize_cons, quoteSize]
  have closerSize : Lexer.byteSize ['"'] = 1 := by decide
  have consumedSize :
      Lexer.byteSize consumed = 1 + Lexer.byteSize rawContent + 1 := by
    dsimp [consumed]
    rw [byteSize_cons, byteSize_append, closerSize, quoteSize]
    omega
  have cursorEnd : cursor + Lexer.byteSize consumed = endByte := by
    rw [consumedSize, endEquation, closeEquation]
    omega
  have sourceTextRaw := suffix.sourceTextAt fullDecomposition
  rw [cursorEnd] at sourceTextRaw
  have sourceText :
      LexicalJudgment.SourceTextAt file cursor endByte
        (String.ofList (('"' :: body).take (consumedCharacters + 1))) := by
    rw [takeEquation]
    exact sourceTextRaw
  refine ⟨String.ofList
      (('"' :: body).take (consumedCharacters + 1)), decoded, ?_,
    contents, sourceText, ?_⟩
  · simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
      suffix.byteAtFirst
  · rfl

private theorem stringContents_to_scanClosed
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {decoded : String}
    {characters decodedRev : List Char}
    (contents :
      LexicalJudgment.StringContents file cursor endByte decoded)
    (suffix : SuffixAt file cursor characters) :
    ∃ consumedCharacters units,
      Lexer.scanString file cursor characters decodedRev =
        .closed endByte consumedCharacters
          (String.ofList decodedRev.reverse ++ decoded) units := by
  induction contents generalizing characters decodedRev with
  | close cursor quote =>
      cases characters with
      | nil =>
          have atEnd := suffix.sourceByteAt
          unfold LexicalJudgment.ByteAt at quote
          rw [atEnd] at quote
          simp at quote
      | cons character remaining =>
          have characterEquation := suffix.character_eq_of_byteAtAscii quote
            (expected := '"') (by decide)
          subst character
          refine ⟨1, 1, ?_⟩
          simpa using Lexer.scanString.eq_2 file cursor decodedRev remaining
  | scalar cursor next endByte character decodedTail scalar notQuote
      notBackslash tail inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      subst characters
      subst next
      have notTrailingBackslash :
          character = '\\' → remaining = [] → False := by
        intro characterEquation _
        exact notBackslash characterEquation
      have notEscapedBackslash :
          ∀ escaped trailing,
            character = '\\' → remaining = escaped :: trailing → False := by
        intro escaped trailing characterEquation _
        exact notBackslash characterEquation
      rcases inductionHypothesis nextSuffix (decodedRev := character :: decodedRev) with
        ⟨consumed, units, scanned⟩
      refine ⟨consumed + 1, units + 1, ?_⟩
      rw [Lexer.scanString.eq_9 file cursor decodedRev character remaining
        notQuote notTrailingBackslash notEscapedBackslash, scanned]
      simp only [List.reverse_cons, String.ofList_append]
      rw [← String.singleton_eq_ofList, String.append_assoc]
  | escapedNewline cursor endByte decodedTail escape tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 'n') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis nextSuffix (decodedRev := '\n' :: decodedRev) with
        ⟨consumed, units, scanned⟩
      have nextCursor : cursor + 1 + 'n'.utf8Size = cursor + 2 := by
        have size : 'n'.utf8Size = 1 := by decide
        omega
      refine ⟨consumed + 2, units + 1, ?_⟩
      rw [Lexer.scanString.eq_4, nextCursor, scanned]
      simp [List.reverse_cons, String.ofList_append, String.append_assoc]
  | escapedTab cursor endByte decodedTail escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 't') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis nextSuffix (decodedRev := '\t' :: decodedRev) with
        ⟨consumed, units, scanned⟩
      have nextCursor : cursor + 1 + 't'.utf8Size = cursor + 2 := by
        have size : 't'.utf8Size = 1 := by decide
        omega
      refine ⟨consumed + 2, units + 1, ?_⟩
      rw [Lexer.scanString.eq_5, nextCursor, scanned]
      simp [List.reverse_cons, String.ofList_append, String.append_assoc]
  | escapedQuote cursor endByte decodedTail escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '"') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis nextSuffix (decodedRev := '"' :: decodedRev) with
        ⟨consumed, units, scanned⟩
      have nextCursor : cursor + 1 + '"'.utf8Size = cursor + 2 := by
        have size : '"'.utf8Size = 1 := by decide
        omega
      refine ⟨consumed + 2, units + 1, ?_⟩
      rw [Lexer.scanString.eq_6, nextCursor, scanned]
      simp [List.reverse_cons, String.ofList_append, String.append_assoc]
  | escapedBackslash cursor endByte decodedTail escape tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '\\') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis nextSuffix (decodedRev := '\\' :: decodedRev) with
        ⟨consumed, units, scanned⟩
      have nextCursor : cursor + 1 + '\\'.utf8Size = cursor + 2 := by
        have size : '\\'.utf8Size = 1 := by decide
        omega
      refine ⟨consumed + 2, units + 1, ?_⟩
      rw [Lexer.scanString.eq_7, nextCursor, scanned]
      simp [List.reverse_cons, String.ofList_append, String.append_assoc]

private theorem stringScanPrefix_suffix
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {characters : List Char}
    (scanPrefix :
      LexicalJudgment.StringScanPrefix file startByte endByte)
    (suffix : SuffixAt file startByte characters) :
    ∃ remaining, SuffixAt file endByte remaining := by
  induction scanPrefix generalizing characters with
  | refl cursor => exact ⟨characters, suffix⟩
  | scalar cursor next endByte character scalar notQuote notBackslash tail
      inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact inductionHypothesis nextSuffix
  | escapedNewline cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 'n') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      exact inductionHypothesis
        (suffix.advanceTwoAscii (by decide) (by decide))
  | escapedTab cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 't') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      exact inductionHypothesis
        (suffix.advanceTwoAscii (by decide) (by decide))
  | escapedQuote cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '"') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      exact inductionHypothesis
        (suffix.advanceTwoAscii (by decide) (by decide))
  | escapedBackslash cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '\\') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      exact inductionHypothesis
        (suffix.advanceTwoAscii (by decide) (by decide))

private theorem invalidStringEscape_range
    {file : WorkspaceFile}
    {escapeStart escapeEnd : Nat}
    {character : Option Char}
    {characters : List Char}
    (suffix : SuffixAt file escapeStart characters)
    (invalid :
      LexicalJudgment.InvalidStringEscapeAt file escapeStart escapeEnd
        character) :
    LexicalJudgment.SourceRange file escapeStart escapeEnd := by
  cases invalid with
  | unsupported endByte escaped backslash scalar unsupported =>
      rcases suffix.characters_eq_cons_of_byteAtAscii backslash
          (expected := '\\') (by decide) with
        ⟨afterBackslashCharacters, decomposition⟩
      subst characters
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      rcases afterBackslash.scalarAt_decomposition scalar with
        ⟨remaining, escapedDecomposition, endEquation, endSuffix⟩
      have fullDecomposition :
          '\\' :: afterBackslashCharacters =
            ['\\', escaped] ++ remaining := by
        rw [escapedDecomposition]
        rfl
      have range := suffix.sourceRange fullDecomposition
      have consumedSize :
          Lexer.byteSize ['\\', escaped] = 1 + escaped.utf8Size := by
        rw [byteSize_cons, byteSize_cons, backslashSize]
        simp [Lexer.byteSize]
      rw [consumedSize] at range
      have normalized : escapeStart + (1 + escaped.utf8Size) =
          escapeStart + 1 + escaped.utf8Size := by omega
      rw [normalized, ← endEquation] at range
      exact range
  | endOfFile backslash atEnd =>
      have range := suffix.rangeToEnd
      rw [← atEnd] at range
      exact range

private theorem unterminatedStringRecognized
    {file : WorkspaceFile}
    {cursor units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('"' :: body))
    (scanned :
      Lexer.scanString file (cursor + 1) body [] = .unterminated units) :
    LexicalJudgment.ByteAt file cursor 34 ∧
      LexicalJudgment.StringScanPrefix file (cursor + 1)
        file.content.utf8ByteSize := by
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  have certified := scanString_certified file (cursor + 1) body [] afterOpener
  rw [scanned] at certified
  refine ⟨?_, certified⟩
  simpa [LexicalJudgment.ByteAt, utf8FirstByte] using suffix.byteAtFirst

private theorem invalidStringRecognized
    {file : WorkspaceFile}
    {cursor units : Nat}
    {body : List Char}
    {diagnostic : LexicalDiagnostic}
    (suffix : SuffixAt file cursor ('"' :: body))
    (scanned :
      Lexer.scanString file (cursor + 1) body [] =
        .invalidEscape diagnostic units) :
    ∃ escapeStart escapeEnd character,
      LexicalJudgment.ByteAt file cursor 34 ∧
      LexicalJudgment.StringScanPrefix file (cursor + 1) escapeStart ∧
      LexicalJudgment.InvalidStringEscapeAt file escapeStart escapeEnd
        character ∧
      LexicalJudgment.SourceRange file escapeStart escapeEnd ∧
      diagnostic = .invalidStringEscape
        (LexicalJudgment.sourceSpan file escapeStart escapeEnd) character := by
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  have certified := scanString_certified file (cursor + 1) body [] afterOpener
  rw [scanned] at certified
  rcases certified with
    ⟨escapeStart, escapeEnd, character, scanPrefix, invalid,
      diagnosticEquation⟩
  rcases stringScanPrefix_suffix scanPrefix afterOpener with
    ⟨escapeCharacters, escapeSuffix⟩
  refine ⟨escapeStart, escapeEnd, character, ?_, scanPrefix, invalid,
    invalidStringEscape_range escapeSuffix invalid, diagnosticEquation⟩
  simpa [LexicalJudgment.ByteAt, utf8FirstByte] using suffix.byteAtFirst

private theorem stringTokenAt_unique
    {file : WorkspaceFile}
    {cursor firstEnd secondEnd : Nat}
    {body : List Char}
    {firstToken secondToken : Token}
    (suffix : SuffixAt file cursor ('"' :: body))
    (first :
      LexicalJudgment.StringTokenAt file cursor firstEnd firstToken)
    (second :
      LexicalJudgment.StringTokenAt file cursor secondEnd secondToken) :
    firstEnd = secondEnd ∧ firstToken = secondToken := by
  rcases first with
    ⟨firstSpelling, firstDecoded, firstQuote, firstContents,
      firstSource, firstTokenEquation⟩
  rcases second with
    ⟨secondSpelling, secondDecoded, secondQuote, secondContents,
      secondSource, secondTokenEquation⟩
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  rcases stringContents_to_scanClosed
      (decodedRev := []) firstContents afterOpener with
    ⟨firstConsumed, firstUnits, firstScan⟩
  rcases stringContents_to_scanClosed
      (decodedRev := []) secondContents afterOpener with
    ⟨secondConsumed, secondUnits, secondScan⟩
  simp only [List.reverse_nil, String.ofList_nil,
    String.empty_append] at firstScan secondScan
  rw [firstScan] at secondScan
  cases secondScan
  have spellingBytes :
      secondSpelling.toByteArray = firstSpelling.toByteArray :=
    secondSource.2.symm.trans firstSource.2
  have spellingEquation : secondSpelling = firstSpelling :=
    String.toByteArray_inj.mp spellingBytes
  subst secondSpelling
  rw [firstTokenEquation, secondTokenEquation]
  exact ⟨rfl, rfl⟩

private theorem candidateAt_of_stringStart
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor ('"' :: body))
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    ∃ endByte token,
      candidate = .token .string token ∧
        LexicalJudgment.StringTokenAt file cursor endByte token := by
  cases recognized with
  | lineComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii recognized.1.1.1
        (expected := '/') (by decide)
      contradiction
  | blockComment endByte comment recognized =>
      have slash := suffix.character_eq_of_byteAtAscii recognized.1.1.1
        (expected := '/') (by decide)
      contradiction
  | string endByte token recognized =>
      exact ⟨endByte, token, rfl, recognized⟩
  | pragmaName endByte token recognized =>
      have first := pragmaToken_first_n suffix recognized
      contradiction
  | identifier endByte token recognized =>
      have letter := identifierToken_firstLetter suffix recognized
      have notLetter : ¬ LexicalJudgment.AsciiLetter '"' := by
        simp [LexicalJudgment.AsciiLetter]
      contradiction
  | decimal endByte token recognized =>
      have digit := decimalToken_firstDigit suffix recognized
      have notDigit : ¬ LexicalJudgment.AsciiDigit '"' := by
        simp [LexicalJudgment.AsciiDigit]
      contradiction
  | hexadecimal endByte token recognized =>
      have zero := hexadecimalToken_first_zero suffix recognized
      contradiction
  | symbol endByte symbol token recognized kind =>
      rcases symbolToken_data suffix recognized kind with
        ⟨remaining, decomposition, sourceText, endEquation,
          slashGuard, assemblyGuard, tokenEquation⟩
      cases symbol <;> simp [Symbol.spelling] at decomposition

private theorem stringCandidateWins
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {pendingAssembly : Bool}
    {body : List Char}
    {decoded : String}
    (suffix : SuffixAt file cursor ('"' :: body))
    (scanned :
      Lexer.scanString file (cursor + 1) body [] =
        .closed endByte consumedCharacters decoded units) :
    let characters := '"' :: body
    let total := consumedCharacters + 1
    let spelling := String.ofList (characters.take total)
    LexicalJudgment.CandidateWinsAt file pendingAssembly cursor
      (.token .string
        (Lexer.tokenAt file cursor endByte
          (.stringLiteral spelling decoded))) := by
  dsimp only
  have selfRecognized := stringTokenRecognized suffix scanned
  refine ⟨LexicalJudgment.CandidateAt.string _ _ selfRecognized, ?_⟩
  intro other recognized
  rcases candidateAt_of_stringStart suffix recognized with
    ⟨otherEnd, otherToken, rfl, otherRecognized⟩
  rcases stringTokenAt_unique suffix selfRecognized otherRecognized with
    ⟨endEquation, tokenEquation⟩
  subst otherEnd
  subst otherToken
  exact Or.inl rfl

private theorem asciiByteStep
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {character : Char}
    (suffix : SuffixAt file cursor characters)
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat character.toNat))
    (ascii : character.toNat ≤ 127)
    (size : character.utf8Size = 1) :
    ∃ remaining,
      SuffixAt file (cursor + 1) remaining ∧
        LexicalJudgment.SourceRange file cursor (cursor + 1) := by
  rcases suffix.characters_eq_cons_of_byteAtAscii byte ascii with
    ⟨remaining, decomposition⟩
  subst characters
  have nextSuffix := suffix.advanceOne
  rw [size] at nextSuffix
  have range := suffix.sourceRange
    (consumed := [character]) (remaining := remaining) (by simp)
  have consumedSize : Lexer.byteSize [character] = 1 := by
    simp [Lexer.byteSize, size]
  rw [consumedSize] at range
  exact ⟨remaining, nextSuffix, range⟩

private theorem asciiPairStep
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {first second : Char}
    (suffix : SuffixAt file cursor characters)
    (pair : LexicalJudgment.BytePairAt file cursor
      (UInt8.ofNat first.toNat) (UInt8.ofNat second.toNat))
    (firstAscii : first.toNat ≤ 127)
    (secondAscii : second.toNat ≤ 127)
    (firstSize : first.utf8Size = 1)
    (secondSize : second.utf8Size = 1) :
    ∃ remaining,
      SuffixAt file (cursor + 2) remaining ∧
        LexicalJudgment.SourceRange file cursor (cursor + 2) := by
  rcases suffix.characters_eq_pair_of_bytePairAscii pair
      firstAscii secondAscii firstSize with
    ⟨remaining, decomposition⟩
  subst characters
  have nextSuffix := suffix.advanceTwoAscii firstSize secondSize
  have range := suffix.sourceRange
    (consumed := [first, second]) (remaining := remaining) (by simp)
  have consumedSize : Lexer.byteSize [first, second] = 2 := by
    rw [byteSize_cons, byteSize_cons, firstSize, secondSize]
    simp [Lexer.byteSize]
  rw [consumedSize] at range
  exact ⟨remaining, nextSuffix, range⟩

private theorem assemblyStep_suffix
    {file : WorkspaceFile}
    {state nextState : LexicalJudgment.AssemblyScannerState}
    {cursor next : Nat}
    {characters : List Char}
    (step :
      LexicalJudgment.AssemblyStep file state cursor nextState next)
    (suffix : SuffixAt file cursor characters) :
    ∃ remaining,
      SuffixAt file next remaining ∧
        LexicalJudgment.SourceRange file cursor next := by
  cases step with
  | openBrace depth cursor positive brace =>
      exact asciiByteStep suffix brace (character := '{')
        (by decide) (by decide)
  | nestedCloseBrace depth cursor nested brace =>
      exact asciiByteStep suffix brace (character := '}')
        (by decide) (by decide)
  | openLineComment depth cursor positive opener =>
      exact asciiPairStep suffix opener (first := '/') (second := '/')
        (by decide) (by decide) (by decide) (by decide)
  | openBlockComment depth cursor positive opener =>
      exact asciiPairStep suffix opener (first := '/') (second := '*')
        (by decide) (by decide) (by decide) (by decide)
  | openString depth cursor positive quote =>
      exact asciiByteStep suffix quote (character := '"')
        (by decide) (by decide)
  | normalScalar depth cursor next character positive notOpenBrace
      notCloseBrace notQuote notLineComment notBlockComment scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact ⟨remaining, nextSuffix, scalar.2.1⟩
  | lineFeed depth cursor positive feed =>
      exact asciiByteStep suffix feed (character := '\n')
        (by decide) (by decide)
  | lineScalar depth cursor next character positive notFeed scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact ⟨remaining, nextSuffix, scalar.2.1⟩
  | nestedBlockOpen braceDepth commentDepth outermostOpen cursor
      bracePositive commentPositive opener =>
      exact asciiPairStep suffix opener (first := '/') (second := '*')
        (by decide) (by decide) (by decide) (by decide)
  | nestedBlockClose braceDepth commentDepth outermostOpen cursor
      bracePositive nested closer =>
      exact asciiPairStep suffix closer (first := '*') (second := '/')
        (by decide) (by decide) (by decide) (by decide)
  | outerBlockClose braceDepth outermostOpen cursor bracePositive closer =>
      exact asciiPairStep suffix closer (first := '*') (second := '/')
        (by decide) (by decide) (by decide) (by decide)
  | blockScalar braceDepth commentDepth outermostOpen cursor next character
      bracePositive commentPositive notOpener notCloser scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact ⟨remaining, nextSuffix, scalar.2.1⟩
  | closeString depth openQuote cursor positive quote =>
      exact asciiByteStep suffix quote (character := '"')
        (by decide) (by decide)
  | escapedStringScalar depth openQuote cursor next character positive
      backslash escaped =>
      rcases asciiByteStep suffix backslash (character := '\\')
          (by decide) (by decide) with
        ⟨afterBackslashCharacters, afterBackslash, backslashRange⟩
      rcases afterBackslash.scalarAt_decomposition escaped with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact ⟨remaining, nextSuffix,
        SuffixAt.sourceRange_trans backslashRange escaped.2.1⟩
  | trailingStringBackslash depth openQuote cursor positive backslash atEnd =>
      exact asciiByteStep suffix backslash (character := '\\')
        (by decide) (by decide)
  | stringScalar depth openQuote cursor next character positive notQuote
      notBackslash scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      exact ⟨remaining, nextSuffix, scalar.2.1⟩

private def assemblyState : Lexer.AssemblyMode →
    LexicalJudgment.AssemblyScannerState
  | .normal depth => .normal depth
  | .lineComment depth => .lineComment depth
  | .blockComment braceDepth commentDepth outermostOpen =>
      .blockComment braceDepth commentDepth outermostOpen
  | .string depth openQuote => .string depth openQuote

private def AssemblyModeValid : Lexer.AssemblyMode → Prop
  | .normal depth => 0 < depth
  | .lineComment depth => 0 < depth
  | .blockComment braceDepth commentDepth _ =>
      0 < braceDepth ∧ 0 < commentDepth
  | .string depth _ => 0 < depth

private def AssemblyFailureDiagnostic
    (file : WorkspaceFile)
    (openBrace : Nat) : Lexer.AssemblyMode → LexicalDiagnostic → Prop
  | .string _ openQuote, diagnostic =>
      diagnostic = .unterminatedAssemblyString
        (LexicalJudgment.sourceSpan file openQuote
          file.content.utf8ByteSize)
  | .blockComment _ _ outermostOpen, diagnostic =>
      diagnostic = .unterminatedAssemblyComment
        (LexicalJudgment.sourceSpan file outermostOpen
          file.content.utf8ByteSize)
  | .normal _, diagnostic
  | .lineComment _, diagnostic =>
      diagnostic = .unterminatedAssemblyBlock
        (LexicalJudgment.sourceSpan file openBrace
          file.content.utf8ByteSize)

private def bumpAssemblyResult
    (consumedCharacters : Nat) : Lexer.AssemblyScanResult →
      Lexer.AssemblyScanResult
  | .closed closeByte endByte consumed units =>
      .closed closeByte endByte (consumed + consumedCharacters) (units + 1)
  | .failed diagnostic units => .failed diagnostic (units + 1)

private def AssemblyScanSpec
    (file : WorkspaceFile)
    (openBrace : Nat)
    (mode : Lexer.AssemblyMode)
    (cursor : Nat)
    (characters : List Char) : Lexer.AssemblyScanResult → Prop
  | .closed closeByte endByte consumedCharacters _ =>
      LexicalJudgment.AssemblyRun file (assemblyState mode) cursor
          (.normal 1) closeByte ∧
        LexicalJudgment.ByteAt file closeByte 125 ∧
        endByte = closeByte + 1 ∧
        SuffixAt file endByte (characters.drop consumedCharacters)
  | .failed diagnostic _ =>
      ∃ finalMode,
        AssemblyModeValid finalMode ∧
        LexicalJudgment.AssemblyRun file (assemblyState mode) cursor
          (assemblyState finalMode) file.content.utf8ByteSize ∧
        AssemblyFailureDiagnostic file openBrace finalMode diagnostic

private theorem AssemblyScanSpec.prepend
    {file : WorkspaceFile}
    {openBrace cursor next consumedCharacters : Nat}
    {mode nextMode : Lexer.AssemblyMode}
    {characters remaining : List Char}
    {result : Lexer.AssemblyScanResult}
    (transition : LexicalJudgment.AssemblyStep file
      (assemblyState mode) cursor (assemblyState nextMode) next)
    (dropEquation : ∀ consumed,
      characters.drop (consumed + consumedCharacters) =
        remaining.drop consumed)
    (certified : AssemblyScanSpec file openBrace nextMode next remaining result) :
    AssemblyScanSpec file openBrace mode cursor characters
      (bumpAssemblyResult consumedCharacters result) := by
  cases result with
  | closed closeByte endByte consumed units =>
      rcases certified with ⟨run, closeBrace, endEquation, suffix⟩
      simp only [bumpAssemblyResult, AssemblyScanSpec]
      refine ⟨.step _ _ _ _ _ _ transition run,
        closeBrace, endEquation, ?_⟩
      rw [dropEquation]
      exact suffix
  | failed diagnostic units =>
      rcases certified with
        ⟨finalMode, finalValid, run, diagnosticEquation⟩
      simp only [bumpAssemblyResult, AssemblyScanSpec]
      exact ⟨finalMode, finalValid,
        .step _ _ _ _ _ _ transition run, diagnosticEquation⟩

private theorem scanAssembly_certified
    (file : WorkspaceFile)
    (openBrace : Nat)
    (mode : Lexer.AssemblyMode)
    (cursor : Nat)
    (characters : List Char) :
    ∀ (_ : AssemblyModeValid mode) (_ : SuffixAt file cursor characters),
      AssemblyScanSpec file openBrace mode cursor characters
        (Lexer.scanAssembly file openBrace mode cursor characters) := by
  induction mode, cursor, characters using
      Lexer.scanAssembly.induct file openBrace with
  | case1 depth openQuote cursor =>
      intro valid suffix
      have atEnd : cursor = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        simpa [Lexer.byteSize] using size.symm
      subst cursor
      simp only [Lexer.scanAssembly.eq_1, AssemblyScanSpec]
      exact ⟨.string depth openQuote, valid, .refl _ _, by
        simp [AssemblyFailureDiagnostic, Lexer.sourceSpan,
          LexicalJudgment.sourceSpan]⟩
  | case2 braceDepth commentDepth outermostOpen cursor =>
      intro valid suffix
      have atEnd : cursor = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        simpa [Lexer.byteSize] using size.symm
      subst cursor
      simp only [Lexer.scanAssembly.eq_2, AssemblyScanSpec]
      exact ⟨.blockComment braceDepth commentDepth outermostOpen,
        valid, .refl _ _, by
          simp [AssemblyFailureDiagnostic, Lexer.sourceSpan,
            LexicalJudgment.sourceSpan]⟩
  | case3 depth cursor =>
      intro valid suffix
      have atEnd : cursor = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        simpa [Lexer.byteSize] using size.symm
      subst cursor
      simp only [Lexer.scanAssembly.eq_3, AssemblyScanSpec]
      exact ⟨.normal depth, valid, .refl _ _, by
        simp [AssemblyFailureDiagnostic, Lexer.sourceSpan,
          LexicalJudgment.sourceSpan]⟩
  | case4 depth cursor =>
      intro valid suffix
      have atEnd : cursor = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        simpa [Lexer.byteSize] using size.symm
      subst cursor
      simp only [Lexer.scanAssembly.eq_4, AssemblyScanSpec]
      exact ⟨.lineComment depth, valid, .refl _ _, by
        simp [AssemblyFailureDiagnostic, Lexer.sourceSpan,
          LexicalJudgment.sourceSpan]⟩
  | case5 cursor tail =>
      intro _ suffix
      simp only [Lexer.scanAssembly.eq_5, AssemblyScanSpec]
      have closeBrace : LexicalJudgment.ByteAt file cursor 125 := by
        simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
          suffix.byteAtFirst
      have afterClose := suffix.advanceOne
      have closeSize : '}'.utf8Size = 1 := by decide
      rw [closeSize] at afterClose
      exact ⟨.refl _ _, closeBrace, True.intro, by simpa using afterClose⟩
  | case6 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have braceSize : '{'.utf8Size = 1 := by decide
      rw [braceSize] at nextSuffix
      have certified := inductionHypothesis (by
        simp [AssemblyModeValid]) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_6, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .normal (depth + 1))
        (consumedCharacters := 1)
        (.openBrace depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case7 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have braceSize : '{'.utf8Size = 1 := by decide
      rw [braceSize] at nextSuffix
      have certified := inductionHypothesis (by
        simp [AssemblyModeValid]) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_6, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .normal (depth + 1))
        (consumedCharacters := 1)
        (.openBrace depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case8 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have braceSize : '}'.utf8Size = 1 := by decide
      rw [braceSize] at nextSuffix
      have certified := inductionHypothesis (by
        simp [AssemblyModeValid]) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_7, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal (depth + 2)) (nextMode := .normal (depth + 1))
        (consumedCharacters := 1)
        (.nestedCloseBrace (depth + 2) cursor (by omega) (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case9 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have braceSize : '}'.utf8Size = 1 := by decide
      rw [braceSize] at nextSuffix
      have certified := inductionHypothesis (by
        simp [AssemblyModeValid]) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_7, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal (depth + 2)) (nextMode := .normal (depth + 1))
        (consumedCharacters := 1)
        (.nestedCloseBrace (depth + 2) cursor (by omega) (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case10 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        simpa [AssemblyModeValid] using valid) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_8, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .lineComment depth)
        (consumedCharacters := 2)
        (.openLineComment depth cursor valid (by
          simpa using suffix.bytePairAtAscii
            (first := '/') (second := '/')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case11 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        simpa [AssemblyModeValid] using valid) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_8, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .lineComment depth)
        (consumedCharacters := 2)
        (.openLineComment depth cursor valid (by
          simpa using suffix.bytePairAtAscii
            (first := '/') (second := '/')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case12 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        change 0 < depth at valid
        exact ⟨valid, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_9, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .blockComment depth 1 cursor)
        (consumedCharacters := 2)
        (.openBlockComment depth cursor valid (by
          simpa using suffix.bytePairAtAscii
            (first := '/') (second := '*')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case13 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        change 0 < depth at valid
        exact ⟨valid, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_9, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .blockComment depth 1 cursor)
        (consumedCharacters := 2)
        (.openBlockComment depth cursor valid (by
          simpa using suffix.bytePairAtAscii
            (first := '/') (second := '*')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case14 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have quoteSize : '"'.utf8Size = 1 := by decide
      rw [quoteSize] at nextSuffix
      have certified := inductionHypothesis (by
        simpa [AssemblyModeValid] using valid) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_10, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .string depth cursor)
        (consumedCharacters := 1)
        (.openString depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case15 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have quoteSize : '"'.utf8Size = 1 := by decide
      rw [quoteSize] at nextSuffix
      have certified := inductionHypothesis (by
        simpa [AssemblyModeValid] using valid) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_10, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .string depth cursor)
        (consumedCharacters := 1)
        (.openString depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case16 depth cursor character rest notOuterClose notOpen
      notNestedClose notLineComment notBlockComment notQuote closeByte endByte
      consumed units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have notOpenBrace : ¬ LexicalJudgment.ByteAt file cursor 123 := by
        intro byte
        have equals := suffix.character_eq_of_byteAtAscii
          (expected := '{') byte (by decide)
        exact notOpen equals
      have notCloseBrace : ¬ LexicalJudgment.ByteAt file cursor 125 := by
        intro byte
        have equals := suffix.character_eq_of_byteAtAscii
          (expected := '}') byte (by decide)
        have positive : 0 < depth := valid
        cases depth with
        | zero => omega
        | succ predecessor =>
            cases predecessor with
            | zero => exact notOuterClose rfl equals
            | succ nested => exact notNestedClose nested rfl equals
      have notQuoteByte : ¬ LexicalJudgment.ByteAt file cursor 34 := by
        intro byte
        exact notQuote (suffix.character_eq_of_byteAtAscii
          (expected := '"') byte (by decide))
      have notLinePair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notLineComment tail characterEquation restEquation
      have notBlockPair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notBlockComment tail characterEquation restEquation
      rw [Lexer.scanAssembly.eq_11 file openBrace cursor depth character rest
        notOuterClose notOpen notNestedClose notLineComment notBlockComment
        notQuote, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.normalScalar depth cursor (cursor + character.utf8Size) character
          valid notOpenBrace notCloseBrace notQuoteByte notLinePair
          notBlockPair suffix.scalarAt)
        (by intro amount; simp) certified
  | case17 depth cursor character rest notOuterClose notOpen
      notNestedClose notLineComment notBlockComment notQuote diagnostic units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have notOpenBrace : ¬ LexicalJudgment.ByteAt file cursor 123 := by
        intro byte
        exact notOpen (suffix.character_eq_of_byteAtAscii
          (expected := '{') byte (by decide))
      have notCloseBrace : ¬ LexicalJudgment.ByteAt file cursor 125 := by
        intro byte
        have equals := suffix.character_eq_of_byteAtAscii
          (expected := '}') byte (by decide)
        have positive : 0 < depth := valid
        cases depth with
        | zero => omega
        | succ predecessor =>
            cases predecessor with
            | zero => exact notOuterClose rfl equals
            | succ nested => exact notNestedClose nested rfl equals
      have notQuoteByte : ¬ LexicalJudgment.ByteAt file cursor 34 := by
        intro byte
        exact notQuote (suffix.character_eq_of_byteAtAscii
          (expected := '"') byte (by decide))
      have notLinePair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notLineComment tail characterEquation restEquation
      have notBlockPair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notBlockComment tail characterEquation restEquation
      rw [Lexer.scanAssembly.eq_11 file openBrace cursor depth character rest
        notOuterClose notOpen notNestedClose notLineComment notBlockComment
        notQuote, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .normal depth) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.normalScalar depth cursor (cursor + character.utf8Size) character
          valid notOpenBrace notCloseBrace notQuoteByte notLinePair
          notBlockPair suffix.scalarAt)
        (by intro amount; simp) certified
  | case18 depth cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have feedSize : '\n'.utf8Size = 1 := by decide
      rw [feedSize] at nextSuffix
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_12, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .lineComment depth) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.lineFeed depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case19 depth cursor rest diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have feedSize : '\n'.utf8Size = 1 := by decide
      rw [feedSize] at nextSuffix
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_12, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .lineComment depth) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.lineFeed depth cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case20 depth cursor character rest notFeed closeByte endByte consumed units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_13 file openBrace cursor depth character rest
        notFeed, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .lineComment depth) (nextMode := .lineComment depth)
        (consumedCharacters := 1)
        (.lineScalar depth cursor (cursor + character.utf8Size) character
          valid notFeed suffix.scalarAt)
        (by intro amount; simp) certified
  | case21 depth cursor character rest notFeed diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_13 file openBrace cursor depth character rest
        notFeed, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .lineComment depth) (nextMode := .lineComment depth)
        (consumedCharacters := 1)
        (.lineScalar depth cursor (cursor + character.utf8Size) character
          valid notFeed suffix.scalarAt)
        (by intro amount; simp) certified
  | case22 braceDepth commentDepth outermostOpen cursor rest closeByte endByte
      consumed units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        change 0 < braceDepth ∧ 0 < commentDepth at valid
        exact ⟨valid.1, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_14, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth commentDepth outermostOpen)
        (nextMode := .blockComment braceDepth (commentDepth + 1)
          outermostOpen)
        (consumedCharacters := 2)
        (.nestedBlockOpen braceDepth commentDepth outermostOpen cursor
          valid.1 valid.2 (by
            simpa using suffix.bytePairAtAscii
              (first := '/') (second := '*')
              (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case23 braceDepth commentDepth outermostOpen cursor rest diagnostic units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        change 0 < braceDepth ∧ 0 < commentDepth at valid
        exact ⟨valid.1, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_14, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth commentDepth outermostOpen)
        (nextMode := .blockComment braceDepth (commentDepth + 1)
          outermostOpen)
        (consumedCharacters := 2)
        (.nestedBlockOpen braceDepth commentDepth outermostOpen cursor
          valid.1 valid.2 (by
            simpa using suffix.bytePairAtAscii
              (first := '/') (second := '*')
              (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case24 braceDepth outermostOpen cursor rest closeByte endByte consumed units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        exact valid.1) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_15, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth 1 outermostOpen)
        (nextMode := .normal braceDepth)
        (consumedCharacters := 2)
        (.outerBlockClose braceDepth outermostOpen cursor valid.1 (by
          simpa using suffix.bytePairAtAscii
            (first := '*') (second := '/')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case25 braceDepth outermostOpen cursor rest diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis valid.1 nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_15, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth 1 outermostOpen)
        (nextMode := .normal braceDepth)
        (consumedCharacters := 2)
        (.outerBlockClose braceDepth outermostOpen cursor valid.1 (by
          simpa using suffix.bytePairAtAscii
            (first := '*') (second := '/')
            (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case26 braceDepth commentDepth outermostOpen cursor rest closeByte endByte
      consumed units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        exact ⟨valid.1, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_16, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth (commentDepth + 2) outermostOpen)
        (nextMode := .blockComment braceDepth (commentDepth + 1)
          outermostOpen)
        (consumedCharacters := 2)
        (.nestedBlockClose braceDepth (commentDepth + 2) outermostOpen cursor
          valid.1 (by omega) (by
            simpa using suffix.bytePairAtAscii
              (first := '*') (second := '/')
              (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case27 braceDepth commentDepth outermostOpen cursor rest diagnostic units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      have certified := inductionHypothesis (by
        exact ⟨valid.1, by omega⟩) nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_16, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth (commentDepth + 2) outermostOpen)
        (nextMode := .blockComment braceDepth (commentDepth + 1)
          outermostOpen)
        (consumedCharacters := 2)
        (.nestedBlockClose braceDepth (commentDepth + 2) outermostOpen cursor
          valid.1 (by omega) (by
            simpa using suffix.bytePairAtAscii
              (first := '*') (second := '/')
              (by decide) (by decide) (by decide)))
        (by intro amount; simp) certified
  | case28 braceDepth commentDepth outermostOpen cursor character rest
      notOpener notOuterCloser notNestedCloser closeByte endByte consumed units
      equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have noOpener :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notOpener tail characterEquation restEquation
      have noCloser :
          ¬ LexicalJudgment.BytePairAt file cursor 42 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '*') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        cases commentDepth with
        | zero => exact (Nat.not_lt_zero _ valid.2)
        | succ predecessor =>
            cases predecessor with
            | zero =>
                exact notOuterCloser tail rfl characterEquation restEquation
            | succ nested =>
                exact notNestedCloser nested tail rfl characterEquation
                  restEquation
      rw [Lexer.scanAssembly.eq_17 file openBrace cursor braceDepth
        commentDepth outermostOpen character rest notOpener notOuterCloser
        notNestedCloser, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth commentDepth outermostOpen)
        (nextMode := .blockComment braceDepth commentDepth outermostOpen)
        (consumedCharacters := 1)
        (.blockScalar braceDepth commentDepth outermostOpen cursor
          (cursor + character.utf8Size) character valid.1 valid.2 noOpener
          noCloser suffix.scalarAt)
        (by intro amount; simp) certified
  | case29 braceDepth commentDepth outermostOpen cursor character rest
      notOpener notOuterCloser notNestedCloser diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have noOpener :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        exact notOpener tail characterEquation restEquation
      have noCloser :
          ¬ LexicalJudgment.BytePairAt file cursor 42 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '*') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨tail, characterEquation, restEquation⟩
        cases commentDepth with
        | zero => exact (Nat.not_lt_zero _ valid.2)
        | succ predecessor =>
            cases predecessor with
            | zero =>
                exact notOuterCloser tail rfl characterEquation restEquation
            | succ nested =>
                exact notNestedCloser nested tail rfl characterEquation
                  restEquation
      rw [Lexer.scanAssembly.eq_17 file openBrace cursor braceDepth
        commentDepth outermostOpen character rest notOpener notOuterCloser
        notNestedCloser, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .blockComment braceDepth commentDepth outermostOpen)
        (nextMode := .blockComment braceDepth commentDepth outermostOpen)
        (consumedCharacters := 1)
        (.blockScalar braceDepth commentDepth outermostOpen cursor
          (cursor + character.utf8Size) character valid.1 valid.2 noOpener
          noCloser suffix.scalarAt)
        (by intro amount; simp) certified
  | case30 depth openQuote cursor rest closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have quoteSize : '"'.utf8Size = 1 := by decide
      rw [quoteSize] at nextSuffix
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_18, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.closeString depth openQuote cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case31 depth openQuote cursor rest diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have quoteSize : '"'.utf8Size = 1 := by decide
      rw [quoteSize] at nextSuffix
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_18, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .normal depth)
        (consumedCharacters := 1)
        (.closeString depth openQuote cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst))
        (by intro amount; simp) certified
  | case32 depth openQuote cursor escaped rest closeByte endByte consumed units
      equation inductionHypothesis =>
      intro valid suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have nextSuffix := afterBackslash.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_19, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 2)
        (.escapedStringScalar depth openQuote cursor
          (cursor + 1 + escaped.utf8Size) escaped valid (by
            simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
              suffix.byteAtFirst) afterBackslash.scalarAt)
        (by intro amount; simp) certified
  | case33 depth openQuote cursor escaped rest diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have nextSuffix := afterBackslash.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_19, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 2)
        (.escapedStringScalar depth openQuote cursor
          (cursor + 1 + escaped.utf8Size) escaped valid (by
            simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
              suffix.byteAtFirst) afterBackslash.scalarAt)
        (by intro amount; simp) certified
  | case34 depth openQuote cursor closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have atEnd : cursor + 1 = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        rw [byteSize_cons, backslashSize] at size
        simpa [Lexer.byteSize] using size.symm
      have certified := inductionHypothesis valid afterBackslash
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_20, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 1)
        (.trailingStringBackslash depth openQuote cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst) atEnd)
        (by intro amount; simp) certified
  | case35 depth openQuote cursor diagnostic units equation
      inductionHypothesis =>
      intro valid suffix
      have afterBackslash := suffix.advanceOne
      have backslashSize : '\\'.utf8Size = 1 := by decide
      rw [backslashSize] at afterBackslash
      have atEnd : cursor + 1 = file.content.utf8ByteSize := by
        have size := suffix.remainingByteSize
        rw [byteSize_cons, backslashSize] at size
        simpa [Lexer.byteSize] using size.symm
      have certified := inductionHypothesis valid afterBackslash
      rw [equation] at certified
      rw [Lexer.scanAssembly.eq_20, equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 1)
        (.trailingStringBackslash depth openQuote cursor valid (by
          simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
            suffix.byteAtFirst) atEnd)
        (by intro amount; simp) certified
  | case36 depth openQuote cursor character rest notQuote notEscapedBackslash
      notTrailingBackslash closeByte endByte consumed units equation
      inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have notBackslash : character ≠ '\\' := by
        intro equals
        cases rest with
        | nil => exact notTrailingBackslash equals rfl
        | cons escaped tail =>
            exact notEscapedBackslash escaped tail equals rfl
      rw [Lexer.scanAssembly.eq_21 file openBrace cursor depth openQuote
        character rest notQuote notEscapedBackslash notTrailingBackslash,
        equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 1)
        (.stringScalar depth openQuote cursor
          (cursor + character.utf8Size) character valid notQuote notBackslash
          suffix.scalarAt)
        (by intro amount; simp) certified
  | case37 depth openQuote cursor character rest notQuote notEscapedBackslash
      notTrailingBackslash diagnostic units equation inductionHypothesis =>
      intro valid suffix
      have nextSuffix := suffix.advanceOne
      have certified := inductionHypothesis valid nextSuffix
      rw [equation] at certified
      have notBackslash : character ≠ '\\' := by
        intro equals
        cases rest with
        | nil => exact notTrailingBackslash equals rfl
        | cons escaped tail =>
            exact notEscapedBackslash escaped tail equals rfl
      rw [Lexer.scanAssembly.eq_21 file openBrace cursor depth openQuote
        character rest notQuote notEscapedBackslash notTrailingBackslash,
        equation]
      simpa only [bumpAssemblyResult] using
        AssemblyScanSpec.prepend
        (mode := .string depth openQuote) (nextMode := .string depth openQuote)
        (consumedCharacters := 1)
        (.stringScalar depth openQuote cursor
          (cursor + character.utf8Size) character valid notQuote notBackslash
          suffix.scalarAt)
        (by intro amount; simp) certified

private theorem lineCommentNextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '/' :: body)) :
    let scanned := Lexer.scanLineComment (cursor + 2) body
    SuffixAt file scanned.endByte
      (('/' :: '/' :: body).drop (scanned.consumedCharacters + 2)) := by
  dsimp only
  rcases scanLineComment_certified (cursor + 2) body with
    ⟨consumed, remaining, decomposition, endEquation,
      consumedEquation, noLineFeeds, boundary⟩
  let consumedPrefix : List Char := '/' :: '/' :: consumed
  have fullDecomposition :
      '/' :: '/' :: body = consumedPrefix ++ remaining := by
    dsimp [consumedPrefix]
    simp [decomposition]
  have prefixLength : consumedPrefix.length =
      (Lexer.scanLineComment (cursor + 2) body).consumedCharacters + 2 := by
    dsimp [consumedPrefix]
    simp [consumedEquation]
  have prefixSize : Lexer.byteSize consumedPrefix =
      2 + Lexer.byteSize consumed := by
    dsimp [consumedPrefix]
    rw [byteSize_cons, byteSize_cons]
    have slashSize : '/'.utf8Size = 1 := by decide
    omega
  have advanced := suffix.advancePrefixDrop fullDecomposition
  rw [prefixSize] at advanced
  have cursorEquation :
      cursor + (2 + Lexer.byteSize consumed) =
        (Lexer.scanLineComment (cursor + 2) body).endByte := by
    rw [endEquation]
    omega
  rw [cursorEquation, prefixLength] at advanced
  exact advanced

private theorem blockCommentNextSuffix
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('/' :: '*' :: body))
    (scanned :
      Lexer.scanBlockComment (cursor + 2) 1 body =
        .closed endByte consumedCharacters units) :
    SuffixAt file endByte
      (('/' :: '*' :: body).drop (consumedCharacters + 2)) := by
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  have certified := scanBlockComment_certified file (cursor + 2) 1 body
    afterOpener (by omega)
  rw [scanned] at certified
  rcases certified with
    ⟨beforeClose, remaining, closeCursor, decomposition,
      consumedEquation, closeEquation, endEquation, run, closer⟩
  let consumedPrefix : List Char :=
    ('/' :: '*' :: beforeClose) ++ ['*', '/']
  have fullDecomposition :
      '/' :: '*' :: body = consumedPrefix ++ remaining := by
    dsimp [consumedPrefix]
    simp [decomposition, List.append_assoc]
  have prefixLength : consumedPrefix.length = consumedCharacters + 2 := by
    dsimp [consumedPrefix]
    simp [consumedEquation]
  have prefixSize :
      Lexer.byteSize consumedPrefix =
        2 + Lexer.byteSize beforeClose + 2 := by
    dsimp [consumedPrefix]
    rw [byteSize_cons, byteSize_cons, byteSize_append]
    have delimiterSize : Lexer.byteSize ['*', '/'] = 2 := by decide
    rw [delimiterSize]
    have slashSize : '/'.utf8Size = 1 := by decide
    have starSize : '*'.utf8Size = 1 := by decide
    omega
  have advanced := suffix.advancePrefixDrop fullDecomposition
  rw [prefixSize] at advanced
  have cursorEquation :
      cursor + (2 + Lexer.byteSize beforeClose + 2) = endByte := by
    rw [endEquation, closeEquation]
    omega
  rw [cursorEquation, prefixLength] at advanced
  exact advanced

private theorem stringNextSuffix
    {file : WorkspaceFile}
    {cursor endByte consumedCharacters units : Nat}
    {body : List Char}
    {decoded : String}
    (suffix : SuffixAt file cursor ('"' :: body))
    (scanned :
      Lexer.scanString file (cursor + 1) body [] =
        .closed endByte consumedCharacters decoded units) :
    SuffixAt file endByte
      (('"' :: body).drop (consumedCharacters + 1)) := by
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  have certified := scanString_certified file (cursor + 1) body [] afterOpener
  rw [scanned] at certified
  rcases certified with
    ⟨rawContent, remaining, closeCursor, decodedContent,
      decomposition, consumedEquation, closeEquation, endEquation,
      contents, decodedEquation⟩
  let consumedPrefix : List Char := ('"' :: rawContent) ++ ['"']
  have fullDecomposition :
      '"' :: body = consumedPrefix ++ remaining := by
    dsimp [consumedPrefix]
    simp [decomposition, List.append_assoc]
  have prefixLength : consumedPrefix.length = consumedCharacters + 1 := by
    dsimp [consumedPrefix]
    simp [consumedEquation]
  have prefixSize :
      Lexer.byteSize consumedPrefix =
        1 + Lexer.byteSize rawContent + 1 := by
    dsimp [consumedPrefix]
    rw [byteSize_cons, byteSize_append]
    have closerSize : Lexer.byteSize ['"'] = 1 := by decide
    rw [closerSize, quoteSize]
    omega
  have advanced := suffix.advancePrefixDrop fullDecomposition
  rw [prefixSize] at advanced
  have cursorEquation :
      cursor + (1 + Lexer.byteSize rawContent + 1) = endByte := by
    rw [endEquation, closeEquation]
    omega
  rw [cursorEquation, prefixLength] at advanced
  exact advanced

private theorem takeWhileNextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (predicate : Char → Bool) :
    let consumed := Lexer.takeWhile predicate characters
    SuffixAt file (cursor + Lexer.byteSize consumed)
      (characters.drop consumed.length) := by
  dsimp only
  rcases takeWhile_decomposition predicate characters with
    ⟨remaining, decomposition⟩
  exact suffix.advancePrefixDrop decomposition

private theorem pragmaNextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {kind : PragmaKind}
    (suffix : SuffixAt file cursor characters)
    (matched : Lexer.pragmaMatch? characters = some kind) :
    SuffixAt file (cursor + kind.spelling.utf8ByteSize)
      (characters.drop kind.spelling.toList.length) := by
  have spelling := pragmaMatch_sound suffix matched
  rcases suffix.sourceTextDecomposition spelling.1 with
    ⟨remaining, decomposition, endEquation⟩
  have advanced := suffix.advancePrefixDrop decomposition
  have sizeEquation :
      Lexer.byteSize kind.spelling.toList = kind.spelling.utf8ByteSize :=
    (stringByteSize_eq_byteSize kind.spelling).symm
  rw [sizeEquation] at advanced
  exact advanced

private theorem hexadecimalNextSuffix
    {file : WorkspaceFile}
    {cursor : Nat}
    {digit : Char}
    {rest : List Char}
    (suffix : SuffixAt file cursor ('0' :: 'x' :: digit :: rest)) :
    let digitsCharacters :=
      Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)
    let digits := String.ofList digitsCharacters
    let spelling := "0x" ++ digits
    let count := digitsCharacters.length + 2
    SuffixAt file (cursor + spelling.utf8ByteSize)
      (('0' :: 'x' :: digit :: rest).drop count) := by
  dsimp only
  rcases takeWhile_decomposition Lexer.isAsciiHexDigit (digit :: rest) with
    ⟨remaining, decomposition⟩
  let consumed : List Char :=
    '0' :: 'x' :: Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)
  have fullDecomposition :
      '0' :: 'x' :: digit :: rest = consumed ++ remaining := by
    dsimp [consumed]
    exact congrArg (fun characters => '0' :: 'x' :: characters)
      decomposition
  have advanced := suffix.advancePrefixDrop fullDecomposition
  have consumedLength : consumed.length =
      (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)).length + 2 := by
    dsimp [consumed]
  have consumedText : String.ofList consumed =
      "0x" ++ String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest)) := by
    apply String.toList_inj.mp
    simp [consumed]
  have sizeEquation : Lexer.byteSize consumed =
      ("0x" ++ String.ofList
        (Lexer.takeWhile Lexer.isAsciiHexDigit (digit :: rest))).utf8ByteSize := by
    rw [Lexer.byteSize, consumedText]
  rw [sizeEquation, consumedLength] at advanced
  exact advanced

private theorem assemblyNextSuffix
    {file : WorkspaceFile}
    {cursor closeByte endByte consumedCharacters units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('{' :: body))
    (scanned :
      Lexer.scanAssembly file cursor (.normal 1) (cursor + 1) body =
        .closed closeByte endByte consumedCharacters units) :
    SuffixAt file endByte
      (('{' :: body).drop (consumedCharacters + 1)) := by
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have certified := scanAssembly_certified file cursor (.normal 1)
    (cursor + 1) body (by simp [AssemblyModeValid]) afterOpener
  rw [scanned] at certified
  rcases certified with ⟨run, closeBrace, endEquation, endSuffix⟩
  simpa using endSuffix

private theorem assemblyTokenRecognized
    {file : WorkspaceFile}
    {cursor closeByte endByte consumedCharacters units : Nat}
    {body : List Char}
    (suffix : SuffixAt file cursor ('{' :: body))
    (scanned :
      Lexer.scanAssembly file cursor (.normal 1) (cursor + 1) body =
        .closed closeByte endByte consumedCharacters units) :
    let outer := Lexer.sourceSpan file cursor endByte
    let slice : AssemblySlice := {
      span := outer
      payload := {
        openBrace := Lexer.sourceSpan file cursor (cursor + 1)
        contents := Lexer.sourceSpan file (cursor + 1) closeByte
        closeBrace := Lexer.sourceSpan file closeByte endByte
      }
    }
    LexicalJudgment.AssemblyTokenAt file cursor endByte
      (Lexer.tokenAt file cursor endByte (.assemblyBlock slice)) := by
  dsimp only
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have certified := scanAssembly_certified file cursor (.normal 1)
    (cursor + 1) body (by simp [AssemblyModeValid]) afterOpener
  rw [scanned] at certified
  rcases certified with ⟨run, closeBrace, endEquation, endSuffix⟩
  let consumed : List Char := '{' :: body.take consumedCharacters
  have fullDecomposition :
      '{' :: body = consumed ++ body.drop consumedCharacters := by
    dsimp [consumed]
    exact congrArg (List.cons '{')
      (List.take_append_drop consumedCharacters body).symm
  have constructedSuffix := suffix.advance fullDecomposition rfl
  have cursorEnd : cursor + Lexer.byteSize consumed = endByte :=
    constructedSuffix.cursor_unique endSuffix
  have rangeRaw := suffix.sourceRange fullDecomposition
  rw [cursorEnd] at rangeRaw
  let slice : AssemblySlice := {
    span := Lexer.sourceSpan file cursor endByte
    payload := {
      openBrace := Lexer.sourceSpan file cursor (cursor + 1)
      contents := Lexer.sourceSpan file (cursor + 1) closeByte
      closeBrace := Lexer.sourceSpan file closeByte endByte
    }
  }
  refine ⟨slice, ?_, ?_⟩
  · refine ⟨?_, closeByte, run, closeBrace, endEquation, rangeRaw, ?_⟩
    · simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
        suffix.byteAtFirst
    · rfl
  · rfl

private theorem scanLineComment_units_le
    (cursor : Nat)
    (characters : List Char) :
    (Lexer.scanLineComment cursor characters).units ≤
        (Lexer.scanLineComment cursor characters).consumedCharacters ∧
      (Lexer.scanLineComment cursor characters).consumedCharacters ≤
        characters.length := by
  induction cursor, characters using Lexer.scanLineComment.induct
  <;> simp_all [Lexer.scanLineComment]

private theorem scanBlockComment_units_le
    (cursor depth : Nat)
    (characters : List Char) :
    match Lexer.scanBlockComment cursor depth characters with
    | .closed _ consumed units =>
        units ≤ consumed ∧ consumed ≤ characters.length
    | .unterminated units => units ≤ characters.length := by
  induction cursor, depth, characters using Lexer.scanBlockComment.induct
  <;> simp_all [Lexer.scanBlockComment] <;> omega

private theorem scanString_units_le
    (file : WorkspaceFile)
    (cursor : Nat)
    (characters decodedRev : List Char) :
    match Lexer.scanString file cursor characters decodedRev with
    | .closed _ consumed _ units =>
        units ≤ consumed ∧ consumed ≤ characters.length
    | .invalidEscape _ units => units ≤ characters.length
    | .unterminated units => units ≤ characters.length := by
  induction cursor, characters, decodedRev using Lexer.scanString.induct file with
  | case1 => simp [Lexer.scanString.eq_1]
  | case2 => simp [Lexer.scanString.eq_2]
  | case3 => simp [Lexer.scanString.eq_3]
  | case4 cursor escaped rest decodedRev decodedOption decodedNone =>
      rcases invalidEscape_ne escaped decodedNone with
        ⟨notNewline, notTab, notQuote, notBackslash⟩
      rw [Lexer.scanString.eq_8 file cursor decodedRev escaped rest
        notNewline notTab notQuote notBackslash]
      simp
  | case5 cursor escaped rest decodedRev next decodedOption decoded
      decodedEquation endByte consumed value units equation
      inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only
      simp only [List.length_cons] at bound ⊢
      omega
  | case6 cursor escaped rest decodedRev next decodedOption decoded
      decodedEquation diagnostic units equation inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only
      simp only [List.length_cons] at bound ⊢
      omega
  | case7 cursor escaped rest decodedRev next decodedOption decoded
      decodedEquation units equation inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [scanString_validEscape_equation file cursor escaped decoded rest
        decodedRev decodedEquation, equation]
      simp only
      simp only [List.length_cons] at bound ⊢
      omega
  | case8 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash endByte consumed value units equation
      inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [List.length_cons] at bound ⊢
      omega
  | case9 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash diagnostic units equation inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [List.length_cons] at bound ⊢
      omega
  | case10 cursor character rest decodedRev notQuote notTrailingBackslash
      notEscapedBackslash units equation inductionHypothesis =>
      have bound := inductionHypothesis
      rw [equation] at bound
      rw [Lexer.scanString.eq_9 file cursor decodedRev character rest notQuote
        notTrailingBackslash notEscapedBackslash, equation]
      simp only [List.length_cons] at bound ⊢
      omega

private theorem scanAssembly_units_le
    (file : WorkspaceFile)
    (openBrace : Nat)
    (mode : Lexer.AssemblyMode)
    (cursor : Nat)
    (characters : List Char) :
    match Lexer.scanAssembly file openBrace mode cursor characters with
    | .closed _ _ consumed units =>
        units ≤ consumed ∧ consumed ≤ characters.length
    | .failed _ units => units ≤ characters.length := by
  induction mode, cursor, characters using
      Lexer.scanAssembly.induct file openBrace
  <;> simp_all [Lexer.scanAssembly] <;> omega

/-- The public brace-depth projection of an assembly scanner state. -/
def assemblyScannerBraceDepth :
    LexicalJudgment.AssemblyScannerState → Nat
  | .normal depth => depth
  | .lineComment depth => depth
  | .blockComment depth _ _ => depth
  | .string depth _ => depth

/-- A recognized assembly slice reaches its first depth-one closing brace. -/
theorem assembly_slice_balanced
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {slice : AssemblySlice}
    (recognized :
      LexicalJudgment.AssemblySliceAt file startByte endByte slice) :
    ∃ closeCursor,
      LexicalJudgment.AssemblyRun file (.normal 1) (startByte + 1)
          (.normal 1) closeCursor ∧
        LexicalJudgment.ByteAt file closeCursor 125 ∧
        endByte = closeCursor + 1 := by
  rcases recognized with ⟨_, closeCursor, run, closeBrace,
    endEquation, _, _⟩
  exact ⟨closeCursor, run, closeBrace, endEquation⟩

/-- One assembly scanner step inside a string cannot change brace depth. -/
theorem assembly_slice_ignores_string_braces
    {file : WorkspaceFile}
    {depth openQuote cursor next : Nat}
    {nextState : LexicalJudgment.AssemblyScannerState}
    (step : LexicalJudgment.AssemblyStep file
      (.string depth openQuote) cursor nextState next) :
    assemblyScannerBraceDepth nextState = depth := by
  cases step <;> rfl

/-- One assembly scanner step inside either comment mode preserves brace depth. -/
theorem assembly_slice_ignores_comment_braces
    {file : WorkspaceFile}
    {state nextState : LexicalJudgment.AssemblyScannerState}
    {cursor next depth : Nat}
    (commentState :
      (∃ commentDepth outermostOpen,
        state = .blockComment depth commentDepth outermostOpen) ∨
      state = .lineComment depth)
    (step : LexicalJudgment.AssemblyStep file state cursor nextState next) :
    assemblyScannerBraceDepth nextState = depth := by
  rcases commentState with
    ⟨commentDepth, outermostOpen, rfl⟩ | rfl
  · cases step <;> rfl
  · cases step <;> rfl

set_option linter.unusedSimpArgs false in
private theorem lexLoop_units_le
    (file : WorkspaceFile)
    (fuel cursor : Nat)
    (characters : List Char)
    (pendingAssembly : Bool)
    (tokensRev : List Token)
    (commentsRev : List Comment)
    (sufficient : characters.length < fuel) :
    (Lexer.lexLoop file fuel cursor characters pendingAssembly
      tokensRev commentsRev sufficient).units ≤ characters.length := by
  induction fuel, cursor, characters, pendingAssembly, tokensRev,
      commentsRev, sufficient using Lexer.lexLoop.induct file with
  | case1 => simp [Lexer.lexLoop.eq_2, Lexer.successfulResult]
  | case2 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient restSufficient whitespace inductionHypothesis =>
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_pos whitespace]
          simpa only [Lexer.addUnits, List.length_cons, List.length_nil]
            using Nat.add_le_add_left inductionHypothesis 1
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_pos whitespace]
          simp only [Lexer.addUnits, List.length_cons]
          simp only [List.length_cons] at inductionHypothesis
          have charged := Nat.add_le_add_left inductionHypothesis 1
          omega
  | case3 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      scanned comment inductionHypothesis =>
      change character :: rest = '/' :: '/' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have scannerBound := scanLineComment_units_le (cursor + 2) body
      simp only [characters, scanned, comment, List.drop_succ_cons]
        at inductionHypothesis
      have dropEquation :
          ('/' :: '/' :: body).drop
              ((Lexer.scanLineComment (cursor + 2) body).consumedCharacters + 2) =
            body.drop
              (Lexer.scanLineComment (cursor + 2) body).consumedCharacters := by
        simp
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '/' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simp [Lexer.addUnits, dropEquation, List.length_drop]
      simp only [List.length_drop] at inductionHypothesis
      omega
  | case4 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      units scanEquation =>
      change character :: rest = '/' :: '*' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have scannerBound := scanBlockComment_units_le (cursor + 2) 1 body
      rw [scanEquation] at scannerBound
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '*' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simp [scanEquation, Lexer.failedResult]
      omega
  | case5 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      endByte consumed units scanEquation comment inductionHypothesis =>
      change character :: rest = '/' :: '*' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have scannerBound := scanBlockComment_units_le (cursor + 2) 1 body
      rw [scanEquation] at scannerBound
      simp only [characters, comment, List.drop_succ_cons]
        at inductionHypothesis
      have dropEquation :
          ('/' :: '*' :: body).drop (consumed + 2) =
            body.drop consumed := by simp
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '*' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simp [scanEquation, Lexer.addUnits, dropEquation,
        List.length_drop]
      simp only [List.length_drop] at inductionHypothesis
      omega
  | case6 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      diagnostic units scanEquation =>
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      cases body with
      | nil => simp [Lexer.scanString] at scanEquation
      | cons next tail =>
          have scannerBound := scanString_units_le file (cursor + 1)
            (next :: tail) []
          rw [scanEquation] at scannerBound
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [scanEquation, Lexer.failedResult]
          omega
  | case7 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      units scanEquation =>
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have scannerBound := scanString_units_le file (cursor + 1) body []
      rw [scanEquation] at scannerBound
      cases body with
      | nil =>
          simp [Lexer.scanString] at scanEquation
          subst units
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [Lexer.scanString, Lexer.failedResult]
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [scanEquation, Lexer.failedResult]
          omega
  | case8 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      endByte consumed decoded units scanEquation total spelling kind token
      inductionHypothesis =>
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      cases body with
      | nil => simp [Lexer.scanString] at scanEquation
      | cons next tail =>
          have scannerBound := scanString_units_le file (cursor + 1)
            (next :: tail) []
          rw [scanEquation] at scannerBound
          simp [characters, total, spelling, kind, token,
            List.length_drop] at inductionHypothesis
          simp only [List.length_cons] at scannerBound
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [scanEquation, Lexer.addUnits, List.length_drop]
          omega
  | case9 fuel cursor character rest tokensRev commentsRev sufficient
      characters restSufficient notWhitespace body equation diagnostic units
      scanEquation =>
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have scannerBound := scanAssembly_units_le file cursor (.normal 1)
        (cursor + 1) body
      rw [scanEquation] at scannerBound
      cases body with
      | nil =>
          simp [Lexer.scanAssembly] at scanEquation
          rcases scanEquation with ⟨diagnosticEquation, unitsEquation⟩
          subst diagnostic
          subst units
          rw [Lexer.lexLoop.eq_4 file cursor true tokensRev commentsRev
            fuel '{' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [Lexer.scanAssembly, Lexer.failedResult]
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor true tokensRev commentsRev
            fuel '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [scanEquation, Lexer.failedResult]
          omega
  | case10 fuel cursor character rest tokensRev commentsRev sufficient
      characters restSufficient notWhitespace body equation closeByte endByte
      consumed units scanEquation outer slice token inductionHypothesis =>
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      cases body with
      | nil => simp [Lexer.scanAssembly] at scanEquation
      | cons next tail =>
          have scannerBound := scanAssembly_units_le file cursor (.normal 1)
            (cursor + 1) (next :: tail)
          rw [scanEquation] at scannerBound
          simp [characters, outer, slice, token, List.length_drop]
            at inductionHypothesis
          simp only [List.length_cons] at scannerBound
          rw [Lexer.lexLoop.eq_3 file cursor true tokensRev commentsRev
            fuel '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [scanEquation, Lexer.addUnits, List.length_drop]
          omega
  | case11 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      notPending endByte token inductionHypothesis =>
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      simp [endByte, token] at inductionHypothesis
      cases body with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel '{' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [notPending, Lexer.addUnits]
          simpa only [endByte, token, List.length_nil] using
            Nat.add_le_add_left inductionHypothesis 1
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simp [notPending, Lexer.addUnits]
          simp only [List.length_cons] at inductionHypothesis ⊢
          have charged := Nat.add_le_add_left inductionHypothesis 1
          omega
  | case12 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace kind matched count
      endByte token notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      rcases pragmaMatch_decomposition matched with
        ⟨remaining, decomposition⟩
      have lengthEquation := congrArg List.length decomposition
      simp only [List.length_append] at lengthEquation
      have dropEquation : characters.drop count = remaining := by
        rw [decomposition]
        simp [count]
      cases rest with
      | nil =>
          simp [characters] at lengthEquation
          simp [characters, count] at dropEquation
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [matched]
            simp only
            simp only [dropEquation]
            simp [characters, count, endByte, token, dropEquation]
              at inductionHypothesis
            simp only [Lexer.addUnits]
            have charged := Nat.add_le_add_left inductionHypothesis
              kind.spelling.toList.length
            calc
              _ ≤ kind.spelling.toList.length + remaining.length := charged
              _ = [character].length := by
                simpa only [List.length_cons, List.length_nil] using
                  lengthEquation.symm
      | cons next tail =>
          simp [characters] at lengthEquation
          simp [characters, count] at dropEquation
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [matched]
            simp only
            simp only [dropEquation]
            simp [characters, count, endByte, token, dropEquation]
              at inductionHypothesis
            simp only [Lexer.addUnits]
            have charged := Nat.add_le_add_left inductionHypothesis
              kind.spelling.toList.length
            calc
              _ ≤ kind.spelling.toList.length + remaining.length := charged
              _ = (character :: next :: tail).length := by
                simpa only [List.length_cons] using lengthEquation.symm
  | case13 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone letter
      spellingChars text endByte kind token notLineComment notBlockComment
      notString notAssembly inductionHypothesis =>
      have takeBound := takeWhile_length_le Lexer.isIdentifierContinue
        characters
      simp [characters] at takeBound
      simp [characters, spellingChars, text, endByte, kind, token,
        List.length_drop] at inductionHypothesis
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone, dif_pos letter]
            simp [Lexer.addUnits, characters, spellingChars, text, endByte,
              kind, token, List.length_drop]
            calc
              _ ≤ (Lexer.takeWhile Lexer.isIdentifierContinue
                    [character]).length +
                  ([character].length -
                    (Lexer.takeWhile Lexer.isIdentifierContinue
                      [character]).length) :=
                Nat.add_le_add_left inductionHypothesis _
              _ = [character].length := Nat.add_sub_of_le takeBound
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone, dif_pos letter]
            simp [Lexer.addUnits, characters, spellingChars, text, endByte,
              kind, token, List.length_drop]
            calc
              _ ≤ (Lexer.takeWhile Lexer.isIdentifierContinue
                    (character :: next :: tail)).length +
                  ((character :: next :: tail).length -
                    (Lexer.takeWhile Lexer.isIdentifierContinue
                      (character :: next :: tail)).length) :=
                Nat.add_le_add_left inductionHypothesis _
              _ = (character :: next :: tail).length :=
                Nat.add_sub_of_le takeBound
  | case14 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digit tail patternInitial hexDigit digitsChars digits spelling
      count endByte kind token
      notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      simp only [characters] at patternInitial
      have headEquation := List.cons.inj patternInitial
      rcases headEquation with ⟨characterEquation, restEquation⟩
      subst character
      subst rest
      have takeBound := takeWhile_length_le Lexer.isAsciiHexDigit
        (digit :: tail)
      simp only [List.length_cons] at takeBound
      simp [characters, digitsChars, digits, spelling, count, endByte,
        kind, token, List.length_drop] at inductionHypothesis
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '0' 'x' (digit :: tail) sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_pos digitStart]
        rw [if_pos hexDigit]
        simp [Lexer.addUnits, characters, digitsChars, digits, spelling,
          count, endByte, kind, token, List.length_drop]
        calc
          _ ≤ (Lexer.takeWhile Lexer.isAsciiHexDigit
                (digit :: tail)).length + 2 +
              ((digit :: tail).length -
                (Lexer.takeWhile Lexer.isAsciiHexDigit
                  (digit :: tail)).length) :=
            Nat.add_le_add_left inductionHypothesis _
          _ = ('0' :: 'x' :: digit :: tail).length :=
            by
              simp only [List.length_cons]
              omega
  | case15 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digit tail pattern notHexDigit digitsChars digits endByte kind
      token notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      simp only [characters] at pattern
      rcases List.cons.inj pattern with ⟨characterEquation, restEquation⟩
      subst character
      subst rest
      have takeBound := takeWhile_length_le Lexer.isAsciiDigit
        ('0' :: 'x' :: digit :: tail)
      simp only [List.length_cons] at takeBound
      simp [characters, digitsChars, digits, endByte, kind, token,
        List.length_drop] at inductionHypothesis
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '0' 'x' (digit :: tail) sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_pos digitStart, if_neg notHexDigit]
        simp [Lexer.addUnits, characters, digitsChars, digits, endByte,
          kind, token, List.length_drop]
        calc
          _ ≤ (Lexer.takeWhile Lexer.isAsciiDigit
                ('0' :: 'x' :: digit :: tail)).length +
              (('0' :: 'x' :: digit :: tail).length -
                (Lexer.takeWhile Lexer.isAsciiDigit
                  ('0' :: 'x' :: digit :: tail)).length) :=
            Nat.add_le_add_left inductionHypothesis _
          _ = ('0' :: 'x' :: digit :: tail).length :=
            Nat.add_sub_of_le takeBound
  | case16 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digitsChars digits endByte kind token notLineComment
      notBlockComment notString notAssembly noHexPattern
      inductionHypothesis =>
      have takeBound := takeWhile_length_le Lexer.isAsciiDigit characters
      simp [characters] at takeBound
      simp [characters, digitsChars, digits, endByte, kind, token,
        List.length_drop] at inductionHypothesis
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone]
            simp only
            rw [dif_neg notLetter, dif_pos digitStart]
            simp [Lexer.addUnits, characters, digitsChars, digits,
              endByte, kind, token, List.length_drop]
            calc
              _ ≤ (Lexer.takeWhile Lexer.isAsciiDigit [character]).length +
                  ([character].length -
                    (Lexer.takeWhile Lexer.isAsciiDigit
                      [character]).length) :=
                Nat.add_le_add_left inductionHypothesis _
              _ = [character].length := Nat.add_sub_of_le takeBound
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone]
            simp only
            rw [dif_neg notLetter, dif_pos digitStart]
            split
            · rename_i digit tail branchEquation
              exact (noHexPattern digit tail (by assumption)).elim
            · simp [Lexer.addUnits, characters, digitsChars, digits,
                endByte, kind, token, List.length_drop]
              calc
                _ ≤ (Lexer.takeWhile Lexer.isAsciiDigit
                      (character :: next :: tail)).length +
                    ((character :: next :: tail).length -
                      (Lexer.takeWhile Lexer.isAsciiDigit
                        (character :: next :: tail)).length) :=
                  Nat.add_le_add_left inductionHypothesis _
                _ = (character :: next :: tail).length :=
                  Nat.add_sub_of_le takeBound
  | case17 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      symbol multiSymbol endByte token sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly inductionHypothesis =>
      simp [endByte, token] at inductionHypothesis
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev commentsRev
        fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, multiSymbol]
        simp [Lexer.addUnits, endByte, token]
        omega
  | case18 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      noMultiSymbol symbol singleSymbol endByte token sufficientAgain
      characters restSufficientAgain pragmaNone notLineComment
      notBlockComment notString notAssembly inductionHypothesis =>
      simp [endByte, token] at inductionHypothesis
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev commentsRev
        fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noMultiSymbol,
          singleSymbol]
        simp [Lexer.addUnits, endByte, token]
        have charged := Nat.add_le_add_left inductionHypothesis 1
        omega
  | case19 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      noMultiSymbol noSingleSymbol sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly =>
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev commentsRev
        fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noMultiSymbol,
          noSingleSymbol]
        simp [Lexer.failedResult]
  | case20 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit sufficient restSufficient symbol
      singleSymbol endByte token sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly inductionHypothesis =>
      simp [endByte, token] at inductionHypothesis
      rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev commentsRev
        fuel character sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, singleSymbol]
        simp [Lexer.addUnits, endByte, token, inductionHypothesis]
  | case21 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit sufficient restSufficient
      noSingleSymbol sufficientAgain characters restSufficientAgain pragmaNone
      notLineComment notBlockComment notString notAssembly =>
      rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev commentsRev
        fuel character sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noSingleSymbol]
        simp [Lexer.failedResult]

private def LexLoopOutcome
    (file : WorkspaceFile)
    (counted : Lexer.CountedResult) : Prop :=
  (∀ lexed, counted.result = .ok lexed →
      lexed.source = file.id ∧
        Lexes file lexed.tokens lexed.comments) ∧
    (∀ diagnostic, counted.result = .error diagnostic →
      LexicalDiagnostic.Applies file diagnostic)

private theorem LexLoopOutcome.addUnits
    {file : WorkspaceFile}
    {counted : Lexer.CountedResult}
    (amount : Nat)
    (outcome : LexLoopOutcome file counted) :
    LexLoopOutcome file (Lexer.addUnits amount counted) := by
  simpa [LexLoopOutcome, Lexer.addUnits] using outcome

private theorem LexLoopOutcome.failed
    {file : WorkspaceFile}
    {diagnostic : LexicalDiagnostic}
    (units : Nat)
    (applies : LexicalDiagnostic.Applies file diagnostic) :
    LexLoopOutcome file (Lexer.failedResult diagnostic units) := by
  constructor
  · intro lexed execution
    simp [Lexer.failedResult] at execution
  · intro emitted execution
    simp [Lexer.failedResult] at execution
    subst emitted
    exact applies

private theorem pendingAfterToken_tokenAt
    (file : WorkspaceFile)
    (startByte endByte : Nat)
    (kind : TokenKind) :
    LexicalJudgment.PendingAfterToken
      (Lexer.tokenAt file startByte endByte kind)
      (Lexer.pendingAfter kind) := by
  cases kind with
  | hardKeyword keyword =>
      cases keyword <;>
        simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
          Lexer.pendingAfter] <;> rfl
  | identifier text =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | pragmaName pragma =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | decimalLiteral spelling digits =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | hexadecimalLiteral spelling digits =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | stringLiteral spelling decoded =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | assemblyBlock slice =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl
  | symbol symbol =>
      simp [LexicalJudgment.PendingAfterToken, Lexer.tokenAt,
        Lexer.pendingAfter] <;> rfl

private theorem byteAt_rangeToEnd_of_notContinuation
    {file : WorkspaceFile}
    {cursor : Nat}
    {byte : UInt8}
    (atCursor : LexicalJudgment.ByteAt file cursor byte)
    (notContinuation : isUtf8ContinuationByte byte = false) :
    LexicalJudgment.SourceRange file cursor
      file.content.utf8ByteSize := by
  have lookup := atCursor
  unfold LexicalJudgment.ByteAt LexicalJudgment.byteAt at lookup
  have arrayBound := (Array.getElem?_eq_some_iff.mp lookup).1
  have bound : cursor < file.content.utf8ByteSize := by
    simpa only [ByteArray.size_data, String.size_toByteArray] using arrayBound
  refine ⟨Nat.le_of_lt bound, Nat.le_refl _, ?_,
    isUtf8Boundary_end file.content⟩
  unfold isUtf8Boundary
  rw [lookup]
  simp [notContinuation]

private def AssemblyStateAnchorsValid
    (file : WorkspaceFile) :
    LexicalJudgment.AssemblyScannerState → Prop
  | .normal _ => True
  | .lineComment _ => True
  | .blockComment _ _ outermostOpen =>
      LexicalJudgment.BytePairAt file outermostOpen 47 42
  | .string _ openQuote =>
      LexicalJudgment.ByteAt file openQuote 34

private theorem assemblyStep_anchorsValid
    {file : WorkspaceFile}
    {state nextState : LexicalJudgment.AssemblyScannerState}
    {cursor next : Nat}
    (valid : AssemblyStateAnchorsValid file state)
    (step : LexicalJudgment.AssemblyStep file state cursor nextState next) :
    AssemblyStateAnchorsValid file nextState := by
  cases step <;> simp_all [AssemblyStateAnchorsValid]

private theorem assemblyRun_anchorsValid
    {file : WorkspaceFile}
    {initialState finalState : LexicalJudgment.AssemblyScannerState}
    {cursor endByte : Nat}
    (valid : AssemblyStateAnchorsValid file initialState)
    (run : LexicalJudgment.AssemblyRun file initialState cursor
      finalState endByte) :
    AssemblyStateAnchorsValid file finalState := by
  induction run with
  | refl => exact valid
  | step state nextState finalState cursor next endByte transition tail
      inductionHypothesis =>
      exact inductionHypothesis
        (assemblyStep_anchorsValid valid transition)

private theorem assemblyFailureApplies
    {file : WorkspaceFile}
    {cursor units : Nat}
    {body : List Char}
    {tokensRev : List Token}
    {commentsRev : List Comment}
    {diagnostic : LexicalDiagnostic}
    (suffix : SuffixAt file cursor ('{' :: body))
    (prior : LexicalJudgment.LexesPrefix file cursor true
      tokensRev.reverse commentsRev.reverse)
    (scanned :
      Lexer.scanAssembly file cursor (.normal 1) (cursor + 1) body =
        .failed diagnostic units) :
    LexicalDiagnostic.Applies file diagnostic := by
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have certified := scanAssembly_certified file cursor (.normal 1)
    (cursor + 1) body (by simp [AssemblyModeValid]) afterOpener
  rw [scanned] at certified
  rcases certified with
    ⟨finalMode, finalValid, run, diagnosticEquation⟩
  have brace : LexicalJudgment.ByteAt file cursor 123 := by
    simpa [LexicalJudgment.ByteAt, utf8FirstByte] using
      suffix.byteAtFirst
  have anchors := assemblyRun_anchorsValid
    (file := file) (by simp [assemblyState, AssemblyStateAnchorsValid]) run
  cases finalMode with
  | normal depth =>
      simp [AssemblyModeValid] at finalValid
      simp [assemblyState, AssemblyFailureDiagnostic] at run diagnosticEquation
      subst diagnostic
      exact LexicalDiagnostic.Applies.unterminatedAssemblyBlock cursor
        tokensRev.reverse commentsRev.reverse prior
        (.normal cursor depth brace finalValid run) suffix.rangeToEnd
  | lineComment depth =>
      simp [AssemblyModeValid] at finalValid
      simp [assemblyState, AssemblyFailureDiagnostic] at run diagnosticEquation
      subst diagnostic
      exact LexicalDiagnostic.Applies.unterminatedAssemblyBlock cursor
        tokensRev.reverse commentsRev.reverse prior
        (.lineComment cursor depth brace finalValid run) suffix.rangeToEnd
  | blockComment braceDepth commentDepth outermostOpen =>
      simp [AssemblyModeValid] at finalValid
      simp [assemblyState, AssemblyFailureDiagnostic,
        AssemblyStateAnchorsValid] at run diagnosticEquation anchors
      subst diagnostic
      have range := byteAt_rangeToEnd_of_notContinuation anchors.1
        (by decide)
      exact LexicalDiagnostic.Applies.unterminatedAssemblyComment cursor
        outermostOpen tokensRev.reverse commentsRev.reverse prior
        ⟨brace, braceDepth, commentDepth, finalValid.1, finalValid.2, run⟩
        range
  | string depth openQuote =>
      simp [AssemblyModeValid] at finalValid
      simp [assemblyState, AssemblyFailureDiagnostic,
        AssemblyStateAnchorsValid] at run diagnosticEquation anchors
      subst diagnostic
      have range := byteAt_rangeToEnd_of_notContinuation anchors
        (by decide)
      exact LexicalDiagnostic.Applies.unterminatedAssemblyString cursor
        openQuote tokensRev.reverse commentsRev.reverse prior
        ⟨brace, depth, finalValid, run⟩ range

set_option linter.unusedSimpArgs false in
private theorem lexLoop_certified
    (file : WorkspaceFile)
    (fuel cursor : Nat)
    (characters : List Char)
    (pendingAssembly : Bool)
    (tokensRev : List Token)
    (commentsRev : List Comment)
    (sufficient : characters.length < fuel) :
    ∀ (_ : SuffixAt file cursor characters)
      (_ : LexicalJudgment.LexesPrefix file cursor pendingAssembly
        tokensRev.reverse commentsRev.reverse),
      LexLoopOutcome file
        (Lexer.lexLoop file fuel cursor characters pendingAssembly
          tokensRev commentsRev sufficient) := by
  induction fuel, cursor, characters, pendingAssembly, tokensRev,
      commentsRev, sufficient using Lexer.lexLoop.induct file with
  | case1 cursor fuel pendingAssembly tokensRev commentsRev sufficient =>
      intro suffix prior
      constructor
      · intro lexed execution
        simp [Lexer.lexLoop.eq_2, Lexer.successfulResult] at execution
        subst lexed
        refine ⟨rfl, .complete file tokensRev.reverse commentsRev.reverse
          pendingAssembly ?_⟩
        have cursorEquation : cursor = file.content.utf8ByteSize := by
          have size := suffix.remainingByteSize
          simpa [Lexer.byteSize] using size.symm
        simpa [cursorEquation] using prior
      · intro diagnostic execution
        simp [Lexer.lexLoop.eq_2, Lexer.successfulResult] at execution
  | case2 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient restSufficient whitespace inductionHypothesis =>
      intro suffix prior
      have nextSuffix := suffix.advanceOne
      have recognized :
          LexicalJudgment.WhitespaceAt file cursor
            (cursor + character.utf8Size) :=
        ⟨character, suffix.scalarAt,
          (isWhitespace_eq_true_iff character).mp whitespace⟩
      have nextPrior := LexicalJudgment.LexesPrefix.whitespace
        cursor (cursor + character.utf8Size) pendingAssembly
        tokensRev.reverse commentsRev.reverse prior recognized
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_pos whitespace]
          exact nextOutcome.addUnits 1
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_pos whitespace]
          exact nextOutcome.addUnits 1
  | case3 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      scanned comment inductionHypothesis =>
      intro suffix prior
      change character :: rest = '/' :: '/' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      simp only [characters, scanned, comment, List.drop_succ_cons]
        at inductionHypothesis
      have winner := lineCommentCandidateWins
        (pendingAssembly := pendingAssembly) suffix
      have nextSuffix := lineCommentNextSuffix suffix
      have nextPriorRaw := LexicalJudgment.LexesPrefix.comment cursor
        pendingAssembly tokensRev.reverse commentsRev.reverse comment prior
        winner
      have nextPrior :
          LexicalJudgment.LexesPrefix file
            (Lexer.scanLineComment (cursor + 2) body).endByte
            pendingAssembly tokensRev.reverse
            (comment :: commentsRev).reverse := by
        simpa [comment, Lexer.commentAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '/' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simpa [characters, scanned, comment, List.drop_succ_cons] using
        nextOutcome.addUnits
          ((Lexer.scanLineComment (cursor + 2) body).units + 1)
  | case4 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      units scanEquation =>
      intro suffix prior
      change character :: rest = '/' :: '*' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have recognized := unterminatedBlockCommentRecognized suffix
        scanEquation
      have applies := LexicalDiagnostic.Applies.unterminatedBlockComment
        cursor pendingAssembly tokensRev.reverse commentsRev.reverse prior
        recognized suffix.rangeToEnd
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '*' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simpa [scanEquation, Lexer.sourceSpan,
        LexicalJudgment.sourceSpan] using
        LexLoopOutcome.failed (file := file) (units + 1) applies
  | case5 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      endByte consumed units scanEquation comment inductionHypothesis =>
      intro suffix prior
      change character :: rest = '/' :: '*' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      simp only [characters, comment, List.drop_succ_cons]
        at inductionHypothesis
      have winner := blockCommentCandidateWins
        (pendingAssembly := pendingAssembly) suffix scanEquation
      have nextSuffix := blockCommentNextSuffix suffix scanEquation
      have nextPriorRaw := LexicalJudgment.LexesPrefix.comment cursor
        pendingAssembly tokensRev.reverse commentsRev.reverse comment prior
        winner
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte pendingAssembly
            tokensRev.reverse (comment :: commentsRev).reverse := by
        simpa [comment, Lexer.commentAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '/' '*' body sufficient restSufficient]
      rw [dif_neg notWhitespace]
      simpa [characters, scanEquation, comment, List.drop_succ_cons] using
        nextOutcome.addUnits (units + 1)
  | case6 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      diagnostic units scanEquation =>
      intro suffix prior
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      rcases invalidStringRecognized suffix scanEquation with
        ⟨escapeStart, escapeEnd, escaped, quote, validPrefix,
          invalidEscape, range, diagnosticEquation⟩
      subst diagnostic
      have applies := LexicalDiagnostic.Applies.invalidStringEscape
        cursor escapeStart escapeEnd pendingAssembly tokensRev.reverse
        commentsRev.reverse escaped prior quote validPrefix invalidEscape range
      cases body with
      | nil => simp [Lexer.scanString] at scanEquation
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [scanEquation, Lexer.sourceSpan,
            LexicalJudgment.sourceSpan] using
            LexLoopOutcome.failed (file := file) (units + 1) applies
  | case7 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      units scanEquation =>
      intro suffix prior
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      rcases unterminatedStringRecognized suffix scanEquation with
        ⟨quote, validToEnd⟩
      have applies := LexicalDiagnostic.Applies.unterminatedString cursor
        pendingAssembly tokensRev.reverse commentsRev.reverse prior quote
        validToEnd suffix.rangeToEnd
      cases body with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [scanEquation, Lexer.sourceSpan,
            LexicalJudgment.sourceSpan] using
            LexLoopOutcome.failed (file := file) (units + 1) applies
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [scanEquation, Lexer.sourceSpan,
            LexicalJudgment.sourceSpan] using
            LexLoopOutcome.failed (file := file) (units + 1) applies
  | case8 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      endByte consumed decoded units scanEquation total spelling kind token
      inductionHypothesis =>
      intro suffix prior
      change character :: rest = '"' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      cases body with
      | nil => simp [Lexer.scanString] at scanEquation
      | cons next tail =>
          simp [characters, total, spelling, kind, token,
            List.length_drop] at inductionHypothesis
          have winner := stringCandidateWins
            (pendingAssembly := pendingAssembly) suffix scanEquation
          have nextSuffix := stringNextSuffix suffix scanEquation
          have nextState :
              LexicalJudgment.PendingAfterToken token false := by
            right
            constructor
            · simp [token, kind, Lexer.tokenAt]
            · rfl
          have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
            pendingAssembly false tokensRev.reverse commentsRev.reverse
            .string token prior winner nextState
          have nextPrior :
              LexicalJudgment.LexesPrefix file endByte false
                (tokensRev.reverse ++
                  [Lexer.tokenAt file cursor endByte
                    (.stringLiteral
                      ("\"" ++ String.ofList
                        (List.take consumed (next :: tail))) decoded)])
                commentsRev.reverse := by
            simpa [characters, total, spelling, kind, token, Lexer.tokenAt,
              Lexer.sourceSpan] using nextPriorRaw
          have nextOutcome := inductionHypothesis nextSuffix nextPrior
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel '"' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [characters, scanEquation, total, spelling, kind, token,
            List.length_drop] using
            nextOutcome.addUnits (units + 1)
  | case9 fuel cursor character rest tokensRev commentsRev sufficient
      characters restSufficient notWhitespace body equation diagnostic units
      scanEquation =>
      intro suffix prior
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have applies := assemblyFailureApplies suffix prior scanEquation
      cases body with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor true tokensRev commentsRev
            fuel '{' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [scanEquation] using
            LexLoopOutcome.failed (file := file) (units + 1) applies
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor true tokensRev commentsRev
            fuel '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [scanEquation] using
            LexLoopOutcome.failed (file := file) (units + 1) applies
  | case10 fuel cursor character rest tokensRev commentsRev sufficient
      characters restSufficient notWhitespace body equation closeByte endByte
      consumed units scanEquation outer slice token inductionHypothesis =>
      intro suffix prior
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      cases body with
      | nil => simp [Lexer.scanAssembly] at scanEquation
      | cons next tail =>
          have recognized := assemblyTokenRecognized suffix scanEquation
          have nextSuffix := assemblyNextSuffix suffix scanEquation
          have nextPriorRaw :=
            LexicalJudgment.LexesPrefix.assemblyBlock cursor endByte
              tokensRev.reverse commentsRev.reverse token prior recognized
          have nextPrior :
              LexicalJudgment.LexesPrefix file endByte false
                (token :: tokensRev).reverse commentsRev.reverse := by
            simpa [token, Lexer.tokenAt, Lexer.sourceSpan] using nextPriorRaw
          have nextOutcome := inductionHypothesis nextSuffix nextPrior
          rw [Lexer.lexLoop.eq_3 file cursor true tokensRev commentsRev fuel
            '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [characters, scanEquation, outer, slice, token,
            List.drop_succ_cons] using nextOutcome.addUnits (units + 1)
  | case11 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace body equation
      notPending endByte token inductionHypothesis =>
      intro suffix prior
      change character :: rest = '{' :: body at equation
      rcases List.cons.inj equation with ⟨headEquation, tailEquation⟩
      subst character
      subst rest
      have pendingEquation : pendingAssembly = false := by
        cases pendingAssembly <;> simp_all
      subst pendingAssembly
      have notLineComment :
          ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
        intro pair
        have first := suffix.character_eq_of_byteAtAscii pair.1
          (expected := '/') (by decide)
        contradiction
      have notBlockComment :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        have first := suffix.character_eq_of_byteAtAscii pair.1
          (expected := '/') (by decide)
        contradiction
      have winner := singleSymbolCandidateWins
        (file := file) (cursor := cursor) (pendingAssembly := false)
        (character := '{') (rest := body) (symbol := .leftBrace) suffix
        (by decide : Lexer.isAsciiLetter '{' = false)
        (by decide : Lexer.isAsciiDigit '{' = false)
        notLineComment notBlockComment
        (by intro next tail decomposition; rfl)
        (by rfl : Lexer.singleSymbol? '{' = some .leftBrace)
        (by intro impossible; contradiction)
      have nextSuffix := suffix.advanceOne
      have braceSize : '{'.utf8Size = 1 := by decide
      rw [braceSize] at nextSuffix
      have nextState : LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [endByte, token, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor false
        false tokensRev.reverse commentsRev.reverse .singleCharacterSymbol
        token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file (cursor + 1) false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [endByte, token, Lexer.tokenAt, Lexer.sourceSpan] using
          nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      cases body with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor false tokensRev commentsRev
            fuel '{' sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [endByte, token] using nextOutcome.addUnits 1
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor false tokensRev commentsRev fuel
            '{' next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          simpa [endByte, token] using nextOutcome.addUnits 1
  | case12 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace kind matched count
      endByte token notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      intro suffix prior
      have winner := pragmaCandidateWins
        (pendingAssembly := pendingAssembly) suffix matched
      have nextSuffix := pragmaNextSuffix suffix matched
      have nextState : LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [endByte, token, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .pragmaName token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file
            (cursor + kind.spelling.utf8ByteSize) false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [endByte, token, Lexer.tokenAt, Lexer.sourceSpan] using
          nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [matched]
            simpa [characters, count, endByte, token] using
              nextOutcome.addUnits kind.spelling.toList.length
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [matched]
            simpa [characters, count, endByte, token] using
              nextOutcome.addUnits kind.spelling.toList.length
  | case13 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone letter
      spellingChars text endByte kind token notLineComment notBlockComment
      notString notAssembly inductionHypothesis =>
      intro suffix prior
      have winner := identifierCandidateWins
        (pendingAssembly := pendingAssembly) suffix letter pragmaNone
      have nextSuffix := takeWhileNextSuffix suffix
        Lexer.isIdentifierContinue
      have nextState := pendingAfterToken_tokenAt file cursor endByte kind
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly (Lexer.pendingAfter kind) tokensRev.reverse
        commentsRev.reverse .identifier token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte (Lexer.pendingAfter kind)
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [token, Lexer.tokenAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone, dif_pos letter]
            simpa [characters, spellingChars, text, endByte, kind, token] using
              nextOutcome.addUnits
                (Lexer.takeWhile Lexer.isIdentifierContinue [character]).length
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone, dif_pos letter]
            simpa [characters, spellingChars, text, endByte, kind, token] using
              nextOutcome.addUnits
                (Lexer.takeWhile Lexer.isIdentifierContinue
                  (character :: next :: tail)).length
  | case14 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digit tail pattern hexDigit digitsChars digits spelling count
      endByte kind token notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      intro suffix prior
      simp only [characters] at pattern
      rcases List.cons.inj pattern with ⟨characterEquation, restEquation⟩
      subst character
      subst rest
      have winner := hexadecimalCandidateWins
        (pendingAssembly := pendingAssembly) suffix hexDigit
      have nextSuffix := hexadecimalNextSuffix suffix
      have nextState : LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, kind, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .numericLiteral token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [token, Lexer.tokenAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '0' 'x' (digit :: tail) sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_pos digitStart, if_pos hexDigit]
        simpa [characters, digitsChars, digits, spelling, count, endByte,
          kind, token] using
          nextOutcome.addUnits
            ((Lexer.takeWhile Lexer.isAsciiHexDigit
              (digit :: tail)).length + 2)
  | case15 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digit tail pattern notHexDigit digitsChars digits endByte kind
      token notLineComment notBlockComment notString notAssembly
      inductionHypothesis =>
      intro suffix prior
      simp only [characters] at pattern
      rcases List.cons.inj pattern with ⟨characterEquation, restEquation⟩
      subst character
      subst rest
      have noHexadecimal :
          ¬ ∃ otherDigit otherTail,
            '0' :: 'x' :: digit :: tail =
                '0' :: 'x' :: otherDigit :: otherTail ∧
              Lexer.isAsciiHexDigit otherDigit = true := by
        rintro ⟨otherDigit, otherTail, decomposition, accepted⟩
        have equality : digit :: tail = otherDigit :: otherTail := by
          simpa using List.cons.inj decomposition |>.2
        rcases List.cons.inj equality with ⟨digitEquation, tailEquation⟩
        subst otherDigit
        exact notHexDigit accepted
      have winner := decimalCandidateWins
        (pendingAssembly := pendingAssembly) suffix digitStart noHexadecimal
      have nextSuffix := takeWhileNextSuffix suffix Lexer.isAsciiDigit
      have nextState : LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, kind, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .numericLiteral token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [token, Lexer.tokenAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel '0' 'x' (digit :: tail) sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_pos digitStart, if_neg notHexDigit]
        simpa [characters, digitsChars, digits, endByte, kind, token] using
          nextOutcome.addUnits
            (Lexer.takeWhile Lexer.isAsciiDigit
              ('0' :: 'x' :: digit :: tail)).length
  | case16 fuel cursor character rest pendingAssembly tokensRev commentsRev
      sufficient characters restSufficient notWhitespace pragmaNone notLetter
      digitStart digitsChars digits endByte kind token notLineComment
      notBlockComment notString notAssembly noHexPattern
      inductionHypothesis =>
      intro suffix prior
      have noHexadecimal :
          ¬ ∃ digit tail,
            character :: rest = '0' :: 'x' :: digit :: tail ∧
              Lexer.isAsciiHexDigit digit = true := by
        rintro ⟨digit, tail, decomposition, accepted⟩
        exact noHexPattern digit tail decomposition
      have winner := decimalCandidateWins
        (pendingAssembly := pendingAssembly) suffix digitStart noHexadecimal
      have nextSuffix := takeWhileNextSuffix suffix Lexer.isAsciiDigit
      have nextState : LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, kind, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .numericLiteral token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [token, Lexer.tokenAt, Lexer.sourceSpan] using nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      cases rest with
      | nil =>
          rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
            commentsRev fuel character sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone]
            simp only
            rw [dif_neg notLetter, dif_pos digitStart]
            simpa [characters, digitsChars, digits, endByte, kind, token] using
              nextOutcome.addUnits
                (Lexer.takeWhile Lexer.isAsciiDigit [character]).length
      | cons next tail =>
          rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
            commentsRev fuel character next tail sufficient restSufficient]
          rw [dif_neg notWhitespace]
          split
          · rename_i body branchEquation
            exact (notLineComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notBlockComment body (by assumption)).elim
          · rename_i body branchEquation
            exact (notString body (by assumption)).elim
          · rename_i body branchEquation
            exact (notAssembly body (by assumption)).elim
          · rw [pragmaNone]
            simp only
            rw [dif_neg notLetter, dif_pos digitStart]
            split
            · rename_i digit tail branchEquation
              exact (noHexPattern digit tail (by assumption)).elim
            · simpa [characters, digitsChars, digits, endByte, kind, token]
                using nextOutcome.addUnits
                  (Lexer.takeWhile Lexer.isAsciiDigit
                    (character :: next :: tail)).length
  | case17 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      symbol multiSymbol endByte token sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly inductionHypothesis =>
      intro suffix prior
      have winner := multiSymbolCandidateWins
        (pendingAssembly := pendingAssembly) suffix multiSymbol
      have nextSuffix := multiSymbol_nextSuffix suffix multiSymbol
      have nextState :
          LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .multiCharacterSymbol token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [endByte, token, Lexer.tokenAt, Lexer.sourceSpan] using
          nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, multiSymbol]
        simpa [endByte, token] using nextOutcome.addUnits 1
  | case18 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      noMultiSymbol symbol singleSymbol endByte token sufficientAgain
      characters restSufficientAgain pragmaNone notLineComment
      notBlockComment notString notAssembly inductionHypothesis =>
      intro suffix prior
      have notLinePair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨remaining, firstEquation, restEquation⟩
        subst character
        rcases List.cons.inj restEquation with
          ⟨nextEquation, tailEquation⟩
        subst next
        exact notLineComment tail rfl
      have notBlockPair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨remaining, firstEquation, restEquation⟩
        subst character
        rcases List.cons.inj restEquation with
          ⟨nextEquation, tailEquation⟩
        subst next
        exact notBlockComment tail rfl
      have noMulti :
          ∀ otherNext otherTail,
            next :: tail = otherNext :: otherTail →
              Lexer.multiSymbol? character otherNext = none := by
        intro otherNext otherTail decomposition
        rcases List.cons.inj decomposition with
          ⟨headEquation, tailEquation⟩
        subst otherNext
        exact noMultiSymbol
      have assemblyGuard :
          pendingAssembly = true → symbol ≠ .leftBrace := by
        intro pendingTrue symbolEquation
        subst symbol
        have spelling := (singleSymbol_sound singleSymbol).1
        simp [Symbol.spelling] at spelling
        subst character
        exact notAssembly (next :: tail) rfl
      have notLetterFalse : Lexer.isAsciiLetter character = false :=
        Bool.eq_false_iff.mpr notLetter
      have notDigitFalse : Lexer.isAsciiDigit character = false :=
        Bool.eq_false_iff.mpr notDigit
      have winner := singleSymbolCandidateWins
        (pendingAssembly := pendingAssembly) suffix notLetterFalse
        notDigitFalse
        notLinePair notBlockPair noMulti singleSymbol assemblyGuard
      have nextSuffix := singleSymbol_nextSuffix suffix singleSymbol
      have nextState :
          LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .singleCharacterSymbol token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [endByte, token, Lexer.tokenAt, Lexer.sourceSpan] using
          nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noMultiSymbol,
          singleSymbol]
        simpa [endByte, token] using nextOutcome.addUnits 1
  | case19 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit next tail sufficient restSufficient
      noMultiSymbol noSingleSymbol sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly =>
      intro suffix prior
      have notQuote : character ≠ '"' := by
        intro characterEquation
        subst character
        exact notString (next :: tail) rfl
      have invalid := invalidLexemeStart notWhitespace notLetter notDigit
        notQuote noSingleSymbol
      have applies := LexicalDiagnostic.Applies.invalidCharacter cursor
        (cursor + character.utf8Size) pendingAssembly tokensRev.reverse
        commentsRev.reverse character prior suffix.scalarAt invalid
      rw [Lexer.lexLoop.eq_3 file cursor pendingAssembly tokensRev
        commentsRev fuel character next tail sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noMultiSymbol,
          noSingleSymbol]
        simpa [Lexer.sourceSpan, LexicalJudgment.sourceSpan] using
          LexLoopOutcome.failed (file := file) 1 applies
  | case20 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit sufficient restSufficient symbol
      singleSymbol endByte token sufficientAgain characters
      restSufficientAgain pragmaNone notLineComment notBlockComment notString
      notAssembly inductionHypothesis =>
      intro suffix prior
      have notLinePair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '/') pair
            (by decide) (by decide) (by decide) with
          ⟨remaining, firstEquation, restEquation⟩
        simp at restEquation
      have notBlockPair :
          ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
        intro pair
        rcases suffix.pair_eq_of_bytePairAscii
            (first := '/') (second := '*') pair
            (by decide) (by decide) (by decide) with
          ⟨remaining, firstEquation, restEquation⟩
        simp at restEquation
      have noMulti :
          ∀ next tail,
            ([] : List Char) = next :: tail →
              Lexer.multiSymbol? character next = none := by
        intro next tail decomposition
        simp at decomposition
      have assemblyGuard :
          pendingAssembly = true → symbol ≠ .leftBrace := by
        intro pendingTrue symbolEquation
        subst symbol
        have spelling := (singleSymbol_sound singleSymbol).1
        simp [Symbol.spelling] at spelling
        subst character
        exact notAssembly [] rfl
      have notLetterFalse : Lexer.isAsciiLetter character = false :=
        Bool.eq_false_iff.mpr notLetter
      have notDigitFalse : Lexer.isAsciiDigit character = false :=
        Bool.eq_false_iff.mpr notDigit
      have winner := singleSymbolCandidateWins
        (pendingAssembly := pendingAssembly) suffix notLetterFalse
        notDigitFalse notLinePair notBlockPair noMulti singleSymbol
        assemblyGuard
      have nextSuffix := singleSymbol_nextSuffix suffix singleSymbol
      have nextState :
          LexicalJudgment.PendingAfterToken token false := by
        right
        exact ⟨by simp [token, Lexer.tokenAt], rfl⟩
      have nextPriorRaw := LexicalJudgment.LexesPrefix.token cursor
        pendingAssembly false tokensRev.reverse commentsRev.reverse
        .singleCharacterSymbol token prior winner nextState
      have nextPrior :
          LexicalJudgment.LexesPrefix file endByte false
            (token :: tokensRev).reverse commentsRev.reverse := by
        simpa [endByte, token, Lexer.tokenAt, Lexer.sourceSpan] using
          nextPriorRaw
      have nextOutcome := inductionHypothesis nextSuffix nextPrior
      rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
        commentsRev fuel character sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, singleSymbol]
        simpa [endByte, token] using nextOutcome.addUnits 1
  | case21 fuel cursor character pendingAssembly tokensRev commentsRev
      notWhitespace notLetter notDigit sufficient restSufficient
      noSingleSymbol sufficientAgain characters restSufficientAgain pragmaNone
      notLineComment notBlockComment notString notAssembly =>
      intro suffix prior
      have notQuote : character ≠ '"' := by
        intro characterEquation
        subst character
        exact notString [] rfl
      have invalid := invalidLexemeStart notWhitespace notLetter notDigit
        notQuote noSingleSymbol
      have applies := LexicalDiagnostic.Applies.invalidCharacter cursor
        (cursor + character.utf8Size) pendingAssembly tokensRev.reverse
        commentsRev.reverse character prior suffix.scalarAt invalid
      rw [Lexer.lexLoop.eq_4 file cursor pendingAssembly tokensRev
        commentsRev fuel character sufficient restSufficient]
      rw [dif_neg notWhitespace]
      split
      · rename_i body branchEquation
        exact (notLineComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notBlockComment body (by assumption)).elim
      · rename_i body branchEquation
        exact (notString body (by assumption)).elim
      · rename_i body branchEquation
        exact (notAssembly body (by assumption)).elim
      · rw [pragmaNone]
        simp only
        rw [dif_neg notLetter, dif_neg notDigit, noSingleSymbol]
        simpa [Lexer.sourceSpan, LexicalJudgment.sourceSpan] using
          LexLoopOutcome.failed (file := file) 1 applies

/-- Successful executor output satisfies the independent lexical judgment. -/
theorem lexer_sound
    {file : WorkspaceFile}
    {lexed : LexedModule}
    (execution : lexModule file = .ok lexed) :
    lexed.source = file.id ∧ Lexes file lexed.tokens lexed.comments := by
  have certified := lexLoop_certified file
    (file.content.toList.length + 1) 0 file.content.toList false [] []
    (by omega) (SuffixAt.initial file) LexicalJudgment.LexesPrefix.start
  exact certified.1 lexed (by
    simpa [lexModule, lexModuleWithUnits, Lexer.execute] using execution)

/-- Every executor failure satisfies its independent diagnostic judgment. -/
theorem lexical_diagnostic_sound
    {file : WorkspaceFile}
    {diagnostic : LexicalDiagnostic}
    (execution : lexModule file = .error diagnostic) :
    LexicalDiagnostic.Applies file diagnostic := by
  have certified := lexLoop_certified file
    (file.content.toList.length + 1) 0 file.content.toList false [] []
    (by omega) (SuffixAt.initial file) LexicalJudgment.LexesPrefix.start
  exact certified.2 diagnostic (by
    simpa [lexModule, lexModuleWithUnits, Lexer.execute] using execution)

private theorem assemblyTokenAt_startByte
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {token : Token}
    (recognized :
      LexicalJudgment.AssemblyTokenAt file cursor endByte token) :
    token.span.startByte = cursor := by
  rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
  subst token
  rfl

private theorem lexesPrefix_retainedTransitions
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    (partition : LexicalJudgment.LexesPrefix file cursor pendingAssembly
      tokens comments) :
    (∀ token ∈ tokens,
      (∃ pendingAssembly candidateClass,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          token.span.startByte (.token candidateClass token)) ∨
      (∃ endByte,
        LexicalJudgment.AssemblyTokenAt file token.span.startByte
          endByte token)) ∧
    (∀ comment ∈ comments,
      ∃ pendingAssembly,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          comment.span.startByte (.comment comment)) := by
  induction partition with
  | start => simp
  | whitespace cursor next pendingAssembly tokens comments prior
      whitespace inductionHypothesis =>
      exact inductionHypothesis
  | comment cursor pendingAssembly tokens comments comment prior winner
      inductionHypothesis =>
      constructor
      · exact inductionHypothesis.1
      · intro retained membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with old | equality
        · exact inductionHypothesis.2 retained old
        · subst retained
          refine ⟨pendingAssembly, ?_⟩
          have start := candidateAt_startByte winner.1
          simp only [LexicalJudgment.Candidate.span] at start
          rw [start]
          exact winner
  | token cursor pendingAssembly nextPending tokens comments candidateClass
      token prior winner nextState inductionHypothesis =>
      constructor
      · intro retained membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with old | equality
        · exact inductionHypothesis.1 retained old
        · subst retained
          left
          refine ⟨pendingAssembly, candidateClass, ?_⟩
          have start := candidateAt_startByte winner.1
          simp only [LexicalJudgment.Candidate.span] at start
          rw [start]
          exact winner
      · exact inductionHypothesis.2
  | assemblyBlock cursor endByte tokens comments token prior recognized
      inductionHypothesis =>
      constructor
      · intro retained membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with old | equality
        · exact inductionHypothesis.1 retained old
        · subst retained
          right
          refine ⟨endByte, ?_⟩
          have start := assemblyTokenAt_startByte recognized
          rw [start]
          exact recognized
      · exact inductionHypothesis.2

/-- Executor output retains exactly maximal normal candidates or assembly scans. -/
theorem lexer_maximal_munch
    {file : WorkspaceFile}
    {lexed : LexedModule}
    (execution : lexModule file = .ok lexed) :
    (∀ token ∈ lexed.tokens,
      (∃ pendingAssembly candidateClass,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          token.span.startByte (.token candidateClass token)) ∨
      (∃ endByte,
        LexicalJudgment.AssemblyTokenAt file token.span.startByte
          endByte token)) ∧
    (∀ comment ∈ lexed.comments,
      ∃ pendingAssembly,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          comment.span.startByte (.comment comment)) := by
  rcases lexer_sound execution with ⟨source, lexical⟩
  rcases lexical with ⟨pendingAssembly, partition⟩
  exact lexesPrefix_retainedTransitions partition

/-- Successful lexer output supplies the parser's token-ownership premise
without an additional caller proof. -/
theorem lexer_tokensOwnedBy
    {file : WorkspaceFile}
    {lexed : LexedModule}
    (execution : lexModule file = .ok lexed) :
    TokensOwnedBy file lexed.tokens := by
  intro token member
  rcases (lexer_maximal_munch execution).1 token member with
      normal | assembly
  · rcases normal with ⟨pendingAssembly, candidateClass, winner⟩
    simpa [LexicalJudgment.Candidate.span] using
      candidateAt_span_valid winner.1
  · rcases assembly with ⟨endByte, recognized⟩
    exact assemblyTokenAt_span_valid recognized

/-- Retained token spans occur in source order and never overlap. -/
def TokenSpansOrdered (tokens : List Token) : Prop :=
  tokens.Pairwise
    (fun left right => left.span.endByte ≤ right.span.startByte)

private theorem assemblyTokenAt_endByte
    {file : WorkspaceFile}
    {startByte endByte : Nat}
    {token : Token}
    (recognized :
      LexicalJudgment.AssemblyTokenAt file startByte endByte token) :
    token.span.endByte = endByte := by
  rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
  subst token
  rfl

private theorem lexesPrefix_tokenSpansOrdered
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    (partition : LexicalJudgment.LexesPrefix file cursor pendingAssembly
      tokens comments) :
    TokenSpansOrdered tokens ∧
      ∀ token ∈ tokens, token.span.endByte ≤ cursor := by
  induction partition with
  | start => simp [TokenSpansOrdered]
  | whitespace cursor next pendingAssembly tokens comments prior recognized
      inductionHypothesis =>
      refine ⟨inductionHypothesis.1, ?_⟩
      intro token member
      exact Nat.le_trans (inductionHypothesis.2 token member)
        (Nat.le_of_lt ((lexer_progress file).1 recognized))
  | comment cursor pendingAssembly tokens comments comment prior winner
      inductionHypothesis =>
      refine ⟨inductionHypothesis.1, ?_⟩
      intro token member
      have progress := (lexer_progress file).2.1 winner.1
      simp only [LexicalJudgment.Candidate.span] at progress
      exact Nat.le_trans (inductionHypothesis.2 token member)
        (Nat.le_of_lt progress)
  | token cursor pendingAssembly nextPending tokens comments candidateClass
      token prior winner nextState inductionHypothesis =>
      have start := candidateAt_startByte winner.1
      simp only [LexicalJudgment.Candidate.span] at start
      have progress := (lexer_progress file).2.1 winner.1
      simp only [LexicalJudgment.Candidate.span] at progress
      constructor
      · rw [TokenSpansOrdered, List.pairwise_append]
        refine ⟨inductionHypothesis.1,
          List.pairwise_singleton _ _, ?_⟩
        intro earlier earlierMember later laterMember
        simp only [List.mem_singleton] at laterMember
        subst later
        calc
          earlier.span.endByte ≤ cursor :=
            inductionHypothesis.2 earlier earlierMember
          _ = token.span.startByte := start.symm
      · intro retained member
        rw [List.mem_append] at member
        rcases member with earlierMember | addedMember
        · exact Nat.le_trans
            (inductionHypothesis.2 retained earlierMember)
            (Nat.le_of_lt progress)
        · simp only [List.mem_singleton] at addedMember
          subst retained
          exact Nat.le_refl _
  | assemblyBlock cursor endByte tokens comments token prior recognized
      inductionHypothesis =>
      have start := assemblyTokenAt_startByte recognized
      have finish := assemblyTokenAt_endByte recognized
      have progress := (lexer_progress file).2.2 recognized
      constructor
      · rw [TokenSpansOrdered, List.pairwise_append]
        refine ⟨inductionHypothesis.1,
          List.pairwise_singleton _ _, ?_⟩
        intro earlier earlierMember later laterMember
        simp only [List.mem_singleton] at laterMember
        subst later
        calc
          earlier.span.endByte ≤ cursor :=
            inductionHypothesis.2 earlier earlierMember
          _ = token.span.startByte := start.symm
      · intro retained member
        rw [List.mem_append] at member
        rcases member with earlierMember | addedMember
        · exact Nat.le_trans
            (inductionHypothesis.2 retained earlierMember)
            (Nat.le_of_lt progress)
        · simp only [List.mem_singleton] at addedMember
          subst retained
          exact Nat.le_of_eq finish

namespace Lexes

/-- A successful lexical partition exposes the exact recognition transition
that retained every token and comment. -/
theorem retainedTransitions
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    (∀ token ∈ tokens,
      (∃ pendingAssembly candidateClass,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          token.span.startByte (.token candidateClass token)) ∨
      (∃ endByte,
        LexicalJudgment.AssemblyTokenAt file token.span.startByte
          endByte token)) ∧
    (∀ comment ∈ comments,
      ∃ pendingAssembly,
        LexicalJudgment.CandidateWinsAt file pendingAssembly
          comment.span.startByte (.comment comment)) := by
  cases lexical with
  | complete pendingAssembly partition =>
      exact lexesPrefix_retainedTransitions partition

/-- Every token retained by a successful lexical partition is owned by its
input file. -/
theorem tokensOwnedBy
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    TokensOwnedBy file tokens := by
  intro token member
  rcases (retainedTransitions lexical).1 token member with normal | assembly
  · rcases normal with ⟨pendingAssembly, candidateClass, winner⟩
    simpa [LexicalJudgment.Candidate.span] using
      candidateAt_span_valid winner.1
  · rcases assembly with ⟨endByte, recognized⟩
    exact assemblyTokenAt_span_valid recognized

/-- A successful lexical partition retains tokens in nonoverlapping source
order. -/
theorem tokenSpansOrdered
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    TokenSpansOrdered tokens := by
  cases lexical with
  | complete pendingAssembly partition =>
      exact (lexesPrefix_tokenSpansOrdered partition).1

end Lexes

private theorem byteAt_functional
    {file : WorkspaceFile}
    {cursor : Nat}
    {first second : UInt8}
    (firstAt : LexicalJudgment.ByteAt file cursor first)
    (secondAt : LexicalJudgment.ByteAt file cursor second) :
    first = second := by
  unfold LexicalJudgment.ByteAt at firstAt secondAt
  rw [firstAt] at secondAt
  exact Option.some.inj secondAt

private theorem scalarAt_functional_of_suffix
    {file : WorkspaceFile}
    {cursor firstNext secondNext : Nat}
    {characters : List Char}
    {firstCharacter secondCharacter : Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.ScalarAt file cursor firstCharacter firstNext)
    (second :
      LexicalJudgment.ScalarAt file cursor secondCharacter secondNext) :
    firstCharacter = secondCharacter ∧ firstNext = secondNext := by
  rcases suffix.scalarAt_decomposition first with
    ⟨firstRemaining, firstDecomposition, firstEnd, firstSuffix⟩
  rcases suffix.scalarAt_decomposition second with
    ⟨secondRemaining, secondDecomposition, secondEnd, secondSuffix⟩
  rw [firstDecomposition] at secondDecomposition
  rcases List.cons.inj secondDecomposition with
    ⟨characterEquation, remainingEquation⟩
  subst secondCharacter
  exact ⟨rfl, by omega⟩

private theorem scalarAt_character_eq_of_byteAtAscii
    {file : WorkspaceFile}
    {cursor next : Nat}
    {characters : List Char}
    {character expected : Char}
    (suffix : SuffixAt file cursor characters)
    (scalar : LexicalJudgment.ScalarAt file cursor character next)
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat expected.toNat))
    (expectedAscii : expected.toNat ≤ 127) :
    character = expected := by
  rcases suffix.characters_eq_cons_of_byteAtAscii byte expectedAscii with
    ⟨expectedRemaining, expectedDecomposition⟩
  rcases suffix.scalarAt_decomposition scalar with
    ⟨scalarRemaining, scalarDecomposition, endEquation, nextSuffix⟩
  rw [expectedDecomposition] at scalarDecomposition
  exact (List.cons.inj scalarDecomposition).1.symm

private theorem suffix_after_backslash
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (backslash : LexicalJudgment.ByteAt file cursor 92) :
    ∃ remaining,
      characters = '\\' :: remaining ∧
        SuffixAt file (cursor + 1) remaining := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '\\') backslash (by decide) with
    ⟨remaining, decomposition⟩
  subst characters
  have advanced := suffix.advanceOne
  have size : '\\'.utf8Size = 1 := by decide
  rw [size] at advanced
  exact ⟨remaining, rfl, advanced⟩

private theorem assemblyStep_functional
    {file : WorkspaceFile}
    {state firstState secondState :
      LexicalJudgment.AssemblyScannerState}
    {cursor firstNext secondNext : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.AssemblyStep file state cursor
      firstState firstNext)
    (second : LexicalJudgment.AssemblyStep file state cursor
      secondState secondNext) :
    firstState = secondState ∧ firstNext = secondNext := by
  cases first <;> cases second <;>
    simp_all [LexicalJudgment.BytePairAt, LexicalJudgment.ByteAt,
      LexicalJudgment.byteAt]
  case normalScalar.normalScalar =>
    exact (scalarAt_functional_of_suffix suffix
      (by assumption) (by assumption)).2
  case lineFeed.lineScalar =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\n') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case lineScalar.lineFeed =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\n') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case lineScalar.lineScalar =>
    exact (scalarAt_functional_of_suffix suffix
      (by assumption) (by assumption)).2
  case blockScalar.blockScalar =>
    exact (scalarAt_functional_of_suffix suffix
      (by assumption) (by assumption)).2
  case closeString.stringScalar =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '"') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case escapedStringScalar.escapedStringScalar =>
    rcases suffix_after_backslash suffix (by assumption) with
      ⟨remaining, decomposition, afterBackslash⟩
    exact (scalarAt_functional_of_suffix afterBackslash
      (by assumption) (by assumption)).2
  case escapedStringScalar.trailingStringBackslash =>
    simp only [LexicalJudgment.ScalarAt, LexicalJudgment.SourceTextAt,
      LexicalJudgment.SourceRange] at *
    omega
  case escapedStringScalar.stringScalar =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\\') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case trailingStringBackslash.escapedStringScalar =>
    simp only [LexicalJudgment.ScalarAt, LexicalJudgment.SourceTextAt,
      LexicalJudgment.SourceRange] at *
    omega
  case trailingStringBackslash.stringScalar =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\\') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case stringScalar.closeString =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '"') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case stringScalar.escapedStringScalar =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\\') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case stringScalar.trailingStringBackslash =>
    have characterEquation := scalarAt_character_eq_of_byteAtAscii
      (expected := '\\') suffix (by assumption) (by assumption) (by decide)
    contradiction
  case stringScalar.stringScalar =>
    exact (scalarAt_functional_of_suffix suffix
      (by assumption) (by assumption)).2

private theorem assemblyStep_nextSuffix
    {file : WorkspaceFile}
    {state nextState : LexicalJudgment.AssemblyScannerState}
    {cursor next : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (step : LexicalJudgment.AssemblyStep file state cursor nextState next) :
    ∃ remaining, SuffixAt file next remaining := by
  cases step with
  | openBrace depth cursor positive brace =>
      rcases suffix.characters_eq_cons_of_byteAtAscii
          (expected := '{') brace (by decide) with ⟨remaining, equation⟩
      subst characters
      have advanced := suffix.advanceOne
      have size : '{'.utf8Size = 1 := by decide
      rw [size] at advanced
      exact ⟨remaining, advanced⟩
  | nestedCloseBrace depth cursor nested brace =>
      rcases suffix.characters_eq_cons_of_byteAtAscii
          (expected := '}') brace (by decide) with ⟨remaining, equation⟩
      subst characters
      have advanced := suffix.advanceOne
      have size : '}'.utf8Size = 1 := by decide
      rw [size] at advanced
      exact ⟨remaining, advanced⟩
  | openLineComment depth cursor positive opener =>
      rcases suffix.characters_eq_pair_of_bytePairAscii opener
          (first := '/') (second := '/') (by decide) (by decide)
          (by decide) with ⟨remaining, equation⟩
      subst characters
      exact ⟨remaining, suffix.advanceTwoAscii (by decide) (by decide)⟩
  | openBlockComment depth cursor positive opener =>
      rcases suffix.characters_eq_pair_of_bytePairAscii opener
          (first := '/') (second := '*') (by decide) (by decide)
          (by decide) with ⟨remaining, equation⟩
      subst characters
      exact ⟨remaining, suffix.advanceTwoAscii (by decide) (by decide)⟩
  | openString depth cursor positive quote =>
      rcases suffix.characters_eq_cons_of_byteAtAscii
          (expected := '"') quote (by decide) with ⟨remaining, equation⟩
      subst characters
      have advanced := suffix.advanceOne
      have size : '"'.utf8Size = 1 := by decide
      rw [size] at advanced
      exact ⟨remaining, advanced⟩
  | normalScalar depth cursor next character positive notOpen notClose
      notQuote notLine notBlock scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, equation, endEquation, advanced⟩
      exact ⟨remaining, advanced⟩

  | lineFeed depth cursor positive feed =>
      rcases suffix.characters_eq_cons_of_byteAtAscii
          (expected := '\n') feed (by decide) with ⟨remaining, equation⟩
      subst characters
      have advanced := suffix.advanceOne
      have size : '\n'.utf8Size = 1 := by decide
      rw [size] at advanced
      exact ⟨remaining, advanced⟩
  | lineScalar depth cursor next character positive notFeed scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, equation, endEquation, advanced⟩
      exact ⟨remaining, advanced⟩
  | nestedBlockOpen braceDepth commentDepth outermostOpen cursor
      bracePositive commentPositive opener =>
      rcases suffix.characters_eq_pair_of_bytePairAscii opener
          (first := '/') (second := '*') (by decide) (by decide)
          (by decide) with ⟨remaining, equation⟩
      subst characters
      exact ⟨remaining, suffix.advanceTwoAscii (by decide) (by decide)⟩
  | nestedBlockClose braceDepth commentDepth outermostOpen cursor
      bracePositive nested closer =>
      rcases suffix.characters_eq_pair_of_bytePairAscii closer
          (first := '*') (second := '/') (by decide) (by decide)
          (by decide) with ⟨remaining, equation⟩
      subst characters
      exact ⟨remaining, suffix.advanceTwoAscii (by decide) (by decide)⟩
  | outerBlockClose braceDepth outermostOpen cursor bracePositive closer =>
      rcases suffix.characters_eq_pair_of_bytePairAscii closer
          (first := '*') (second := '/') (by decide) (by decide)
          (by decide) with ⟨remaining, equation⟩
      subst characters
      exact ⟨remaining, suffix.advanceTwoAscii (by decide) (by decide)⟩
  | blockScalar braceDepth commentDepth outermostOpen cursor next character
      bracePositive commentPositive notOpener notCloser scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, equation, endEquation, advanced⟩
      exact ⟨remaining, advanced⟩
  | closeString depth openQuote cursor positive quote =>
      rcases suffix.characters_eq_cons_of_byteAtAscii
          (expected := '"') quote (by decide) with ⟨remaining, equation⟩
      subst characters
      have advanced := suffix.advanceOne
      have size : '"'.utf8Size = 1 := by decide
      rw [size] at advanced
      exact ⟨remaining, advanced⟩
  | escapedStringScalar depth openQuote cursor next character positive
      backslash escaped =>
      rcases suffix_after_backslash suffix backslash with
        ⟨afterSlash, equation, afterBackslash⟩
      rcases afterBackslash.scalarAt_decomposition escaped with
        ⟨remaining, decomposition, endEquation, advanced⟩
      exact ⟨remaining, advanced⟩
  | trailingStringBackslash depth openQuote cursor positive backslash atEnd =>
      rcases suffix_after_backslash suffix backslash with
        ⟨remaining, equation, afterBackslash⟩
      exact ⟨remaining, afterBackslash⟩
  | stringScalar depth openQuote cursor next character positive notQuote
      notBackslash scalar =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, equation, endEquation, advanced⟩
      exact ⟨remaining, advanced⟩

private theorem assemblyStep_at_outerClose_impossible
    {file : WorkspaceFile}
    {cursor next : Nat}
    {nextState : LexicalJudgment.AssemblyScannerState}
    (closeBrace : LexicalJudgment.ByteAt file cursor 125)
    (step : LexicalJudgment.AssemblyStep file (.normal 1) cursor
      nextState next) : False := by
  cases step <;>
    simp_all [LexicalJudgment.BytePairAt, LexicalJudgment.ByteAt,
      LexicalJudgment.byteAt]

private theorem assemblyRun_functional_of_terminal
    {file : WorkspaceFile}
    {initialState finalState : LexicalJudgment.AssemblyScannerState}
    {cursor firstEnd secondEnd : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.AssemblyRun file initialState cursor
      finalState firstEnd)
    (second : LexicalJudgment.AssemblyRun file initialState cursor
      finalState secondEnd)
    (firstTerminal : ∀ nextState next,
      LexicalJudgment.AssemblyStep file finalState firstEnd
        nextState next → False)
    (secondTerminal : ∀ nextState next,
      LexicalJudgment.AssemblyStep file finalState secondEnd
        nextState next → False) :
    firstEnd = secondEnd := by
  induction first generalizing characters secondEnd with
  | refl state cursor =>
      cases second with
      | refl => rfl
      | step state nextState finalState cursor next endByte transition tail =>
          exact False.elim (firstTerminal _ _ transition)
  | step state nextState finalState cursor next firstEnd transition tail
      inductionHypothesis =>
      cases second with
      | refl =>
          exact False.elim (secondTerminal _ _ transition)
      | step state' nextState' finalState' cursor' next' secondEnd
          transition' tail' =>
          have sameStep := assemblyStep_functional suffix
            transition transition'
          cases sameStep.1
          cases sameStep.2
          rcases assemblyStep_nextSuffix suffix transition with
            ⟨remaining, nextSuffix⟩
          exact inductionHypothesis nextSuffix tail' firstTerminal
            secondTerminal

private theorem assemblyRun_close_functional
    {file : WorkspaceFile}
    {initialState : LexicalJudgment.AssemblyScannerState}
    {cursor firstEnd secondEnd : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.AssemblyRun file initialState cursor
      (.normal 1) firstEnd)
    (second : LexicalJudgment.AssemblyRun file initialState cursor
      (.normal 1) secondEnd)
    (firstClose : LexicalJudgment.ByteAt file firstEnd 125)
    (secondClose : LexicalJudgment.ByteAt file secondEnd 125) :
    firstEnd = secondEnd := by
  apply assemblyRun_functional_of_terminal suffix first second
  · intro nextState next step
    exact assemblyStep_at_outerClose_impossible firstClose step
  · intro nextState next step
    exact assemblyStep_at_outerClose_impossible secondClose step

private theorem assemblyTokenAt_functional_of_suffix
    {file : WorkspaceFile}
    {cursor firstEnd secondEnd : Nat}
    {characters : List Char}
    {firstToken secondToken : Token}
    (suffix : SuffixAt file cursor characters)
    (first :
      LexicalJudgment.AssemblyTokenAt file cursor firstEnd firstToken)
    (second :
      LexicalJudgment.AssemblyTokenAt file cursor secondEnd secondToken) :
    firstEnd = secondEnd ∧ firstToken = secondToken := by
  rcases first with ⟨firstSlice, firstSliceAt, firstTokenEquation⟩
  rcases second with ⟨secondSlice, secondSliceAt, secondTokenEquation⟩
  rcases firstSliceAt with
    ⟨firstBrace, firstClose, firstRun, firstCloseBrace,
      firstEndEquation, firstRange, firstSliceEquation⟩
  rcases secondSliceAt with
    ⟨secondBrace, secondClose, secondRun, secondCloseBrace,
      secondEndEquation, secondRange, secondSliceEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') firstBrace (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have closeEquation := assemblyRun_close_functional afterOpener
    firstRun secondRun firstCloseBrace secondCloseBrace
  subst secondClose
  subst firstEnd
  subst secondEnd
  have sliceEquation : firstSlice = secondSlice := by
    rw [firstSliceEquation, secondSliceEquation]
  subst secondSlice
  subst firstSlice
  constructor
  · rfl
  · rw [firstTokenEquation, secondTokenEquation]

private theorem sourceTextAt_nextSuffix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {text : String}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.SourceTextAt file cursor endByte text) :
    ∃ remaining, SuffixAt file endByte remaining := by
  rcases suffix.sourceTextDecomposition recognized with
    ⟨remaining, decomposition, endEquation⟩
  refine ⟨remaining, suffix.advance decomposition ?_⟩
  rw [stringByteSize_eq_byteSize] at endEquation
  exact endEquation

private theorem candidateAt_nextSuffix
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    ∃ remaining,
      SuffixAt file candidate.span.endByte remaining := by
  cases recognized with
  | lineComment endByte comment recognized =>
      rcases suffix.characters_eq_pair_of_bytePairAscii recognized.1.1
          (first := '/') (second := '/') (by decide) (by decide)
          (by decide) with ⟨body, decomposition⟩
      subst characters
      have canonical := lineCommentRecognized suffix
      have endEquation := lineCommentSpan_end_unique recognized.1 canonical.1
      have nextSuffix := lineCommentNextSuffix suffix
      rw [recognized.2]
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      rw [endEquation]
      exact ⟨_, nextSuffix⟩
  | blockComment endByte comment recognized =>
      rcases suffix.characters_eq_pair_of_bytePairAscii recognized.1.1
          (first := '/') (second := '*') (by decide) (by decide)
          (by decide) with ⟨body, decomposition⟩
      subst characters
      rcases recognized.1 with
        ⟨opener, closeCursor, run, closer, endEquation, range⟩
      have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
      rcases blockCommentRun_to_scanClosed run rfl afterOpener closer with
        ⟨consumed, units, scanned⟩
      have nextSuffix := blockCommentNextSuffix suffix scanned
      rw [recognized.2]
      simp only [LexicalJudgment.Candidate.span,
        LexicalJudgment.sourceSpan]
      rw [endEquation]
      exact ⟨_, nextSuffix⟩
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quote, contents, sourceText, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix sourceText with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩
  | pragmaName endByte token recognized =>
      rcases recognized with ⟨kind, spelling, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix spelling.1 with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩
  | identifier endByte token recognized =>
      rcases recognized with
        ⟨text, kind, valid, sourceText, classification, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix sourceText with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩
  | decimal endByte token recognized =>
      rcases recognized with ⟨digits, valid, sourceText, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix sourceText with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩
  | hexadecimal endByte token recognized =>
      rcases recognized with ⟨digits, valid, sourceText, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix sourceText with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩
  | symbol endByte symbol token recognized kind =>
      rcases recognized with
        ⟨written, sourceText, slashGuard, assemblyGuard, tokenEquation⟩
      rcases sourceTextAt_nextSuffix suffix sourceText with
        ⟨remaining, nextSuffix⟩
      rw [tokenEquation]
      exact ⟨remaining, nextSuffix⟩

private theorem assemblyRun_nextSuffix
    {file : WorkspaceFile}
    {initialState finalState : LexicalJudgment.AssemblyScannerState}
    {cursor endByte : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (run : LexicalJudgment.AssemblyRun file initialState cursor
      finalState endByte) :
    ∃ remaining, SuffixAt file endByte remaining := by
  induction run generalizing characters with
  | refl => exact ⟨characters, suffix⟩
  | step state nextState finalState cursor next endByte transition tail
      inductionHypothesis =>
      rcases assemblyStep_nextSuffix suffix transition with
        ⟨nextCharacters, nextSuffix⟩
      exact inductionHypothesis nextSuffix

private theorem assemblyTokenAt_nextSuffix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.AssemblyTokenAt file cursor endByte token) :
    ∃ remaining, SuffixAt file endByte remaining := by
  rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
  rcases sliceAt with
    ⟨brace, closeCursor, run, closeBrace, endEquation, range,
      sliceEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') brace (by decide) with ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  rcases assemblyRun_nextSuffix afterOpener run with
    ⟨atCloseCharacters, atClose⟩
  rcases atClose.characters_eq_cons_of_byteAtAscii
      (expected := '}') closeBrace (by decide) with
    ⟨remaining, closeDecomposition⟩
  subst atCloseCharacters
  have afterClose := atClose.advanceOne
  have closeSize : '}'.utf8Size = 1 := by decide
  rw [closeSize, ← endEquation] at afterClose
  exact ⟨remaining, afterClose⟩

private theorem whitespaceAt_nextSuffix
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (recognized : LexicalJudgment.WhitespaceAt file cursor endByte) :
    ∃ remaining, SuffixAt file endByte remaining := by
  rcases recognized with ⟨character, scalar, whitespace⟩
  rcases suffix.scalarAt_decomposition scalar with
    ⟨remaining, decomposition, endEquation, nextSuffix⟩
  exact ⟨remaining, nextSuffix⟩

private theorem whitespaceAt_end_functional_of_suffix
    {file : WorkspaceFile}
    {cursor firstEnd secondEnd : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.WhitespaceAt file cursor firstEnd)
    (second : LexicalJudgment.WhitespaceAt file cursor secondEnd) :
    firstEnd = secondEnd := by
  rcases first with ⟨firstCharacter, firstScalar, firstWhitespace⟩
  rcases second with ⟨secondCharacter, secondScalar, secondWhitespace⟩
  exact (scalarAt_functional_of_suffix suffix firstScalar secondScalar).2

private theorem pendingAfterToken_functional
    {token : Token}
    {first second : Bool}
    (firstState : LexicalJudgment.PendingAfterToken token first)
    (secondState : LexicalJudgment.PendingAfterToken token second) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [LexicalJudgment.PendingAfterToken]

private theorem whitespace_candidate_exclusive
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor endByte : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (whitespace : LexicalJudgment.WhitespaceAt file cursor endByte)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    False := by
  rcases whitespace with ⟨character, scalar, whitespaceCharacter⟩
  rcases suffix.scalarAt_decomposition scalar with
    ⟨remaining, decomposition, endEquation, nextSuffix⟩
  subst characters
  have whitespaceCases :
      character = ' ' ∨ character = '\t' ∨ character = '\n' ∨
        character = '\r' ∨ character = '\u000c' := by
    rcases whitespaceCharacter with
      space | tab | lineFeed | carriageReturn | formFeed
    · exact Or.inl space
    · exact Or.inr (Or.inl tab)
    · exact Or.inr (Or.inr (Or.inl lineFeed))
    · exact Or.inr (Or.inr (Or.inr (Or.inl carriageReturn)))
    · right
      right
      right
      right
      apply Char.toNat_inj.mp
      simpa using formFeed
  rcases whitespaceCases with rfl | rfl | rfl | rfl | rfl
  all_goals
    have notLineComment :
        ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
      intro pair
      rcases suffix.pair_eq_of_bytePairAscii
          (first := '/') (second := '/') pair
          (by decide) (by decide) (by decide) with
        ⟨tail, firstEquation, restEquation⟩
      contradiction
    have notBlockComment :
        ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
      intro pair
      rcases suffix.pair_eq_of_bytePairAscii
          (first := '/') (second := '*') pair
          (by decide) (by decide) (by decide) with
        ⟨tail, firstEquation, restEquation⟩
      contradiction
    rcases candidateAt_of_symbolStart suffix (by decide) (by decide)
        (by decide) notLineComment notBlockComment recognized with
      ⟨candidateEnd, symbol, token, candidateEquation, symbolAt, kind⟩
    rcases symbolToken_data suffix symbolAt kind with
      ⟨symbolRemaining, symbolDecomposition, sourceText,
        symbolEndEquation, slashGuard, assemblyGuard, tokenEquation⟩
    cases symbol <;> simp [Symbol.spelling] at symbolDecomposition

private theorem whitespace_assembly_exclusive
    {file : WorkspaceFile}
    {cursor whitespaceEnd assemblyEnd : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (whitespace :
      LexicalJudgment.WhitespaceAt file cursor whitespaceEnd)
    (assembly :
      LexicalJudgment.AssemblyTokenAt file cursor assemblyEnd token) :
    False := by
  rcases whitespace with ⟨character, scalar, whitespaceCharacter⟩
  rcases assembly with ⟨slice, sliceAt, tokenEquation⟩
  have characterEquation := scalarAt_character_eq_of_byteAtAscii
    (expected := '{') suffix scalar sliceAt.1 (by decide)
  subst character
  simp [LexicalJudgment.WhitespaceCharacter] at whitespaceCharacter

private theorem candidate_assembly_exclusive
    {file : WorkspaceFile}
    {cursor assemblyEnd : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (candidateAt :
      LexicalJudgment.CandidateAt file true cursor candidate)
    (assemblyAt :
      LexicalJudgment.AssemblyTokenAt file cursor assemblyEnd token) :
    False := by
  rcases assemblyAt with ⟨slice, sliceAt, tokenEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') sliceAt.1 (by decide) with
    ⟨remaining, decomposition⟩
  subst characters
  have notLineComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
    intro pair
    rcases suffix.pair_eq_of_bytePairAscii
        (first := '/') (second := '/') pair
        (by decide) (by decide) (by decide) with
      ⟨tail, firstEquation, restEquation⟩
    contradiction
  have notBlockComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
    intro pair
    rcases suffix.pair_eq_of_bytePairAscii
        (first := '/') (second := '*') pair
        (by decide) (by decide) (by decide) with
      ⟨tail, firstEquation, restEquation⟩
    contradiction
  rcases candidateAt_of_symbolStart suffix (by decide) (by decide)
      (by decide) notLineComment notBlockComment candidateAt with
    ⟨candidateEnd, symbol, candidateToken, candidateEquation,
      symbolAt, kind⟩
  rcases symbolToken_data suffix symbolAt kind with
    ⟨symbolRemaining, symbolDecomposition, sourceText,
      symbolEndEquation, slashGuard, assemblyGuard,
      candidateTokenEquation⟩
  cases symbol <;> simp_all [Symbol.spelling]

private structure LexState where
  cursor : Nat
  pendingAssembly : Bool
  tokens : List Token
  comments : List Comment

private inductive LexStep (file : WorkspaceFile) :
    LexState → LexState → Prop where
  | whitespace
      (cursor next : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (recognized : LexicalJudgment.WhitespaceAt file cursor next) :
      LexStep file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        ⟨next, pendingAssembly, tokens, comments⟩
  | comment
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (comment : Comment)
      (winner : LexicalJudgment.CandidateWinsAt file pendingAssembly
        cursor (.comment comment)) :
      LexStep file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        ⟨comment.span.endByte, pendingAssembly, tokens,
          comments ++ [comment]⟩
  | token
      (cursor : Nat)
      (pendingAssembly nextPending : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (candidateClass : LexicalJudgment.CandidateClass)
      (token : Token)
      (winner : LexicalJudgment.CandidateWinsAt file pendingAssembly
        cursor (.token candidateClass token))
      (nextState : LexicalJudgment.PendingAfterToken token nextPending) :
      LexStep file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        ⟨token.span.endByte, nextPending, tokens ++ [token], comments⟩
  | assemblyBlock
      (cursor endByte : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (token : Token)
      (recognized :
        LexicalJudgment.AssemblyTokenAt file cursor endByte token) :
      LexStep file
        ⟨cursor, true, tokens, comments⟩
        ⟨endByte, false, tokens ++ [token], comments⟩

private theorem lexState_ext
    {first second : LexState}
    (cursor : first.cursor = second.cursor)
    (pendingAssembly :
      first.pendingAssembly = second.pendingAssembly)
    (tokens : first.tokens = second.tokens)
    (comments : first.comments = second.comments) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem lexStep_functional
    {file : WorkspaceFile}
    {current firstNext secondNext : LexState}
    {characters : List Char}
    (suffix : SuffixAt file current.cursor characters)
    (first : LexStep file current firstNext)
    (second : LexStep file current secondNext) :
    firstNext = secondNext := by
  cases first with
  | whitespace cursor firstEnd pendingAssembly tokens comments
      firstRecognized =>
      cases second with
      | whitespace _ secondEnd _ _ _ secondRecognized =>
          have endEquation := whitespaceAt_end_functional_of_suffix
            suffix firstRecognized secondRecognized
          exact lexState_ext endEquation rfl rfl rfl
      | comment _ _ _ _ _ secondWinner =>
          exact False.elim (whitespace_candidate_exclusive suffix
            firstRecognized secondWinner.1)
      | token _ _ _ _ _ _ _ secondWinner _ =>
          exact False.elim (whitespace_candidate_exclusive suffix
            firstRecognized secondWinner.1)
      | assemblyBlock _ _ _ _ _ secondRecognized =>
          exact False.elim (whitespace_assembly_exclusive suffix
            firstRecognized secondRecognized)
  | comment cursor pendingAssembly tokens comments firstComment
      firstWinner =>
      cases second with
      | whitespace _ _ _ _ _ secondRecognized =>
          exact False.elim (whitespace_candidate_exclusive suffix
            secondRecognized firstWinner.1)
      | comment _ _ _ _ secondComment secondWinner =>
          have candidateEquation := candidateWinner_unique
            firstWinner secondWinner
          have commentEquation : firstComment = secondComment := by
            simpa using candidateEquation
          cases commentEquation
          rfl
      | token _ _ _ _ _ _ _ secondWinner _ =>
          have candidateEquation := candidateWinner_unique
            firstWinner secondWinner
          cases candidateEquation
      | assemblyBlock _ _ _ _ _ secondRecognized =>
          exact False.elim (candidate_assembly_exclusive suffix
            firstWinner.1 secondRecognized)
  | token cursor pendingAssembly firstPending tokens comments firstClass
      firstToken firstWinner firstPendingAfter =>
      cases second with
      | whitespace _ _ _ _ _ secondRecognized =>
          exact False.elim (whitespace_candidate_exclusive suffix
            secondRecognized firstWinner.1)
      | comment _ _ _ _ _ secondWinner =>
          have candidateEquation := candidateWinner_unique
            firstWinner secondWinner
          cases candidateEquation
      | token _ _ secondPending _ _ secondClass secondToken
          secondWinner secondPendingAfter =>
          have candidateEquation := candidateWinner_unique
            firstWinner secondWinner
          have candidateFields :
              firstClass = secondClass ∧ firstToken = secondToken := by
            simpa using candidateEquation
          rcases candidateFields with
            ⟨classEquation, tokenEquation⟩
          subst secondClass
          subst secondToken
          have pendingEquation := pendingAfterToken_functional
            firstPendingAfter secondPendingAfter
          exact lexState_ext rfl pendingEquation rfl rfl
      | assemblyBlock _ _ _ _ _ secondRecognized =>
          exact False.elim (candidate_assembly_exclusive suffix
            firstWinner.1 secondRecognized)
  | assemblyBlock cursor firstEnd tokens comments firstToken
      firstRecognized =>
      cases second with
      | whitespace _ _ _ _ _ secondRecognized =>
          exact False.elim (whitespace_assembly_exclusive suffix
            secondRecognized firstRecognized)
      | comment _ _ _ _ _ secondWinner =>
          exact False.elim (candidate_assembly_exclusive suffix
            secondWinner.1 firstRecognized)
      | token _ _ _ _ _ _ _ secondWinner _ =>
          exact False.elim (candidate_assembly_exclusive suffix
            secondWinner.1 firstRecognized)
      | assemblyBlock _ secondEnd _ _ secondToken secondRecognized =>
          rcases assemblyTokenAt_functional_of_suffix suffix
              firstRecognized secondRecognized with
            ⟨endEquation, tokenEquation⟩
          exact lexState_ext endEquation rfl
            (congrArg (tokens ++ [.]) tokenEquation) rfl

private theorem lexStep_progress
    {file : WorkspaceFile}
    {current next : LexState}
    (step : LexStep file current next) :
    current.cursor < next.cursor := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact (lexer_progress file).1 recognized
  | comment _ _ _ _ _ winner =>
      exact (lexer_progress file).2.1 winner.1
  | token _ _ _ _ _ _ _ winner _ =>
      exact (lexer_progress file).2.1 winner.1
  | assemblyBlock _ _ _ _ _ recognized =>
      exact (lexer_progress file).2.2 recognized

private theorem lexStep_nextSuffix
    {file : WorkspaceFile}
    {current next : LexState}
    {characters : List Char}
    (suffix : SuffixAt file current.cursor characters)
    (step : LexStep file current next) :
    ∃ remaining, SuffixAt file next.cursor remaining := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_nextSuffix suffix recognized
  | comment _ _ _ _ _ winner =>
      exact candidateAt_nextSuffix suffix winner.1
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_nextSuffix suffix winner.1
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_nextSuffix suffix recognized

private inductive LexPath (file : WorkspaceFile) :
    LexState → LexState → Prop where
  | refl (state : LexState) : LexPath file state state
  | cons
      {current next final : LexState}
      (head : LexStep file current next)
      (tail : LexPath file next final) :
      LexPath file current final

private theorem lexPath_snoc
    {file : WorkspaceFile}
    {start middle final : LexState}
    (path : LexPath file start middle)
    (step : LexStep file middle final) :
    LexPath file start final := by
  induction path with
  | refl => exact .cons step (.refl final)
  | cons head tail inductionHypothesis =>
      exact .cons head (inductionHypothesis step)

private theorem lexesPrefix_to_path
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    (partition : LexicalJudgment.LexesPrefix file cursor
      pendingAssembly tokens comments) :
    LexPath file ⟨0, false, [], []⟩
      ⟨cursor, pendingAssembly, tokens, comments⟩ := by
  induction partition with
  | start => exact .refl _
  | whitespace cursor next pendingAssembly tokens comments prior
      recognized inductionHypothesis =>
      exact lexPath_snoc inductionHypothesis
        (.whitespace cursor next pendingAssembly tokens comments recognized)
  | comment cursor pendingAssembly tokens comments comment prior winner
      inductionHypothesis =>
      exact lexPath_snoc inductionHypothesis
        (.comment cursor pendingAssembly tokens comments comment winner)
  | token cursor pendingAssembly nextPending tokens comments candidateClass
      token prior winner nextState inductionHypothesis =>
      exact lexPath_snoc inductionHypothesis
        (.token cursor pendingAssembly nextPending tokens comments
          candidateClass token winner nextState)
  | assemblyBlock cursor endByte tokens comments token prior recognized
      inductionHypothesis =>
      exact lexPath_snoc inductionHypothesis
        (.assemblyBlock cursor endByte tokens comments token recognized)

private theorem lexPath_cursor_le
    {file : WorkspaceFile}
    {start final : LexState}
    (path : LexPath file start final) :
    start.cursor ≤ final.cursor := by
  induction path with
  | refl => exact Nat.le_refl _
  | cons head tail inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt (lexStep_progress head))
        inductionHypothesis

private theorem lexPath_nextSuffix
    {file : WorkspaceFile}
    {start final : LexState}
    {characters : List Char}
    (suffix : SuffixAt file start.cursor characters)
    (path : LexPath file start final) :
    ∃ remaining, SuffixAt file final.cursor remaining := by
  induction path generalizing characters with
  | refl => exact ⟨characters, suffix⟩
  | cons head tail inductionHypothesis =>
      rcases lexStep_nextSuffix suffix head with
        ⟨nextCharacters, nextSuffix⟩
      exact inductionHypothesis nextSuffix

private theorem lexPath_prefix_of_cursor_le
    {file : WorkspaceFile}
    {start shorterFinal longerFinal : LexState}
    {characters : List Char}
    (suffix : SuffixAt file start.cursor characters)
    (shorter : LexPath file start shorterFinal)
    (longer : LexPath file start longerFinal)
    (cursorBound : shorterFinal.cursor ≤ longerFinal.cursor) :
    LexPath file shorterFinal longerFinal := by
  induction shorter generalizing characters longerFinal with
  | refl => exact longer
  | cons shorterHead shorterTail inductionHypothesis =>
      cases longer with
      | refl =>
          have headProgress := lexStep_progress shorterHead
          have tailBound := lexPath_cursor_le shorterTail
          omega
      | cons longerHead longerTail =>
          have nextEquation := lexStep_functional suffix
            shorterHead longerHead
          subst_vars
          rcases lexStep_nextSuffix suffix shorterHead with
            ⟨nextCharacters, nextSuffix⟩
          exact inductionHypothesis nextSuffix longerTail cursorBound

private theorem lexPath_functional_of_cursor
    {file : WorkspaceFile}
    {start firstFinal secondFinal : LexState}
    {characters : List Char}
    (suffix : SuffixAt file start.cursor characters)
    (first : LexPath file start firstFinal)
    (second : LexPath file start secondFinal)
    (endCursor : firstFinal.cursor = secondFinal.cursor) :
    firstFinal = secondFinal := by
  induction first generalizing characters secondFinal with
  | refl =>
      cases second with
      | refl => rfl
      | cons secondHead secondTail =>
          have headProgress := lexStep_progress secondHead
          have tailBound := lexPath_cursor_le secondTail
          omega
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | refl =>
          have headProgress := lexStep_progress firstHead
          have tailBound := lexPath_cursor_le firstTail
          omega
      | cons secondHead secondTail =>
          have nextEquation := lexStep_functional suffix
            firstHead secondHead
          subst_vars
          rcases lexStep_nextSuffix suffix firstHead with
            ⟨nextCharacters, nextSuffix⟩
          exact inductionHypothesis nextSuffix secondTail endCursor

namespace Lexes

/-- The independent successful lexical partition has a unique output. -/
theorem functional
    {file : WorkspaceFile}
    {firstTokens secondTokens : List Token}
    {firstComments secondComments : List Comment}
    (first : Lexes file firstTokens firstComments)
    (second : Lexes file secondTokens secondComments) :
    firstTokens = secondTokens ∧ firstComments = secondComments := by
  rcases first with ⟨firstPending, firstPartition⟩
  rcases second with ⟨secondPending, secondPartition⟩
  have firstPath := lexesPrefix_to_path firstPartition
  have secondPath := lexesPrefix_to_path secondPartition
  have finalEquation := lexPath_functional_of_cursor
    (SuffixAt.initial file) firstPath secondPath (by rfl)
  exact ⟨congrArg LexState.tokens finalEquation,
    congrArg LexState.comments finalEquation⟩

end Lexes

private theorem whitespaceAt_byteAtAscii_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {expected : Char}
    (suffix : SuffixAt file cursor characters)
    (whitespace : LexicalJudgment.WhitespaceAt file cursor endByte)
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat expected.toNat))
    (ascii : expected.toNat ≤ 127)
    (notWhitespace :
      ¬ LexicalJudgment.WhitespaceCharacter expected) :
    False := by
  rcases whitespace with ⟨character, scalar, recognized⟩
  have characterEquation := scalarAt_character_eq_of_byteAtAscii
    (expected := expected) suffix scalar byte ascii
  subst character
  exact notWhitespace recognized

private theorem assemblyTokenAt_byteAtAscii_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {token : Token}
    {expected : UInt8}
    (assembly :
      LexicalJudgment.AssemblyTokenAt file cursor endByte token)
    (byte : LexicalJudgment.ByteAt file cursor expected)
    (different : expected ≠ 123) :
    False := by
  rcases assembly with ⟨slice, sliceAt, tokenEquation⟩
  have byteEquation := byteAt_functional sliceAt.1 byte
  exact different byteEquation.symm

private theorem candidateAt_pending_openBrace_exclusive
    {file : WorkspaceFile}
    {cursor : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (brace : LexicalJudgment.ByteAt file cursor 123)
    (recognized :
      LexicalJudgment.CandidateAt file true cursor candidate) :
    False := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') brace (by decide) with
    ⟨remaining, decomposition⟩
  subst characters
  have notLineComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 47 := by
    intro pair
    have firstEquation := byteAt_functional brace pair.1
    simp at firstEquation
  have notBlockComment :
      ¬ LexicalJudgment.BytePairAt file cursor 47 42 := by
    intro pair
    have firstEquation := byteAt_functional brace pair.1
    simp at firstEquation
  rcases candidateAt_of_symbolStart suffix (by decide) (by decide)
      (by decide) notLineComment notBlockComment recognized with
    ⟨candidateEnd, symbol, token, candidateEquation, symbolAt, kind⟩
  rcases symbolToken_data suffix symbolAt kind with
    ⟨symbolRemaining, symbolDecomposition, sourceText,
      symbolEndEquation, slashGuard, assemblyGuard, tokenEquation⟩
  have symbolEquation : symbol = .leftBrace := by
    cases symbol <;> simp_all [Symbol.spelling]
  exact assemblyGuard rfl symbolEquation

private theorem assemblyStep_progress
    {file : WorkspaceFile}
    {state nextState : LexicalJudgment.AssemblyScannerState}
    {cursor next : Nat}
    (step : LexicalJudgment.AssemblyStep file state cursor nextState next) :
    cursor < next := by
  cases step <;> try omega
  all_goals
    unfold LexicalJudgment.ScalarAt at *
    omega

private theorem assemblyRun_terminal_of_cursor_le
    {file : WorkspaceFile}
    {initialState terminalState finalState :
      LexicalJudgment.AssemblyScannerState}
    {cursor terminalCursor finalCursor : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (terminalRun : LexicalJudgment.AssemblyRun file initialState cursor
      terminalState terminalCursor)
    (otherRun : LexicalJudgment.AssemblyRun file initialState cursor
      finalState finalCursor)
    (cursorBound : terminalCursor ≤ finalCursor)
    (terminal : ∀ nextState next,
      LexicalJudgment.AssemblyStep file terminalState terminalCursor
        nextState next → False) :
    terminalCursor = finalCursor ∧ terminalState = finalState := by
  induction terminalRun generalizing characters finalState finalCursor with
  | refl =>
      cases otherRun with
      | refl => exact ⟨rfl, rfl⟩
      | step _ _ _ _ _ _ transition _ =>
          exact False.elim (terminal _ _ transition)
  | step state nextState terminalState cursor next terminalCursor
      transition tail inductionHypothesis =>
      cases otherRun with
      | refl =>
          have transitionProgress := assemblyStep_progress transition
          have tailBound := assemblyRun_cursor_le tail
          omega
      | step _ otherNextState _ _ otherNext _ otherTransition otherTail =>
          have nextEquation := assemblyStep_functional suffix
            transition otherTransition
          cases nextEquation.1
          cases nextEquation.2
          rcases assemblyStep_nextSuffix suffix transition with
            ⟨nextCharacters, nextSuffix⟩
          exact inductionHypothesis nextSuffix otherTail cursorBound terminal

private theorem assemblyTokenAt_runToEnd_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    {finalState : LexicalJudgment.AssemblyScannerState}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.AssemblyTokenAt file cursor endByte token)
    (runToEnd : LexicalJudgment.AssemblyRun file (.normal 1)
      (cursor + 1) finalState file.content.utf8ByteSize) :
    False := by
  rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
  rcases sliceAt with
    ⟨brace, closeCursor, closedRun, closeBrace, endEquation,
      range, sliceEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') brace (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have closeBound : closeCursor ≤ file.content.utf8ByteSize := by
    unfold LexicalJudgment.SourceRange at range
    omega
  have terminal : ∀ nextState next,
      LexicalJudgment.AssemblyStep file (.normal 1) closeCursor
        nextState next → False := by
    intro nextState next step
    exact assemblyStep_at_outerClose_impossible closeBrace step
  have cursors := assemblyRun_terminal_of_cursor_le afterOpener
    closedRun runToEnd closeBound terminal
  unfold LexicalJudgment.SourceRange at range
  omega

private theorem byteAt_cursor_lt
    {file : WorkspaceFile}
    {cursor : Nat}
    {byte : UInt8}
    (recognized : LexicalJudgment.ByteAt file cursor byte) :
    cursor < file.content.utf8ByteSize := by
  unfold LexicalJudgment.ByteAt LexicalJudgment.byteAt at recognized
  have arrayBound := (Array.getElem?_eq_some_iff.mp recognized).1
  simpa only [ByteArray.size_data, String.size_toByteArray] using arrayBound

private theorem lexes_step_at_prefix
    {file : WorkspaceFile}
    {finalTokens : List Token}
    {finalComments : List Comment}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor
      pendingAssembly tokens comments)
    (beforeEnd : cursor < file.content.utf8ByteSize) :
    ∃ characters next,
      SuffixAt file cursor characters ∧
        LexStep file
          ⟨cursor, pendingAssembly, tokens, comments⟩ next := by
  rcases lexical with ⟨finalPending, partition⟩
  have priorPath := lexesPrefix_to_path prior
  have fullPath := lexesPrefix_to_path partition
  have tailPath := lexPath_prefix_of_cursor_le
    (SuffixAt.initial file) priorPath fullPath (Nat.le_of_lt beforeEnd)
  rcases lexPath_nextSuffix (SuffixAt.initial file) priorPath with
    ⟨characters, suffix⟩
  cases tailPath with
  | refl => omega
  | cons head tail => exact ⟨characters, _, suffix, head⟩

private theorem candidateAt_lexemeStart
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor next : Nat}
    {characters : List Char}
    {character : Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (scalar : LexicalJudgment.ScalarAt file cursor character next)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate) :
    LexicalJudgment.LexemeStartCharacter character := by
  rcases suffix.scalarAt_decomposition scalar with
    ⟨remaining, decomposition, endEquation, nextSuffix⟩
  subst characters
  cases recognized with
  | lineComment endByte comment recognized =>
      have characterEquation := scalarAt_character_eq_of_byteAtAscii
        (expected := '/') suffix scalar recognized.1.1.1 (by decide)
      subst character
      right
      right
      right
      right
      exact ⟨.slash, [], by decide⟩
  | blockComment endByte comment recognized =>
      have characterEquation := scalarAt_character_eq_of_byteAtAscii
        (expected := '/') suffix scalar recognized.1.1.1 (by decide)
      subst character
      right
      right
      right
      right
      exact ⟨.slash, [], by decide⟩
  | string endByte token recognized =>
      rcases recognized with
        ⟨spelling, decoded, quote, contents, sourceText, tokenEquation⟩
      have characterEquation := scalarAt_character_eq_of_byteAtAscii
        (expected := '"') suffix scalar quote (by decide)
      exact Or.inr (Or.inr (Or.inr (Or.inl characterEquation)))
  | pragmaName endByte token recognized =>
      have characterEquation := pragmaToken_first_n suffix recognized
      subst character
      exact Or.inr (Or.inl (by
        simp [LexicalJudgment.AsciiLetter]))
  | identifier endByte token recognized =>
      exact Or.inr (Or.inl
        (identifierToken_firstLetter suffix recognized))
  | decimal endByte token recognized =>
      exact Or.inr (Or.inr (Or.inl
        (decimalToken_firstDigit suffix recognized)))
  | hexadecimal endByte token recognized =>
      have characterEquation := hexadecimalToken_first_zero suffix recognized
      subst character
      exact Or.inr (Or.inr (Or.inl (by
        simp [LexicalJudgment.AsciiDigit])))
  | symbol endByte symbol token recognized kind =>
      rcases symbolToken_data suffix recognized kind with
        ⟨symbolRemaining, symbolDecomposition, sourceText,
          symbolEndEquation, slashGuard, assemblyGuard, tokenEquation⟩
      right
      right
      right
      right
      refine ⟨symbol, symbol.spelling.toList.tail, ?_⟩
      cases symbol <;> simp_all [Symbol.spelling]

private theorem lexes_invalidCharacter_exclusive
    {file : WorkspaceFile}
    {finalTokens : List Token}
    {finalComments : List Comment}
    {cursor next : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    {character : Char}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor
      pendingAssembly tokens comments)
    (scalar : LexicalJudgment.ScalarAt file cursor character next)
    (invalid :
      ¬ LexicalJudgment.LexemeStartCharacter character) :
    False := by
  have beforeEnd : cursor < file.content.utf8ByteSize := by
    have progress := scalar.1
    have endBound := scalar.2.1.2.1
    omega
  rcases lexes_step_at_prefix lexical prior beforeEnd with
    ⟨characters, nextState, suffix, step⟩
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      rcases recognized with ⟨otherCharacter, otherScalar, whitespace⟩
      have characterEquation :=
        (scalarAt_functional_of_suffix suffix scalar otherScalar).1
      subst otherCharacter
      exact invalid (Or.inl whitespace)
  | comment _ _ _ _ _ winner =>
      exact invalid (candidateAt_lexemeStart suffix scalar winner.1)
  | token _ _ _ _ _ _ _ winner _ =>
      exact invalid (candidateAt_lexemeStart suffix scalar winner.1)
  | assemblyBlock _ _ _ _ _ recognized =>
      rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
      have characterEquation := scalarAt_character_eq_of_byteAtAscii
        (expected := '{') suffix scalar sliceAt.1 (by decide)
      subst character
      apply invalid
      right
      right
      right
      right
      exact ⟨.leftBrace, [], by decide⟩

private theorem lexes_unterminatedAssembly_exclusive
    {file : WorkspaceFile}
    {finalTokens tokens : List Token}
    {finalComments comments : List Comment}
    {cursor : Nat}
    {finalState : LexicalJudgment.AssemblyScannerState}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor true
      tokens comments)
    (brace : LexicalJudgment.ByteAt file cursor 123)
    (runToEnd : LexicalJudgment.AssemblyRun file (.normal 1)
      (cursor + 1) finalState file.content.utf8ByteSize) :
    False := by
  rcases lexes_step_at_prefix lexical prior
      (byteAt_cursor_lt brace) with
    ⟨characters, nextState, suffix, step⟩
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '{')
        suffix recognized brace (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_pending_openBrace_exclusive suffix brace winner.1
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_pending_openBrace_exclusive suffix brace winner.1
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_runToEnd_exclusive suffix recognized runToEnd

private theorem blockCommentRun_to_scanUnterminated
    {file : WorkspaceFile}
    {depth cursor finalDepth finalCursor : Nat}
    {characters : List Char}
    (run : LexicalJudgment.BlockCommentRun file depth cursor finalDepth
      finalCursor)
    (finalPositive : 0 < finalDepth)
    (atEnd : finalCursor = file.content.utf8ByteSize)
    (suffix : SuffixAt file cursor characters) :
    ∃ units,
      Lexer.scanBlockComment cursor depth characters =
        .unterminated units := by
  induction run generalizing characters with
  | refl depth cursor =>
      have remainingSize := suffix.remainingByteSize
      have charactersEquation : characters = [] := by
        cases characters with
        | nil => rfl
        | cons character rest =>
            rw [byteSize_cons] at remainingSize
            have positive := character.utf8Size_pos
            omega
      subst characters
      exact ⟨0, rfl⟩
  | nestedOpen depth cursor finalDepth endByte positive opener tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '/') (second := '*') opener
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis finalPositive atEnd nextSuffix with
        ⟨units, scanned⟩
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanBlockComment.eq_2, scanned]
  | nestedClose depth cursor finalDepth endByte nested closer tail
      inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '*') (second := '/') closer
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      cases depth with
      | zero => omega
      | succ predecessor =>
          cases predecessor with
          | zero => omega
          | succ nestedDepth =>
              have nextSuffix := suffix.advanceTwoAscii
                (by decide) (by decide)
              rcases inductionHypothesis finalPositive atEnd nextSuffix with
                ⟨units, scanned⟩
              have recursiveDepth :
                  nestedDepth + 1 + 1 - 1 = nestedDepth + 1 := by omega
              rw [recursiveDepth] at scanned
              refine ⟨units + 1, ?_⟩
              rw [Lexer.scanBlockComment.eq_4, scanned]
  | scalar depth cursor next finalDepth endByte character positive
      notOpener notCloser scalar tail inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      subst characters
      subst next
      have notOpenPattern :
          ∀ trailing,
            character = '/' → remaining = '*' :: trailing → False := by
        intro trailing characterEquation remainingEquation
        subst character
        subst remaining
        exact notOpener (slashStarBytePair suffix)
      have notOuterClosePattern :
          ∀ trailing,
            depth = 1 → character = '*' →
              remaining = '/' :: trailing → False := by
        intro trailing depthEquation characterEquation remainingEquation
        subst character
        subst remaining
        exact notCloser (starSlashBytePair suffix)
      have notNestedClosePattern :
          ∀ nestedDepth trailing,
            depth = nestedDepth + 2 → character = '*' →
              remaining = '/' :: trailing → False := by
        intro nestedDepth trailing depthEquation characterEquation
          remainingEquation
        subst character
        subst remaining
        exact notCloser (starSlashBytePair suffix)
      rcases inductionHypothesis finalPositive atEnd nextSuffix with
        ⟨units, scanned⟩
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanBlockComment.eq_5 _ _ _ _ notOpenPattern
        notOuterClosePattern notNestedClosePattern, scanned]

private theorem blockCommentAt_unterminated_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {comment : Comment}
    (suffix : SuffixAt file cursor characters)
    (completed :
      LexicalJudgment.BlockCommentAt file cursor endByte comment)
    (unfinished :
      LexicalJudgment.UnterminatedBlockCommentAt file cursor) :
    False := by
  rcases completed.1 with
    ⟨completedOpener, closeCursor, completedRun, closer,
      endEquation, range⟩
  rcases unfinished with
    ⟨unfinishedOpener, finalDepth, finalPositive, runToEnd⟩
  rcases suffix.characters_eq_pair_of_bytePairAscii
      (first := '/') (second := '*') unfinishedOpener
      (by decide) (by decide) (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceTwoAscii (by decide) (by decide)
  rcases blockCommentRun_to_scanClosed completedRun rfl
      afterOpener closer with
    ⟨closedCharacters, closedUnits, closed⟩
  rcases blockCommentRun_to_scanUnterminated runToEnd finalPositive rfl
      afterOpener with
    ⟨unfinishedUnits, unterminated⟩
  rw [closed] at unterminated
  cases unterminated

private theorem candidateAt_unterminatedBlockComment_exclusive
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate)
    (unfinished :
      LexicalJudgment.UnterminatedBlockCommentAt file cursor) :
    False := by
  rcases unfinished with
    ⟨opener, finalDepth, finalPositive, runToEnd⟩
  rcases suffix.characters_eq_pair_of_bytePairAscii
      (first := '/') (second := '*') opener
      (by decide) (by decide) (by decide) with
    ⟨body, decomposition⟩
  subst characters
  rcases candidateAt_of_blockStart suffix recognized with
    ⟨endByte, comment, candidateEquation, completed⟩
  exact blockCommentAt_unterminated_exclusive suffix completed
    ⟨opener, finalDepth, finalPositive, runToEnd⟩

private theorem lexes_unterminatedBlockComment_exclusive
    {file : WorkspaceFile}
    {finalTokens tokens : List Token}
    {finalComments comments : List Comment}
    {cursor : Nat}
    {pendingAssembly : Bool}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor pendingAssembly
      tokens comments)
    (unfinished :
      LexicalJudgment.UnterminatedBlockCommentAt file cursor) :
    False := by
  have slash := unfinished.1.1
  rcases lexes_step_at_prefix lexical prior
      (byteAt_cursor_lt slash) with
    ⟨characters, nextState, suffix, step⟩
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '/')
        suffix recognized slash (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_unterminatedBlockComment_exclusive
        suffix winner.1 unfinished
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_unterminatedBlockComment_exclusive
        suffix winner.1 unfinished
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized slash
        (by decide)

private theorem stringScanPrefix_to_scanUnterminated
    {file : WorkspaceFile}
    {cursor finalCursor : Nat}
    {characters : List Char}
    (scanPrefix :
      LexicalJudgment.StringScanPrefix file cursor finalCursor)
    (atEnd : finalCursor = file.content.utf8ByteSize)
    (suffix : SuffixAt file cursor characters)
    (decodedRev : List Char) :
    ∃ units,
      Lexer.scanString file cursor characters decodedRev =
        .unterminated units := by
  induction scanPrefix generalizing characters decodedRev with
  | refl cursor =>
      have remainingSize := suffix.remainingByteSize
      have charactersEquation : characters = [] := by
        cases characters with
        | nil => rfl
        | cons character rest =>
            rw [byteSize_cons] at remainingSize
            have positive := character.utf8Size_pos
            omega
      subst characters
      exact ⟨0, rfl⟩
  | scalar cursor next endByte character scalar notQuote notBackslash tail
      inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      subst characters
      subst next
      have notTrailingBackslash :
          character = '\\' → remaining = [] → False := by
        intro characterEquation _
        exact notBackslash characterEquation
      have notEscapedBackslash :
          ∀ escaped trailing,
            character = '\\' → remaining = escaped :: trailing →
              False := by
        intro escaped trailing characterEquation _
        exact notBackslash characterEquation
      rcases inductionHypothesis atEnd nextSuffix
          (character :: decodedRev) with
        ⟨units, scanned⟩
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_9 file cursor decodedRev character remaining
        notQuote notTrailingBackslash notEscapedBackslash, scanned]
  | escapedNewline cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 'n') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis atEnd nextSuffix ('\n' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + 'n'.utf8Size = cursor + 2 := by
        have size : 'n'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_4, nextCursor, scanned]
  | escapedTab cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 't') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis atEnd nextSuffix ('\t' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + 't'.utf8Size = cursor + 2 := by
        have size : 't'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_5, nextCursor, scanned]
  | escapedQuote cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '"') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis atEnd nextSuffix ('"' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + '"'.utf8Size = cursor + 2 := by
        have size : '"'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_6, nextCursor, scanned]
  | escapedBackslash cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '\\') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis atEnd nextSuffix ('\\' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + '\\'.utf8Size = cursor + 2 := by
        have size : '\\'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_7, nextCursor, scanned]

private theorem stringTokenAt_unterminated_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters : List Char}
    {token : Token}
    (suffix : SuffixAt file cursor characters)
    (completed :
      LexicalJudgment.StringTokenAt file cursor endByte token)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
      file.content.utf8ByteSize) :
    False := by
  rcases completed with
    ⟨spelling, decoded, completedQuote, contents, sourceText,
      tokenEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  rcases stringContents_to_scanClosed
      (decodedRev := []) contents afterOpener with
    ⟨closedCharacters, closedUnits, closed⟩
  rcases stringScanPrefix_to_scanUnterminated validToEnd rfl
      afterOpener [] with
    ⟨unfinishedUnits, unterminated⟩
  rw [closed] at unterminated
  cases unterminated

private theorem candidateAt_unterminatedString_exclusive
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
      file.content.utf8ByteSize) :
    False := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  rcases candidateAt_of_stringStart suffix recognized with
    ⟨endByte, token, candidateEquation, completed⟩
  exact stringTokenAt_unterminated_exclusive suffix completed quote
    validToEnd

private theorem lexes_unterminatedString_exclusive
    {file : WorkspaceFile}
    {finalTokens tokens : List Token}
    {finalComments comments : List Comment}
    {cursor : Nat}
    {pendingAssembly : Bool}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor pendingAssembly
      tokens comments)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
      file.content.utf8ByteSize) :
    False := by
  rcases lexes_step_at_prefix lexical prior
      (byteAt_cursor_lt quote) with
    ⟨characters, nextState, suffix, step⟩
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '"')
        suffix recognized quote (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_unterminatedString_exclusive suffix winner.1
        quote validToEnd
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_unterminatedString_exclusive suffix winner.1
        quote validToEnd
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized quote
        (by decide)

private theorem invalidStringEscape_to_scanInvalid
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {characters decodedRev : List Char}
    {character : Option Char}
    (suffix : SuffixAt file cursor characters)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file cursor endByte
      character) :
    ∃ units,
      Lexer.scanString file cursor characters decodedRev =
        .invalidEscape
          (.invalidStringEscape
            (Lexer.sourceSpan file cursor endByte) character) units := by
  cases invalid with
  | unsupported endByte escaped backslash scalar unsupported =>
      rcases suffix_after_backslash suffix backslash with
        ⟨afterBackslashCharacters, decomposition, afterBackslash⟩
      rcases afterBackslash.scalarAt_decomposition scalar with
        ⟨remaining, escapedDecomposition, endEquation, endSuffix⟩
      subst characters
      subst afterBackslashCharacters
      refine ⟨1, ?_⟩
      rw [Lexer.scanString.eq_8 file cursor decodedRev escaped remaining
        unsupported.1 unsupported.2.1 unsupported.2.2.1
        unsupported.2.2.2]
      rw [endEquation]
  | endOfFile backslash atEnd =>
      rcases suffix_after_backslash suffix backslash with
        ⟨remaining, decomposition, afterBackslash⟩
      have remainingSize := afterBackslash.remainingByteSize
      have remainingEquation : remaining = [] := by
        cases remaining with
        | nil => rfl
        | cons next rest =>
            rw [byteSize_cons] at remainingSize
            have positive := next.utf8Size_pos
            omega
      subst characters
      subst remaining
      exact ⟨1, Lexer.scanString.eq_3 file cursor decodedRev⟩

private theorem stringScanPrefix_to_scanInvalid
    {file : WorkspaceFile}
    {cursor escapeStart escapeEnd : Nat}
    {characters : List Char}
    {escapedCharacter : Option Char}
    (scanPrefix :
      LexicalJudgment.StringScanPrefix file cursor escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter)
    (suffix : SuffixAt file cursor characters)
    (decodedRev : List Char) :
    ∃ units,
      Lexer.scanString file cursor characters decodedRev =
        .invalidEscape
          (.invalidStringEscape
            (Lexer.sourceSpan file escapeStart escapeEnd) escapedCharacter)
          units := by
  induction scanPrefix generalizing characters decodedRev with
  | refl cursor =>
      exact invalidStringEscape_to_scanInvalid suffix invalid
  | scalar cursor next endByte character scalar notQuote notBackslash tail
      inductionHypothesis =>
      rcases suffix.scalarAt_decomposition scalar with
        ⟨remaining, decomposition, nextEquation, nextSuffix⟩
      subst characters
      subst next
      have notTrailingBackslash :
          character = '\\' → remaining = [] → False := by
        intro characterEquation _
        exact notBackslash characterEquation
      have notEscapedBackslash :
          ∀ escaped trailing,
            character = '\\' → remaining = escaped :: trailing →
              False := by
        intro escaped trailing characterEquation _
        exact notBackslash characterEquation
      rcases inductionHypothesis invalid nextSuffix
          (character :: decodedRev) with
        ⟨units, scanned⟩
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_9 file cursor decodedRev character remaining
        notQuote notTrailingBackslash notEscapedBackslash, scanned]
  | escapedNewline cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 'n') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis invalid nextSuffix ('\n' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + 'n'.utf8Size = cursor + 2 := by
        have size : 'n'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_4, nextCursor, scanned]
  | escapedTab cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := 't') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis invalid nextSuffix ('\t' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + 't'.utf8Size = cursor + 2 := by
        have size : 't'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_5, nextCursor, scanned]
  | escapedQuote cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '"') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis invalid nextSuffix ('"' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + '"'.utf8Size = cursor + 2 := by
        have size : '"'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_6, nextCursor, scanned]
  | escapedBackslash cursor endByte escape tail inductionHypothesis =>
      rcases suffix.characters_eq_pair_of_bytePairAscii
          (first := '\\') (second := '\\') escape
          (by decide) (by decide) (by decide) with
        ⟨remaining, decomposition⟩
      subst characters
      have nextSuffix := suffix.advanceTwoAscii (by decide) (by decide)
      rcases inductionHypothesis invalid nextSuffix ('\\' :: decodedRev) with
        ⟨units, scanned⟩
      have nextCursor : cursor + 1 + '\\'.utf8Size = cursor + 2 := by
        have size : '\\'.utf8Size = 1 := by decide
        omega
      refine ⟨units + 1, ?_⟩
      rw [Lexer.scanString.eq_7, nextCursor, scanned]

private theorem stringTokenAt_invalidEscape_exclusive
    {file : WorkspaceFile}
    {cursor endByte escapeStart escapeEnd : Nat}
    {characters : List Char}
    {token : Token}
    {escapedCharacter : Option Char}
    (suffix : SuffixAt file cursor characters)
    (completed :
      LexicalJudgment.StringTokenAt file cursor endByte token)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (scanPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter) :
    False := by
  rcases completed with
    ⟨spelling, decoded, completedQuote, contents, sourceText,
      tokenEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  rcases stringContents_to_scanClosed
      (decodedRev := []) contents afterOpener with
    ⟨closedCharacters, closedUnits, closed⟩
  rcases stringScanPrefix_to_scanInvalid scanPrefix invalid
      afterOpener [] with
    ⟨invalidUnits, invalidScan⟩
  rw [closed] at invalidScan
  cases invalidScan

private theorem candidateAt_invalidStringEscape_exclusive
    {file : WorkspaceFile}
    {pendingAssembly : Bool}
    {cursor escapeStart escapeEnd : Nat}
    {characters : List Char}
    {candidate : LexicalJudgment.Candidate}
    {escapedCharacter : Option Char}
    (suffix : SuffixAt file cursor characters)
    (recognized :
      LexicalJudgment.CandidateAt file pendingAssembly cursor candidate)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (scanPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter) :
    False := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  rcases candidateAt_of_stringStart suffix recognized with
    ⟨endByte, token, candidateEquation, completed⟩
  exact stringTokenAt_invalidEscape_exclusive suffix completed quote
    scanPrefix invalid

private theorem lexes_invalidStringEscape_exclusive
    {file : WorkspaceFile}
    {finalTokens tokens : List Token}
    {finalComments comments : List Comment}
    {cursor escapeStart escapeEnd : Nat}
    {pendingAssembly : Bool}
    {escapedCharacter : Option Char}
    (lexical : Lexes file finalTokens finalComments)
    (prior : LexicalJudgment.LexesPrefix file cursor pendingAssembly
      tokens comments)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (scanPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter) :
    False := by
  rcases lexes_step_at_prefix lexical prior
      (byteAt_cursor_lt quote) with
    ⟨characters, nextState, suffix, step⟩
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '"')
        suffix recognized quote (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_invalidStringEscape_exclusive suffix winner.1
        quote scanPrefix invalid
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_invalidStringEscape_exclusive suffix winner.1
        quote scanPrefix invalid
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized quote
        (by decide)

private theorem lexes_applies_exclusive
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    {diagnostic : LexicalDiagnostic}
    (lexical : Lexes file tokens comments)
    (applies : LexicalDiagnostic.Applies file diagnostic) :
    False := by
  cases applies with
  | invalidCharacter cursor next pendingAssembly priorTokens priorComments
      character prior scalar invalid =>
      exact lexes_invalidCharacter_exclusive lexical prior scalar invalid
  | unterminatedBlockComment cursor pendingAssembly priorTokens priorComments
      prior unfinished range =>
      exact lexes_unterminatedBlockComment_exclusive lexical prior unfinished
  | unterminatedString cursor pendingAssembly priorTokens priorComments prior
      quote validToEnd range =>
      exact lexes_unterminatedString_exclusive lexical prior quote validToEnd
  | invalidStringEscape stringStart escapeStart escapeEnd pendingAssembly
      priorTokens priorComments character prior quote scanPrefix invalid range =>
      exact lexes_invalidStringEscape_exclusive lexical prior quote
        scanPrefix invalid
  | unterminatedAssemblyString openBrace openQuote priorTokens priorComments
      prior unfinished range =>
      rcases unfinished with ⟨brace, depth, positive, runToEnd⟩
      exact lexes_unterminatedAssembly_exclusive lexical prior brace runToEnd
  | unterminatedAssemblyComment openBrace outermostOpen priorTokens
      priorComments prior unfinished range =>
      rcases unfinished with
        ⟨brace, braceDepth, commentDepth, bracePositive,
          commentPositive, runToEnd⟩
      exact lexes_unterminatedAssembly_exclusive lexical prior brace runToEnd
  | unterminatedAssemblyBlock openBrace priorTokens priorComments prior
      unfinished range =>
      cases unfinished with
      | normal depth brace positive runToEnd =>
          exact lexes_unterminatedAssembly_exclusive lexical prior brace
            runToEnd
      | lineComment depth brace positive runToEnd =>
          exact lexes_unterminatedAssembly_exclusive lexical prior brace
            runToEnd

/-- Every independent successful lexical partition is the executor output. -/
theorem lexer_complete
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    lexModule file = .ok {
      source := file.id
      tokens := tokens
      comments := comments
    } := by
  cases execution : lexModule file with
  | error diagnostic =>
      exact False.elim (lexes_applies_exclusive lexical
        (lexical_diagnostic_sound execution))
  | ok lexed =>
      rcases lexer_sound execution with ⟨sourceEquation, executorLexes⟩
      rcases Lexes.functional lexical executorLexes with
        ⟨tokensEquation, commentsEquation⟩
      cases lexed with
      | mk outputSource outputTokens outputComments =>
          simp only at sourceEquation tokensEquation commentsEquation
          subst outputSource
          subst outputTokens
          subst outputComments
          rfl

private inductive LexFailureAt (file : WorkspaceFile) :
    LexState → LexicalDiagnostic → Prop where
  | invalidCharacter
      (cursor next : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (character : Char)
      (scalar : LexicalJudgment.ScalarAt file cursor character next)
      (invalid :
        ¬ LexicalJudgment.LexemeStartCharacter character) :
      LexFailureAt file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        (.invalidCharacter
          (LexicalJudgment.sourceSpan file cursor next) character)
  | unterminatedBlockComment
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (unfinished :
        LexicalJudgment.UnterminatedBlockCommentAt file cursor) :
      LexFailureAt file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        (.unterminatedBlockComment
          (LexicalJudgment.sourceSpan file cursor
            file.content.utf8ByteSize))
  | unterminatedString
      (cursor : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (quote : LexicalJudgment.ByteAt file cursor 34)
      (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
        file.content.utf8ByteSize) :
      LexFailureAt file
        ⟨cursor, pendingAssembly, tokens, comments⟩
        (.unterminatedString
          (LexicalJudgment.sourceSpan file cursor
            file.content.utf8ByteSize))
  | invalidStringEscape
      (stringStart escapeStart escapeEnd : Nat)
      (pendingAssembly : Bool)
      (tokens : List Token)
      (comments : List Comment)
      (character : Option Char)
      (quote : LexicalJudgment.ByteAt file stringStart 34)
      (validPrefix : LexicalJudgment.StringScanPrefix file
        (stringStart + 1) escapeStart)
      (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
        escapeEnd character) :
      LexFailureAt file
        ⟨stringStart, pendingAssembly, tokens, comments⟩
        (.invalidStringEscape
          (LexicalJudgment.sourceSpan file escapeStart escapeEnd) character)
  | unterminatedAssemblyString
      (openBrace openQuote : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (unfinished : LexicalJudgment.UnterminatedAssemblyStringAt file
        openBrace openQuote) :
      LexFailureAt file ⟨openBrace, true, tokens, comments⟩
        (.unterminatedAssemblyString
          (LexicalJudgment.sourceSpan file openQuote
            file.content.utf8ByteSize))
  | unterminatedAssemblyComment
      (openBrace outermostOpen : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (unfinished : LexicalJudgment.UnterminatedAssemblyCommentAt file
        openBrace outermostOpen) :
      LexFailureAt file ⟨openBrace, true, tokens, comments⟩
        (.unterminatedAssemblyComment
          (LexicalJudgment.sourceSpan file outermostOpen
            file.content.utf8ByteSize))
  | unterminatedAssemblyBlock
      (openBrace : Nat)
      (tokens : List Token)
      (comments : List Comment)
      (unfinished :
        LexicalJudgment.UnterminatedAssemblyBlockAt file openBrace) :
      LexFailureAt file ⟨openBrace, true, tokens, comments⟩
        (.unterminatedAssemblyBlock
          (LexicalJudgment.sourceSpan file openBrace
            file.content.utf8ByteSize))

private theorem applies_to_failureFrontier
    {file : WorkspaceFile}
    {diagnostic : LexicalDiagnostic}
    (applies : LexicalDiagnostic.Applies file diagnostic) :
    ∃ state,
      LexPath file ⟨0, false, [], []⟩ state ∧
        LexFailureAt file state diagnostic := by
  cases applies with
  | invalidCharacter cursor next pendingAssembly tokens comments character
      prior scalar invalid =>
      exact ⟨_, lexesPrefix_to_path prior,
        .invalidCharacter cursor next pendingAssembly tokens comments
          character scalar invalid⟩
  | unterminatedBlockComment cursor pendingAssembly tokens comments prior
      unfinished range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .unterminatedBlockComment cursor pendingAssembly tokens comments
          unfinished⟩
  | unterminatedString cursor pendingAssembly tokens comments prior quote
      validToEnd range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .unterminatedString cursor pendingAssembly tokens comments quote
          validToEnd⟩
  | invalidStringEscape stringStart escapeStart escapeEnd pendingAssembly
      tokens comments character prior quote validPrefix invalid range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .invalidStringEscape stringStart escapeStart escapeEnd
          pendingAssembly tokens comments character quote validPrefix invalid⟩
  | unterminatedAssemblyString openBrace openQuote tokens comments prior
      unfinished range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .unterminatedAssemblyString openBrace openQuote tokens comments
          unfinished⟩
  | unterminatedAssemblyComment openBrace outermostOpen tokens comments prior
      unfinished range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .unterminatedAssemblyComment openBrace outermostOpen tokens comments
          unfinished⟩
  | unterminatedAssemblyBlock openBrace tokens comments prior unfinished
      range =>
      exact ⟨_, lexesPrefix_to_path prior,
        .unterminatedAssemblyBlock openBrace tokens comments unfinished⟩

private theorem lexStep_invalidCharacter_exclusive
    {file : WorkspaceFile}
    {cursor scalarEnd : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    {character : Char}
    {characters : List Char}
    {next : LexState}
    (suffix : SuffixAt file cursor characters)
    (scalar : LexicalJudgment.ScalarAt file cursor character scalarEnd)
    (invalid :
      ¬ LexicalJudgment.LexemeStartCharacter character)
    (step : LexStep file
      ⟨cursor, pendingAssembly, tokens, comments⟩ next) :
    False := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      rcases recognized with ⟨otherCharacter, otherScalar, whitespace⟩
      have characterEquation :=
        (scalarAt_functional_of_suffix suffix scalar otherScalar).1
      subst otherCharacter
      exact invalid (Or.inl whitespace)
  | comment _ _ _ _ _ winner =>
      exact invalid (candidateAt_lexemeStart suffix scalar winner.1)
  | token _ _ _ _ _ _ _ winner _ =>
      exact invalid (candidateAt_lexemeStart suffix scalar winner.1)
  | assemblyBlock _ _ _ _ _ recognized =>
      rcases recognized with ⟨slice, sliceAt, tokenEquation⟩
      have characterEquation := scalarAt_character_eq_of_byteAtAscii
        (expected := '{') suffix scalar sliceAt.1 (by decide)
      subst character
      apply invalid
      right
      right
      right
      right
      exact ⟨.leftBrace, [], by decide⟩

private theorem lexStep_unterminatedBlockComment_exclusive
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    {characters : List Char}
    {next : LexState}
    (suffix : SuffixAt file cursor characters)
    (unfinished :
      LexicalJudgment.UnterminatedBlockCommentAt file cursor)
    (step : LexStep file
      ⟨cursor, pendingAssembly, tokens, comments⟩ next) :
    False := by
  have slash := unfinished.1.1
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '/')
        suffix recognized slash (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_unterminatedBlockComment_exclusive
        suffix winner.1 unfinished
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_unterminatedBlockComment_exclusive
        suffix winner.1 unfinished
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized slash
        (by decide)

private theorem lexStep_unterminatedString_exclusive
    {file : WorkspaceFile}
    {cursor : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    {characters : List Char}
    {next : LexState}
    (suffix : SuffixAt file cursor characters)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
      file.content.utf8ByteSize)
    (step : LexStep file
      ⟨cursor, pendingAssembly, tokens, comments⟩ next) :
    False := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '"')
        suffix recognized quote (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_unterminatedString_exclusive suffix winner.1
        quote validToEnd
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_unterminatedString_exclusive suffix winner.1
        quote validToEnd
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized quote
        (by decide)

private theorem lexStep_invalidStringEscape_exclusive
    {file : WorkspaceFile}
    {cursor escapeStart escapeEnd : Nat}
    {pendingAssembly : Bool}
    {tokens : List Token}
    {comments : List Comment}
    {escapedCharacter : Option Char}
    {characters : List Char}
    {next : LexState}
    (suffix : SuffixAt file cursor characters)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (scanPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter)
    (step : LexStep file
      ⟨cursor, pendingAssembly, tokens, comments⟩ next) :
    False := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '"')
        suffix recognized quote (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_invalidStringEscape_exclusive suffix winner.1
        quote scanPrefix invalid
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_invalidStringEscape_exclusive suffix winner.1
        quote scanPrefix invalid
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_byteAtAscii_exclusive recognized quote
        (by decide)

private theorem lexStep_unterminatedAssemblyRun_exclusive
    {file : WorkspaceFile}
    {cursor : Nat}
    {tokens : List Token}
    {comments : List Comment}
    {characters : List Char}
    {next : LexState}
    {finalState : LexicalJudgment.AssemblyScannerState}
    (suffix : SuffixAt file cursor characters)
    (brace : LexicalJudgment.ByteAt file cursor 123)
    (runToEnd : LexicalJudgment.AssemblyRun file (.normal 1)
      (cursor + 1) finalState file.content.utf8ByteSize)
    (step : LexStep file ⟨cursor, true, tokens, comments⟩ next) :
    False := by
  cases step with
  | whitespace _ _ _ _ _ recognized =>
      exact whitespaceAt_byteAtAscii_exclusive (expected := '{')
        suffix recognized brace (by decide) (by
          simp [LexicalJudgment.WhitespaceCharacter])
  | comment _ _ _ _ _ winner =>
      exact candidateAt_pending_openBrace_exclusive suffix brace winner.1
  | token _ _ _ _ _ _ _ winner _ =>
      exact candidateAt_pending_openBrace_exclusive suffix brace winner.1
  | assemblyBlock _ _ _ _ _ recognized =>
      exact assemblyTokenAt_runToEnd_exclusive suffix recognized runToEnd

private theorem lexFailureAt_step_exclusive
    {file : WorkspaceFile}
    {state next : LexState}
    {diagnostic : LexicalDiagnostic}
    {characters : List Char}
    (suffix : SuffixAt file state.cursor characters)
    (failure : LexFailureAt file state diagnostic)
    (step : LexStep file state next) :
    False := by
  cases failure with
  | invalidCharacter _ _ _ _ _ _ scalar invalid =>
      exact lexStep_invalidCharacter_exclusive suffix scalar invalid step
  | unterminatedBlockComment _ _ _ _ unfinished =>
      exact lexStep_unterminatedBlockComment_exclusive suffix unfinished step
  | unterminatedString _ _ _ _ quote validToEnd =>
      exact lexStep_unterminatedString_exclusive suffix quote validToEnd step
  | invalidStringEscape _ _ _ _ _ _ _ quote scanPrefix invalid =>
      exact lexStep_invalidStringEscape_exclusive suffix quote scanPrefix
        invalid step
  | unterminatedAssemblyString _ _ _ _ unfinished =>
      rcases unfinished with ⟨brace, depth, positive, runToEnd⟩
      exact lexStep_unterminatedAssemblyRun_exclusive suffix brace runToEnd
        step
  | unterminatedAssemblyComment _ _ _ _ unfinished =>
      rcases unfinished with
        ⟨brace, braceDepth, commentDepth, bracePositive,
          commentPositive, runToEnd⟩
      exact lexStep_unterminatedAssemblyRun_exclusive suffix brace runToEnd
        step
  | unterminatedAssemblyBlock _ _ _ unfinished =>
      cases unfinished with
      | normal depth brace positive runToEnd =>
          exact lexStep_unterminatedAssemblyRun_exclusive suffix brace
            runToEnd step
      | lineComment depth brace positive runToEnd =>
          exact lexStep_unterminatedAssemblyRun_exclusive suffix brace
            runToEnd step

private theorem assemblyRun_state_functional_of_cursor
    {file : WorkspaceFile}
    {initialState firstFinalState secondFinalState :
      LexicalJudgment.AssemblyScannerState}
    {cursor firstEnd secondEnd : Nat}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (first : LexicalJudgment.AssemblyRun file initialState cursor
      firstFinalState firstEnd)
    (second : LexicalJudgment.AssemblyRun file initialState cursor
      secondFinalState secondEnd)
    (endEquation : firstEnd = secondEnd) :
    firstFinalState = secondFinalState := by
  induction first generalizing characters secondFinalState secondEnd with
  | refl =>
      cases second with
      | refl => rfl
      | step _ _ _ _ _ _ transition tail =>
          have transitionProgress := assemblyStep_progress transition
          have tailBound := assemblyRun_cursor_le tail
          omega
  | step _ _ _ _ _ _ firstTransition firstTail inductionHypothesis =>
      cases second with
      | refl =>
          have transitionProgress := assemblyStep_progress firstTransition
          have tailBound := assemblyRun_cursor_le firstTail
          omega
      | step _ _ _ _ _ _ secondTransition secondTail =>
          have nextEquation := assemblyStep_functional suffix
            firstTransition secondTransition
          cases nextEquation.1
          cases nextEquation.2
          rcases assemblyStep_nextSuffix suffix firstTransition with
            ⟨nextCharacters, nextSuffix⟩
          exact inductionHypothesis nextSuffix secondTail endEquation

private def assemblyFailureDiagnosticAt
    (file : WorkspaceFile)
    (openBrace : Nat) :
    LexicalJudgment.AssemblyScannerState → LexicalDiagnostic
  | .normal _ | .lineComment _ =>
      .unterminatedAssemblyBlock
        (LexicalJudgment.sourceSpan file openBrace
          file.content.utf8ByteSize)
  | .blockComment _ _ outermostOpen =>
      .unterminatedAssemblyComment
        (LexicalJudgment.sourceSpan file outermostOpen
          file.content.utf8ByteSize)
  | .string _ openQuote =>
      .unterminatedAssemblyString
        (LexicalJudgment.sourceSpan file openQuote
          file.content.utf8ByteSize)

private def AssemblyFailureWitness
    (file : WorkspaceFile)
    (openBrace : Nat)
    (diagnostic : LexicalDiagnostic) : Prop :=
  ∃ finalState,
    LexicalJudgment.ByteAt file openBrace 123 ∧
      LexicalJudgment.AssemblyRun file (.normal 1)
        (openBrace + 1) finalState file.content.utf8ByteSize ∧
      diagnostic = assemblyFailureDiagnosticAt file openBrace finalState

private theorem assemblyStringFailureWitness
    {file : WorkspaceFile}
    {openBrace openQuote : Nat}
    (unfinished : LexicalJudgment.UnterminatedAssemblyStringAt file
      openBrace openQuote) :
    AssemblyFailureWitness file openBrace
      (.unterminatedAssemblyString
        (LexicalJudgment.sourceSpan file openQuote
          file.content.utf8ByteSize)) := by
  rcases unfinished with ⟨brace, depth, positive, runToEnd⟩
  exact ⟨.string depth openQuote, brace, runToEnd, rfl⟩

private theorem assemblyCommentFailureWitness
    {file : WorkspaceFile}
    {openBrace outermostOpen : Nat}
    (unfinished : LexicalJudgment.UnterminatedAssemblyCommentAt file
      openBrace outermostOpen) :
    AssemblyFailureWitness file openBrace
      (.unterminatedAssemblyComment
        (LexicalJudgment.sourceSpan file outermostOpen
          file.content.utf8ByteSize)) := by
  rcases unfinished with
    ⟨brace, braceDepth, commentDepth, bracePositive,
      commentPositive, runToEnd⟩
  exact ⟨.blockComment braceDepth commentDepth outermostOpen,
    brace, runToEnd, rfl⟩

private theorem assemblyBlockFailureWitness
    {file : WorkspaceFile}
    {openBrace : Nat}
    (unfinished :
      LexicalJudgment.UnterminatedAssemblyBlockAt file openBrace) :
    AssemblyFailureWitness file openBrace
      (.unterminatedAssemblyBlock
        (LexicalJudgment.sourceSpan file openBrace
          file.content.utf8ByteSize)) := by
  cases unfinished with
  | normal depth brace positive runToEnd =>
      exact ⟨.normal depth, brace, runToEnd, rfl⟩
  | lineComment depth brace positive runToEnd =>
      exact ⟨.lineComment depth, brace, runToEnd, rfl⟩

private theorem assemblyFailureWitness_functional
    {file : WorkspaceFile}
    {openBrace : Nat}
    {firstDiagnostic secondDiagnostic : LexicalDiagnostic}
    {characters : List Char}
    (suffix : SuffixAt file openBrace characters)
    (first : AssemblyFailureWitness file openBrace firstDiagnostic)
    (second : AssemblyFailureWitness file openBrace secondDiagnostic) :
    firstDiagnostic = secondDiagnostic := by
  rcases first with
    ⟨firstState, firstBrace, firstRun, firstDiagnosticEquation⟩
  rcases second with
    ⟨secondState, secondBrace, secondRun, secondDiagnosticEquation⟩
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '{') firstBrace (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have braceSize : '{'.utf8Size = 1 := by decide
  rw [braceSize] at afterOpener
  have stateEquation := assemblyRun_state_functional_of_cursor
    afterOpener firstRun secondRun rfl
  rw [firstDiagnosticEquation, secondDiagnosticEquation, stateEquation]

private theorem byteAt_distinct_exclusive
    {file : WorkspaceFile}
    {cursor : Nat}
    {first second : UInt8}
    (firstAt : LexicalJudgment.ByteAt file cursor first)
    (secondAt : LexicalJudgment.ByteAt file cursor second)
    (different : first ≠ second) :
    False := by
  exact different (byteAt_functional firstAt secondAt)

private theorem invalidCharacter_byteAt_exclusive
    {file : WorkspaceFile}
    {cursor endByte : Nat}
    {character expected : Char}
    {characters : List Char}
    (suffix : SuffixAt file cursor characters)
    (scalar : LexicalJudgment.ScalarAt file cursor character endByte)
    (invalid :
      ¬ LexicalJudgment.LexemeStartCharacter character)
    (byte : LexicalJudgment.ByteAt file cursor
      (UInt8.ofNat expected.toNat))
    (ascii : expected.toNat ≤ 127)
    (starts : LexicalJudgment.LexemeStartCharacter expected) :
    False := by
  have characterEquation := scalarAt_character_eq_of_byteAtAscii
    (expected := expected) suffix scalar byte ascii
  subst character
  exact invalid starts

private theorem unterminatedString_invalidEscape_exclusive
    {file : WorkspaceFile}
    {cursor escapeStart escapeEnd : Nat}
    {characters : List Char}
    {escapedCharacter : Option Char}
    (suffix : SuffixAt file cursor characters)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (validToEnd : LexicalJudgment.StringScanPrefix file (cursor + 1)
      file.content.utf8ByteSize)
    (validPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      escapeStart)
    (invalid : LexicalJudgment.InvalidStringEscapeAt file escapeStart
      escapeEnd escapedCharacter) :
    False := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  rcases stringScanPrefix_to_scanUnterminated validToEnd rfl
      afterOpener [] with
    ⟨unterminatedUnits, unterminated⟩
  rcases stringScanPrefix_to_scanInvalid validPrefix invalid
      afterOpener [] with
    ⟨invalidUnits, invalidScan⟩
  rw [unterminated] at invalidScan
  cases invalidScan

private theorem invalidStringEscape_diagnostic_functional
    {file : WorkspaceFile}
    {cursor firstEscapeStart firstEscapeEnd secondEscapeStart
      secondEscapeEnd : Nat}
    {characters : List Char}
    {firstCharacter secondCharacter : Option Char}
    (suffix : SuffixAt file cursor characters)
    (quote : LexicalJudgment.ByteAt file cursor 34)
    (firstPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      firstEscapeStart)
    (firstInvalid : LexicalJudgment.InvalidStringEscapeAt file
      firstEscapeStart firstEscapeEnd firstCharacter)
    (secondPrefix : LexicalJudgment.StringScanPrefix file (cursor + 1)
      secondEscapeStart)
    (secondInvalid : LexicalJudgment.InvalidStringEscapeAt file
      secondEscapeStart secondEscapeEnd secondCharacter) :
    LexicalDiagnostic.invalidStringEscape
        (LexicalJudgment.sourceSpan file firstEscapeStart firstEscapeEnd)
        firstCharacter =
      .invalidStringEscape
        (LexicalJudgment.sourceSpan file secondEscapeStart secondEscapeEnd)
        secondCharacter := by
  rcases suffix.characters_eq_cons_of_byteAtAscii
      (expected := '"') quote (by decide) with
    ⟨body, decomposition⟩
  subst characters
  have afterOpener := suffix.advanceOne
  have quoteSize : '"'.utf8Size = 1 := by decide
  rw [quoteSize] at afterOpener
  rcases stringScanPrefix_to_scanInvalid firstPrefix firstInvalid
      afterOpener [] with
    ⟨firstUnits, firstScan⟩
  rcases stringScanPrefix_to_scanInvalid secondPrefix secondInvalid
      afterOpener [] with
    ⟨secondUnits, secondScan⟩
  rw [firstScan] at secondScan
  injection secondScan

private theorem lexFailureAt_functional
    {file : WorkspaceFile}
    {state : LexState}
    {firstDiagnostic secondDiagnostic : LexicalDiagnostic}
    {characters : List Char}
    (suffix : SuffixAt file state.cursor characters)
    (first : LexFailureAt file state firstDiagnostic)
    (second : LexFailureAt file state secondDiagnostic) :
    firstDiagnostic = secondDiagnostic := by
  cases first with
  | invalidCharacter cursor firstEnd pendingAssembly tokens comments
      firstCharacter firstScalar firstInvalid =>
      cases second with
      | invalidCharacter _ secondEnd _ _ _ secondCharacter secondScalar
          secondInvalid =>
          rcases scalarAt_functional_of_suffix suffix firstScalar
              secondScalar with
            ⟨characterEquation, endEquation⟩
          cases characterEquation
          cases endEquation
          rfl
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '/') suffix firstScalar firstInvalid
            unfinished.1.1 (by decide) (by
              right
              right
              right
              right
              exact ⟨.slash, [], by decide⟩))
      | unterminatedString _ _ _ _ quote validToEnd =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '"') suffix firstScalar firstInvalid quote
            (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | invalidStringEscape _ _ _ _ _ _ _ quote validPrefix invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '"') suffix firstScalar firstInvalid quote
            (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | unterminatedAssemblyString _ _ _ _ unfinished =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '{') suffix firstScalar firstInvalid
            unfinished.1 (by decide) (by
              right
              right
              right
              right
              exact ⟨.leftBrace, [], by decide⟩))
      | unterminatedAssemblyComment _ _ _ _ unfinished =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '{') suffix firstScalar firstInvalid
            unfinished.1 (by decide) (by
              right
              right
              right
              right
              exact ⟨.leftBrace, [], by decide⟩))
      | unterminatedAssemblyBlock _ _ _ unfinished =>
          cases unfinished with
          | normal depth brace positive runToEnd =>
              exact False.elim (invalidCharacter_byteAt_exclusive
                (expected := '{') suffix firstScalar firstInvalid brace
                (by decide) (by
                  right
                  right
                  right
                  right
                  exact ⟨.leftBrace, [], by decide⟩))
          | lineComment depth brace positive runToEnd =>
              exact False.elim (invalidCharacter_byteAt_exclusive
                (expected := '{') suffix firstScalar firstInvalid brace
                (by decide) (by
                  right
                  right
                  right
                  right
                  exact ⟨.leftBrace, [], by decide⟩))
  | unterminatedBlockComment cursor pendingAssembly tokens comments
      firstUnfinished =>
      have slash := firstUnfinished.1.1
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '/') suffix scalar invalid slash (by decide) (by
              right
              right
              right
              right
              exact ⟨.slash, [], by decide⟩))
      | unterminatedBlockComment _ _ _ _ secondUnfinished => rfl
      | unterminatedString _ _ _ _ quote validToEnd =>
          exact False.elim (byteAt_distinct_exclusive slash quote (by decide))
      | invalidStringEscape _ _ _ _ _ _ _ quote validPrefix invalid =>
          exact False.elim (byteAt_distinct_exclusive slash quote (by decide))
      | unterminatedAssemblyString _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive slash unfinished.1 (by decide))
      | unterminatedAssemblyComment _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive slash unfinished.1 (by decide))
      | unterminatedAssemblyBlock _ _ _ unfinished =>
          cases unfinished with
          | normal depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive slash brace (by decide))
          | lineComment depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive slash brace (by decide))
  | unterminatedString cursor pendingAssembly tokens comments firstQuote
      firstValidToEnd =>
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '"') suffix scalar invalid firstQuote
            (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1.1
              (by decide))
      | unterminatedString _ _ _ _ secondQuote secondValidToEnd => rfl
      | invalidStringEscape _ _ _ _ _ _ _ secondQuote secondPrefix
          secondInvalid =>
          exact False.elim (unterminatedString_invalidEscape_exclusive
            suffix firstQuote firstValidToEnd secondPrefix secondInvalid)
      | unterminatedAssemblyString _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1 (by decide))
      | unterminatedAssemblyComment _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1 (by decide))
      | unterminatedAssemblyBlock _ _ _ unfinished =>
          cases unfinished with
          | normal depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive firstQuote brace (by decide))
          | lineComment depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive firstQuote brace (by decide))
  | invalidStringEscape cursor firstEscapeStart firstEscapeEnd pendingAssembly
      tokens comments firstCharacter firstQuote firstPrefix firstInvalid =>
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '"') suffix scalar invalid firstQuote
            (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1.1
              (by decide))
      | unterminatedString _ _ _ _ secondQuote secondValidToEnd =>
          exact False.elim (unterminatedString_invalidEscape_exclusive
            suffix secondQuote secondValidToEnd firstPrefix firstInvalid)
      | invalidStringEscape _ secondEscapeStart secondEscapeEnd _ _ _
          secondCharacter secondQuote secondPrefix secondInvalid =>
          exact invalidStringEscape_diagnostic_functional suffix firstQuote
            firstPrefix firstInvalid secondPrefix secondInvalid
      | unterminatedAssemblyString _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1 (by decide))
      | unterminatedAssemblyComment _ _ _ _ unfinished =>
          exact False.elim
            (byteAt_distinct_exclusive firstQuote unfinished.1 (by decide))
      | unterminatedAssemblyBlock _ _ _ unfinished =>
          cases unfinished with
          | normal depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive firstQuote brace (by decide))
          | lineComment depth brace positive runToEnd =>
              exact False.elim
                (byteAt_distinct_exclusive firstQuote brace (by decide))
  | unterminatedAssemblyString openBrace openQuote tokens comments
      firstUnfinished =>
      have firstWitness := assemblyStringFailureWitness firstUnfinished
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '{') suffix scalar invalid firstUnfinished.1
            (by decide) (by
              right
              right
              right
              right
              exact ⟨.leftBrace, [], by decide⟩))
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            unfinished.1.1 (by decide))
      | unterminatedString _ _ _ _ quote validToEnd =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            quote (by decide))
      | invalidStringEscape _ _ _ _ _ _ _ quote validPrefix invalid =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            quote (by decide))
      | unterminatedAssemblyString _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyStringFailureWitness secondUnfinished)
      | unterminatedAssemblyComment _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyCommentFailureWitness secondUnfinished)
      | unterminatedAssemblyBlock _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyBlockFailureWitness secondUnfinished)
  | unterminatedAssemblyComment openBrace outermostOpen tokens comments
      firstUnfinished =>
      have firstWitness := assemblyCommentFailureWitness firstUnfinished
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '{') suffix scalar invalid firstUnfinished.1
            (by decide) (by
              right
              right
              right
              right
              exact ⟨.leftBrace, [], by decide⟩))
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            unfinished.1.1 (by decide))
      | unterminatedString _ _ _ _ quote validToEnd =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            quote (by decide))
      | invalidStringEscape _ _ _ _ _ _ _ quote validPrefix invalid =>
          exact False.elim (byteAt_distinct_exclusive firstUnfinished.1
            quote (by decide))
      | unterminatedAssemblyString _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyStringFailureWitness secondUnfinished)
      | unterminatedAssemblyComment _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyCommentFailureWitness secondUnfinished)
      | unterminatedAssemblyBlock _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyBlockFailureWitness secondUnfinished)
  | unterminatedAssemblyBlock openBrace tokens comments firstUnfinished =>
      have firstWitness := assemblyBlockFailureWitness firstUnfinished
      have firstBrace : LexicalJudgment.ByteAt file openBrace 123 := by
        cases firstUnfinished with
        | normal depth brace positive runToEnd => exact brace
        | lineComment depth brace positive runToEnd => exact brace
      cases second with
      | invalidCharacter _ _ _ _ _ character scalar invalid =>
          exact False.elim (invalidCharacter_byteAt_exclusive
            (expected := '{') suffix scalar invalid firstBrace
            (by decide) (by
              right
              right
              right
              right
              exact ⟨.leftBrace, [], by decide⟩))
      | unterminatedBlockComment _ _ _ _ unfinished =>
          exact False.elim (byteAt_distinct_exclusive firstBrace
            unfinished.1.1 (by decide))
      | unterminatedString _ _ _ _ quote validToEnd =>
          exact False.elim
            (byteAt_distinct_exclusive firstBrace quote (by decide))
      | invalidStringEscape _ _ _ _ _ _ _ quote validPrefix invalid =>
          exact False.elim
            (byteAt_distinct_exclusive firstBrace quote (by decide))
      | unterminatedAssemblyString _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyStringFailureWitness secondUnfinished)
      | unterminatedAssemblyComment _ _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyCommentFailureWitness secondUnfinished)
      | unterminatedAssemblyBlock _ _ _ secondUnfinished =>
          exact assemblyFailureWitness_functional suffix firstWitness
            (assemblyBlockFailureWitness secondUnfinished)

private theorem lexicalDiagnosticApplies_functional
    {file : WorkspaceFile}
    {firstDiagnostic secondDiagnostic : LexicalDiagnostic}
    (first : LexicalDiagnostic.Applies file firstDiagnostic)
    (second : LexicalDiagnostic.Applies file secondDiagnostic) :
    firstDiagnostic = secondDiagnostic := by
  rcases applies_to_failureFrontier first with
    ⟨firstState, firstPath, firstFailure⟩
  rcases applies_to_failureFrontier second with
    ⟨secondState, secondPath, secondFailure⟩
  rcases lexPath_nextSuffix (SuffixAt.initial file) firstPath with
    ⟨firstCharacters, firstSuffix⟩
  rcases lexPath_nextSuffix (SuffixAt.initial file) secondPath with
    ⟨secondCharacters, secondSuffix⟩
  by_cases firstBefore : firstState.cursor < secondState.cursor
  · have tail := lexPath_prefix_of_cursor_le (SuffixAt.initial file)
      firstPath secondPath (Nat.le_of_lt firstBefore)
    cases tail with
    | refl => omega
    | cons head rest =>
        exact False.elim
          (lexFailureAt_step_exclusive firstSuffix firstFailure head)
  by_cases secondBefore : secondState.cursor < firstState.cursor
  · have tail := lexPath_prefix_of_cursor_le (SuffixAt.initial file)
      secondPath firstPath (Nat.le_of_lt secondBefore)
    cases tail with
    | refl => omega
    | cons head rest =>
        exact False.elim
          (lexFailureAt_step_exclusive secondSuffix secondFailure head)
  have cursorEquation : firstState.cursor = secondState.cursor := by omega
  have stateEquation := lexPath_functional_of_cursor
    (SuffixAt.initial file) firstPath secondPath cursorEquation
  subst secondState
  exact lexFailureAt_functional firstSuffix firstFailure secondFailure

/-- Every independent lexical diagnostic is exactly the executor failure. -/
theorem lexical_diagnostic_complete
    {file : WorkspaceFile}
    {diagnostic : LexicalDiagnostic}
    (applies : LexicalDiagnostic.Applies file diagnostic) :
    lexModule file = .error diagnostic := by
  cases execution : lexModule file with
  | ok lexed =>
      rcases lexer_sound execution with ⟨sourceEquation, lexical⟩
      exact False.elim (lexes_applies_exclusive lexical applies)
  | error emitted =>
      have emittedApplies := lexical_diagnostic_sound execution
      have diagnosticEquation := lexicalDiagnosticApplies_functional
        emittedApplies applies
      cases diagnosticEquation
      rfl

private theorem characterLength_le_byteSize
    (characters : List Char) :
    characters.length ≤ Lexer.byteSize characters := by
  induction characters with
  | nil => simp [Lexer.byteSize]
  | cons character rest inductionHypothesis =>
      rw [byteSize_cons]
      simp only [List.length_cons]
      have positive := character.utf8Size_pos
      omega

/-- The executor's exact semantic work stays within the public lexer bound. -/
theorem lexBound_sufficient (file : WorkspaceFile) :
    lexActualUnits file ≤ lexBound file.content.utf8ByteSize := by
  have unitBound := lexLoop_units_le file
    (file.content.toList.length + 1) 0 file.content.toList false [] []
    (by omega)
  have executionBound :
      lexActualUnits file ≤ file.content.toList.length := by
    simpa [lexActualUnits, lexModuleWithUnits, Lexer.execute] using unitBound
  have characterBound :
      file.content.toList.length ≤ file.content.utf8ByteSize := by
    rw [stringByteSize_eq_byteSize]
    exact characterLength_le_byteSize file.content.toList
  simp only [lexBound]
  omega

/-- File-only frontend execution, from lexing through the total parser. -/
def executeObservedContextualFrontend
    (file : WorkspaceFile) :
    Except SurfaceDiagnostic ParsedModuleV1 :=
  match lexing : lexModule file with
  | .error diagnostic => .error (.lexical diagnostic)
  | .ok lexed =>
      match executeObservedContextualParse file lexed.tokens
          (lexer_tokensOwnedBy lexing) with
      | .ok module => .ok module
      | .error diagnostic => .error (.parse diagnostic)

/-- Successful lexing exposes exactly the total parser branch. -/
theorem executeObservedContextualFrontend_eq_of_lexing
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed) :
    executeObservedContextualFrontend file =
      match executeObservedContextualParse file lexed.tokens
          (lexer_tokensOwnedBy lexing) with
      | .ok module => .ok module
      | .error diagnostic => .error (.parse diagnostic) := by
  have requested := lexing
  unfold executeObservedContextualFrontend
  split
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
    rfl

/-- Lexical failure is selected without entering the parser. -/
theorem executeObservedContextualFrontend_eq_of_lexicalDiagnostic
    {file : WorkspaceFile} {diagnostic : LexicalDiagnostic}
    (lexing : lexModule file = .error diagnostic) :
    executeObservedContextualFrontend file =
      .error (.lexical diagnostic) := by
  have requested := lexing
  unfold executeObservedContextualFrontend
  split
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
    rfl
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted

/-- The file-only frontend selects the lexer failure or the implementation's
parser outcome exactly. -/
theorem executeObservedContextualFrontend_selected
    (file : WorkspaceFile) :
    match lexing : lexModule file with
    | .error diagnostic =>
        executeObservedContextualFrontend file =
          .error (.lexical diagnostic)
    | .ok lexed =>
        let owned := lexer_tokensOwnedBy lexing
        let result := Chart.executeObservedContextualValueWorklistMulti
          file lexed.tokens owned
        (result.parseOutcome? file).map (fun outcome =>
          match outcome with
          | .ok module => .ok module
          | .error diagnostic => .error (.parse diagnostic)) =
            some (executeObservedContextualFrontend file) := by
  split
  · rename_i diagnostic lexing
    exact executeObservedContextualFrontend_eq_of_lexicalDiagnostic lexing
  · rename_i lexed lexing
    dsimp only
    rw [executeObservedContextualParse_selected
      file lexed.tokens (lexer_tokensOwnedBy lexing)]
    rw [executeObservedContextualFrontend_eq_of_lexing lexing]
    cases executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) <;> rfl

/-- Every file-only result satisfies its corresponding declarative judgment;
the frontend cannot construct a structural diagnostic. -/
theorem executeObservedContextualFrontend_sound
    (file : WorkspaceFile) :
    match executeObservedContextualFrontend file with
    | .ok module =>
        ∃ lexed, lexModule file = .ok lexed ∧
          Parses file lexed.tokens module
    | .error (.lexical diagnostic) =>
        LexicalDiagnostic.Applies file diagnostic
    | .error (.parse diagnostic) =>
        ∃ lexed, lexModule file = .ok lexed ∧
          ParseDiagnostic.Applies file lexed.tokens diagnostic
    | .error (.structural _) => False := by
  cases lexing : lexModule file with
  | error diagnostic =>
      rw [executeObservedContextualFrontend_eq_of_lexicalDiagnostic lexing]
      exact lexical_diagnostic_sound lexing
  | ok lexed =>
      let owned := lexer_tokensOwnedBy lexing
      have parserSound := executeObservedContextualParse_sound
        file lexed.tokens owned
      cases parsing : executeObservedContextualParse
          file lexed.tokens owned with
      | ok module =>
          rw [executeObservedContextualFrontend_eq_of_lexing lexing,
            parsing]
          rw [parsing] at parserSound
          exact ⟨lexed, rfl, parserSound⟩
      | error diagnostic =>
          rw [executeObservedContextualFrontend_eq_of_lexing lexing,
            parsing]
          rw [parsing] at parserSound
          exact ⟨lexed, rfl, parserSound⟩

end Solcore.Surface.Multi
