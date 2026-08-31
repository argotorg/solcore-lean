import Solcore.Syntax.Lexer.StateOrder
import Solcore.Syntax.Lexer.ScanProperties

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

private def emitTextToken (file : SourceFile) (state : State)
    (kind : TokenKind) (remaining : List Char) : State :=
  let endByte := state.cursor + kind.spelling.utf8ByteSize
  state.emitToken file endByte remaining kind

private def scanLine (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  let scan := scanLineComment (state.cursor + 2) remaining
  state.emitComment file scan.endByte scan.remaining .line
    (String.ofList scan.body)

private def scanBlock (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanBlockComment (state.cursor + 2) 1 remaining [] with
  | .closed endByte body rest =>
      state.emitComment file endByte rest .block (String.ofList body)
  | .unterminated =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .unterminatedBlockComment

private def scanBacktick (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanDelimitedMeta '`' (state.cursor + 1) remaining ['`'] with
  | some scan =>
      state.emitToken file scan.endByte scan.remaining
        (.yulMetaBacktick scan.spelling)
  | none =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .invalidToken

private def scanInterpolation (file : SourceFile) (state : State)
    (remaining : List Char) : Option State :=
  match scanDelimitedMeta '}' (state.cursor + 2) remaining ['{', '$'] with
  | some scan =>
      some (state.emitToken file scan.endByte scan.remaining
        (.yulMetaInterpolation scan.spelling))
  | none => none

private def scanQuoted (file : SourceFile) (state : State)
    (remaining : List Char) : State :=
  match scanQuotedString state.cursor remaining with
  | .closed endByte spelling _decoded rest =>
      state.emitToken file endByte rest (.stringLiteral spelling)
  | .invalidEscape _ _ _escape tokenEndByte rest =>
      state.recover file state.cursor tokenEndByte tokenEndByte rest
        .invalidStringEscape
  | .invalidPrefix endByte rest =>
      state.recover file state.cursor endByte endByte rest
        .invalidToken
  | .unterminated =>
      let endByte := file.content.utf8ByteSize
      state.recover file state.cursor endByte endByte []
        .invalidToken

private def scanDecimal (file : SourceFile) (state : State)
    (characters : List Char) : State :=
  let scan := takeWhile isAsciiDigit characters
  let spelling := String.ofList scan.consumed
  emitTextToken file state (.decimalLiteral spelling) scan.remaining

private def scanHexadecimal? (file : SourceFile) (state : State)
    (remaining : List Char) : Option State :=
  match remaining with
  | 'x' :: digit :: rest =>
      if isAsciiHexDigit digit then
        let tail := takeWhile isAsciiHexDigit rest
        let spelling := String.ofList ('0' :: 'x' :: digit :: tail.consumed)
        some (emitTextToken file state (.hexadecimalLiteral spelling)
          tail.remaining)
      else none
  | _ => none

private def scanLetterName (file : SourceFile) (state : State)
    (first : Char) (remaining : List Char) : State :=
  let scan := scanLetterIdentifier first remaining
  emitTextToken file state scan.kind scan.remaining

private def scanMarkedName (file : SourceFile) (state : State)
    (first : Char) (remaining : List Char) : State :=
  let scan := scanMarkedYulIdentifier first remaining
  emitTextToken file state scan.kind scan.remaining

private def emitSymbol (file : SourceFile) (state : State)
    (symbol : Symbol) (remaining : List Char) : State :=
  emitTextToken file state (.symbol symbol) remaining

private theorem Advances.prependPrefix (leading : List Char)
    {startByte endByte : Nat} {input remaining : List Char}
    (progress : Advances (startByte + byteSize leading)
      input endByte remaining) :
    Advances startByte (leading ++ input) endByte remaining := by
  rcases progress with ⟨consumed, partition, endEq⟩
  refine ⟨leading ++ consumed, by simp [partition, List.append_assoc], ?_⟩
  rw [byteSize_append]
  simpa [Nat.add_assoc] using endEq

private theorem State.ValidFor.advanceToEnd {file : SourceFile}
    {state : State} (valid : state.ValidFor file) :
    Advances state.cursor state.remaining file.content.utf8ByteSize [] := by
  refine ⟨state.remaining, by simp, ?_⟩
  exact valid.cursorSuffix.remainingByteSize

private theorem emitTextToken_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (kind : TokenKind)
    (remaining : List Char)
    (progress : Advances state.cursor state.remaining
      (state.cursor + kind.spelling.utf8ByteSize) remaining) :
    (emitTextToken file state kind remaining).ValidFor file := by
  exact valid.emitToken _ _ _ progress

private theorem scanLine_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '/' :: '/' :: remaining) :
    (scanLine file state remaining).ValidFor file := by
  unfold scanLine
  let scan := scanLineComment (state.cursor + 2) remaining
  apply valid.emitComment
  rw [inputEq]
  have inner := scanLineComment_advances (state.cursor + 2) remaining
  simpa [scan, byteSize_cons] using
    (Advances.prependPrefix ['/', '/'] inner)

private theorem scanBlock_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '/' :: '*' :: remaining) :
    (scanBlock file state remaining).ValidFor file := by
  unfold scanBlock
  cases result : scanBlockComment (state.cursor + 2) 1 remaining [] with
  | closed endByte body rest =>
      apply valid.emitComment
      rw [inputEq]
      have inner := scanBlockComment_closed_advances
        (state.cursor + 2) 1 remaining [] endByte body rest result
      simpa [byteSize_cons] using
        (Advances.prependPrefix ['/', '*'] inner)
  | unterminated =>
      have progress := valid.advanceToEnd
      exact valid.recover _ _ _ _ _ progress
        (valid.cursorSuffix.sourceSpan_validFor progress)

private theorem scanBacktick_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '`' :: remaining) :
    (scanBacktick file state remaining).ValidFor file := by
  unfold scanBacktick
  cases result :
      scanDelimitedMeta '`' (state.cursor + 1) remaining ['`'] with
  | none =>
      have progress := valid.advanceToEnd
      exact valid.recover _ _ _ _ _ progress
        (valid.cursorSuffix.sourceSpan_validFor progress)
  | some scan =>
      apply valid.emitToken
      rw [inputEq]
      have inner := scanDelimitedMeta_some_advances '`'
        (state.cursor + 1) remaining ['`'] scan result
      simpa [byteSize_cons] using
        (Advances.prependPrefix ['`'] inner)

private theorem scanInterpolation_some_validFor
    {file : SourceFile} {state next : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '$' :: '{' :: remaining)
    (result : scanInterpolation file state remaining = some next) :
    next.ValidFor file := by
  unfold scanInterpolation at result
  cases scanResult :
      scanDelimitedMeta '}' (state.cursor + 2) remaining ['{', '$'] with
  | none => simp [scanResult] at result
  | some scan =>
      simp only [scanResult, Option.some.injEq] at result
      subst next
      apply valid.emitToken
      rw [inputEq]
      have inner := scanDelimitedMeta_some_advances '}'
        (state.cursor + 2) remaining ['{', '$'] scan scanResult
      simpa [byteSize_cons] using
        (Advances.prependPrefix ['$', '{'] inner)

private theorem scanQuoted_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '"' :: remaining) :
    (scanQuoted file state remaining).ValidFor file := by
  unfold scanQuoted
  cases result : scanQuotedString state.cursor remaining with
  | closed endByte spelling decoded rest =>
      apply valid.emitToken
      rw [inputEq]
      exact scanQuotedString_closed_advances state.cursor remaining endByte
        spelling decoded rest result
  | invalidEscape escapeStart escapeEnd escape tokenEndByte rest =>
      have progress : Advances state.cursor state.remaining tokenEndByte rest := by
        rw [inputEq]
        exact scanQuotedString_invalidEscape_advances state.cursor remaining
          escapeStart escapeEnd escape tokenEndByte rest result
      exact valid.recover _ _ _ _ _ progress
        (valid.cursorSuffix.sourceSpan_validFor progress)
  | invalidPrefix endByte rest =>
      have progress : Advances state.cursor state.remaining endByte rest := by
        rw [inputEq]
        exact scanQuotedString_invalidPrefix_advances state.cursor remaining
          endByte rest result
      exact valid.recover _ _ _ _ _ progress
        (valid.cursorSuffix.sourceSpan_validFor progress)
  | unterminated =>
      have progress := valid.advanceToEnd
      exact valid.recover _ _ _ _ _ progress
        (valid.cursorSuffix.sourceSpan_validFor progress)

private theorem scanDecimal_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (characters : List Char)
    (inputEq : state.remaining = characters) :
    (scanDecimal file state characters).ValidFor file := by
  unfold scanDecimal
  let scan := takeWhile isAsciiDigit characters
  apply emitTextToken_validFor valid
  rw [inputEq]
  simpa [scan, byteSize, TokenKind.spelling] using
    takeWhile_advances isAsciiDigit state.cursor characters

private theorem scanLetterName_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (first : Char) (remaining : List Char)
    (inputEq : state.remaining = first :: remaining) :
    (scanLetterName file state first remaining).ValidFor file := by
  unfold scanLetterName
  apply emitTextToken_validFor valid
  rw [inputEq]
  exact scanLetterIdentifier_advances state.cursor first remaining

private theorem scanMarkedName_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (first : Char) (remaining : List Char)
    (inputEq : state.remaining = first :: remaining) :
    (scanMarkedName file state first remaining).ValidFor file := by
  unfold scanMarkedName
  apply emitTextToken_validFor valid
  rw [inputEq]
  exact scanMarkedYulIdentifier_advances state.cursor first remaining

private theorem scanHexadecimal?_some_validFor
    {file : SourceFile} {state next : State}
    (valid : state.ValidFor file) (remaining : List Char)
    (inputEq : state.remaining = '0' :: remaining)
    (result : scanHexadecimal? file state remaining = some next) :
    next.ValidFor file := by
  fun_cases scanHexadecimal? file state remaining with
  | case1 digit rest isHex tail spelling =>
      simp only [scanHexadecimal?, isHex, if_true, Option.some.injEq] at result
      subst next
      apply emitTextToken_validFor valid
      rw [inputEq]
      have inner := takeWhile_advances isAsciiHexDigit
        (state.cursor + byteSize ['0', 'x', digit]) rest
      simpa [tail, spelling, byteSize, TokenKind.spelling, Nat.add_assoc] using
        (Advances.prependPrefix ['0', 'x', digit] inner)
  | case2 => simp_all [scanHexadecimal?]
  | case3 => simp_all [scanHexadecimal?]

private theorem multiSymbol?_spelling (left right : Char) (symbol : Symbol)
    (found : multiSymbol? left right = some symbol) :
    symbol.spelling = String.ofList [left, right] := by
  fun_cases multiSymbol? left right <;>
    simp_all [multiSymbol?] <;> cases found <;> rfl

private theorem singleSymbol?_spelling (character : Char) (symbol : Symbol)
    (found : singleSymbol? character = some symbol) :
    symbol.spelling = String.ofList [character] := by
  fun_cases singleSymbol? character <;>
    simp_all [singleSymbol?] <;> cases found <;> rfl

private theorem emitSymbol_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (symbol : Symbol)
    (consumed remaining : List Char)
    (inputEq : state.remaining = consumed ++ remaining)
    (spelling : symbol.spelling = String.ofList consumed) :
    (emitSymbol file state symbol remaining).ValidFor file := by
  unfold emitSymbol
  apply emitTextToken_validFor valid
  exact ⟨consumed, inputEq, by simp [byteSize, TokenKind.spelling, spelling]⟩

private theorem recoverCharacter_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (character : Char)
    (remaining : List Char)
    (inputEq : state.remaining = character :: remaining) :
    State.ValidFor
      (state.recover file state.cursor (state.cursor + character.utf8Size)
        (state.cursor + character.utf8Size) remaining .invalidToken)
      file := by
  have progress : Advances state.cursor state.remaining
      (state.cursor + character.utf8Size) remaining := by
    rw [inputEq]
    exact Advances.single character state.cursor remaining
  exact valid.recover _ _ _ _ _ progress
    (valid.cursorSuffix.sourceSpan_validFor progress)

private theorem skipCharacter_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (character : Char)
    (remaining : List Char)
    (inputEq : state.remaining = character :: remaining) :
    State.ValidFor
      (state.skipTo (state.cursor + character.utf8Size) remaining) file := by
  apply valid.skipTo
  rw [inputEq]
  exact Advances.single character state.cursor remaining

private theorem emitMultiSymbol_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (left right : Char) (after : List Char)
    (symbol : Symbol) (inputEq : state.remaining = left :: right :: after)
    (found : multiSymbol? left right = some symbol) :
    (emitSymbol file state symbol after).ValidFor file :=
  emitSymbol_validFor valid symbol [left, right] after
    (by simpa using inputEq) (multiSymbol?_spelling left right symbol found)

private theorem emitSingleSymbol_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (character : Char) (after : List Char)
    (symbol : Symbol) (inputEq : state.remaining = character :: after)
    (found : singleSymbol? character = some symbol) :
    (emitSymbol file state symbol after).ValidFor file :=
  emitSymbol_validFor valid symbol [character] after
    (by simpa using inputEq) (singleSymbol?_spelling character symbol found)

private theorem emitUnderscore_validFor {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (after : List Char)
    (inputEq : state.remaining = '_' :: after) :
    (emitSymbol file state .underscore after).ValidFor file :=
  emitSingleSymbol_validFor valid '_' after .underscore inputEq rfl

/--
Perform one maximal-munch transition. Callers only use this on nonempty input;
every branch consumes at least one source character.
-/
def step (file : SourceFile) (state : State) : State :=
  match state.remaining with
  | [] => state
  | first :: rest =>
      if isWhitespace first then
        state.skipTo (state.cursor + first.utf8Size) rest
      else
        match first, rest with
        | '/', '/' :: tail => scanLine file state tail
        | '/', '*' :: tail => scanBlock file state tail
        | '`', tail => scanBacktick file state tail
        | '"', tail => scanQuoted file state tail
        | '$', '{' :: tail =>
            match scanInterpolation file state tail with
            | some next => next
            | none => scanMarkedName file state '$' ('{' :: tail)
        | '0', tail =>
            match scanHexadecimal? file state tail with
            | some next => next
            | none => scanDecimal file state ('0' :: tail)
        | digit, tail =>
            if isAsciiDigit digit then
              scanDecimal file state (digit :: tail)
            else if isCoreIdentifierStart digit then
              scanLetterName file state digit tail
            else
              match digit, tail with
              | '_', next :: after =>
                  if isYulIdentifierContinue next then
                    scanMarkedName file state '_' (next :: after)
                  else
                    emitSymbol file state .underscore (next :: after)
              | '_', [] => emitSymbol file state .underscore []
              | '$', after => scanMarkedName file state '$' after
              | left, right :: after =>
                  match multiSymbol? left right with
                  | some symbol => emitSymbol file state symbol after
                  | none =>
                      match singleSymbol? left with
                      | some symbol =>
                          emitSymbol file state symbol (right :: after)
                      | none =>
                          state.recover file state.cursor
                            (state.cursor + left.utf8Size)
                            (state.cursor + left.utf8Size) (right :: after)
                            .invalidToken
              | character, [] =>
                  match singleSymbol? character with
                  | some symbol => emitSymbol file state symbol []
                  | none =>
                      state.recover file state.cursor
                        (state.cursor + character.utf8Size)
                        (state.cursor + character.utf8Size) []
                        .invalidToken

private theorem scanLine_remaining_length_lt (file : SourceFile)
    (state : State) (remaining : List Char) :
    (scanLine file state remaining).remaining.length <
      ('/' :: '/' :: remaining).length := by
  have strict := Advances.remaining_length_lt_prepend
    (leading := ['/', '/'])
    (scanLineComment_advances (state.cursor + 2) remaining) (by simp)
  simpa [scanLine, State.emitComment] using strict

private theorem scanBlock_remaining_length_lt (file : SourceFile)
    (state : State) (remaining : List Char) :
    (scanBlock file state remaining).remaining.length <
      ('/' :: '*' :: remaining).length := by
  unfold scanBlock
  cases result : scanBlockComment (state.cursor + 2) 1 remaining [] with
  | closed endByte body rest =>
      have progress := scanBlockComment_closed_advances
        (state.cursor + 2) 1 remaining [] endByte body rest result
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['/', '*']) progress (by simp)
      simpa [result, State.emitComment] using strict
  | unterminated => simp [State.recover]

private theorem scanBacktick_remaining_length_lt (file : SourceFile)
    (state : State) (remaining : List Char) :
    (scanBacktick file state remaining).remaining.length <
      ('`' :: remaining).length := by
  unfold scanBacktick
  cases result :
      scanDelimitedMeta '`' (state.cursor + 1) remaining ['`'] with
  | none => simp [State.recover]
  | some scan =>
      have progress := scanDelimitedMeta_some_advances '`'
        (state.cursor + 1) remaining ['`'] scan result
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['`']) progress (by simp)
      simpa [result, State.emitToken] using strict

private theorem scanInterpolation_some_remaining_length_lt
    (file : SourceFile) (state next : State) (remaining : List Char)
    (result : scanInterpolation file state remaining = some next) :
    next.remaining.length < ('$' :: '{' :: remaining).length := by
  unfold scanInterpolation at result
  cases scanResult :
      scanDelimitedMeta '}' (state.cursor + 2) remaining ['{', '$'] with
  | none => simp [scanResult] at result
  | some scan =>
      simp only [scanResult, Option.some.injEq] at result
      subst next
      have progress := scanDelimitedMeta_some_advances '}'
        (state.cursor + 2) remaining ['{', '$'] scan scanResult
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['$', '{']) progress (by simp)
      simpa [State.emitToken] using strict

private theorem scanQuoted_remaining_length_lt (file : SourceFile)
    (state : State) (remaining : List Char) :
    (scanQuoted file state remaining).remaining.length <
      ('"' :: remaining).length := by
  unfold scanQuoted
  cases result : scanQuotedString state.cursor remaining with
  | closed endByte spelling decoded rest =>
      unfold scanQuotedString at result
      have progress :=
        scanString_progress (state.cursor + 1) remaining ['"'] [] none
      rw [result] at progress
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['"']) progress (by simp)
      simpa [result, State.emitToken] using strict
  | invalidEscape escapeStart escapeEnd escape tokenEndByte rest =>
      unfold scanQuotedString at result
      have progress :=
        scanString_progress (state.cursor + 1) remaining ['"'] [] none
      rw [result] at progress
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['"']) progress (by simp)
      simpa [result, State.recover] using strict
  | invalidPrefix endByte rest =>
      unfold scanQuotedString at result
      have progress :=
        scanString_progress (state.cursor + 1) remaining ['"'] [] none
      rw [result] at progress
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['"']) progress (by simp)
      simpa [result, State.recover] using strict
  | unterminated => simp [State.recover]

private theorem scanDecimal_remaining_length_lt (file : SourceFile)
    (state : State) (first : Char) (remaining : List Char)
    (accepted : isAsciiDigit first = true) :
    (scanDecimal file state (first :: remaining)).remaining.length <
      (first :: remaining).length := by
  simpa [scanDecimal, emitTextToken, State.emitToken] using
    takeWhile_remaining_length_lt_of_true isAsciiDigit first remaining accepted

private theorem scanHexadecimal?_some_remaining_length_lt
    (file : SourceFile) (state next : State) (remaining : List Char)
    (result : scanHexadecimal? file state remaining = some next) :
    next.remaining.length < ('0' :: remaining).length := by
  fun_cases scanHexadecimal? file state remaining with
  | case1 digit rest isHex tail spelling =>
      simp only [scanHexadecimal?, isHex, if_true, Option.some.injEq] at result
      subst next
      have progress := takeWhile_advances isAsciiHexDigit
        (state.cursor + byteSize ['0', 'x', digit]) rest
      have strict := Advances.remaining_length_lt_prepend
        (leading := ['0', 'x', digit]) progress (by simp)
      simpa [tail, emitTextToken, State.emitToken] using strict
  | case2 => simp_all [scanHexadecimal?]
  | case3 => simp_all [scanHexadecimal?]

private theorem scanLetterName_remaining_length_lt (file : SourceFile)
    (state : State) (first : Char) (remaining : List Char) :
    (scanLetterName file state first remaining).remaining.length <
      (first :: remaining).length := by
  simpa [scanLetterName, emitTextToken, State.emitToken] using
    scanLetterIdentifier_remaining_length_lt first remaining

private theorem scanMarkedName_remaining_length_lt (file : SourceFile)
    (state : State) (first : Char) (remaining : List Char) :
    (scanMarkedName file state first remaining).remaining.length <
      (first :: remaining).length := by
  simpa [scanMarkedName, emitTextToken, State.emitToken] using
    scanMarkedYulIdentifier_remaining_length_lt first remaining

/-- Every lexer step on nonempty input strictly shortens its input suffix. -/
theorem step_remaining_length_lt (file : SourceFile) {state : State}
    (nonempty : state.remaining ≠ []) :
    (step file state).remaining.length < state.remaining.length := by
  fun_cases step file state
  case case1 => contradiction
  case case2 => simp_all [State.skipTo]
  case case3 tail _ inputEq =>
    rw [inputEq]
    exact scanLine_remaining_length_lt file state tail
  case case4 tail _ inputEq =>
    rw [inputEq]
    exact scanBlock_remaining_length_lt file state tail
  case case5 tail _ inputEq =>
    rw [inputEq]
    exact scanBacktick_remaining_length_lt file state tail
  case case6 tail _ inputEq =>
    rw [inputEq]
    exact scanQuoted_remaining_length_lt file state tail
  case case7 tail next result _ inputEq =>
    rw [inputEq]
    exact scanInterpolation_some_remaining_length_lt
      file state next tail result
  case case8 tail _result _ inputEq =>
    rw [inputEq]
    exact scanMarkedName_remaining_length_lt file state '$' ('{' :: tail)
  case case9 tail next result _ inputEq =>
    rw [inputEq]
    exact scanHexadecimal?_some_remaining_length_lt
      file state next tail result
  case case10 tail _result _ inputEq =>
    rw [inputEq]
    exact scanDecimal_remaining_length_lt file state '0' tail (by decide)
  case case11 digit tail _ _ _ _ _ _ accepted _ inputEq =>
    rw [inputEq]
    exact scanDecimal_remaining_length_lt file state digit tail accepted
  case case12 digit tail _ _ _ _ _ _ _ _ _ inputEq =>
    rw [inputEq]
    exact scanLetterName_remaining_length_lt file state digit tail
  case case13 next after _ _ _ _ _ _ _ _ _ _ inputEq =>
    rw [inputEq]
    exact scanMarkedName_remaining_length_lt file state '_'
      (next :: after)
  case case14 =>
    simp_all [emitSymbol, emitTextToken, State.emitToken]
  case case15 => simp_all [emitSymbol, emitTextToken, State.emitToken]
  case case16 after _ _ _ _ _ _ _ _ _ inputEq =>
    rw [inputEq]
    exact scanMarkedName_remaining_length_lt file state '$' after
  case case17 =>
    simp_all [emitSymbol, emitTextToken, State.emitToken]
    omega
  case case18 =>
    simp_all [emitSymbol, emitTextToken, State.emitToken]
  case case19 =>
    simp_all [State.recover]
  case case20 => simp_all [emitSymbol, emitTextToken, State.emitToken]
  case case21 => simp_all [State.recover]

/-- Every canonical lexer step preserves source and carrier provenance. -/
theorem step_validFor (file : SourceFile) (state : State)
    (valid : state.ValidFor file) :
    (step file state).ValidFor file := by
  fun_cases step file state
  case case1 => exact valid
  case case2 => apply skipCharacter_validFor valid <;> assumption
  case case3 => apply scanLine_validFor valid <;> assumption
  case case4 => apply scanBlock_validFor valid <;> assumption
  case case5 => apply scanBacktick_validFor valid <;> assumption
  case case6 => apply scanQuoted_validFor valid <;> assumption
  case case7 => apply scanInterpolation_some_validFor valid <;> assumption
  case case8 => apply scanMarkedName_validFor valid <;> assumption
  case case9 => apply scanHexadecimal?_some_validFor valid <;> assumption
  case case10 => apply scanDecimal_validFor valid <;> assumption
  case case11 => apply scanDecimal_validFor valid <;> assumption
  case case12 => apply scanLetterName_validFor valid <;> assumption
  case case13 => apply scanMarkedName_validFor valid <;> assumption
  case case14 => apply emitUnderscore_validFor valid <;> assumption
  case case15 => apply emitUnderscore_validFor valid <;> assumption
  case case16 => apply scanMarkedName_validFor valid <;> assumption
  case case17 => apply emitMultiSymbol_validFor valid <;> assumption
  case case18 => apply emitSingleSymbol_validFor valid <;> assumption
  case case19 => apply recoverCharacter_validFor valid <;> assumption
  case case20 => apply emitSingleSymbol_validFor valid <;> assumption
  case case21 => apply recoverCharacter_validFor valid <;> assumption

private theorem emitTextToken_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (kind : TokenKind)
    (remaining : List Char)
    (progress : Advances state.cursor state.remaining
      (state.cursor + kind.spelling.utf8ByteSize) remaining)
    (shorter : remaining.length < state.remaining.length) :
    (emitTextToken file state kind remaining).OrderedValidFor file := by
  unfold emitTextToken
  exact ordered.emitToken _ _ _ progress
    (progress.startByte_lt_endByte_of_remaining_length_lt shorter)

private theorem emitSymbol_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (symbol : Symbol)
    (consumed remaining : List Char)
    (inputEq : state.remaining = consumed ++ remaining)
    (spelling : symbol.spelling = String.ofList consumed)
    (nonempty : consumed ≠ []) :
    (emitSymbol file state symbol remaining).OrderedValidFor file := by
  unfold emitSymbol
  apply emitTextToken_orderedValidFor ordered
  · exact ⟨consumed, inputEq, by
      simp [byteSize, TokenKind.spelling, spelling]⟩
  · rw [inputEq, List.length_append]
    have positive := List.length_pos_iff.mpr nonempty
    omega

private theorem recoverCharacter_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (character : Char)
    (remaining : List Char)
    (inputEq : state.remaining = character :: remaining) :
    State.OrderedValidFor
      (state.recover file state.cursor (state.cursor + character.utf8Size)
        (state.cursor + character.utf8Size) remaining .invalidToken)
      file := by
  have progress : Advances state.cursor state.remaining
      (state.cursor + character.utf8Size) remaining := by
    rw [inputEq]
    exact Advances.single character state.cursor remaining
  exact ordered.recover _ _ _ _ _ progress
    (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)

private theorem emitMultiSymbol_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (left right : Char)
    (after : List Char) (symbol : Symbol)
    (inputEq : state.remaining = left :: right :: after)
    (found : multiSymbol? left right = some symbol) :
    (emitSymbol file state symbol after).OrderedValidFor file :=
  emitSymbol_orderedValidFor ordered symbol [left, right] after
    (by simpa using inputEq) (multiSymbol?_spelling left right symbol found)
    (by simp)

private theorem emitSingleSymbol_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (character : Char)
    (after : List Char) (symbol : Symbol)
    (inputEq : state.remaining = character :: after)
    (found : singleSymbol? character = some symbol) :
    (emitSymbol file state symbol after).OrderedValidFor file :=
  emitSymbol_orderedValidFor ordered symbol [character] after
    (by simpa using inputEq) (singleSymbol?_spelling character symbol found)
    (by simp)

private theorem emitUnderscore_orderedValidFor
    {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (after : List Char)
    (inputEq : state.remaining = '_' :: after) :
    (emitSymbol file state .underscore after).OrderedValidFor file :=
  emitSingleSymbol_orderedValidFor ordered '_' after .underscore inputEq rfl

/-- Every canonical lexer step preserves reverse-accumulator source order. -/
theorem step_orderedValidFor (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    (step file state).OrderedValidFor file := by
  fun_cases step file state
  case case1 => exact ordered
  case case2 first rest inputEq _ =>
    apply ordered.skipTo
    rw [inputEq]
    exact Advances.single first state.cursor rest
  case case3 tail _ inputEq =>
    unfold scanLine
    let scan := scanLineComment (state.cursor + 2) tail
    have progress : Advances state.cursor state.remaining
        scan.endByte scan.remaining := by
      rw [inputEq]
      have inner := scanLineComment_advances (state.cursor + 2) tail
      simpa [scan, byteSize_cons] using
        (Advances.prependPrefix ['/', '/'] inner)
    apply ordered.emitComment _ _ _ _ progress
    apply progress.startByte_lt_endByte_of_remaining_length_lt
    rw [inputEq]
    exact scanLine_remaining_length_lt file state tail
  case case4 tail _ inputEq =>
    unfold scanBlock
    cases result : scanBlockComment (state.cursor + 2) 1 tail [] with
    | closed endByte body rest =>
        have inner := scanBlockComment_closed_advances
          (state.cursor + 2) 1 tail [] endByte body rest result
        have progress : Advances state.cursor state.remaining endByte rest := by
          rw [inputEq]
          simpa [byteSize_cons] using
            (Advances.prependPrefix ['/', '*'] inner)
        apply ordered.emitComment _ _ _ _ progress
        apply progress.startByte_lt_endByte_of_remaining_length_lt
        rw [inputEq]
        exact Advances.remaining_length_lt_prepend
          (leading := ['/', '*']) inner (by simp)
    | unterminated =>
        have progress := ordered.validFor.advanceToEnd
        exact ordered.recover _ _ _ _ _ progress
          (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)
  case case5 tail _ inputEq =>
    unfold scanBacktick
    cases result :
        scanDelimitedMeta '`' (state.cursor + 1) tail ['`'] with
    | none =>
        have progress := ordered.validFor.advanceToEnd
        exact ordered.recover _ _ _ _ _ progress
          (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)
    | some scan =>
        have inner := scanDelimitedMeta_some_advances '`'
          (state.cursor + 1) tail ['`'] scan result
        have progress : Advances state.cursor state.remaining
            scan.endByte scan.remaining := by
          rw [inputEq]
          simpa [byteSize_cons] using
            (Advances.prependPrefix ['`'] inner)
        apply ordered.emitToken _ _ _ progress
        apply progress.startByte_lt_endByte_of_remaining_length_lt
        rw [inputEq]
        exact Advances.remaining_length_lt_prepend
          (leading := ['`']) inner (by simp)
  case case6 tail _ inputEq =>
    unfold scanQuoted
    cases result : scanQuotedString state.cursor tail with
    | closed endByte spelling decoded rest =>
        have progress : Advances state.cursor state.remaining endByte rest := by
          rw [inputEq]
          exact scanQuotedString_closed_advances state.cursor tail endByte
            spelling decoded rest result
        apply ordered.emitToken _ _ _ progress
        apply progress.startByte_lt_endByte_of_remaining_length_lt
        rw [inputEq]
        have shorter := scanQuoted_remaining_length_lt file state tail
        simpa [scanQuoted, result, State.emitToken] using shorter
    | invalidEscape escapeStart escapeEnd escape tokenEndByte rest =>
        have progress : Advances state.cursor state.remaining tokenEndByte rest := by
          rw [inputEq]
          exact scanQuotedString_invalidEscape_advances state.cursor tail
            escapeStart escapeEnd escape tokenEndByte rest result
        exact ordered.recover _ _ _ _ _ progress
          (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)
    | invalidPrefix endByte rest =>
        have progress : Advances state.cursor state.remaining endByte rest := by
          rw [inputEq]
          exact scanQuotedString_invalidPrefix_advances state.cursor tail
            endByte rest result
        exact ordered.recover _ _ _ _ _ progress
          (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)
    | unterminated =>
        have progress := ordered.validFor.advanceToEnd
        exact ordered.recover _ _ _ _ _ progress
          (ordered.validFor.cursorSuffix.sourceSpan_validFor progress)
  case case7 tail next result _ inputEq =>
    unfold scanInterpolation at result
    cases scanResult :
        scanDelimitedMeta '}' (state.cursor + 2) tail ['{', '$'] with
    | none => simp [scanResult] at result
    | some scan =>
        simp only [scanResult, Option.some.injEq] at result
        subst next
        have inner := scanDelimitedMeta_some_advances '}'
          (state.cursor + 2) tail ['{', '$'] scan scanResult
        have progress : Advances state.cursor state.remaining
            scan.endByte scan.remaining := by
          rw [inputEq]
          simpa [byteSize_cons] using
            (Advances.prependPrefix ['$', '{'] inner)
        apply ordered.emitToken _ _ _ progress
        apply progress.startByte_lt_endByte_of_remaining_length_lt
        rw [inputEq]
        exact Advances.remaining_length_lt_prepend
          (leading := ['$', '{']) inner (by simp)
  case case8 tail _ _ inputEq =>
    unfold scanMarkedName
    let scan := scanMarkedYulIdentifier '$' ('{' :: tail)
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      exact scanMarkedYulIdentifier_advances state.cursor '$' ('{' :: tail)
    · rw [inputEq]
      exact scanMarkedYulIdentifier_remaining_length_lt '$' ('{' :: tail)
  case case9 tail next result _ inputEq =>
    fun_cases scanHexadecimal? file state tail with
    | case1 digit rest isHex scan spelling =>
        simp only [scanHexadecimal?, isHex, if_true,
          Option.some.injEq] at result
        subst next
        have inner := takeWhile_advances isAsciiHexDigit
          (state.cursor + byteSize ['0', 'x', digit]) rest
        have progress : Advances state.cursor state.remaining
            (state.cursor +
              (TokenKind.hexadecimalLiteral spelling).spelling.utf8ByteSize)
            scan.remaining := by
          rw [inputEq]
          simpa [scan, spelling, byteSize, TokenKind.spelling,
            Nat.add_assoc] using
              (Advances.prependPrefix ['0', 'x', digit] inner)
        apply emitTextToken_orderedValidFor ordered _ _ progress
        rw [inputEq]
        exact Advances.remaining_length_lt_prepend
          (leading := ['0', 'x', digit]) inner (by simp)
    | case2 => simp_all [scanHexadecimal?]
    | case3 => simp_all [scanHexadecimal?]
  case case10 tail _ _ inputEq =>
    unfold scanDecimal
    let scan := takeWhile isAsciiDigit ('0' :: tail)
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      simpa [scan, byteSize, TokenKind.spelling] using
        takeWhile_advances isAsciiDigit state.cursor ('0' :: tail)
    · rw [inputEq]
      exact takeWhile_remaining_length_lt_of_true
        isAsciiDigit '0' tail (by decide)
  case case11 digit tail _ _ _ _ _ _ accepted _ inputEq =>
    unfold scanDecimal
    let scan := takeWhile isAsciiDigit (digit :: tail)
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      simpa [scan, byteSize, TokenKind.spelling] using
        takeWhile_advances isAsciiDigit state.cursor (digit :: tail)
    · rw [inputEq]
      exact takeWhile_remaining_length_lt_of_true
        isAsciiDigit digit tail accepted
  case case12 first tail _ _ _ _ _ _ _ _ _ inputEq =>
    unfold scanLetterName
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      exact scanLetterIdentifier_advances state.cursor first tail
    · rw [inputEq]
      exact scanLetterIdentifier_remaining_length_lt first tail
  case case13 next after _ _ _ _ _ _ _ _ _ _ inputEq =>
    unfold scanMarkedName
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      exact scanMarkedYulIdentifier_advances state.cursor '_'
        (next :: after)
    · rw [inputEq]
      exact scanMarkedYulIdentifier_remaining_length_lt '_'
        (next :: after)
  case case14 => apply emitUnderscore_orderedValidFor ordered <;> assumption
  case case15 => apply emitUnderscore_orderedValidFor ordered <;> assumption
  case case16 after _ _ _ _ _ _ _ _ _ inputEq =>
    unfold scanMarkedName
    apply emitTextToken_orderedValidFor ordered
    · rw [inputEq]
      exact scanMarkedYulIdentifier_advances state.cursor '$' after
    · rw [inputEq]
      exact scanMarkedYulIdentifier_remaining_length_lt '$' after
  case case17 => apply emitMultiSymbol_orderedValidFor ordered <;> assumption
  case case18 => apply emitSingleSymbol_orderedValidFor ordered <;> assumption
  case case19 => apply recoverCharacter_orderedValidFor ordered <;> assumption
  case case20 => apply emitSingleSymbol_orderedValidFor ordered <;> assumption
  case case21 => apply recoverCharacter_orderedValidFor ordered <;> assumption

end Solcore.Syntax.Lexer
