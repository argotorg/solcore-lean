import Solcore.Syntax.Parser.Internal.SourceFileSoundness
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.ModuleTotality
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.DeclarationTotality

/-!
Totality of the parsers of file items: on valid input they make progress and end in an
ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsTotalityProperties
/-! Conditional totality for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The one remaining totality premise at the complete-item boundary. -/
def ParseItemsItemInvariantFree : Prop :=
  ∀ input, input.ValidFor → ∀ error,
    parseItemsItem input ≠ .invariant error

private theorem rewindAfterItemReject_validFor
    {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := by
  exact {
    tokens := failedValid.tokens
    cursor_le_endIndex := by
      simpa [windowEq] using inputValid.cursor_le_endIndex
    endIndex_le_size := failedValid.endIndex_le_size
    endByte_le_source := failedValid.endByte_le_source
    endByte_boundary := failedValid.endByte_boundary
    diagnosticsRev := failedValid.diagnosticsRev
  }

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor)
    (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  simp only [State.remainingCount] at adequate ⊢
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  rw [endIndexEq]
  omega

/--
If complete-item parsing itself cannot expose an invariant, more fuel than
remaining tokens makes the complete-file loop return successfully.  Thus both
loop fuel exhaustion and its no-progress check are unreachable.
-/
theorem parseItems_exists_ok_of_remainingCount_lt
    (itemInvariantFree : ParseItemsItemInvariantFree) :
    ∀ fuel itemsRev input,
      input.ValidFor → input.remainingCount < fuel →
      ∃ items final, parseItems fuel itemsRev input = .ok items final := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input inputValid adequate
      unfold parseItems
      split
      · exact ⟨_, _, rfl⟩
      · rename_i notAtEnd
        have itemReply := parseItemsItem_complete_validFor input inputValid
        have itemWindow :=
          parseItemsItem_complete_contract.preservesTokenWindow input
        cases itemResult : parseItemsItem input with
        | invariant error =>
            exact False.elim
              (itemInvariantFree input inputValid error itemResult)
        | ok item next =>
            rw [itemResult] at itemReply itemWindow
            have progress := parseItemsItem_cursor_lt_onSuccess itemResult
            have nextAdequate := remainingCount_lt_after_strict_progress
              itemReply.2.1 itemWindow.2 progress adequate
            have recursive := inductionHypothesis (item :: itemsRev) next
              itemReply.2.1 nextAdequate
            dsimp only
            split
            · exact recursive
            · omega
        | reject failure failedState =>
            rw [itemResult] at itemReply itemWindow
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundValid : rewound.ValidFor :=
              rewindAfterItemReject_validFor inputValid itemReply.2.1
                itemWindow.2
            have rewoundNotAtEnd : rewound.atEnd = false := by
              simpa [rewound, State.atEnd, itemWindow.2] using notAtEnd
            dsimp only
            split
            · exact ⟨_, _, rfl⟩
            · rcases recoverTopItem_exists_ok_of_validFor_not_atEnd
                  rewound rewoundValid rewoundNotAtEnd with
                ⟨recovered, next, recoveryResult, progress⟩
              have recoveryReply := recoverTopItem_validFor rewound rewoundValid
              rw [recoveryResult] at recoveryReply
              have recoveryWindow :=
                recoverTopItem_preservesTokenWindow rewound
              rw [recoveryResult] at recoveryWindow
              have rewoundAdequate :
                  rewound.remainingCount < fuel + 1 := by
                simpa only [State.remainingCount, rewound, itemWindow.2]
                  using adequate
              have nextAdequate := remainingCount_lt_after_strict_progress
                recoveryReply.2.1 recoveryWindow.2 progress
                rewoundAdequate
              have recursive := inductionHypothesis
                (recovered :: itemsRev) next recoveryReply.2.1 nextAdequate
              change ∃ items final,
                (match recoverTopItem rewound with
                | .ok recovered next =>
                    parseItems fuel (recovered :: itemsRev) next
                | .reject recoveryFailure rejected =>
                    .reject recoveryFailure rejected
                | .invariant error => .invariant error) = .ok items final
              simpa only [recoveryResult] using recursive

/-- The production fuel selected by the file parser always suffices. -/
theorem parseItems_production_exists_ok
    (itemInvariantFree : ParseItemsItemInvariantFree)
    (itemsRev : List TopItem) (input : State) (inputValid : input.ValidFor) :
    ∃ items final,
      parseItems (input.remainingCount + 1) itemsRev input = .ok items final :=
  parseItems_exists_ok_of_remainingCount_lt itemInvariantFree
    (input.remainingCount + 1) itemsRev input inputValid (by omega)

/-- A complete source-file parse succeeds under the single item premise. -/
theorem sourceFile_exists_ok
    (itemInvariantFree : ParseItemsItemInvariantFree)
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final := by
  rcases parseItems_production_exists_ok itemInvariantFree [] input inputValid
      with ⟨items, final, parsedItems⟩
  unfold sourceFile
  simp only [parsedItems]
  exact ⟨_, _, rfl⟩

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicTotalityProperties
/-! Conditional totality at the public syntax-parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Every valid lexer result produces a public parser output.  Preflight validity
rules out its error branch, nesting overflow is an ordinary diagnostic output,
and the complete-file branch uses the single item-parser premise.
-/
theorem parseLexed_exists_ok_of_validFor
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output := by
  unfold parseLexed
  rw [validateLexed_validFor_ok file lexed lexedValid]
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      dsimp only
      exact ⟨_, rfl⟩
  | none =>
      dsimp only
      have initialValid := State.initial_validFor lexedValid
      rcases FileInternals.sourceFile_exists_ok itemInvariantFree
          lexed.comments (State.initial file lexed) initialValid with
        ⟨parsed, final, grammar⟩
      simp only [grammar]
      exact ⟨_, rfl⟩

/-- No parser invariant can escape from valid already-tokenized input. -/
theorem parseLexed_ne_error_of_validFor
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file) (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error := by
  intro failed
  rcases parseLexed_exists_ok_of_validFor itemInvariantFree file lexed
      lexedValid with ⟨output, parsed⟩
  rw [parsed] at failed
  contradiction

/-- Public source parsing returns an output for every source file. -/
theorem parse_exists_ok
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) :
    ∃ output, parse file = .ok output := by
  rcases Lexer.lex_total_validFor file with
    ⟨lexed, lexing, lexedValid⟩
  rcases parseLexed_exists_ok_of_validFor itemInvariantFree file lexed
      lexedValid with ⟨output, parsing⟩
  unfold parse
  simp only [lexing, parsing]
  exact ⟨output, rfl⟩

/-- Under the item premise, no public syntax invariant error is reachable. -/
theorem parse_ne_error
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error := by
  intro failed
  rcases parse_exists_ok itemInvariantFree file with ⟨output, parsed⟩
  rw [parsed] at failed
  contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FilePlainTopItemTotalityProperties
/-! Conditional invariant freedom for top-level declaration dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Mapping a successful value cannot introduce an invariant reply. -/
theorem mapTopItem_invariantFreeOnValid {alpha : Type}
    {parser : Parser alpha} (wrap : alpha → TopItem)
    (invariantFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (mapTopItem parser wrap) := by
  intro input inputValid
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨wrap value, next, by
      unfold mapTopItem
      simp only [result]⟩
  · exact Or.inr ⟨failure, next, by
      unfold mapTopItem
      simp only [result]⟩

/-- The five declaration parsers whose totality remains an explicit input. -/
structure PlainTopItemTotalityContract : Prop where
  moduleFunction : Parser.InvariantFreeOnValid (functionDecl .module)
  enumDecl : Parser.InvariantFreeOnValid (enumDecl none)
  traitDecl : Parser.InvariantFreeOnValid traitDecl
  implDecl : Parser.InvariantFreeOnValid implDecl
  contractDecl : Parser.InvariantFreeOnValid contractDecl

/--
All declaration branches compose in implementation order. Pragma totality and
the terminal top-item rejection are discharged internally.
-/
theorem plainTopItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid plainTopItem := by
  intro input inputValid
  unfold plainTopItem
  split
  · exact (mapTopItem_invariantFreeOnValid wrapImport
      importDecl_invariantFreeOnValid) input inputValid
  · split
    · exact (mapTopItem_invariantFreeOnValid wrapExport
        exportDecl_invariantFreeOnValid) input inputValid
    · split
      · exact (mapTopItem_invariantFreeOnValid wrapPragma
          (fun state _stateValid => pragmaDecl_ordinary state))
          input inputValid
      · split
        · exact (mapTopItem_invariantFreeOnValid wrapTypeAlias
            typeAlias_invariantFreeOnValid) input inputValid
        · split
          · exact (mapTopItem_invariantFreeOnValid wrapFunction
              contract.moduleFunction) input inputValid
          · split
            · exact (mapTopItem_invariantFreeOnValid wrapEnum
                contract.enumDecl) input inputValid
            · split
              · exact (mapTopItem_invariantFreeOnValid wrapTrait
                  contract.traitDecl) input inputValid
              · split
                · exact (mapTopItem_invariantFreeOnValid wrapImpl
                    contract.implDecl) input inputValid
                · split
                  · exact (mapTopItem_invariantFreeOnValid wrapContract
                      contract.contractDecl) input inputValid
                  · exact (Parser.rejectAt_invariantFreeOnValid
                      (alpha := TopItem)
                      { head := .topItem, tail := [] } .topItem)
                      input inputValid

/-- Conditional plain dispatch cannot expose an invariant on valid input. -/
theorem plainTopItem_ne_invariant
    (contract : PlainTopItemTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  (plainTopItem_invariantFreeOnValid contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemTotalityProperties
/-! Conditional totality from derive-aware items through public parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Attaching a parsed derive attribute cannot introduce an invariant reply. -/
theorem attachDeriveAttribute_invariantFreeOnValid
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.InvariantFreeOnValid (attachDeriveAttribute derive item) := by
  intro input _inputValid
  rcases item with ⟨span, comments, value⟩
  cases value <;> left <;>
    simp [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]

/-- The derive-aware top-item parser inherits the six plain branch inputs. -/
theorem topItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid topItem := by
  intro input inputValid
  unfold topItem
  by_cases attributed : isSymbol input .hash
  · simp only [attributed, if_true]
    have deriveReply := deriveAttribute_validFor input inputValid
    rcases deriveAttribute_ordinary input inputValid with
      ⟨derive, afterDerive, deriveResult⟩ |
      ⟨failure, rejected, deriveResult⟩
    · rw [deriveResult] at deriveReply
      have plainValid :=
        (plainTopItem_contract contractDecl_canonical_inputs).validFor
          afterDerive deriveReply.2.1
      rcases plainTopItem_invariantFreeOnValid contract afterDerive
          deriveReply.2.1 with
        ⟨item, next, itemResult⟩ | ⟨failure, rejected, itemResult⟩
      · rw [itemResult] at plainValid
        rcases attachDeriveAttribute_invariantFreeOnValid derive item next
            plainValid.2.1 with
          ⟨attached, final, attachedResult⟩ |
          ⟨failure, rejected, attachedResult⟩
        · left
          exact ⟨attached, final, by
            simp only [deriveResult, itemResult, attachedResult]⟩
        · right
          exact ⟨failure, rejected, by
            simp only [deriveResult, itemResult, attachedResult]⟩
      · right
        exact ⟨failure, rejected, by
          simp only [deriveResult, itemResult]⟩
    · right
      exact ⟨failure, rejected, by simp only [deriveResult]⟩
  · simpa [attributed] using
      plainTopItem_invariantFreeOnValid contract input inputValid

/-- The file-loop item boundary has the same conditional totality contract. -/
theorem parseItemsItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid parseItemsItem := by
  simpa only [parseItemsItem] using topItem_invariantFreeOnValid contract

/-- Convert the compositional parser contract to the file-loop premise. -/
theorem parseItemsItemInvariantFree_of_plainTopItemContract
    (contract : PlainTopItemTotalityContract) :
    ParseItemsItemInvariantFree := by
  intro input inputValid error
  exact (parseItemsItem_invariantFreeOnValid contract).ne_invariant
    input inputValid error

/-- Complete-file parsing succeeds under exactly the six plain branch inputs. -/
theorem sourceFile_exists_ok_of_plainTopItemContract
    (contract : PlainTopItemTotalityContract)
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final :=
  sourceFile_exists_ok
    (parseItemsItemInvariantFree_of_plainTopItemContract contract)
    comments input inputValid

end Solcore.Syntax.Parser.FileInternals

namespace Solcore.Syntax.Parser

/-- Valid tokenized input produces output under the six branch inputs. -/
theorem parseLexed_exists_ok_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output :=
  parseLexed_exists_ok_of_validFor
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file lexed lexedValid

/-- No parser error escapes valid tokenized input under those same inputs. -/
theorem parseLexed_ne_error_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file)
    (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error :=
  parseLexed_ne_error_of_validFor
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file lexed lexedValid error

/-- Public source parsing succeeds under exactly the six branch inputs. -/
theorem parse_exists_ok_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file

/-- Public source parsing exposes no invariant error under those inputs. -/
theorem parse_ne_error_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error :=
  parse_ne_error
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file error

end Solcore.Syntax.Parser
end
