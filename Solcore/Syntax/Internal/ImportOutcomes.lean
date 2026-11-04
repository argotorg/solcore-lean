import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Internal.ExportOutcomes
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.TypeOutcomes

/-!
Properties of the declarative grammar of imports, module paths and pragmas: outcomes are
deterministic, and successful values and rejection points are unique. Nothing here
mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeHidingClauseOutcomeProperties
/-! Deterministic and exclusive broad ordinary hiding-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span
      value := kind
    }) : False :=
  absent ⟨span, present⟩

private theorem HidingClauseOrdinaryParses.marker_present
    {input output : Remainder} {clause : Syntax.HidingClause}
    (parsed : HidingClauseOrdinaryParses input clause output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .identifier ContextualKeyword.hiding.spelling
    } := by
  unfold HidingClauseOrdinaryParses HidingClauseParses at parsed
  rcases parsed with ⟨markerSpan, listSpan, markerToken, namesParsed,
    spanEq⟩
  exact ⟨markerSpan, markerToken⟩

/-- Ordinary hiding clauses have one final remainder. -/
theorem HidingClauseOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.HidingClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold HidingClauseOrdinaryParses HidingClauseParses at leftParsed rightParsed
  rcases leftParsed with ⟨leftMarkerSpan, leftListSpan, leftMarker,
    leftNames, leftSpanEq⟩
  rcases rightParsed with ⟨rightMarkerSpan, rightListSpan, rightMarker,
    rightNames, rightSpanEq⟩
  unfold NonemptySelectorListParses at leftNames rightNames
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftBrace) (closing := .rightBrace)
    (elementParses := SelectorNameOrdinaryParses)
    SelectorNameOrdinaryParses.output_unique leftNames rightNames

/-- Exact required-clause rejection excludes every ordinary success. -/
theorem HidingClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : HidingClauseRejects input rejected) :
    ¬ ∃ clause output,
      HidingClauseOrdinaryParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | markerMissing markerAbsent =>
      rcases successful.marker_present with ⟨span, markerPresent⟩
      exact absent_conflicts_token markerAbsent markerPresent
  | namesRejected markerSpan markerParsed namesRejected =>
      unfold HidingClauseOrdinaryParses HidingClauseParses at successful
      rcases successful with ⟨successfulMarkerSpan, listSpan,
        successfulMarker, namesParsed, spanEq⟩
      rw [markerParsed.2] at namesRejected
      unfold NonemptySelectorListParses at namesParsed
      exact namesRejected.disjointNonemptyTrailing
        selectorNameDeterministicOutcomeSpec (fun parsed => parsed)
        ⟨_, _, namesParsed⟩

/-- Required hiding clauses have deterministic and exclusive broad ordinary
outcomes. -/
theorem hidingClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec HidingClauseOrdinaryParses
      HidingClauseRejects where
  successOutputUnique := HidingClauseOrdinaryParses.output_unique
  successRejectDisjoint := HidingClauseRejects.disjointOrdinary

/-- Ordinary optional hiding clauses have one final remainder. -/
theorem OptionalHidingOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.HidingClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          rcases HidingClauseOrdinaryParses.marker_present rightClause with
            ⟨span, markerPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent markerPresent)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases HidingClauseOrdinaryParses.marker_present leftClause with
            ⟨span, markerPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent markerPresent)
      | present rightClause =>
          exact HidingClauseOrdinaryParses.output_unique leftClause
            rightClause

/-- Guarded optional rejection excludes absent and present ordinary success. -/
theorem OptionalHidingRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalHidingRejects input rejected) :
    ¬ ∃ hidden output,
      OptionalHidingOrdinaryParses input hidden output := by
  rintro ⟨hidden, output, successful⟩
  cases rejection with
  | present markerPresent clauseRejected =>
      cases successful with
      | absent markerAbsent =>
          rcases markerPresent with ⟨span, markerToken⟩
          exact absent_conflicts_token markerAbsent markerToken
      | present clauseParsed =>
          exact hidingClauseDeterministicOutcomeSpec.successRejectDisjoint
            clauseRejected ⟨_, _, clauseParsed⟩

/-- Optional hiding clauses have deterministic and exclusive broad ordinary
outcomes. -/
theorem optionalHidingDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalHidingOrdinaryParses
      OptionalHidingRejects where
  successOutputUnique := OptionalHidingOrdinaryParses.output_unique
  successRejectDisjoint := OptionalHidingRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeHidingClauseExactnessProperties
/-! Exact hiding-clause lists, covered ranges, and optional-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem hiding_marker_present {input output : Remainder}
    {clause : Syntax.HidingClause}
    (parsed : HidingClauseOrdinaryParses input clause output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      {span, value := .identifier ContextualKeyword.hiding.spelling} := by
  rcases parsed with ⟨markerSpan, _, markerToken, _⟩
  exact ⟨markerSpan, markerToken⟩

/-- Hiding-clause success fixes its nonempty names and marker-to-list span. -/
theorem HidingClauseOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.HidingClause}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftMarkerSpan, leftListSpan, leftMarker, leftNamesParsed, leftSpan⟩
  rcases rightParsed with ⟨rightMarkerSpan, rightListSpan, rightMarker, rightNamesParsed, rightSpan⟩
  have markerEq := leftMarker.token_unique rightMarker
  have namesEq := NonemptyTrailingDelimitedListParses.value_unique
    selectorNameExactOutcomeSpec leftNamesParsed rightNamesParsed
  cases left with
  | mk _ leftValue =>
      cases leftValue with
      | mk leftNames =>
          cases leftNames
          cases right with
          | mk _ rightValue =>
              cases rightValue with
              | mk rightNames =>
                  cases rightNames
                  simp_all [Syntax.NonemptyList.toList]

/-- Required hiding clauses have one complete successful result. -/
theorem HidingClauseOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.HidingClause}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Required hiding-clause rejection fixes its first failing endpoint. -/
theorem HidingClauseRejects.output_unique {input left right : Remainder}
    (leftRejected : HidingClauseRejects input left)
    (rightRejected : HidingClauseRejects input right) : left = right := by
  have listExact := nonemptyTrailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    selectorNameExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [absent_conflicts_exact, ExactTokenParses.output_unique,
      listExact.rejectOutputUnique]

/-- Required hiding clauses have fully functional success and rejection. -/
theorem hidingClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec HidingClauseOrdinaryParses HidingClauseRejects where
  toDeterministicOutcomeSpec := hidingClauseDeterministicOutcomeSpec
  successValueUnique := HidingClauseOrdinaryParses.value_unique
  rejectOutputUnique := HidingClauseRejects.output_unique

/-- Maximal optional hiding fixes both clause presence and the located AST. -/
theorem OptionalHidingOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.HidingClause}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause => exact False.elim (leftAbsent (hiding_marker_present rightClause))
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent (hiding_marker_present leftClause))
      | present rightClause =>
          exact congrArg some (hidingClauseExactOutcomeSpec.successValueUnique
            leftClause rightClause)

/-- Optional hiding fixes the complete successful result. -/
theorem OptionalHidingOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.HidingClause}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Optional hiding rejection inherits the required clause's exact endpoint. -/
theorem OptionalHidingRejects.output_unique {input left right : Remainder}
    (leftRejected : OptionalHidingRejects input left)
    (rightRejected : OptionalHidingRejects input right) : left = right := by
  cases leftRejected with
  | present _ leftClause =>
      cases rightRejected with
      | present _ rightClause => exact leftClause.output_unique rightClause

/-- Optional hiding has fully functional success and rejection outcomes. -/
theorem optionalHidingExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalHidingOrdinaryParses OptionalHidingRejects where
  toDeterministicOutcomeSpec := optionalHidingDeterministicOutcomeSpec
  successValueUnique := OptionalHidingOrdinaryParses.value_unique
  rejectOutputUnique := OptionalHidingRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedAliasOutcomeProperties
/-! Deterministic and exclusive broad outcomes for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token_variant {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordinary selected aliases have one final remainder. -/
theorem SelectedAliasOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present markerSpan markerToken nameToken tokensEq endIndexEq cursorEq =>
          exact False.elim
            (absent_conflicts_token_variant leftAbsent markerToken)
  | present markerSpan markerToken nameToken tokensEq endIndexEq cursorEq =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_token_variant rightAbsent markerToken)
      | present rightMarkerSpan rightMarkerToken rightNameToken rightTokensEq
          rightEndIndexEq rightCursorEq =>
          cases input
          cases afterLeft
          cases afterRight
          simp_all

/-- Selected-alias rejection stops immediately after the committed `as`. -/
theorem SelectedAliasRejects.output_eq {input rejected : Remainder}
    (rejection : SelectedAliasRejects input rejected) :
    rejected = { input with cursor := input.cursor + 1 } := by
  cases rejection with
  | nameRejected markerSpan markerParsed nameRejected =>
      cases nameRejected
      exact markerParsed.2

/-- Exact selected-alias rejection excludes absent and present success. -/
theorem SelectedAliasRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedAliasRejects input rejected) :
    ¬ ∃ alias output,
      SelectedAliasOrdinaryParses input alias output := by
  rintro ⟨alias, output, successful⟩
  cases rejection with
  | nameRejected markerSpan markerParsed nameRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_token_variant markerAbsent markerParsed.1
      | present successfulMarkerSpan successfulMarker nameToken tokensEq
          endIndexEq cursorEq =>
          cases nameRejected with
          | absent identifierAbsent =>
              rw [markerParsed.2] at identifierAbsent
              exact identifierAbsent ⟨_, _, by simpa using nameToken⟩

/-- Selected-import aliases have deterministic and exclusive broad ordinary
outcomes. -/
theorem selectedAliasDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedAliasOrdinaryParses
      SelectedAliasRejects where
  successOutputUnique := SelectedAliasOrdinaryParses.output_unique
  successRejectDisjoint := SelectedAliasRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedAliasExactnessProperties
/-! Exact optional aliases of selected imports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The committed alias marker fixes its complete optional identifier. -/
theorem SelectedAliasOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Identifier}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightMarker _ _ _ _ => exact False.elim (leftAbsent ⟨_, rightMarker⟩)
  | @present _ leftNameValue _ leftMarker leftName _ _ _ =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftMarker⟩)
      | @present _ rightNameValue _ _ rightName _ _ _ =>
          have nameEq := leftName.token_unique rightName
          congr 1
          cases leftNameValue
          cases rightNameValue
          simp_all

/-- Alias success fixes both the optional located identifier and remainder. -/
theorem SelectedAliasOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Identifier}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A malformed alias has one endpoint immediately after its marker. -/
theorem SelectedAliasRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedAliasRejects input left)
    (rightRejected : SelectedAliasRejects input right) : left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Optional selected aliases have exact values and rejecting endpoints. -/
theorem selectedAliasExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedAliasOrdinaryParses SelectedAliasRejects where
  toDeterministicOutcomeSpec := selectedAliasDeterministicOutcomeSpec
  successValueUnique := SelectedAliasOrdinaryParses.value_unique
  rejectOutputUnique := SelectedAliasRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportOutcomeProperties
/-! Deterministic and exclusive broad outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import success has one final remainder. -/
theorem SelectedImportOrdinaryParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold SelectedImportOrdinaryParses SelectedImportParses at leftParsed rightParsed
  rcases leftParsed with
    ⟨afterLeftSource, leftSource, leftAlias, leftSpan⟩
  rcases rightParsed with
    ⟨afterRightSource, rightSource, rightAlias, rightSpan⟩
  have afterSourceEq :=
    selectorNameDeterministicOutcomeSpec.successOutputUnique leftSource
      rightSource
  subst afterRightSource
  exact selectedAliasDeterministicOutcomeSpec.successOutputUnique leftAlias
    rightAlias

/-- Exact selected-import rejection excludes every ordinary success. -/
theorem SelectedImportRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedImportRejects input rejected) :
    ¬ ∃ selection output,
      SelectedImportOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  unfold SelectedImportOrdinaryParses SelectedImportParses at successful
  rcases successful with
    ⟨afterSource, sourceParsed, aliasParsed, spanEq⟩
  cases rejection with
  | sourceRejected sourceRejected =>
      exact selectorNameDeterministicOutcomeSpec.successRejectDisjoint
        sourceRejected ⟨_, afterSource, sourceParsed⟩
  | aliasRejected rejectedSourceParsed aliasRejected =>
      have afterSourceEq :=
        selectorNameDeterministicOutcomeSpec.successOutputUnique
          rejectedSourceParsed sourceParsed
      subst afterSource
      exact selectedAliasDeterministicOutcomeSpec.successRejectDisjoint
        aliasRejected ⟨_, output, aliasParsed⟩

/-- Selected imports have deterministic and exclusive broad ordinary
outcomes. -/
theorem selectedImportDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedImportOrdinaryParses
      SelectedImportRejects where
  successOutputUnique := SelectedImportOrdinaryParses.output_unique
  successRejectDisjoint := SelectedImportRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportExactnessProperties
/-! Exact source names, optional aliases, and covered selected-import spans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A selected import fixes its full source/alias record and covered span. -/
theorem SelectedImportOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftAfterSource, leftSource, leftAlias, leftSpan⟩
  rcases rightParsed with ⟨rightAfterSource, rightSource, rightAlias, rightSpan⟩
  rcases selectorNameExactOutcomeSpec.successResultUnique leftSource rightSource with
    ⟨sourceEq, afterSourceEq⟩
  subst afterSourceEq
  have aliasEq := selectedAliasExactOutcomeSpec.successValueUnique leftAlias rightAlias
  cases left with
  | mk _ leftValue =>
      cases right with
      | mk _ rightValue =>
          cases leftValue
          cases rightValue
          simp_all

/-- Selected-import success fixes both the full located AST and remainder. -/
theorem SelectedImportOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- The first failing selected-import stage fixes its exact endpoint. -/
theorem SelectedImportRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedImportRejects input left)
    (rightRejected : SelectedImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [selectorNameExactOutcomeSpec.successOutputUnique,
      selectorNameExactOutcomeSpec.rejectOutputUnique,
      selectorNameExactOutcomeSpec.successRejectDisjoint,
      SelectedAliasRejects.output_unique]

/-- Complete selected-import outcomes have exact values and rejecting endpoints. -/
theorem selectedImportExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedImportOrdinaryParses SelectedImportRejects where
  toDeterministicOutcomeSpec := selectedImportDeterministicOutcomeSpec
  successValueUnique := SelectedImportOrdinaryParses.value_unique
  rejectOutputUnique := SelectedImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportsOutcomeProperties
/-! Deterministic and exclusive broad outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import lists have one final remainder. -/
theorem SelectedImportsOrdinaryParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold SelectedImportsOrdinaryParses SelectedImportsParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftBrace) (closing := .rightBrace)
    (elementParses := SelectedImportOrdinaryParses)
    SelectedImportOrdinaryParses.output_unique leftParsed rightParsed

/-- Exact list rejection excludes every ordinary selected-import-list
success. -/
theorem SelectedImportsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedImportsRejects input rejected) :
    ¬ ∃ selections output,
      SelectedImportsOrdinaryParses input selections output := by
  rintro ⟨selections, output, parsed⟩
  unfold SelectedImportsOrdinaryParses SelectedImportsParses at parsed
  exact rejection.disjointNonemptyTrailing
    selectedImportDeterministicOutcomeSpec (fun ordinary => ordinary)
      ⟨_, _, parsed⟩

/-- Required selected-import lists have deterministic and exclusive broad
ordinary outcomes. -/
theorem selectedImportsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedImportsOrdinaryParses
      SelectedImportsRejects where
  successOutputUnique := SelectedImportsOrdinaryParses.output_unique
  successRejectDisjoint := SelectedImportsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportsExactnessProperties
/-! Exact nonempty source-order selected-import lists, including delimiter spans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A selected-import list fixes its nonempty elements and complete range. -/
theorem SelectedImportsOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) : left = right := by
  have valueEq := NonemptyTrailingDelimitedListParses.value_unique
    selectedImportExactOutcomeSpec leftParsed rightParsed
  cases left with
  | mk _ leftElements =>
      cases leftElements
      cases right with
      | mk _ rightElements =>
          cases rightElements
          simp_all [Syntax.NonemptyList.toList]

/-- The complete selected-import-list result is unique. -/
theorem SelectedImportsOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A selected-import list has one exact first-failure endpoint. -/
theorem SelectedImportsRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedImportsRejects input left)
    (rightRejected : SelectedImportsRejects input right) : left = right :=
  (nonemptyTrailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    selectedImportExactOutcomeSpec).rejectOutputUnique leftRejected rightRejected

/-- Required selected-import lists are fully exact. -/
theorem selectedImportsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedImportsOrdinaryParses SelectedImportsRejects where
  toDeterministicOutcomeSpec := selectedImportsDeterministicOutcomeSpec
  successValueUnique := SelectedImportsOrdinaryParses.value_unique
  rejectOutputUnique := SelectedImportsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
/-! Deterministic and exclusive broad ordinary import-terminator outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem topItemStart_conflicts_absent {input : Remainder}
    (starts : ImportTerminatorTopItemStartsAt input)
    (absent : TopItemKindsAbsentAt input
      ImportTerminatorTopItemStartKinds) : False := by
  rcases starts with ⟨kind, member, span, token⟩
  exact absent kind member ⟨span, token⟩

/-- Ordinary import terminators have one final remainder. -/
theorem ImportTerminatorOrdinaryParses.output_unique (lastSpan : SourceSpan)
    {input : Remainder} {left right : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImportTerminatorOrdinaryParses lastSpan input left afterLeft)
    (rightParsed :
      ImportTerminatorOrdinaryParses lastSpan input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact exactToken_output_unique leftSemicolon rightSemicolon
      | recovered rightAbsent rightStarts =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftSemicolon)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact False.elim
            (absent_conflicts_exact leftAbsent rightSemicolon)
      | recovered rightAbsent rightStarts => rfl

/-- Missing import-terminator rejection excludes every ordinary success. -/
theorem ImportTerminatorRejects.disjointOrdinary (lastSpan : SourceSpan)
    {input rejected : Remainder}
    (rejection : ImportTerminatorRejects input rejected) :
    ¬ ∃ span output,
      ImportTerminatorOrdinaryParses lastSpan input span output := by
  rintro ⟨span, output, successful⟩
  cases rejection with
  | missing semicolonAbsent topItemStartAbsent =>
      cases successful with
      | semicolon semicolonSpan semicolonParsed =>
          exact absent_conflicts_exact semicolonAbsent semicolonParsed
      | recovered otherSemicolonAbsent topItemStarts =>
          exact topItemStart_conflicts_absent topItemStarts
            topItemStartAbsent

/-- Import terminators have deterministic and exclusive broad ordinary
outcomes for each fixed preceding span. -/
theorem importTerminatorDeterministicOutcomeSpec (lastSpan : SourceSpan) :
    DeterministicOutcomeSpec (ImportTerminatorOrdinaryParses lastSpan)
      ImportTerminatorRejects where
  successOutputUnique :=
    ImportTerminatorOrdinaryParses.output_unique lastSpan
  successRejectDisjoint :=
    ImportTerminatorRejects.disjointOrdinary lastSpan

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties
/-! Exact import termination, including diagnosed nonconsuming recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A shared preceding span fixes both consumed and recovered terminator values. -/
theorem ImportTerminatorOrdinaryParses.result_unique (lastSpan : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : SourceSpan}
    (leftParsed : ImportTerminatorOrdinaryParses lastSpan input left afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses lastSpan input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | semicolon _ leftToken =>
      cases rightParsed with
      | semicolon _ rightToken => exact leftToken.result_unique rightToken
      | recovered absent _ => exact False.elim (absent ⟨_, leftToken.1⟩)
  | recovered absent _ =>
      cases rightParsed with
      | semicolon _ rightToken => exact False.elim (absent ⟨_, rightToken.1⟩)
      | recovered => exact ⟨rfl, rfl⟩

/-- Import-terminator rejection fixes the original complete remainder. -/
theorem ImportTerminatorRejects.output_unique {input left right : Remainder}
    (leftRejected : ImportTerminatorRejects input left)
    (rightRejected : ImportTerminatorRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- The full import-terminator contract is exact at each fixed preceding span. -/
theorem importTerminatorExactOutcomeSpec (lastSpan : SourceSpan) :
    ExactDeterministicOutcomeSpec (ImportTerminatorOrdinaryParses lastSpan)
      ImportTerminatorRejects where
  toDeterministicOutcomeSpec := importTerminatorDeterministicOutcomeSpec lastSpan
  successValueUnique := fun left right =>
    (left.result_unique lastSpan right).1
  rejectOutputUnique := ImportTerminatorRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaItemsOutcomeProperties
/-! Deterministic and exclusive broad outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : PragmaItemsTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- A pragma-item suffix has one successful final remainder. -/
theorem PragmaItemsTailOrdinaryParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => rfl
      | trailing _ rightCommaPresent _ _ =>
          exact False.elim
            (present_conflicts_absent rightCommaPresent leftCommaAbsent)
      | next _ rightCommaPresent _ _ _ _ =>
          exact False.elim
            (present_conflicts_absent rightCommaPresent leftCommaAbsent)
  | trailing leftCommaSpan leftCommaPresent leftComma leftSemicolon =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (present_conflicts_absent leftCommaPresent rightCommaAbsent)
      | trailing _ _ rightComma rightSemicolon =>
          exact exactToken_output_unique leftComma rightComma
      | next _ _ rightComma rightSemicolonAbsent rightItem rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (present_conflicts_absent leftSemicolon rightSemicolonAbsent)
  | next leftCommaSpan leftCommaPresent leftComma leftSemicolonAbsent
      leftItem leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (present_conflicts_absent leftCommaPresent rightCommaAbsent)
      | trailing _ _ rightComma rightSemicolon =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (present_conflicts_absent rightSemicolon leftSemicolonAbsent)
      | next _ _ rightComma rightSemicolonAbsent rightItem rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterItemEq := IdentifierParses.output_unique leftItem rightItem
          subst afterItemEq
          exact inductionHypothesis rightTail

/-- Exact pragma-tail rejection excludes every successful suffix. -/
theorem PragmaItemsTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : PragmaItemsTailRejects input rejected) :
    ¬ ∃ items output,
      PragmaItemsTailOrdinaryParses input items output := by
  induction rejection with
  | identifierRejected rejectedCommaSpan rejectedCommaPresent rejectedComma
      rejectedSemicolonAbsent itemRejected =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done successfulCommaAbsent =>
          exact present_conflicts_absent rejectedCommaPresent
            successfulCommaAbsent
      | trailing _ _ successfulComma successfulSemicolon =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact present_conflicts_absent successfulSemicolon
            rejectedSemicolonAbsent
      | next _ _ successfulComma successfulSemicolonAbsent itemParsed tail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            itemRejected ⟨_, _, itemParsed⟩
  | laterRejected rejectedCommaSpan rejectedCommaPresent rejectedComma
      rejectedSemicolonAbsent rejectedItem tailRejected inductionHypothesis =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done successfulCommaAbsent =>
          exact present_conflicts_absent rejectedCommaPresent
            successfulCommaAbsent
      | trailing _ _ successfulComma successfulSemicolon =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact present_conflicts_absent successfulSemicolon
            rejectedSemicolonAbsent
      | next _ _ successfulComma successfulSemicolonAbsent successfulItem
          successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterItemEq := IdentifierParses.output_unique rejectedItem
            successfulItem
          subst afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Deterministic broad outcomes for pragma-item suffixes. -/
theorem pragmaItemsTailDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaItemsTailOrdinaryParses
      PragmaItemsTailRejects where
  successOutputUnique := PragmaItemsTailOrdinaryParses.output_unique
  successRejectDisjoint := PragmaItemsTailRejects.disjointOrdinary

/-- A complete pragma-item scan has one successful final remainder. -/
theorem PragmaItemsOrdinaryParses.output_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | empty leftSemicolon =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightSemicolonAbsent rightFirst rightTail =>
          exact False.elim
            (present_conflicts_absent leftSemicolon rightSemicolonAbsent)
  | nonempty leftSemicolonAbsent leftFirst leftTail =>
      cases rightParsed with
      | empty rightSemicolon =>
          exact False.elim
            (present_conflicts_absent rightSemicolon leftSemicolonAbsent)
      | nonempty rightSemicolonAbsent rightFirst rightTail =>
          have afterFirstEq := IdentifierParses.output_unique leftFirst
            rightFirst
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Exact complete pragma-item rejection excludes every successful scan. -/
theorem PragmaItemsRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : PragmaItemsRejects input rejected) :
    ¬ ∃ items output, PragmaItemsOrdinaryParses input items output := by
  rintro ⟨items, output, successful⟩
  cases rejection with
  | firstIdentifierRejected semicolonAbsent firstRejected =>
      cases successful with
      | empty semicolonPresent =>
          exact present_conflicts_absent semicolonPresent semicolonAbsent
      | nonempty successfulSemicolonAbsent firstParsed tailParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            firstRejected ⟨_, _, firstParsed⟩
  | tailRejected semicolonAbsent rejectedFirst tailRejected =>
      cases successful with
      | empty semicolonPresent =>
          exact present_conflicts_absent semicolonPresent semicolonAbsent
      | nonempty successfulSemicolonAbsent successfulFirst successfulTail =>
          have afterFirstEq := IdentifierParses.output_unique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact pragmaItemsTailDeterministicOutcomeSpec.successRejectDisjoint
            tailRejected ⟨_, _, successfulTail⟩

/-- Deterministic broad outcomes for the complete pragma-item scan. -/
theorem pragmaItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaItemsOrdinaryParses PragmaItemsRejects where
  successOutputUnique := PragmaItemsOrdinaryParses.output_unique
  successRejectDisjoint := PragmaItemsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaOutcomeProperties
/-! Deterministic and exclusive broad outcomes for complete pragmas. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary complete pragma success has one final remainder. -/
theorem PragmaDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftSemicolonSpan leftKeyword leftName leftItems
      leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightSemicolonSpan rightKeyword rightName
          rightItems rightSemicolon =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterItemsEq := leftItems.output_unique rightItems
          subst afterItemsEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact complete pragma rejection excludes every ordinary success. -/
theorem PragmaDeclRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : PragmaDeclRejects input rejected) :
    ¬ ∃ declaration output,
      PragmaDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulSemicolonSpan successfulKeyword
      successfulName successfulItems successfulSemicolon =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | itemsRejected rejectedKeywordSpan rejectedKeyword rejectedName
          itemsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact pragmaItemsDeterministicOutcomeSpec.successRejectDisjoint
            itemsRejected ⟨_, _, successfulItems⟩
      | semicolonMissing rejectedKeywordSpan rejectedKeyword rejectedName
          rejectedItems semicolonAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterItemsEq := rejectedItems.output_unique successfulItems
          subst afterItemsEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Complete broad pragmas have deterministic and exclusive ordinary
outcomes. -/
theorem pragmaDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PragmaDeclOrdinaryParses PragmaDeclRejects where
  successOutputUnique := PragmaDeclOrdinaryParses.output_unique
  successRejectDisjoint := PragmaDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaItemsExactnessProperties
/-! Exact values and rejection endpoints for forward-order pragma items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragmaItems_present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : PragmaItemsTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- One pragma-item suffix fixes its complete source-order identifier list. -/
theorem PragmaItemsTailOrdinaryParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent]
  | trailing leftCommaSpan leftCommaPresent leftComma leftSemicolon =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent,
          ExactTokenParses.output_unique]
  | next leftCommaSpan leftCommaPresent leftComma leftSemicolonAbsent
      leftItem leftTail inductionHypothesis =>
      cases rightParsed <;>
        grind [pragmaItems_present_conflicts_absent,
          ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.successResultUnique]

/-- One pragma-item suffix fixes its identifiers and final remainder. -/
theorem PragmaItemsTailOrdinaryParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsTailOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsTailOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The first rejecting pragma-item suffix stage fixes its exact endpoint. -/
theorem PragmaItemsTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaItemsTailRejects input left)
    (rightRejected : PragmaItemsTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | identifierRejected leftCommaSpan leftCommaPresent leftComma
      leftSemicolonAbsent leftItem =>
      cases rightRejected <;>
        grind [ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.rejectOutputUnique,
          identifierExactOutcomeSpec.successRejectDisjoint]
  | laterRejected leftCommaSpan leftCommaPresent leftComma
      leftSemicolonAbsent leftItem leftTail inductionHypothesis =>
      cases rightRejected <;>
        grind [ExactTokenParses.output_unique,
          identifierExactOutcomeSpec.successOutputUnique,
          identifierExactOutcomeSpec.successRejectDisjoint]

/-- Pragma-item suffixes have unconditionally exact ordinary outcomes. -/
theorem pragmaItemsTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaItemsTailOrdinaryParses
      PragmaItemsTailRejects where
  toDeterministicOutcomeSpec := pragmaItemsTailDeterministicOutcomeSpec
  successValueUnique := PragmaItemsTailOrdinaryParses.value_unique
  rejectOutputUnique := PragmaItemsTailRejects.output_unique

/-- A complete pragma-item scan fixes its source-order identifier list. -/
theorem PragmaItemsOrdinaryParses.value_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [pragmaItems_present_conflicts_absent,
      identifierExactOutcomeSpec.successResultUnique,
      pragmaItemsTailExactOutcomeSpec.successValueUnique]

/-- A complete pragma-item scan fixes its identifiers and final remainder. -/
theorem PragmaItemsOrdinaryParses.result_unique
    {input : Remainder} {left right : List Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaItemsOrdinaryParses input left afterLeft)
    (rightParsed : PragmaItemsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete pragma-item rejection fixes its exact first failed endpoint. -/
theorem PragmaItemsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaItemsRejects input left)
    (rightRejected : PragmaItemsRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      pragmaItemsTailExactOutcomeSpec.rejectOutputUnique]

/-- Complete pragma-item scans have unconditionally exact ordinary outcomes. -/
theorem pragmaItemsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaItemsOrdinaryParses
      PragmaItemsRejects where
  toDeterministicOutcomeSpec := pragmaItemsDeterministicOutcomeSpec
  successValueUnique := PragmaItemsOrdinaryParses.value_unique
  rejectOutputUnique := PragmaItemsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaExactnessProperties
/-! Exact pragma declarations, including located names and ordered items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragma_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Broad pragma success fixes its marker-to-semicolon span, located name,
and complete source-order item list. -/
theorem PragmaDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique,
      identifierExactOutcomeSpec.successResultUnique,
      pragmaItemsExactOutcomeSpec.successResultUnique]

/-- Broad pragma success fixes its complete AST and final remainder. -/
theorem PragmaDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.PragmaDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PragmaDeclOrdinaryParses input left afterLeft)
    (rightParsed : PragmaDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The prioritized first rejected pragma stage fixes its exact endpoint. -/
theorem PragmaDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PragmaDeclRejects input left)
    (rightRejected : PragmaDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [pragma_absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      pragmaItemsExactOutcomeSpec.successOutputUnique,
      pragmaItemsExactOutcomeSpec.successRejectDisjoint,
      pragmaItemsExactOutcomeSpec.rejectOutputUnique]

/-- Complete pragmas have unconditional exact AST, remainder, and rejection
endpoint outcomes; no diagnostic payload equality is asserted. -/
theorem pragmaDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PragmaDeclOrdinaryParses
      PragmaDeclRejects where
  toDeterministicOutcomeSpec := pragmaDeclDeterministicOutcomeSpec
  successValueUnique := PragmaDeclOrdinaryParses.value_unique
  rejectOutputUnique := PragmaDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeModulePathOutcomeProperties
/-! Deterministic and exclusive broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem at_conflicts_identifier {input : Remainder}
    {markerSpan : SourceSpan} {name : Syntax.Identifier}
    (markerToken : TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .symbol .at
    })
    (nameToken : TokenAt input.tokens input.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    }) : False := by
  have kindEq : (.symbol .at : TokenKind) = .identifier name.value :=
    typeTokenAt_kind_eq markerToken nameToken
  cases kindEq

/-- Ordinary module paths have one final remainder. -/
theorem ModulePathOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | «local» leftName =>
      cases rightParsed with
      | «local» rightName =>
          exact QualifiedNameParses.output_unique leftName rightName
      | externalPackage markerSpan markerToken rightName =>
          rcases leftName with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact False.elim (at_conflicts_identifier markerToken firstToken)
  | externalPackage markerSpan markerToken leftName =>
      cases rightParsed with
      | «local» rightName =>
          rcases rightName with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact False.elim (at_conflicts_identifier markerToken firstToken)
      | externalPackage rightMarkerSpan rightMarkerToken rightName =>
          exact QualifiedNameParses.output_unique leftName rightName

/-- Exact module-path rejection excludes every ordinary success. -/
theorem ModulePathRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ModulePathRejects input rejected) :
    ¬ ∃ path output, ModulePathOrdinaryParses input path output := by
  rintro ⟨path, output, successful⟩
  cases rejection with
  | localRejected markerAbsent nameRejected =>
      cases successful with
      | «local» nameParsed =>
          exact nameRejected.disjointQualified ⟨_, _, nameParsed⟩
      | externalPackage markerSpan markerToken nameParsed =>
          exact typeTokenAbsent_conflicts_token markerAbsent markerToken
  | externalRejected markerSpan markerParsed nameRejected =>
      cases successful with
      | «local» nameParsed =>
          rcases nameParsed with
            ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
          exact at_conflicts_identifier markerParsed.1 firstToken
      | externalPackage successfulMarkerSpan successfulMarker nameParsed =>
          rw [markerParsed.2] at nameRejected
          exact nameRejected.disjointQualified ⟨_, _, nameParsed⟩

/-- Module paths have deterministic and exclusive broad ordinary outcomes. -/
theorem modulePathDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ModulePathOrdinaryParses ModulePathRejects where
  successOutputUnique := ModulePathOrdinaryParses.output_unique
  successRejectDisjoint := ModulePathRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeModulePathExactnessProperties
/-! Exact local and external-package module-path values and rejecting endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem at_conflicts_qualified {input output : Remainder}
    {markerSpan : SourceSpan} {name : Syntax.QualifiedName}
    (marker : TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan, value := .symbol .at })
    (parsed : QualifiedNameParses input name output) : False := by
  have tokenEq := marker.token_unique parsed.2.2.1
  have kindEq := congrArg (fun token : Token => token.value) tokenEq
  cases kindEq

/-- The selected local/external branch fixes every marker, name, and covering span. -/
theorem ModulePathOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | «local» leftName =>
      cases rightParsed with
      | «local» rightName =>
          cases leftName.value_unique rightName
          rfl
      | externalPackage _ rightMarker _ =>
          exact False.elim (at_conflicts_qualified rightMarker leftName)
  | externalPackage leftSpan leftMarker leftName =>
      cases rightParsed with
      | «local» rightName =>
          exact False.elim (at_conflicts_qualified leftMarker rightName)
      | externalPackage rightSpan rightMarker rightName =>
          have spanEq := congrArg (fun token : Token => token.span)
            (leftMarker.token_unique rightMarker)
          subst spanEq
          cases leftName.value_unique rightName
          rfl

/-- An ordinary module path fixes its complete AST and final remainder. -/
theorem ModulePathOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Local/external branch priority fixes the exact failing module-path endpoint. -/
theorem ModulePathRejects.output_unique {input left right : Remainder}
    (leftRejected : ModulePathRejects input left)
    (rightRejected : ModulePathRejects input right) : left = right := by
  cases leftRejected with
  | localRejected leftAbsent leftName =>
      cases rightRejected with
      | localRejected _ rightName => exact leftName.output_unique rightName
      | externalRejected _ rightMarker _ =>
          exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | externalRejected _ leftMarker leftName =>
      cases rightRejected with
      | localRejected rightAbsent _ =>
          exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | externalRejected _ rightMarker rightName =>
          have outputEq := leftMarker.output_unique rightMarker
          subst outputEq
          exact leftName.output_unique rightName

/-- Module paths have fully exact successful values and rejecting endpoints. -/
theorem modulePathExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ModulePathOrdinaryParses ModulePathRejects where
  toDeterministicOutcomeSpec := modulePathDeterministicOutcomeSpec
  successValueUnique := ModulePathOrdinaryParses.value_unique
  rejectOutputUnique := ModulePathRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamespaceImportOutcomeProperties
/-! Deterministic and exclusive broad namespace-import helper outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem importTerminator_cross_output_unique
    {leftLast rightLast : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : ImportTerminatorOrdinaryParses leftLast input leftSpan
      afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses rightLast input rightSpan
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSemicolonSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact exactToken_output_unique leftSemicolon rightSemicolon
      | recovered rightAbsent rightStarts =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftSemicolon)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact False.elim
            (absent_conflicts_exact leftAbsent rightSemicolon)
      | recovered rightAbsent rightStarts => rfl

/-- Ordinary namespace-import helper success has one final remainder. -/
theorem NamespaceImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftStarSpan leftAsSpan leftFromSpan leftEndSpan leftStar leftAs
        leftAlias leftFrom leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightStarSpan rightAsSpan rightFromSpan rightEndSpan rightStar
            rightAs rightAlias rightFrom rightPath rightTerminator =>
          have afterStarEq := exactToken_output_unique leftStar rightStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique leftAs rightAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique leftAlias
            rightAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique leftFrom rightFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique leftPath
            rightPath
          subst afterPathEq
          exact importTerminator_cross_output_unique leftTerminator
            rightTerminator

/-- Exact namespace-import rejection excludes every broad ordinary success. -/
theorem NamespaceImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : NamespaceImportRejects input rejected) :
    ¬ ∃ declaration output,
      NamespaceImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulStarSpan successfulAsSpan successfulFromSpan
        successfulEndSpan successfulStar successfulAs successfulAlias
        successfulFrom successfulPath successfulTerminator =>
      cases rejection with
      | starMissing starAbsent =>
          exact absent_conflicts_exact starAbsent successfulStar
      | asMissing rejectedStarSpan rejectedStar asAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          exact absent_conflicts_exact asAbsent successfulAs
      | aliasRejected rejectedStarSpan rejectedAsSpan rejectedStar rejectedAs
            aliasRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            aliasRejected ⟨_, _, successfulAlias⟩
      | fromMissing rejectedStarSpan rejectedAsSpan rejectedStar rejectedAs
            rejectedAlias fromAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedStarSpan rejectedAsSpan rejectedFromSpan
            rejectedStar rejectedAs rejectedAlias rejectedFrom pathRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | terminatorRejected rejectedStarSpan rejectedAsSpan rejectedFromSpan
            rejectedStar rejectedAs rejectedAlias rejectedFrom rejectedPath
            terminatorRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterAsEq := exactToken_output_unique rejectedAs successfulAs
          subst afterAsEq
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            successfulAlias
          subst afterAliasEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact ImportTerminatorRejects.disjointOrdinary _
            terminatorRejected ⟨_, _, successfulTerminator⟩

/-- Namespace-import helpers have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem namespaceImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (NamespaceImportOrdinaryParses start)
      NamespaceImportRejects where
  successOutputUnique := NamespaceImportOrdinaryParses.output_unique start
  successRejectDisjoint := NamespaceImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamespaceImportExactnessProperties
/-! Exact namespace-import aliases, paths, spans, and first-failure endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A namespace payload fixes its alias, module path, and complete covered span. -/
theorem NamespaceImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ _ _ _ leftStar leftAs leftAlias leftFrom leftPath leftTerminator =>
      cases rightParsed with
      | parsed _ _ _ _ rightStar rightAs rightAlias rightFrom rightPath rightTerminator =>
          have afterStarEq := leftStar.output_unique rightStar
          subst afterStarEq
          have afterAsEq := leftAs.output_unique rightAs
          subst afterAsEq
          rcases leftAlias.result_unique rightAlias with ⟨aliasEq, afterAliasEq⟩
          subst aliasEq
          subst afterAliasEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Namespace-import success fixes the full located AST and remainder. -/
theorem NamespaceImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : NamespaceImportOrdinaryParses start input left afterLeft)
    (rightParsed : NamespaceImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- Namespace-import rejection fixes the first unsuccessful stage's endpoint. -/
theorem NamespaceImportRejects.output_unique {input left right : Remainder}
    (leftRejected : NamespaceImportRejects input left)
    (rightRejected : NamespaceImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Namespace-import payload outcomes are fully exact at a fixed outer start. -/
theorem namespaceImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (NamespaceImportOrdinaryParses start)
      NamespaceImportRejects where
  toDeterministicOutcomeSpec := namespaceImportDeterministicOutcomeSpec start
  successValueUnique := NamespaceImportOrdinaryParses.value_unique start
  rejectOutputUnique := NamespaceImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWildcardImportOutcomeProperties
/-! Deterministic and exclusive broad wildcard-import outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary wildcard-import payloads have one final remainder. -/
theorem WildcardImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftStarSpan leftFromSpan leftStar leftFrom leftPath leftHiding
        leftTerminator =>
      cases rightParsed with
      | parsed rightStarSpan rightFromSpan rightStar rightFrom rightPath
            rightHiding rightTerminator =>
          have afterStarEq := exactToken_output_unique leftStar rightStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique leftFrom rightFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique leftPath
            rightPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            leftHiding rightHiding
          subst afterHidingEq
          exact importTerminator_cross_output_unique leftTerminator
            rightTerminator

/-- Exact wildcard-import rejection excludes every broad ordinary success. -/
theorem WildcardImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : WildcardImportRejects input rejected) :
    ¬ ∃ declaration output,
      WildcardImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulStarSpan successfulFromSpan successfulStar
        successfulFrom successfulPath successfulHiding
        successfulTerminator =>
      cases rejection with
      | starMissing starAbsent =>
          exact absent_conflicts_exact starAbsent successfulStar
      | fromMissing rejectedStarSpan rejectedStar fromAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom pathRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | hidingRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom rejectedPath hidingRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact optionalHidingDeterministicOutcomeSpec.successRejectDisjoint
            hidingRejected ⟨_, _, successfulHiding⟩
      | terminatorRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom rejectedPath rejectedHiding terminatorRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            rejectedHiding successfulHiding
          subst afterHidingEq
          exact ImportTerminatorRejects.disjointOrdinary _
            terminatorRejected ⟨_, _, successfulTerminator⟩

/-- Wildcard-import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem wildcardImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (WildcardImportOrdinaryParses start)
      WildcardImportRejects where
  successOutputUnique := WildcardImportOrdinaryParses.output_unique start
  successRejectDisjoint := WildcardImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWildcardImportExactnessProperties
/-! Exact wildcard imports, including optional hiding and recovered terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The fixed outer start and exact optional hiding fix the complete wildcard AST. -/
theorem WildcardImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ _ leftStar leftFrom leftPath leftHiding leftTerminator =>
      cases rightParsed with
      | parsed _ _ rightStar rightFrom rightPath rightHiding rightTerminator =>
          have afterStarEq := leftStar.output_unique rightStar
          subst afterStarEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          rcases optionalHidingExactOutcomeSpec.successResultUnique leftHiding rightHiding with
            ⟨hidingEq, afterHidingEq⟩
          subst hidingEq
          subst afterHidingEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Wildcard-import success fixes the full located AST and remainder. -/
theorem WildcardImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A wildcard payload fixes the first failing path, hiding, or terminator endpoint. -/
theorem WildcardImportRejects.output_unique {input left right : Remainder}
    (leftRejected : WildcardImportRejects input left)
    (rightRejected : WildcardImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      optionalHidingExactOutcomeSpec.successOutputUnique,
      optionalHidingExactOutcomeSpec.rejectOutputUnique,
      optionalHidingExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Wildcard-import payload outcomes are fully exact at a fixed outer start. -/
theorem wildcardImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (WildcardImportOrdinaryParses start)
      WildcardImportRejects where
  toDeterministicOutcomeSpec := wildcardImportDeterministicOutcomeSpec start
  successValueUnique := WildcardImportOrdinaryParses.value_unique start
  rejectOutputUnique := WildcardImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectiveImportOutcomeProperties
/-! Deterministic and exclusive broad selective-import outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selective-import payloads have one final remainder. -/
theorem SelectiveImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftFromSpan leftSelection leftFrom leftPath leftHiding
        leftTerminator =>
      cases rightParsed with
      | parsed rightFromSpan rightSelection rightFrom rightPath rightHiding
            rightTerminator =>
          have afterSelectionEq := SelectedImportsOrdinaryParses.output_unique
            leftSelection rightSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique leftFrom rightFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique leftPath
            rightPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            leftHiding rightHiding
          subst afterHidingEq
          exact importTerminator_cross_output_unique leftTerminator
            rightTerminator

/-- Exact selective-import rejection excludes every broad ordinary success. -/
theorem SelectiveImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : SelectiveImportRejects input rejected) :
    ¬ ∃ declaration output,
      SelectiveImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulFromSpan successfulSelection successfulFrom
        successfulPath successfulHiding successfulTerminator =>
      cases rejection with
      | selectionRejected selectionRejected =>
          exact selectedImportsDeterministicOutcomeSpec.successRejectDisjoint
            selectionRejected ⟨_, _, successfulSelection⟩
      | fromMissing rejectedSelection fromAbsent =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedFromSpan rejectedSelection rejectedFrom
            pathRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | hidingRejected rejectedFromSpan rejectedSelection rejectedFrom
            rejectedPath hidingRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact optionalHidingDeterministicOutcomeSpec.successRejectDisjoint
            hidingRejected ⟨_, _, successfulHiding⟩
      | terminatorRejected rejectedFromSpan rejectedSelection rejectedFrom
            rejectedPath rejectedHiding terminatorRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            rejectedHiding successfulHiding
          subst afterHidingEq
          exact ImportTerminatorRejects.disjointOrdinary _
            terminatorRejected ⟨_, _, successfulTerminator⟩

/-- Selective-import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem selectiveImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (SelectiveImportOrdinaryParses start)
      SelectiveImportRejects where
  successOutputUnique := SelectiveImportOrdinaryParses.output_unique start
  successRejectDisjoint := SelectiveImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectiveImportExactnessProperties
/-! Exact selective imports, including source-order selectors and optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact selectors, path, and hiding fix the entire selective-import AST. -/
theorem SelectiveImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ leftSelection leftFrom leftPath leftHiding leftTerminator =>
      cases rightParsed with
      | parsed _ rightSelection rightFrom rightPath rightHiding rightTerminator =>
          rcases selectedImportsExactOutcomeSpec.successResultUnique
              leftSelection rightSelection with ⟨selectionEq, afterSelectionEq⟩
          subst selectionEq
          subst afterSelectionEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          rcases optionalHidingExactOutcomeSpec.successResultUnique leftHiding rightHiding with
            ⟨hidingEq, afterHidingEq⟩
          subst hidingEq
          subst afterHidingEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Selective-import success fixes the full located AST and remainder. -/
theorem SelectiveImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A selective payload fixes the first failing stage's exact remainder. -/
theorem SelectiveImportRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectiveImportRejects input left)
    (rightRejected : SelectiveImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      selectedImportsExactOutcomeSpec.successOutputUnique,
      selectedImportsExactOutcomeSpec.rejectOutputUnique,
      selectedImportsExactOutcomeSpec.successRejectDisjoint,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      optionalHidingExactOutcomeSpec.successOutputUnique,
      optionalHidingExactOutcomeSpec.rejectOutputUnique,
      optionalHidingExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Selective-import payload outcomes are fully exact at a fixed outer start. -/
theorem selectiveImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (SelectiveImportOrdinaryParses start)
      SelectiveImportRejects where
  toDeterministicOutcomeSpec := selectiveImportDeterministicOutcomeSpec start
  successValueUnique := SelectiveImportOrdinaryParses.value_unique start
  rejectOutputUnique := SelectiveImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainImportOutcomeProperties
/-! Deterministic and exclusive broad outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem importTerminator_output_unique_anyLast
    {leftLast rightLast : SourceSpan}
    {input afterLeft afterRight : Remainder}
    {leftEnd rightEnd : SourceSpan}
    (leftParsed : ImportTerminatorOrdinaryParses leftLast input leftEnd
      afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses rightLast input rightEnd
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          rw [leftSemicolon.2, rightSemicolon.2]
      | recovered rightAbsent rightStarts =>
          exact False.elim (rightAbsent ⟨leftEnd, leftSemicolon.1⟩)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSpan rightSemicolon =>
          exact False.elim (leftAbsent ⟨rightEnd, rightSemicolon.1⟩)
      | recovered rightAbsent rightStarts => rfl

/-- Ordinary plain-import payloads have one final remainder. -/
theorem PlainImportOrdinaryParses.output_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightPath rightTerminator =>
          have afterPathEq :=
            modulePathDeterministicOutcomeSpec.successOutputUnique leftPath
              rightPath
          subst afterPathEq
          exact importTerminator_output_unique_anyLast leftTerminator
            rightTerminator

/-- Exact plain-import rejection excludes every ordinary success. -/
theorem PlainImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : PlainImportRejects input rejected) :
    ¬ ∃ declaration output,
      PlainImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulPath successfulTerminator =>
      cases rejection with
      | pathRejected pathRejected =>
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | terminatorRejected rejectedPath terminatorRejected =>
          have afterPathEq :=
            modulePathDeterministicOutcomeSpec.successOutputUnique
              rejectedPath successfulPath
          subst afterPathEq
          exact (importTerminatorDeterministicOutcomeSpec _)
            |>.successRejectDisjoint terminatorRejected
              ⟨_, _, successfulTerminator⟩

/-- Plain import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed outer start span. -/
theorem plainImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (PlainImportOrdinaryParses start)
      PlainImportRejects where
  successOutputUnique := PlainImportOrdinaryParses.output_unique start
  successRejectDisjoint := PlainImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportDeclOutcomeProperties
/-! Deterministic exact broad outcomes for complete import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem dispatch_present_conflicts_absent
    {input : Remainder} {offset : Nat} {kind : TokenKind}
    (present : ImportDispatchTokenPresentAt input offset kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex
      (input.cursor + offset) kind) : False := by
  rcases present with ⟨span, tokenAt⟩
  exact absent ⟨span, tokenAt⟩

private theorem exactToken_span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  have tokenEq :
      ({ span := leftSpan, value := kind } : Token) =
        { span := rightSpan, value := kind } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  exact congrArg (fun token : Token => token.span) tokenEq

private theorem dispatch_conflict_after_keyword
    {input leftAfter rightAfter : Remainder}
    {leftSpan rightSpan : SourceSpan} {offset : Nat} {kind : TokenKind}
    (leftKeyword : ExactTokenParses (.keyword .importKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .importKw) input rightSpan
      rightAfter)
    (present : ImportDispatchTokenPresentAt leftAfter offset kind)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      (rightAfter.cursor + offset) kind) : False := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  exact dispatch_present_conflicts_absent present absent

private theorem payload_output_unique_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ImportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input leftAfter rightAfter leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    {left right : Syntax.ImportDecl}
    (leftKeyword : ExactTokenParses (.keyword .importKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .importKw) input rightSpan
      rightAfter)
    (leftPayload : payload leftSpan leftAfter left leftOutput)
    (rightPayload : payload rightSpan rightAfter right rightOutput) :
    leftOutput = rightOutput := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique leftKeyword rightKeyword
  subst keywordSpanEq
  exact (outcomes leftSpan).successOutputUnique leftPayload rightPayload

private theorem payload_reject_disjoint_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ImportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input rejectedAfter successfulAfter rejected output : Remainder}
    {rejectedSpan successfulSpan : SourceSpan}
    {declaration : Syntax.ImportDecl}
    (rejectedKeyword : ExactTokenParses (.keyword .importKw) input
      rejectedSpan rejectedAfter)
    (successfulKeyword : ExactTokenParses (.keyword .importKw) input
      successfulSpan successfulAfter)
    (payloadRejected : payloadRejects rejectedAfter rejected)
    (payloadParsed : payload successfulSpan successfulAfter declaration
      output) : False := by
  have afterKeywordEq := exactToken_output_unique rejectedKeyword
    successfulKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique rejectedKeyword
    successfulKeyword
  subst keywordSpanEq
  exact (outcomes rejectedSpan).successRejectDisjoint payloadRejected
    ⟨_, _, payloadParsed⟩

/-- Complete broad import success has one final remainder. -/
theorem ImportDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | namespaceImport leftSpan leftKeyword leftStar leftAs leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact payload_output_unique_after_keyword
            namespaceImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftAs rightAs)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
  | wildcardImport leftSpan leftKeyword leftStar leftAs leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightAs leftAs)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact payload_output_unique_after_keyword
            wildcardImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftStar rightStar)
  | selectiveImport leftSpan leftKeyword leftStar leftBrace leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact payload_output_unique_after_keyword
            selectiveImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword leftKeyword
            rightKeyword leftBrace rightBrace)
  | plainImport leftSpan leftKeyword leftStar leftBrace leftPayload =>
      cases rightParsed with
      | namespaceImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | wildcardImport rightSpan rightKeyword rightStar rightAs rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightStar leftStar)
      | selectiveImport rightSpan rightKeyword rightStar rightBrace
            rightPayload =>
          exact False.elim (dispatch_conflict_after_keyword rightKeyword
            leftKeyword rightBrace leftBrace)
      | plainImport rightSpan rightKeyword rightStar rightBrace rightPayload =>
          exact payload_output_unique_after_keyword
            plainImportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPayload rightPayload

/-- Exact complete-import rejection excludes every broad ordinary success. -/
theorem ImportDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ImportDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ImportDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | keywordMissing keywordAbsent =>
      cases successful <;> exact absent_conflicts_exact keywordAbsent (by assumption)
  | namespaceImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedAs payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            namespaceImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedAs successfulAs
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
  | wildcardImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedAs payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulAs rejectedAs
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            wildcardImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedStar successfulStar
  | selectiveImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedBrace payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            selectiveImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword rejectedKeyword
            successfulKeyword rejectedBrace successfulBrace
  | plainImportRejected rejectedSpan rejectedKeyword rejectedStar
        rejectedBrace payloadRejected =>
      cases successful with
      | namespaceImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | wildcardImport successfulSpan successfulKeyword successfulStar
            successfulAs payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulStar rejectedStar
      | selectiveImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact dispatch_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulBrace rejectedBrace
      | plainImport successfulSpan successfulKeyword successfulStar
            successfulBrace payloadParsed =>
          exact payload_reject_disjoint_after_keyword
            plainImportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected payloadParsed

/-- Complete imports have deterministic and exclusive broad outcomes. -/
theorem importDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects where
  successOutputUnique := ImportDeclOrdinaryParses.output_unique
  successRejectDisjoint := ImportDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainImportExactnessProperties
/-! Exact plain-import payloads with explicit and recovered terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed outer start span determines the complete plain-import AST. -/
theorem PlainImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftPath leftTerminator =>
      cases rightParsed with
      | parsed rightPath rightTerminator =>
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Plain-import payload success fixes the full located AST and remainder. -/
theorem PlainImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : PlainImportOrdinaryParses start input left afterLeft)
    (rightParsed : PlainImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A plain-import payload has one exact first rejecting endpoint. -/
theorem PlainImportRejects.output_unique {input left right : Remainder}
    (leftRejected : PlainImportRejects input left)
    (rightRejected : PlainImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Plain-import payload outcomes are fully exact at a fixed outer start. -/
theorem plainImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (PlainImportOrdinaryParses start) PlainImportRejects where
  toDeterministicOutcomeSpec := plainImportDeterministicOutcomeSpec start
  successValueUnique := PlainImportOrdinaryParses.value_unique start
  rejectOutputUnique := PlainImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportDeclExactnessProperties
/-! Exact prioritized import declarations over arbitrary token remainders. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem dispatch_present_conflicts_absent_variant
    {input : Remainder} {offset : Nat} {kind : TokenKind}
    (present : ImportDispatchTokenPresentAt input offset kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex
      (input.cursor + offset) kind) : False :=
  absent present

/-- Import priority, keyword span, and exact payloads determine one located AST. -/
theorem ImportDeclOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 12) [ExactTokenParses.result_unique,
      dispatch_present_conflicts_absent_variant,
      PlainImportOrdinaryParses.value_unique,
      NamespaceImportOrdinaryParses.value_unique,
      WildcardImportOrdinaryParses.value_unique,
      SelectiveImportOrdinaryParses.value_unique]

/-- Complete import success fixes its exact AST and full remainder. -/
theorem ImportDeclOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : ImportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImportDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Import dispatch and the selected first failing stage fix one rejection endpoint. -/
theorem ImportDeclRejects.output_unique {input left right : Remainder}
    (leftRejected : ImportDeclRejects input left)
    (rightRejected : ImportDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      dispatch_present_conflicts_absent_variant, PlainImportRejects.output_unique,
      NamespaceImportRejects.output_unique, WildcardImportRejects.output_unique,
      SelectiveImportRejects.output_unique]

/-- Prioritized broad import declarations have fully exact success and rejection. -/
theorem importDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects where
  toDeterministicOutcomeSpec := importDeclDeterministicOutcomeSpec
  successValueUnique := ImportDeclOrdinaryParses.value_unique
  rejectOutputUnique := ImportDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
