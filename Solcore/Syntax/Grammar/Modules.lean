import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.Grammar.Basics

/-!
Declarative grammar of module paths, imports, exports and pragmas.

Main declarations: `ModulePathOrdinaryParses`, `PragmaDeclOrdinaryParses`,
`ExportPathOrdinaryParses`, `ExportSelectionOrdinaryParses`, `SelectorNameOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeModulePathOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary module-path success is the existing exact prioritized grammar. -/
abbrev ModulePathOrdinaryParses := ModulePathParses

/-- Exact module-path rejection in local and external-package priority order. -/
inductive ModulePathRejects : Remainder → Remainder → Prop where
  | localRejected {input rejected : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .at))
      (nameRejected : TypeQualifiedNameRejects input rejected) :
      ModulePathRejects input rejected
  | externalRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (nameRejected : TypeQualifiedNameRejects afterMarker rejected) :
      ModulePathRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedAliasOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for an optional selected-import
alias.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-alias success is the existing exact prioritized
grammar: absence is nonconsuming, while `as` commits to one identifier. -/
abbrev SelectedAliasOrdinaryParses := SelectedAliasParses

/-- Exact rejection after a present `as` marker commits to its identifier. -/
inductive SelectedAliasRejects : Remainder → Remainder → Prop where
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .asKw) input markerSpan
        afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      SelectedAliasRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for import and export selector
names.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No symbol accepted by the operator-selector collector occurs at one
cursor. -/
def SelectorOperatorPartAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ symbol span,
    SelectorOperatorSymbol symbol ∧
      TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol symbol
      }

/-- Fuel-independent maximal scan of consecutive operator-selector symbols.

The result is in forward source order.  The `done` premise ensures that the
scan cannot stop before another accepted symbol. -/
inductive MaximalSelectorOperatorPartsParses :
    Remainder → List String → Remainder → Prop where
  | done {input : Remainder}
      (partAbsent : SelectorOperatorPartAbsentAt input) :
      MaximalSelectorOperatorPartsParses input [] input
  | next {input output : Remainder} {symbol : Symbol}
      {parts : List String}
      (allowed : SelectorOperatorSymbol symbol)
      (span : SourceSpan)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol symbol
      })
      (tail : MaximalSelectorOperatorPartsParses
        { input with cursor := input.cursor + 1 } parts output) :
      MaximalSelectorOperatorPartsParses input
        (symbol.spelling :: parts) output

/-- Ordinary selector-name success is the existing exact identifier/operator
grammar. -/
abbrev SelectorNameOrdinaryParses := SelectorNameParses

/-- Exact prioritized executable rejection of one selector name. -/
inductive SelectorNameRejects : Remainder → Remainder → Prop where
  | identifierRejected {input rejected : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameRejected : IdentifierRejects input rejected) :
      SelectorNameRejects input rejected
  | emptyOperator {input afterOpening : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (partAbsent : SelectorOperatorPartAbsentAt afterOpening) :
      SelectorNameRejects input afterOpening
  | closingMissing {input afterOpening afterParts : Remainder}
      {parts : List String}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (partsParsed : MaximalSelectorOperatorPartsParses afterOpening parts
        afterParts)
      (partsNonempty : parts ≠ [])
      (closingAbsent : TokenKindAbsentAt afterParts.tokens
        afterParts.endIndex afterParts.cursor (.symbol .rightParen)) :
      SelectorNameRejects input afterParts

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for import hiding clauses and their
optional guarded wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary hiding-clause success is the existing exact marker and nonempty
allow-trailing selector-list grammar. -/
abbrev HidingClauseOrdinaryParses := HidingClauseParses

/-- Exact rejection of the required nonempty, allow-trailing selector list
after a consumed `hiding` marker. -/
abbrev HidingSelectorListRejects :=
  DelimitedListRejects .leftBrace .rightBrace false true
    SelectorNameOrdinaryParses SelectorNameRejects

/-- Exact first rejecting stage of one required hiding clause. -/
inductive HidingClauseRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.hiding.spelling)) :
      HidingClauseRejects input input
  | namesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.hiding.spelling) input markerSpan
          afterMarker)
      (namesRejected : HidingSelectorListRejects afterMarker rejected) :
      HidingClauseRejects input rejected

/-- Ordinary optional hiding success is the existing prioritized grammar:
absence is nonconsuming and a present marker commits to the clause. -/
abbrev OptionalHidingOrdinaryParses := OptionalHidingParses

/-- A positive `hiding` lookahead commits the optional wrapper to the required
clause.  The positive witness makes its nested `markerMissing` branch
uninhabitable and keeps absent success exclusive. -/
inductive OptionalHidingRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (markerPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span
          value := .identifier ContextualKeyword.hiding.spelling
        })
      (clauseRejected : HidingClauseRejects input rejected) :
      OptionalHidingRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import success is the existing exact source/alias
grammar, including its AST span equation and final remainder. -/
abbrev SelectedImportOrdinaryParses := SelectedImportParses

/-- Exact first rejecting stage of one selected import. -/
inductive SelectedImportRejects : Remainder → Remainder → Prop where
  | sourceRejected {input rejected : Remainder}
      (sourceRejected : SelectorNameRejects input rejected) :
      SelectedImportRejects input rejected
  | aliasRejected {input afterSource rejected : Remainder}
      {source : Syntax.SelectorName}
      (sourceParsed : SelectorNameOrdinaryParses input source afterSource)
      (aliasRejected : SelectedAliasRejects afterSource rejected) :
      SelectedImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectedImportsOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import-list success is the existing exact nonempty,
allow-trailing braced-list grammar. -/
abbrev SelectedImportsOrdinaryParses := SelectedImportsParses

/-- Exact rejection of the required nonempty, allow-trailing braced list. -/
abbrev SelectedImportsRejects :=
  DelimitedListRejects .leftBrace .rightBrace false true
    SelectedImportOrdinaryParses SelectedImportRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaItemsOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive current-token guard used by pragma item dispatch. -/
def PragmaItemsTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Exact successful suffix after a pragma's first item. -/
inductive PragmaItemsTailOrdinaryParses :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | done {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma)) :
      PragmaItemsTailOrdinaryParses input [] input
  | trailing {input afterComma : Remainder} (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonPresent : PragmaItemsTokenPresentAt afterComma
        (.symbol .semicolon)) :
      PragmaItemsTailOrdinaryParses input [] afterComma
  | next {input afterComma afterItem output : Remainder}
      {item : Syntax.Identifier} {items : List Syntax.Identifier}
      (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailParsed : PragmaItemsTailOrdinaryParses afterItem items output) :
      PragmaItemsTailOrdinaryParses input (item :: items) output

/-- Exact first rejecting stage of a pragma item suffix. -/
inductive PragmaItemsTailRejects : Remainder → Remainder → Prop where
  | identifierRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemRejected : IdentifierRejects afterComma rejected) :
      PragmaItemsTailRejects input rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.Identifier} (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailRejected : PragmaItemsTailRejects afterItem rejected) :
      PragmaItemsTailRejects input rejected

/-- Exact successful scan of all pragma items before the semicolon. -/
inductive PragmaItemsOrdinaryParses :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | empty {input : Remainder}
      (semicolonPresent : PragmaItemsTokenPresentAt input
        (.symbol .semicolon)) :
      PragmaItemsOrdinaryParses input [] input
  | nonempty {input afterFirst output : Remainder}
      {first : Syntax.Identifier} {rest : List Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailParsed : PragmaItemsTailOrdinaryParses afterFirst rest output) :
      PragmaItemsOrdinaryParses input (first :: rest) output

/-- Exact first rejecting stage of the complete pragma item scan. -/
inductive PragmaItemsRejects : Remainder → Remainder → Prop where
  | firstIdentifierRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstRejected : IdentifierRejects input rejected) :
      PragmaItemsRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailRejected : PragmaItemsTailRejects afterFirst rejected) :
      PragmaItemsRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for complete pragmas. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad pragma success in executable stage order. -/
inductive PragmaDeclOrdinaryParses :
    Remainder → Syntax.PragmaDecl → Remainder → Prop where
  | parsed {input afterKeyword afterName afterItems output : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      (keywordSpan semicolonSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsOrdinaryParses afterName items afterItems)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterItems
        semicolonSpan output) :
      PragmaDeclOrdinaryParses input {
        span := SourceSpan.cover keywordSpan semicolonSpan
        value := { name, items }
      } output

/-- Exact first rejecting stage of one complete pragma attempt. -/
inductive PragmaDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw)) :
      PragmaDeclRejects input input
  | nameRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected) :
      PragmaDeclRejects input rejected
  | itemsRejected {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsRejected : PragmaItemsRejects afterName rejected) :
      PragmaDeclRejects input rejected
  | semicolonMissing
      {input afterKeyword afterName afterItems : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsOrdinaryParses afterName items afterItems)
      (semicolonAbsent : TokenKindAbsentAt afterItems.tokens
        afterItems.endIndex afterItems.cursor (.symbol .semicolon)) :
      PragmaDeclRejects input afterItems

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePragmaNameRejectionGrammar
/-! Independent exact first-name rejection of a pragma declaration. The
uncommitted failure report is distinguished from an emitted diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pragma marker is consumed, then an unavailable raw name selects the
current-input failure span and found token under fixed source/byte context. -/
inductive PragmaNameMissingAt (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → SourceSpan → Option TokenKind → Prop where
  | missing {input afterKeyword : Remainder} {marker failureSpan : SourceSpan}
      {found : Option TokenKind}
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (nameAbsent : IdentifierAbsentAt afterKeyword)
      (current : CurrentInputAt source endByte afterKeyword failureSpan found) :
      PragmaNameMissingAt source endByte input afterKeyword failureSpan found

/-- The exact missing-name report refines the existing ordinary pragma rejection. -/
theorem PragmaNameMissingAt.rejects
    {source : SourceId} {endByte : Nat} {input after : Remainder}
    {failureSpan : SourceSpan} {found : Option TokenKind}
    (missing : PragmaNameMissingAt source endByte input after failureSpan found) :
    PragmaDeclRejects input after := by
  cases missing with
  | missing keywordParsed nameAbsent _ =>
      exact .nameRejected _ keywordParsed (.absent nameAbsent)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportPathOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export-path success is the existing exact maximal path grammar. -/
abbrev ExportPathOrdinaryParses := ExportPathParses

/-- An export path can reject only at its required first checked identifier. -/
inductive ExportPathRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (identifierRejected : IdentifierRejects input rejected) :
      ExportPathRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorSelectionOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for export constructor selections.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary constructor-selection success is the existing exact grammar. -/
abbrev ConstructorSelectionOrdinaryParses := ConstructorSelectionParses

/-- Exact prioritized rejection of an all-or-named constructor selection. -/
inductive ConstructorSelectionRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder} (markerSpan : SourceSpan)
      (markerToken : TokenAt input.tokens input.endIndex
        (input.cursor + 1) {
          span := markerSpan
          value := .symbol .star
        })
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      ConstructorSelectionRejects input input
  | closingMissing {input afterOpening afterMarker : Remainder}
      (openingSpan markerSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses (.symbol .star) afterOpening
        markerSpan afterMarker)
      (closingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .rightParen)) :
      ConstructorSelectionRejects input afterMarker
  | namedRejected {input rejected : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        (input.cursor + 1) (.symbol .star))
      (namesRejected : DelimitedListRejects .leftParen .rightParen false false
        IdentifierParses IdentifierRejects input rejected) :
      ConstructorSelectionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportNameOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact evidence for a token kind at the current export-name cursor. -/
def ExportNameTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Ordinary export-name success is the existing exact prioritized grammar. -/
abbrev ExportNameOrdinaryParses := ExportNameParses

/-- Exact first rejecting stage of one prioritized export-name attempt. -/
inductive ExportNameRejects : Remainder → Remainder → Prop where
  | operatorRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingPresent : ExportNameTokenPresentAt input
        (.symbol .leftParen))
      (selectorRejected : SelectorNameRejects input rejected) :
      ExportNameRejects input rejected
  | identifierRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameRejected : IdentifierRejects input rejected) :
      ExportNameRejects input rejected
  | constructorsRejected {input afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameParsed : IdentifierParses input name afterName)
      (openingPresent : ExportNameTokenPresentAt afterName
        (.symbol .leftParen))
      (selectionRejected : ConstructorSelectionRejects afterName rejected) :
      ExportNameRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportSelectionOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export-selection success is the existing exact prioritized
grammar. -/
abbrev ExportSelectionOrdinaryParses := ExportSelectionParses

/-- A non-wildcard export selection rejects only in its braced name list. -/
inductive ExportSelectionRejects : Remainder → Remainder → Prop where
  | selectedRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (itemsRejected : DelimitedListRejects .leftBrace .rightBrace true true
        ExportNameOrdinaryParses ExportNameRejects input rejected) :
      ExportSelectionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportItemOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive guard for the prioritized qualified-wildcard branch. -/
def LocalExportItemQualifiedStartAt (input : Remainder) : Prop :=
  ∃ identifierSpan dotSpan text,
    TokenAt input.tokens input.endIndex input.cursor {
      span := identifierSpan
      value := .identifier text
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := dotSpan
      value := .symbol .dot
    }

/-- Ordinary local-export-item success is the existing prioritized grammar. -/
abbrev LocalExportItemOrdinaryParses := LocalExportItemParses

/-- Exact reachable rejection stages of one local export item. -/
inductive LocalExportItemRejects : Remainder → Remainder → Prop where
  | moduleDotMissing {input afterPath : Remainder}
      {path : Syntax.QualifiedName}
      (qualifiedStart : LocalExportItemQualifiedStartAt input)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot)) :
      LocalExportItemRejects input afterPath
  | moduleStarMissing {input afterPath afterDot : Remainder}
      {path : Syntax.QualifiedName}
      (qualifiedStart : LocalExportItemQualifiedStartAt input)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (starAbsent : TokenKindAbsentAt afterDot.tokens afterDot.endIndex
        afterDot.cursor (.symbol .star)) :
      LocalExportItemRejects input afterDot
  | nameRejected {input rejected : Remainder}
      (qualifiedAbsent : IdentifierDotAbsentAt input.tokens input.endIndex
        input.cursor)
      (nameRejected : ExportNameRejects input rejected) :
      LocalExportItemRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFinishExportOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for finishing an export. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export finishing is the existing exact semicolon grammar. -/
abbrev FinishExportOrdinaryParses := FinishExportParses

/-- An export finish rejects exactly when its required semicolon is absent. -/
inductive FinishExportRejects : Remainder → Remainder → Prop where
  | semicolonMissing {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      FinishExportRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePathExportOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive current-token guard for path-export suffix dispatch. -/
def PathExportTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Ordinary path-export success is the existing exact prioritized grammar. -/
abbrev PathExportOrdinaryParses (start : SourceSpan) :=
  PathExportTailParses start

/-- Exact first rejecting stage of a prioritized path export payload. -/
inductive PathExportRejects : Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (pathRejected : ExportPathRejects input rejected) :
      PathExportRejects input rejected
  | selectionRejected
      {input afterPath afterDot rejected : Remainder}
      {path : Syntax.QualifiedName} (dotSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotPresent : PathExportTokenPresentAt afterPath (.symbol .dot))
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (selectionRejected : ExportSelectionRejects afterDot rejected) :
      PathExportRejects input rejected
  | selectionFinishRejected
      {input afterPath afterDot afterSelection rejected : Remainder}
      {path : Syntax.QualifiedName} {selection : Syntax.ExportSelection}
      (dotSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotPresent : PathExportTokenPresentAt afterPath (.symbol .dot))
      (dotParsed : ExactTokenParses (.symbol .dot) afterPath dotSpan afterDot)
      (selectionParsed : ExportSelectionOrdinaryParses afterDot selection
        afterSelection)
      (finishRejected : FinishExportRejects afterSelection rejected) :
      PathExportRejects input rejected
  | aliasRejected {input afterPath afterAs rejected : Remainder}
      {path : Syntax.QualifiedName} (asSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asPresent : PathExportTokenPresentAt afterPath (.keyword .asKw))
      (asParsed : ExactTokenParses (.keyword .asKw) afterPath asSpan afterAs)
      (aliasRejected : IdentifierRejects afterAs rejected) :
      PathExportRejects input rejected
  | aliasFinishRejected
      {input afterPath afterAs afterAlias rejected : Remainder}
      {path : Syntax.QualifiedName} {alias : Syntax.Identifier}
      (asSpan : SourceSpan)
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asPresent : PathExportTokenPresentAt afterPath (.keyword .asKw))
      (asParsed : ExactTokenParses (.keyword .asKw) afterPath asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (finishRejected : FinishExportRejects afterAlias rejected) :
      PathExportRejects input rejected
  | moduleFinishRejected {input afterPath rejected : Remainder}
      {path : Syntax.QualifiedName}
      (pathParsed : ExportPathOrdinaryParses input path afterPath)
      (dotAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.symbol .dot))
      (asAbsent : TokenKindAbsentAt afterPath.tokens afterPath.endIndex
        afterPath.cursor (.keyword .asKw))
      (finishRejected : FinishExportRejects afterPath rejected) :
      PathExportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary local-export success is the existing exact list-and-finish
grammar for a fixed outer start span. -/
abbrev LocalExportOrdinaryParses (start : SourceSpan) :=
  LocalExportTailParses start

/-- Exact first rejecting stage of a local export payload. -/
inductive LocalExportRejects : Remainder → Remainder → Prop where
  | itemsRejected {input rejected : Remainder}
      (itemsRejected : DelimitedListRejects .leftBrace .rightBrace true true
        LocalExportItemOrdinaryParses LocalExportItemRejects input rejected) :
      LocalExportRejects input rejected
  | finishRejected {input afterItems rejected : Remainder}
      {items : DelimitedList Syntax.LocalExportItem}
      (itemsParsed : TrailingDelimitedListParses .leftBrace .rightBrace
        LocalExportItemOrdinaryParses input items afterItems)
      (finishRejected : FinishExportRejects afterItems rejected) :
      LocalExportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportDeclOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for complete exports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive left-brace guard for the outer export dispatcher. -/
def ExportDeclLeftBracePresentAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .symbol .leftBrace
  }

/-- Ordinary complete-export success is the existing exact four-form grammar. -/
abbrev ExportDeclOrdinaryParses := ExportDeclParses

/-- Exact first rejecting stage of a complete prioritized export declaration. -/
inductive ExportDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw)) :
      ExportDeclRejects input input
  | localRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .exportKw) input keywordSpan
        afterKeyword)
      (leftBracePresent : ExportDeclLeftBracePresentAt afterKeyword)
      (payloadRejected : LocalExportRejects afterKeyword rejected) :
      ExportDeclRejects input rejected
  | pathRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .exportKw) input keywordSpan
        afterKeyword)
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex afterKeyword.cursor (.symbol .leftBrace))
      (payloadRejected : PathExportRejects afterKeyword rejected) :
      ExportDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for import terminators.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact finite token kinds recognized as top-item starts by import recovery. -/
def ImportTerminatorTopItemStartKinds : List TokenKind := [
  .keyword .importKw,
  .keyword .exportKw,
  .keyword .pragmaKw,
  .keyword .typeKw,
  .keyword .contractKw,
  .keyword .functionKw,
  .keyword .defaultKw,
  .symbol .hash,
  .identifier ContextualKeyword.enum.spelling,
  .identifier ContextualKeyword.trait.spelling,
  .identifier ContextualKeyword.impl.spelling
]

/-- A token recognized as a top-item start occurs at the current cursor. -/
def ImportTerminatorTopItemStartsAt (input : Remainder) : Prop :=
  ∃ kind ∈ ImportTerminatorTopItemStartKinds, ∃ span,
    TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Exact prioritized success of an import terminator.  A semicolon consumes
one token and returns its span.  Otherwise a top-item start recovers without
consuming input and returns the fixed preceding span. -/
inductive ImportTerminatorOrdinaryParses (lastSpan : SourceSpan) :
    Remainder → SourceSpan → Remainder → Prop where
  | semicolon {input output : Remainder} (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      ImportTerminatorOrdinaryParses lastSpan input semicolonSpan output
  | recovered {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (topItemStarts : ImportTerminatorTopItemStartsAt input) :
      ImportTerminatorOrdinaryParses lastSpan input lastSpan input

/-- Exact nonconsuming rejection when neither a semicolon nor a top-item start
occurs at the current cursor. -/
inductive ImportTerminatorRejects : Remainder → Remainder → Prop where
  | missing {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (topItemStartAbsent : TopItemKindsAbsentAt input
        ImportTerminatorTopItemStartKinds) :
      ImportTerminatorRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectiveImportOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for selective import payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad selective-import success in executable stage order, including
optional hiding and explicit-or-recovered terminator success. -/
inductive SelectiveImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterSelection afterFrom afterPath afterHiding
        output : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      {endSpan : SourceSpan} (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorParsed : ImportTerminatorOrdinaryParses
        (match hidden with
          | some clause => clause.span
          | none => path.span)
        afterHiding endSpan output) :
      SelectiveImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .selected selection path hidden
      } output

/-- Exact first rejecting stage of one selective-import helper attempt. -/
inductive SelectiveImportRejects : Remainder → Remainder → Prop where
  | selectionRejected {input rejected : Remainder}
      (selectionRejected : SelectedImportsRejects input rejected) :
      SelectiveImportRejects input rejected
  | fromMissing {input afterSelection : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromAbsent : TokenKindAbsentAt afterSelection.tokens
        afterSelection.endIndex afterSelection.cursor
          (.identifier ContextualKeyword.from.spelling)) :
      SelectiveImportRejects input afterSelection
  | pathRejected
      {input afterSelection afterFrom rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      SelectiveImportRejects input rejected
  | hidingRejected
      {input afterSelection afterFrom afterPath rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingRejected : OptionalHidingRejects afterPath rejected) :
      SelectiveImportRejects input rejected
  | terminatorRejected
      {input afterSelection afterFrom afterPath afterHiding
        rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorRejected : ImportTerminatorRejects afterHiding rejected) :
      SelectiveImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeWildcardImportOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for wildcard import payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad wildcard-import success in executable stage order, including
optional hiding and explicit-or-recovered terminator success. -/
inductive WildcardImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterStar afterFrom afterPath afterHiding output : Remainder}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      {endSpan : SourceSpan} (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorParsed : ImportTerminatorOrdinaryParses
        (match hidden with
          | some clause => clause.span
          | none => path.span)
        afterHiding endSpan output) :
      WildcardImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .wildcard path hidden
      } output

/-- Exact first rejecting stage of one wildcard-import helper attempt. -/
inductive WildcardImportRejects : Remainder → Remainder → Prop where
  | starMissing {input : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star)) :
      WildcardImportRejects input input
  | fromMissing {input afterStar : Remainder} (starSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromAbsent : TokenKindAbsentAt afterStar.tokens afterStar.endIndex
        afterStar.cursor (.identifier ContextualKeyword.from.spelling)) :
      WildcardImportRejects input afterStar
  | pathRejected {input afterStar afterFrom rejected : Remainder}
      (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      WildcardImportRejects input rejected
  | hidingRejected
      {input afterStar afterFrom afterPath rejected : Remainder}
      {path : Syntax.ModulePath} (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingRejected : OptionalHidingRejects afterPath rejected) :
      WildcardImportRejects input rejected
  | terminatorRejected
      {input afterStar afterFrom afterPath afterHiding
        rejected : Remainder}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorRejected : ImportTerminatorRejects afterHiding rejected) :
      WildcardImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainImportOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad success of `plainImport` after the outer `import` keyword. -/
inductive PlainImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed {input afterPath output : Remainder}
      {path : Syntax.ModulePath} {endSpan : SourceSpan}
      (pathParsed : ModulePathOrdinaryParses input path afterPath)
      (terminatorParsed : ImportTerminatorOrdinaryParses path.span afterPath
        endSpan output) :
      PlainImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .plain path
      } output

/-- Exact first rejecting stage of a plain import payload. -/
inductive PlainImportRejects : Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (pathRejected : ModulePathRejects input rejected) :
      PlainImportRejects input rejected
  | terminatorRejected {input afterPath rejected : Remainder}
      {path : Syntax.ModulePath}
      (pathParsed : ModulePathOrdinaryParses input path afterPath)
      (terminatorRejected : ImportTerminatorRejects afterPath rejected) :
      PlainImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamespaceImportOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for the namespace-import helper
after the outer `import` keyword has already been consumed.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad namespace-import success in executable stage order.  The
terminator includes both consumed-semicolon and diagnosed recovery success. -/
inductive NamespaceImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterStar afterAs afterAlias afterFrom afterPath output : Remainder}
      {alias : Syntax.Identifier} {path : Syntax.ModulePath}
      (starSpan asSpan fromSpan endSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (terminatorParsed : ImportTerminatorOrdinaryParses path.span afterPath
        endSpan output) :
      NamespaceImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .namespace path alias
      } output

/-- Exact first rejecting stage of one namespace-import helper attempt. -/
inductive NamespaceImportRejects : Remainder → Remainder → Prop where
  | starMissing {input : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star)) :
      NamespaceImportRejects input input
  | asMissing {input afterStar : Remainder}
      (starSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asAbsent : TokenKindAbsentAt afterStar.tokens afterStar.endIndex
        afterStar.cursor (.keyword .asKw)) :
      NamespaceImportRejects input afterStar
  | aliasRejected {input afterStar afterAs rejected : Remainder}
      (starSpan asSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasRejected : IdentifierRejects afterAs rejected) :
      NamespaceImportRejects input rejected
  | fromMissing
      {input afterStar afterAs afterAlias : Remainder}
      {alias : Syntax.Identifier} (starSpan asSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromAbsent : TokenKindAbsentAt afterAlias.tokens afterAlias.endIndex
        afterAlias.cursor (.identifier ContextualKeyword.from.spelling)) :
      NamespaceImportRejects input afterAlias
  | pathRejected
      {input afterStar afterAs afterAlias afterFrom rejected : Remainder}
      {alias : Syntax.Identifier} (starSpan asSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      NamespaceImportRejects input rejected
  | terminatorRejected
      {input afterStar afterAs afterAlias afterFrom afterPath
        rejected : Remainder}
      {alias : Syntax.Identifier} {path : Syntax.ModulePath}
      (starSpan asSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (terminatorRejected : ImportTerminatorRejects afterPath rejected) :
      NamespaceImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImportDeclOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for the complete prioritized import
declaration dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token-kind evidence used by an import-payload dispatch lookahead. -/
def ImportDispatchTokenPresentAt (input : Remainder) (offset : Nat)
    (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex (input.cursor + offset) {
    span
    value := kind
  }

/-- Exact broad success of the complete prioritized import declaration. -/
inductive ImportDeclOrdinaryParses :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | namespaceImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asPresent : ImportDispatchTokenPresentAt afterKeyword 1
        (.keyword .asKw))
      (payloadParsed : NamespaceImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | wildcardImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 1) (.keyword .asKw))
      (payloadParsed : WildcardImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | selectiveImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBracePresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .leftBrace))
      (payloadParsed : SelectiveImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output
  | plainImport {input afterKeyword output : Remainder}
      {declaration : Syntax.ImportDecl} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex (afterKeyword.cursor + 0) (.symbol .leftBrace))
      (payloadParsed : PlainImportOrdinaryParses keywordSpan afterKeyword
        declaration output) :
      ImportDeclOrdinaryParses input declaration output

/-- Exact first rejecting stage of the complete prioritized import declaration. -/
inductive ImportDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw)) :
      ImportDeclRejects input input
  | namespaceImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asPresent : ImportDispatchTokenPresentAt afterKeyword 1
        (.keyword .asKw))
      (payloadRejected : NamespaceImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | wildcardImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starPresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .star))
      (asAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 1) (.keyword .asKw))
      (payloadRejected : WildcardImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | selectiveImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBracePresent : ImportDispatchTokenPresentAt afterKeyword 0
        (.symbol .leftBrace))
      (payloadRejected : SelectiveImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected
  | plainImportRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .importKw) input keywordSpan
        afterKeyword)
      (starAbsent : TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
        (afterKeyword.cursor + 0) (.symbol .star))
      (leftBraceAbsent : TokenKindAbsentAt afterKeyword.tokens
        afterKeyword.endIndex (afterKeyword.cursor + 0) (.symbol .leftBrace))
      (payloadRejected : PlainImportRejects afterKeyword rejected) :
      ImportDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end
