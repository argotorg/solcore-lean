import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Modules
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Internal.ImportOutcomes

/-!
Proofs about the parsers of imports: token-window and cursor laws, source validity,
soundness against the declarative grammar, and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ExportDeclSoundnessProperties
/-! Aggregate success soundness of all canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful export follows one exact declarative form. -/
theorem exportDecl_success_sound {input next : State}
    {declaration : ExportDecl}
    (result : exportDecl input = .ok declaration next) :
    DeclarativeGrammar.ExportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  unfold exportDecl at result
  cases keywordResult : keyword .exportKw .exportDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject failure rejected => simp [bind, keywordResult] at result
  | ok exportKeyword afterKeyword =>
      have keywordSound := keyword_ok_tokenAt .exportKw .exportDecl
        keywordResult
      simp only [bind, keywordResult, getState] at result
      split at result
      · have tailGrammar := localExport_success_sound exportKeyword.span
          result
        apply DeclarativeGrammar.ExportDeclParses.ofLocal
        unfold DeclarativeGrammar.LocalExportDeclParses
        refine ⟨exportKeyword.span, keywordSound.1, ?_⟩
        simpa only [keywordSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using tailGrammar
      · have leftBraceFalse :
            isSymbol afterKeyword .leftBrace = false := by
          cases found : isSymbol afterKeyword .leftBrace <;> simp_all
        have leftBraceAbsentAfter := symbolAbsentAt_of_isSymbol_eq_false
          .leftBrace leftBraceFalse
        have leftBraceAbsentInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1)
              (.symbol .leftBrace) := by
          simpa only [keywordSound.2, State.tokens, State.window,
            State.cursor] using leftBraceAbsentAfter
        have tailGrammar := pathExport_success_sound exportKeyword.span result
        cases tailGrammar with
        | itemsFrom parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofItemsFrom
            unfold DeclarativeGrammar.ItemsFromExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed
        | moduleAs parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofModuleAs
            unfold DeclarativeGrammar.ModuleAsExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed
        | module parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofModule
            unfold DeclarativeGrammar.ModuleExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed

/-- Aggregate export grammar soundness composes with source validity. -/
theorem exportDecl_success_sound_and_validFor {input next : State}
    {declaration : ExportDecl} (inputValid : input.ValidFor)
    (result : exportDecl input = .ok declaration next) :
    DeclarativeGrammar.ExportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨exportDecl_success_sound result, ?_⟩
  have valid := exportDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NameOperatorDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection for shared name and selector parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

private theorem qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next result diagnosticFree
      simp [qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next result diagnosticFree
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next result
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess context afterDot
                    component afterComponent componentResult afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot context input
                  dot afterDot dotResult afterDotFree
      · unfold finishQualifiedName at result
        cases result
        exact diagnosticFree

end QualifiedNameInternals

/-- Qualified-name parsing cannot erase an incoming diagnostic. -/
theorem qualifiedName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess (qualifiedName context phase) := by
  intro input value next result diagnosticFree
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree :=
        QualifiedNameInternals.qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
          context phase first (afterFirst.remainingCount + 1) first []
            afterFirst value next result diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess context input first
        afterFirst firstResult afterFirstFree

/-- Module-path parsing cannot erase an incoming diagnostic. -/
theorem modulePath_reflectsDiagnosticFreeOnSuccess (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (modulePath context) := by
  intro input value next result diagnosticFree
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name afterName =>
            simp only [nameResult] at result
            cases result
            have afterMarkerFree :=
              qualifiedName_reflectsDiagnosticFreeOnSuccess context .topLevel
                afterMarker name next nameResult diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .at context input
              marker afterMarker markerResult afterMarkerFree
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_reflectsDiagnosticFreeOnSuccess context .topLevel
          input name next nameResult diagnosticFree

namespace OperatorInternals

private theorem operatorParts_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) : ∀ fuel partsRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (operatorParts context fuel partsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input value next result diagnosticFree
      simp [operatorParts] at result
  | succ fuel inductionHypothesis =>
      intro partsRev input value next result diagnosticFree
      unfold operatorParts at result
      cases found : input.peek? with
      | some token =>
          simp only [found] at result
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only [part] at result
              exact inductionHypothesis (spelling :: partsRev)
                { input with cursor := input.cursor + 1 } value next result
                  diagnosticFree
          | none =>
              simp only [part] at result
              split at result
              · simp [rejectAt] at result
              · cases result
                exact diagnosticFree
      | none =>
          simp only [found] at result
          split at result
          · simp [rejectAt] at result
          · cases result
            exact diagnosticFree

end OperatorInternals

/-- Parenthesized operator parsing cannot erase an incoming diagnostic. -/
theorem operatorSelector_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (operatorSelector context) := by
  intro input value next result diagnosticFree
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : OperatorInternals.operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing afterClosing =>
              simp only [closingResult] at result
              cases result
              have afterPartsFree :=
                symbol_reflectsDiagnosticFreeOnSuccess .rightParen context
                  afterParts closing next closingResult diagnosticFree
              have afterOpeningFree :=
                OperatorInternals.operatorParts_reflectsDiagnosticFreeOnSuccess
                  context (afterOpening.remainingCount + 1) [] afterOpening
                    parts afterParts partsResult afterPartsFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen context
                input opening afterOpening openingResult afterOpeningFree

/-- Selector-name parsing cannot erase an incoming diagnostic. -/
theorem selectorName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (selectorName context) := by
  intro input value next result diagnosticFree
  unfold selectorName at result
  split at result
  · exact operatorSelector_reflectsDiagnosticFreeOnSuccess context input
      value next result diagnosticFree
  · cases nameResult : identifier context input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact identifier_reflectsDiagnosticFreeOnSuccess context input name
          next nameResult diagnosticFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection for canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExportInternals

private theorem exportPathTail_reflectsDiagnosticFreeOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next result diagnosticFree
      simp [exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next result diagnosticFree
      unfold exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next result
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
                    afterDot component afterComponent componentResult
                      afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl
                  input dot afterDot dotResult afterDotFree
      · unfold finishExportPath at result
        cases result
        exact diagnosticFree

private theorem exportPath_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportPath := by
  intro input value next result diagnosticFree
  unfold exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := exportPathTail_reflectsDiagnosticFreeOnSuccess
        first (afterFirst.remainingCount + 1) first [] afterFirst value next
          result diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl input first
        afterFirst firstResult afterFirstFree

private theorem requireConstructorNames_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireConstructorNames values) := by
  unfold requireConstructorNames
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem constructorSelection_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess constructorSelection := by
  unfold constructorSelection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .exportDecl)
    intro opening
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .exportDecl)
    intro closing
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
        .leftParen .rightParen false (identifier .exportDecl) .exportDecl
          .topLevel
            (identifier_reflectsDiagnosticFreeOnSuccess .exportDecl))
    intro values
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireConstructorNames_reflectsDiagnosticFreeOnSuccess values)
    intro constructors
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem exportName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportName := by
  intro input value next result diagnosticFree
  unfold exportName at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl input
          marker next markerResult diagnosticFree
  · split at result
    · cases selectorResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectorResult] at result
      | reject failure rejected => simp [selectorResult] at result
      | ok selected afterSelected =>
          simp only [selectorResult] at result
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at result
          | operator spelling =>
              simp only [selectedValue] at result
              cases result
              exact operatorSelector_reflectsDiagnosticFreeOnSuccess
                .exportDecl input selected next selectorResult diagnosticFree
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          split at result
          · cases constructorsResult : constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | reject failure rejected => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at result
                cases result
                have afterNameFree :=
                  constructorSelection_reflectsDiagnosticFreeOnSuccess
                    afterName constructors next constructorsResult
                      diagnosticFree
                exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
                  input name afterName nameResult afterNameFree
          · cases result
            exact identifier_reflectsDiagnosticFreeOnSuccess .exportDecl
              input name next nameResult diagnosticFree

private theorem localExportItem_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess localExportItem := by
  intro input value next result diagnosticFree
  unfold localExportItem at result
  split at result
  · cases pathResult : exportPath input with
    | invariant error => simp [pathResult] at result
    | reject failure rejected => simp [pathResult] at result
    | ok path afterPath =>
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | reject failure rejected => simp [markerResult] at result
            | ok marker afterMarker =>
                simp only [markerResult] at result
                cases result
                have afterDotFree :=
                  symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl
                    afterDot marker next markerResult diagnosticFree
                have afterPathFree :=
                  symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl
                    afterPath dot afterDot dotResult afterDotFree
                exact exportPath_reflectsDiagnosticFreeOnSuccess input path
                  afterPath pathResult afterPathFree
  · cases nameResult : exportName input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact exportName_reflectsDiagnosticFreeOnSuccess input name next
          nameResult diagnosticFree

private theorem exportSelection_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportSelection := by
  intro input value next result diagnosticFree
  unfold exportSelection at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .star .exportDecl input
          marker next markerResult diagnosticFree
  · cases itemsResult : delimited .leftBrace .rightBrace true exportName
        .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | reject failure rejected => simp [itemsResult] at result
    | ok items afterItems =>
        simp only [itemsResult] at result
        cases result
        exact delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace
          true exportName .exportDecl .topLevel
            exportName_reflectsDiagnosticFreeOnSuccess input items next
              itemsResult diagnosticFree

private theorem finishExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (value : ExportDeclValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess (finishExport start value) := by
  unfold finishExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .exportDecl)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem localExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (localExport start) := by
  unfold localExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace true
      localExportItem .exportDecl .topLevel
        localExportItem_reflectsDiagnosticFreeOnSuccess)
  intro items
  exact finishExport_reflectsDiagnosticFreeOnSuccess start (.local items)

private theorem pathExport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (pathExport start) := by
  unfold pathExport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    exportPath_reflectsDiagnosticFreeOnSuccess
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .dot .exportDecl)
    intro dot
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      exportSelection_reflectsDiagnosticFreeOnSuccess
    intro selection
    exact finishExport_reflectsDiagnosticFreeOnSuccess start
      (.itemsFrom path selection)
  · split
    · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (keyword_reflectsDiagnosticFreeOnSuccess .asKw .exportDecl)
      intro asMarker
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (identifier_reflectsDiagnosticFreeOnSuccess .exportDecl)
      intro alias
      exact finishExport_reflectsDiagnosticFreeOnSuccess start
        (.moduleAs path alias)
    · exact finishExport_reflectsDiagnosticFreeOnSuccess start (.module path)

end Solcore.Syntax.Parser.ExportInternals

namespace Solcore.Syntax.Parser

/-- Export parsing cannot erase an incoming diagnostic. -/
theorem exportDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess exportDecl := by
  unfold exportDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .exportKw .exportDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · exact ExportInternals.localExport_reflectsDiagnosticFreeOnSuccess
      marker.span
  · exact ExportInternals.pathExport_reflectsDiagnosticFreeOnSuccess
      marker.span

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection for canonical import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImportInternals

private theorem selectedAlias_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedAlias := by
  unfold selectedAlias
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .asKw .importDecl)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (identifier_reflectsDiagnosticFreeOnSuccess .importDecl)
    intro name
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end ImportInternals

private theorem selectedImport_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedImport := by
  unfold selectedImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (selectorName_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro source
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ImportInternals.selectedAlias_reflectsDiagnosticFreeOnSuccess
  intro alias
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

namespace ImportInternals

private theorem requireSelected_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList SelectedImport) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireSelected values) := by
  unfold requireSelected
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem selectedImports_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess selectedImports := by
  unfold selectedImports
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel
      selectedImport_reflectsDiagnosticFreeOnSuccess)
  exact requireSelected_reflectsDiagnosticFreeOnSuccess

private theorem requireSelectorNames_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList SelectorName) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireSelectorNames values) := by
  unfold requireSelectorNames
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem hidingClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess hidingClause := by
  unfold hidingClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .hiding .importDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel
      (selectorName_reflectsDiagnosticFreeOnSuccess .importDecl))
  intro values
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (requireSelectorNames_reflectsDiagnosticFreeOnSuccess values)
  intro names
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem optionalHiding_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalHiding := by
  unfold optionalHiding
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      hidingClause_reflectsDiagnosticFreeOnSuccess
    intro clause
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem terminator_reflectsDiagnosticFreeOnSuccess
    (lastSpan : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (terminator lastSpan) := by
  intro input value next result diagnosticFree
  unfold terminator at result
  split at result
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult] at result
        cases result
        exact symbol_reflectsDiagnosticFreeOnSuccess .semicolon .importDecl
          input semicolon next semicolonResult diagnosticFree
  · split at result
    · cases result
      simp [State.emit] at diagnosticFree
    · simp [rejectAt] at result

private theorem finish_reflectsDiagnosticFreeOnSuccess
    (start last : SourceSpan) (value : ImportDeclValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess (finish start last value) := by
  unfold finish
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (terminator_reflectsDiagnosticFreeOnSuccess last)
  intro endSpan
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem plainImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (plainImport start) := by
  unfold plainImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  exact finish_reflectsDiagnosticFreeOnSuccess start path.span (.plain path)

private theorem namespaceImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (namespaceImport start) := by
  unfold namespaceImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .asKw .importDecl)
  intro asMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro alias
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  exact finish_reflectsDiagnosticFreeOnSuccess start path.span
    (.namespace path alias)

private theorem wildcardImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (wildcardImport start) := by
  unfold wildcardImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalHiding_reflectsDiagnosticFreeOnSuccess
  intro hidden
  exact finish_reflectsDiagnosticFreeOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

private theorem selectiveImport_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess (selectiveImport start) := by
  unfold selectiveImport
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    selectedImports_reflectsDiagnosticFreeOnSuccess
  intro selection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modulePath_reflectsDiagnosticFreeOnSuccess .importDecl)
  intro path
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalHiding_reflectsDiagnosticFreeOnSuccess
  intro hidden
  exact finish_reflectsDiagnosticFreeOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

end ImportInternals

/-- Import parsing cannot erase an incoming diagnostic. -/
theorem importDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess importDecl := by
  unfold importDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .importKw .importDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · split
    · exact ImportInternals.namespaceImport_reflectsDiagnosticFreeOnSuccess
        marker.span
    · exact ImportInternals.wildcardImport_reflectsDiagnosticFreeOnSuccess
        marker.span
  · split
    · exact ImportInternals.selectiveImport_reflectsDiagnosticFreeOnSuccess
        marker.span
    · exact ImportInternals.plainImport_reflectsDiagnosticFreeOnSuccess
        marker.span

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.HidingClauseOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for required and optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every required hiding-clause rejection is either the missing contextual
marker or the exact nested nonempty allow-trailing selector-list rejection. -/
theorem hidingClause_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.hidingClause input =
      .reject failure rejected) :
    DeclarativeGrammar.HidingClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.hidingClause at result
  cases markerResult : contextual .hiding .importDecl input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .hiding .importDecl
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .hiding .importDecl markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .hiding
        .importDecl markerResult
      cases valuesResult : delimited .leftBrace .rightBrace false
          (selectorName .importDecl) .importDecl .topLevel afterMarker with
      | invariant error => simp [valuesResult] at result
      | reject valuesFailure valuesRejected =>
          simp only [valuesResult] at result
          cases result
          exact .namesRejected marker.span markerParsed
            (delimited_reject_sound .leftBrace .rightBrace false
              (selectorName .importDecl)
              DeclarativeGrammar.SelectorNameOrdinaryParses
              DeclarativeGrammar.SelectorNameRejects .importDecl .topLevel
              (selectorName_success_ordinaryOutcome_sound .importDecl)
              (selectorName_reject_ordinaryOutcome_sound .importDecl)
              valuesResult)
      | ok values afterValues =>
          simp only [valuesResult] at result
          cases namesResult : ImportInternals.requireSelectorNames values
              afterValues with
          | invariant error => simp [namesResult] at result
          | reject namesFailure namesRejected =>
              unfold ImportInternals.requireSelectorNames at namesResult
              cases elements : values.elements <;>
                simp [elements, pure] at namesResult
          | ok names afterNames => simp [namesResult, pure] at result

/-- Optional hiding can reject only after its positive contextual guard commits
to a required hiding clause. -/
theorem optionalHiding_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.optionalHiding input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalHidingRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.optionalHiding getState at result
  simp only [bind] at result
  by_cases present : isContextual input .hiding = true
  · simp only [present, if_true] at result
    rcases contextual_eq_ok_of_isContextual_eq_true .hiding .importDecl
        present with
      ⟨marker, markerResult⟩
    cases clauseResult : ImportInternals.hidingClause input with
    | invariant error => simp [clauseResult] at result
    | ok clause output => simp [clauseResult, pure] at result
    | reject clauseFailure clauseRejected =>
        simp only [clauseResult] at result
        cases result
        exact .present
          ⟨marker.span,
            (contextual_success_exactTokenParses .hiding .importDecl
              markerResult).1⟩
          (hidingClause_reject_ordinaryOutcome_sound clauseResult)
  · have absent : isContextual input .hiding = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable top-item-start predicate admits exactly the finite token
kinds recorded by the declarative import-terminator grammar. -/
theorem importTerminatorTopItemStartKind_iff (kind : TokenKind) :
    isTopItemStartKind kind = true ↔
      kind ∈ DeclarativeGrammar.ImportTerminatorTopItemStartKinds := by
  cases kind with
  | keyword keyword =>
      cases keyword <;> simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | symbol symbol =>
      cases symbol <;> simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | identifier text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual, Bool.or_eq_true, or_assoc]
  | yulIdentifier text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | decimalLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | hexadecimalLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | stringLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | yulMetaBacktick text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | yulMetaInterpolation text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]

/-- Positive executable top-item lookahead exposes the exact current token. -/
theorem importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true
    {input : State} (present : atTopItemStart input = true) :
    DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder := by
  unfold atTopItemStart State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      simp only [found, Option.map_some] at present
      exact ⟨kind, (importTerminatorTopItemStartKind_iff kind).mp present,
        span, tokenAt_of_peek?_eq_some found⟩

/-- Negative executable top-item lookahead excludes every admitted start
kind at the current cursor. -/
theorem importTerminatorTopItemStartAbsentAt_of_atTopItemStart_eq_false
    {input : State} (absent : atTopItemStart input = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds := by
  intro kind member
  rintro ⟨span, inside, found⟩
  change input.cursor < input.window.endIndex at inside
  change input.tokens[input.cursor]? = some { span, value := kind } at found
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [inside, ↓reduceIte, found, Option.map_some]
  have stopped : isTopItemStartKind kind = false := by
    simpa [atTopItemStart, peekKind] using absent
  have starts : isTopItemStartKind kind = true :=
    (importTerminatorTopItemStartKind_iff kind).mpr member
  rw [starts] at stopped
  contradiction

/-- Every executable import-terminator success is an exact semicolon success
or the nonconsuming diagnostic recovery before a top-item start. -/
theorem importTerminator_success_ordinaryOutcome_sound (lastSpan : SourceSpan)
    {input output : State} {endSpan : SourceSpan}
    (result : ImportInternals.terminator lastSpan input = .ok endSpan output) :
    DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
      input.declarativeRemainder endSpan output.declarativeRemainder := by
  unfold ImportInternals.terminator at result
  by_cases semicolonPresent : isSymbol input .semicolon = true
  · simp only [semicolonPresent, if_true] at result
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok token next =>
        simp only [semicolonResult] at result
        cases result
        exact .semicolon token.span
          (symbol_success_exactTokenParses .semicolon .importDecl
            semicolonResult)
  · have semicolonAbsent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr semicolonPresent
    simp only [semicolonAbsent, Bool.false_eq_true, if_false] at result
    by_cases topItemPresent : atTopItemStart input = true
    · simp only [topItemPresent, if_true] at result
      cases result
      simpa only [State.emit, State.declarativeRemainder] using
        (DeclarativeGrammar.ImportTerminatorOrdinaryParses.recovered
          (lastSpan := lastSpan)
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonAbsent)
          (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true
            topItemPresent))
    · have topItemAbsent : atTopItemStart input = false :=
        Bool.eq_false_iff.mpr topItemPresent
      simp [topItemAbsent, rejectAt] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable import-terminator rejection is the exact nonconsuming
endpoint where both the semicolon and top-item-start guards are absent. -/
theorem importTerminator_reject_ordinaryOutcome_sound (lastSpan : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.terminator lastSpan input =
      .reject failure rejected) :
    DeclarativeGrammar.ImportTerminatorRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.terminator at result
  by_cases semicolonPresent : isSymbol input .semicolon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .importDecl
        semicolonPresent with ⟨token, semicolonResult⟩
    simp [semicolonPresent, semicolonResult] at result
  · have semicolonAbsent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr semicolonPresent
    simp only [semicolonAbsent, Bool.false_eq_true, if_false] at result
    by_cases topItemPresent : atTopItemStart input = true
    · simp [topItemPresent] at result
    · have topItemAbsent : atTopItemStart input = false :=
        Bool.eq_false_iff.mpr topItemPresent
      simp only [topItemAbsent, Bool.false_eq_true, if_false] at result
      unfold rejectAt at result
      cases result
      exact .missing
        (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonAbsent)
        (importTerminatorTopItemStartAbsentAt_of_atTopItemStart_eq_false
          topItemAbsent)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamespaceImportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for namespace-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_reject_tokenKindAbsentAt
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

/-- Every executable namespace-import rejection records its exact first
rejecting stage among `*`, `as`, alias, `from`, path, and terminator. -/
theorem namespaceImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.namespaceImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.NamespaceImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.namespaceImport at result
  cases starResult : symbol .star .importDecl input with
  | invariant error => simp [bind, starResult] at result
  | reject starFailure starRejected =>
      have starRejectedEq := symbol_reject_state_eq .star .importDecl
        starResult
      subst starRejected
      simp only [bind, starResult] at result
      cases result
      exact .starMissing
        (symbol_reject_tokenKindAbsentAt .star .importDecl starResult)
  | ok star afterStar =>
      simp only [bind, starResult] at result
      have starParsed := symbol_success_exactTokenParses .star .importDecl
        starResult
      cases asResult : keyword .asKw .importDecl afterStar with
      | invariant error => simp [asResult] at result
      | reject asFailure asRejected =>
          have asRejectedEq := keyword_reject_state_eq .asKw .importDecl
            asResult
          subst asRejected
          simp only [asResult] at result
          cases result
          exact .asMissing star.span starParsed
            (keyword_reject_tokenKindAbsentAt .asKw .importDecl asResult)
      | ok asToken afterAs =>
          simp only [asResult] at result
          have asParsed := keyword_success_exactTokenParses .asKw .importDecl
            asResult
          cases aliasResult : identifier .importDecl afterAs with
          | invariant error => simp [aliasResult] at result
          | reject aliasFailure aliasRejected =>
              simp only [aliasResult] at result
              cases result
              exact .aliasRejected star.span asToken.span starParsed asParsed
                (identifier_reject_sound .importDecl aliasResult)
          | ok alias afterAlias =>
              simp only [aliasResult] at result
              have aliasParsed := identifier_success_sound .importDecl
                aliasResult
              cases fromResult : contextual .from .importDecl afterAlias with
              | invariant error => simp [fromResult] at result
              | reject fromFailure fromRejected =>
                  have fromRejectedEq := contextual_reject_state_eq .from
                    .importDecl fromResult
                  subst fromRejected
                  simp only [fromResult] at result
                  cases result
                  exact .fromMissing star.span asToken.span starParsed asParsed
                    aliasParsed
                    (contextual_reject_tokenKindAbsentAt .from .importDecl
                      fromResult)
              | ok fromToken afterFrom =>
                  simp only [fromResult] at result
                  have fromParsed := contextual_success_exactTokenParses
                    .from .importDecl fromResult
                  cases pathResult : modulePath .importDecl afterFrom with
                  | invariant error => simp [pathResult] at result
                  | reject pathFailure pathRejected =>
                      simp only [pathResult] at result
                      cases result
                      exact .pathRejected star.span asToken.span fromToken.span
                        starParsed asParsed aliasParsed fromParsed
                        (modulePath_reject_ordinaryOutcome_sound .importDecl
                          pathResult)
                  | ok path afterPath =>
                      simp only [pathResult] at result
                      have pathParsed :=
                        modulePath_success_ordinaryOutcome_sound .importDecl
                          pathResult
                      unfold ImportInternals.finish at result
                      cases terminatorResult :
                          ImportInternals.terminator path.span afterPath with
                      | invariant error => simp [bind, terminatorResult] at result
                      | ok endSpan output =>
                          simp [bind, terminatorResult, pure] at result
                      | reject terminatorFailure terminatorRejected =>
                          simp only [bind, terminatorResult] at result
                          cases result
                          exact .terminatorRejected star.span asToken.span
                            fromToken.span starParsed asParsed aliasParsed
                            fromParsed pathParsed
                            (importTerminator_reject_ordinaryOutcome_sound
                              path.span terminatorResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainImportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable plain-import rejection occurs first in its module path,
or after an exact path success in its import terminator. -/
theorem plainImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.plainImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.PlainImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  cases pathResult : modulePath .importDecl input with
  | invariant error => simp [bind, pathResult] at result
  | reject pathFailure pathRejected =>
      simp only [bind, pathResult] at result
      cases result
      exact .pathRejected
        (modulePath_reject_ordinaryOutcome_sound .importDecl pathResult)
  | ok path afterPath =>
      simp only [bind, pathResult] at result
      have pathParsed :=
        modulePath_success_ordinaryOutcome_sound .importDecl pathResult
      unfold ImportInternals.finish at result
      cases terminatorResult :
          ImportInternals.terminator path.span afterPath with
      | invariant error => simp [bind, terminatorResult] at result
      | reject terminatorFailure terminatorRejected =>
          simp only [bind, terminatorResult] at result
          cases result
          exact .terminatorRejected pathParsed
            (importTerminator_reject_ordinaryOutcome_sound path.span
              terminatorResult)
      | ok endSpan afterEnd => simp [bind, terminatorResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportTerminatorOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package import-terminator semicolon/recovery success and exact rejection. -/
theorem importTerminator_ordinaryOutcome_sound (lastSpan : SourceSpan) :
    (∀ {input output : State} {endSpan : SourceSpan},
      ImportInternals.terminator lastSpan input = .ok endSpan output →
        DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
          input.declarativeRemainder endSpan output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.terminator lastSpan input = .reject failure rejected →
        DeclarativeGrammar.ImportTerminatorRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨importTerminator_success_ordinaryOutcome_sound lastSpan,
    importTerminator_reject_ordinaryOutcome_sound lastSpan⟩

/-- Re-export deterministic and exclusive import-terminator outcomes. -/
theorem importTerminator_ordinaryOutcomeSpec (lastSpan : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan)
      DeclarativeGrammar.ImportTerminatorRejects :=
  DeclarativeGrammar.importTerminatorDeterministicOutcomeSpec lastSpan


/-- Exact values and endpoints for the independent importTerminator grammar. -/
theorem importTerminator_exactOutcomeSpec (lastSpan : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan) DeclarativeGrammar.ImportTerminatorRejects :=
  DeclarativeGrammar.importTerminatorExactOutcomeSpec lastSpan

/-- Executable successes agree on their complete value and remainder. -/
theorem importTerminator_success_result_unique (lastSpan : SourceSpan)
    {input leftOutput rightOutput : State} {left right : SourceSpan}
    (leftResult : ImportInternals.terminator lastSpan input = .ok left leftOutput)
    (rightResult : ImportInternals.terminator lastSpan input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importTerminator_exactOutcomeSpec lastSpan).successResultUnique
    (importTerminator_success_ordinaryOutcome_sound lastSpan leftResult)
    (importTerminator_success_ordinaryOutcome_sound lastSpan rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem importTerminator_reject_output_unique (lastSpan : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.terminator lastSpan input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.terminator lastSpan input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importTerminator_exactOutcomeSpec lastSpan).rejectOutputUnique
    (importTerminator_reject_ordinaryOutcome_sound lastSpan leftResult)
    (importTerminator_reject_ordinaryOutcome_sound lastSpan rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamespaceImportOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for namespace-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_success_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable namespace-import success preserves the exact fixed
prefix, alias, module path, recovered-or-explicit terminator, AST, span, and
final remainder. -/
theorem namespaceImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.namespaceImport start input =
      .ok declaration output) :
    DeclarativeGrammar.NamespaceImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.namespaceImport at result
  rcases bind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  rcases bind_success_components rest with
    ⟨asToken, afterAs, asResult, rest⟩
  rcases bind_success_components rest with
    ⟨alias, afterAlias, aliasResult, rest⟩
  rcases bind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases bind_success_components rest with
    ⟨path, afterPath, pathResult, finishResult⟩
  unfold ImportInternals.finish at finishResult
  rcases bind_success_components finishResult with
    ⟨endSpan, afterTerminator, terminatorResult, finished⟩
  cases finished
  exact .parsed star.span asToken.span fromToken.span endSpan
    (symbol_success_exactTokenParses .star .importDecl starResult)
    (keyword_success_exactTokenParses .asKw .importDecl asResult)
    (identifier_success_sound .importDecl aliasResult)
    (contextual_success_exactTokenParses .from .importDecl fromResult)
    (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
    (importTerminator_success_ordinaryOutcome_sound path.span
      terminatorResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamespaceImportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for namespace import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package namespace-import success and exact stagewise rejection. -/
theorem namespaceImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.namespaceImport start input = .ok declaration output →
        DeclarativeGrammar.NamespaceImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.namespaceImport start input = .reject failure rejected →
        DeclarativeGrammar.NamespaceImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namespaceImport_success_ordinaryOutcome_sound start,
    namespaceImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive namespace-import outcomes. -/
theorem namespaceImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.NamespaceImportOrdinaryParses start)
      DeclarativeGrammar.NamespaceImportRejects :=
  DeclarativeGrammar.namespaceImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainImportOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable plain-import success preserves its exact module path,
ordinary terminator outcome, AST span, and final remainder. -/
theorem plainImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.plainImport start input =
      .ok declaration output) :
    DeclarativeGrammar.PlainImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  cases pathResult : modulePath .importDecl input with
  | invariant error => simp [bind, pathResult] at result
  | reject failure rejected => simp [bind, pathResult] at result
  | ok path afterPath =>
      simp only [bind, pathResult] at result
      have pathParsed :=
        modulePath_success_ordinaryOutcome_sound .importDecl pathResult
      unfold ImportInternals.finish at result
      cases terminatorResult :
          ImportInternals.terminator path.span afterPath with
      | invariant error => simp [bind, terminatorResult] at result
      | reject failure rejected => simp [bind, terminatorResult] at result
      | ok endSpan afterEnd =>
          simp only [bind, terminatorResult] at result
          cases result
          exact .parsed pathParsed
            (importTerminator_success_ordinaryOutcome_sound path.span
              terminatorResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainImportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package plain-import success and exact path/terminator rejection. -/
theorem plainImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.plainImport start input = .ok declaration output →
        DeclarativeGrammar.PlainImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.plainImport start input = .reject failure rejected →
        DeclarativeGrammar.PlainImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨plainImport_success_ordinaryOutcome_sound start,
    plainImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive plain-import outcomes. -/
theorem plainImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PlainImportOrdinaryParses start)
      DeclarativeGrammar.PlainImportRejects :=
  DeclarativeGrammar.plainImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedAliasOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-alias rejection is the missing identifier after
its positively guarded and exactly consumed `as` marker. -/
theorem selectedAlias_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectedAlias input = .reject failure rejected) :
    DeclarativeGrammar.SelectedAliasRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectedAlias getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .asKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .asKw .importDecl present with
      ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases nameResult : identifier .importDecl
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [nameResult] at result
    | ok name afterName => simp [nameResult, pure] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .nameRejected marker.span
          (keyword_success_exactTokenParses .asKw .importDecl markerResult)
          (identifier_reject_sound .importDecl nameResult)
  · have absent : isKeyword input .asKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportProperties
/-! Compositional contracts for canonical import parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem importBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Optional selected-import aliases retain their identifier range. -/
theorem selectedAlias_validFor :
    ImportInternals.selectedAlias.ValidFor
      (Option.ValidFor Located.ValidFor) := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .asKw .importDecl)
    intro marker
    apply Parser.bind_validFor_of_value (identifier_validFor .importDecl)
    intro name input inputValid nameValid
    exact ⟨by simpa only [Option.ValidFor] using nameValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none
      (Option.ValidFor Located.ValidFor) (fun _ => trivial)

/-- Optional aliases preserve every ordinary token window. -/
theorem selectedAlias_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .asKw .importDecl)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (identifier_preservesTokenWindow .importDecl)
    intro name
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Optional aliases preserve the immutable token carrier on success. -/
theorem selectedAlias_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.selectedAlias :=
  selectedAlias_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional selected-import aliases never rewind the parser cursor. -/
theorem selectedAlias_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .asKw .importDecl)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (identifier_cursorMonotoneOnSuccess .importDecl)
    intro name
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

private theorem requireSelectorNames_validFor
    (values : DelimitedList SelectorName) :
    (ImportInternals.requireSelectorNames values).ValidFor
      (fun _ _ => True) := by
  intro input inputValid
  unfold ImportInternals.requireSelectorNames
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨trivial, inputValid, rfl⟩

private theorem requireSelectorNames_preservesTokenWindow
    (values : DelimitedList SelectorName) :
    Parser.PreservesTokenWindow
      (ImportInternals.requireSelectorNames values) := by
  intro input
  unfold ImportInternals.requireSelectorNames
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

private theorem requireSelectorNames_cursorMonotoneOnSuccess
    (values : DelimitedList SelectorName) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.requireSelectorNames values) := by
  intro input names next result
  unfold ImportInternals.requireSelectorNames at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

/-- Hiding clauses retain their keyword cover and every selector range. -/
theorem hidingClause_validFor :
    ImportInternals.hidingClause.ValidFor HidingClause.ValidFor := by
  have weak : ImportInternals.hidingClause.ValidFor
      (fun _ _ => True) := by
    unfold ImportInternals.hidingClause
    apply Parser.bind_validFor
      (contextual_validFor .hiding .importDecl)
    intro marker
    apply Parser.bind_validFor (delimited_validFor SelectorName.ValidFor
      .leftBrace .rightBrace false (selectorName .importDecl)
      .importDecl .topLevel (selectorName_validFor .importDecl)
      (selectorName_preservesTokensOnSuccess .importDecl))
    intro values
    apply Parser.bind_validFor (requireSelectorNames_validFor values)
    intro names
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : ImportInternals.hidingClause input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok clause final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold ImportInternals.hidingClause at stages
      rcases importBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨values, afterValues, valuesResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨names, afterNames, namesResult, finished⟩
      have markerValid := contextual_validFor .hiding .importDecl
        input inputValid
      rw [markerResult] at markerValid
      have valuesValid := delimited_validFor SelectorName.ValidFor
        .leftBrace .rightBrace false (selectorName .importDecl)
        .importDecl .topLevel (selectorName_validFor .importDecl)
        (selectorName_preservesTokensOnSuccess .importDecl)
        afterMarker markerValid.2.1
      rw [valuesResult] at valuesValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have valuesValidInput :
          DelimitedList.ValidFor SelectorName.ValidFor input.file values := by
        simpa [markerValid.2.2] using valuesValid.1
      have markerShape := acceptToken_ok_state_shape
        (.contextual .hiding) .importDecl (·.isContextual .hiding)
        markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases delimited_startsAtCurrentTokenOnSuccess .leftBrace .rightBrace
          false (selectorName .importDecl) .importDecl .topLevel
          afterMarker values afterValues valuesResult with
        ⟨opening, openingFound, valuesStart⟩
      have markerBeforeValues :=
        inputValid.consumed_end_le_peek_start_after_advance
          markerAdvanced openingFound
      have ordered : marker.span.startByte ≤ values.span.endByte :=
        Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeValues (by
            rw [valuesStart]
            exact valuesValidInput.1.2.1))
      unfold ImportInternals.requireSelectorNames at namesResult
      cases elements : values.elements with
      | nil =>
          rw [elements] at namesResult
          contradiction
      | cons head tail =>
          rw [elements] at namesResult
          cases namesResult
          cases finished
          exact ⟨⟨SourceSpan.cover_validFor markerSpanValid
              valuesValidInput.1 ordered, by
                simpa [NonemptyList.toList, elements] using
                  valuesValidInput.2⟩,
            weakResult.2.1, weakResult.2.2⟩

/-- Hiding clauses preserve every ordinary token window. -/
theorem hidingClause_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.hidingClause := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .hiding .importDecl)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel
      (selectorName_preservesTokenWindow .importDecl))
  intro values
  apply Parser.bind_preservesTokenWindow
    (requireSelectorNames_preservesTokenWindow values)
  intro names
  exact Parser.pure_preservesTokenWindow _

theorem hidingClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.hidingClause :=
  hidingClause_preservesTokenWindow.preservesTokensOnSuccess

/-- Hiding clauses never rewind the parser cursor. -/
theorem hidingClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.hidingClause := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .hiding .importDecl)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel)
  intro values
  apply Parser.bind_cursorMonotoneOnSuccess
    (requireSelectorNames_cursorMonotoneOnSuccess values)
  intro names
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A hiding clause starts at its `hiding` token. -/
theorem hidingClause_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ImportInternals.hidingClause (·.span) := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.contextual .hiding) .importDecl (·.isContextual .hiding))
  intro marker input clause final parsed
  rcases importBind_ok_components parsed with
    ⟨values, afterValues, _valuesResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨names, afterNames, _namesResult, finished⟩
  cases finished
  rfl

/-- Optional hiding clauses preserve present-clause provenance. -/
theorem optionalHiding_validFor :
    ImportInternals.optionalHiding.ValidFor
      (Option.ValidFor HidingClause.ValidFor) := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor_of_value hidingClause_validFor
    intro clause input inputValid clauseValid
    exact ⟨by simpa only [Option.ValidFor] using clauseValid,
      inputValid, rfl⟩
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional hiding clauses preserve every ordinary token window. -/
theorem optionalHiding_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.optionalHiding := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow hidingClause_preservesTokenWindow
    intro clause
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow none

theorem optionalHiding_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.optionalHiding :=
  optionalHiding_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional hiding clauses never rewind the parser cursor. -/
theorem optionalHiding_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.optionalHiding := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      hidingClause_cursorMonotoneOnSuccess
    intro clause
    exact Parser.pure_cursorMonotoneOnSuccess _
  · exact Parser.pure_cursorMonotoneOnSuccess none

private theorem optionalHiding_some_components {input next : State}
    {clause : HidingClause}
    (parsed : ImportInternals.optionalHiding input = .ok (some clause) next) :
    ImportInternals.hidingClause input = .ok clause next := by
  unfold ImportInternals.optionalHiding at parsed
  rcases importBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, rest⟩
  unfold getState at observedResult
  cases observedResult
  split at rest
  · rcases importBind_ok_components rest with
      ⟨parsedClause, afterClause, clauseResult, finished⟩
    cases finished
    exact clauseResult
  · change Reply.ok none input = .ok (some clause) next at rest
    cases rest

/-- Import terminators retain a semicolon or the validated recovery span. -/
theorem importTerminator_validFor (lastSpan : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (lastValid : lastSpan.ValidFor input.file) :
    (ImportInternals.terminator lastSpan input).ValidFor input
      (fun file span => span.ValidFor file) := by
  unfold ImportInternals.terminator
  split
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have valid := symbol_validFor .semicolon .importDecl input inputValid
        rw [semicolonResult] at valid
        simpa only [Reply.ValidFor] using valid
    | ok token next =>
        have valid := symbol_validFor .semicolon .importDecl input inputValid
        rw [semicolonResult] at valid
        exact ⟨by simpa only [Located.ValidFor] using valid.1,
          valid.2.1, valid.2.2⟩
  · split
    · exact ⟨lastValid,
        inputValid.emit_validFor _ inputValid.currentSpan_validFor, rfl⟩
    · unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

private theorem importTerminator_end_order (start last : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (ordered : start.startByte ≤ last.endByte)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    {endSpan : SourceSpan} {next : State}
    (parsed : ImportInternals.terminator last input = .ok endSpan next) :
    start.startByte ≤ endSpan.endByte := by
  unfold ImportInternals.terminator at parsed
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at parsed
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at parsed
    | reject failure rejected => simp [semicolonResult] at parsed
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult] at parsed
        cases parsed
        have semicolonShape :=
          symbol_ok_state_shape .semicolon .importDecl semicolonResult
        have semicolonAt :=
          State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
        have startBeforeSemicolon :=
          inputValid.token_end_le_token_start_of_getElem?_lt
            startFound semicolonAt startBefore
        have semicolonValid :=
          inputValid.peek?_span_validFor semicolonShape.1
        exact Nat.le_trans startValid.2.1
          (Nat.le_trans (by simpa [startSpan] using startBeforeSemicolon)
            semicolonValid.2.1)
  · simp only [present] at parsed
    by_cases topStart : atTopItemStart input = true
    · simp only [topStart, if_true] at parsed
      cases parsed
      exact ordered
    · simp only [topStart] at parsed
      unfold rejectAt at parsed
      contradiction

/-- Finishing an import preserves both its cover and payload provenance. -/
theorem finishImport_validFor (start last : SourceSpan)
    (value : ImportDeclValue) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (lastValid : last.ValidFor input.file)
    (ordered : start.startByte ≤ last.endByte)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    (valueValid : match value with
      | .plain modulePath => ModulePath.ValidFor input.file modulePath
      | .namespace modulePath alias =>
          ModulePath.ValidFor input.file modulePath ∧
            alias.span.ValidFor input.file
      | .wildcard modulePath hidingClause =>
          ModulePath.ValidFor input.file modulePath ∧
            ∀ clause ∈ hidingClause, HidingClause.ValidFor input.file clause
      | .selected selection modulePath hidingClause =>
          selection.span.ValidFor input.file ∧
            (∀ item ∈ selection.elements.toList,
              SelectedImport.ValidFor input.file item) ∧
            ModulePath.ValidFor input.file modulePath ∧
            ∀ clause ∈ hidingClause,
              HidingClause.ValidFor input.file clause) :
    (ImportInternals.finish start last value input).ValidFor input
      ImportDecl.ValidFor := by
  have terminatorValid := importTerminator_validFor last input inputValid lastValid
  unfold ImportInternals.finish
  cases terminatorResult : ImportInternals.terminator last input with
  | invariant error =>
      simp only [bind, terminatorResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [terminatorResult] at terminatorValid
      simpa only [bind, terminatorResult, Reply.ValidFor] using
        terminatorValid
  | ok endSpan next =>
      rw [terminatorResult] at terminatorValid
      simp only [bind, terminatorResult, Reply.ValidFor, ImportDecl.ValidFor]
      refine ⟨⟨SourceSpan.cover_validFor startValid terminatorValid.1 ?_,
        valueValid⟩, terminatorValid.2.1, terminatorValid.2.2⟩
      exact importTerminator_end_order start last input inputValid startValid
        ordered startFound startSpan startBefore terminatorResult

private theorem finishAfterModulePath_validFor (start : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    {path : ModulePath} {afterPath : State}
    (pathResult : modulePath .importDecl input = .ok path afterPath)
    (value : ImportDeclValue)
    (valueValid : match value with
      | .plain modulePath => ModulePath.ValidFor afterPath.file modulePath
      | .namespace modulePath alias =>
          ModulePath.ValidFor afterPath.file modulePath ∧
            alias.span.ValidFor afterPath.file
      | .wildcard modulePath hidingClause =>
          ModulePath.ValidFor afterPath.file modulePath ∧
            ∀ clause ∈ hidingClause, HidingClause.ValidFor afterPath.file clause
      | .selected selection modulePath hidingClause =>
          selection.span.ValidFor afterPath.file ∧
            (∀ item ∈ selection.elements.toList,
              SelectedImport.ValidFor afterPath.file item) ∧
            ModulePath.ValidFor afterPath.file modulePath ∧
            ∀ clause ∈ hidingClause,
              HidingClause.ValidFor afterPath.file clause) :
    (ImportInternals.finish start path.span value afterPath).ValidFor input
      ImportDecl.ValidFor := by
  have pathReply := modulePath_validFor .importDecl input inputValid
  rw [pathResult] at pathReply
  rcases modulePath_startsAtCurrentTokenOnSuccess .importDecl
      input path afterPath pathResult with ⟨firstToken, firstFound, firstStart⟩
  have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have startBeforeFirst :=
    inputValid.token_end_le_token_start_of_getElem?_lt
      startFound firstAt startBefore
  have startValidAfter : start.ValidFor afterPath.file := by
    simpa [pathReply.2.2] using startValid
  have pathValidAfter : ModulePath.ValidFor afterPath.file path := by
    simpa [pathReply.2.2] using pathReply.1
  have startFoundAfter :
      afterPath.tokens[startIndex]? = some startToken := by
    simpa [modulePath_preservesTokensOnSuccess .importDecl
      input path afterPath pathResult] using startFound
  have startBeforeAfter : startIndex < afterPath.cursor :=
    Nat.lt_of_lt_of_le startBefore
      (modulePath_cursorMonotoneOnSuccess .importDecl
        input path afterPath pathResult)
  have ordered : start.startByte ≤ path.span.endByte :=
    Nat.le_trans startValid.2.1
      (Nat.le_trans (by simpa [startSpan] using startBeforeFirst)
        (by rw [firstStart]; exact pathReply.1.1.2.1))
  have finished := finishImport_validFor start path.span value afterPath
    pathReply.2.1 startValidAfter pathValidAfter.1 ordered startFoundAfter
    startSpan startBeforeAfter valueValid
  exact finished.of_file_eq pathReply.2.2

private theorem finishImport_weakValidFor (start last : SourceSpan)
    (value : ImportDeclValue) (input : State)
    (inputValid : input.ValidFor)
    (lastValid : last.ValidFor input.file) :
    (ImportInternals.finish start last value input).ValidFor input
      (fun _ _ => True) := by
  have terminatorValid := importTerminator_validFor last input inputValid lastValid
  unfold ImportInternals.finish
  cases terminatorResult : ImportInternals.terminator last input with
  | invariant error =>
      simp only [bind, terminatorResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [terminatorResult] at terminatorValid
      simpa only [bind, terminatorResult, Reply.ValidFor] using
        terminatorValid
  | ok endSpan next =>
      rw [terminatorResult] at terminatorValid
      simp only [bind, terminatorResult, Reply.ValidFor]
      exact ⟨trivial, terminatorValid.2.1, terminatorValid.2.2⟩

private theorem optionalHidingFinish_weakValidFor (start : SourceSpan)
    (path : ModulePath) (makeValue : Option HidingClause → ImportDeclValue)
    (input : State) (inputValid : input.ValidFor)
    (pathValid : ModulePath.ValidFor input.file path) :
    ((ImportInternals.optionalHiding >>= fun hidden =>
        ImportInternals.finish start
          (match hidden with
          | some clause => clause.span
          | none => path.span)
          (makeValue hidden)) input).ValidFor input (fun _ _ => True) := by
  have hiddenReply := optionalHiding_validFor input inputValid
  cases hiddenResult : ImportInternals.optionalHiding input with
  | invariant error =>
      simp only [bind, hiddenResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [hiddenResult] at hiddenReply
      simpa only [bind, hiddenResult, Reply.ValidFor] using hiddenReply
  | ok hidden afterHidden =>
      rw [hiddenResult] at hiddenReply
      have pathValidAfter : ModulePath.ValidFor afterHidden.file path := by
        simpa [hiddenReply.2.2] using pathValid
      cases hidden with
      | none =>
          have finished := finishImport_weakValidFor start path.span
            (makeValue none) afterHidden hiddenReply.2.1 pathValidAfter.1
          simpa only [bind, hiddenResult] using
            finished.of_file_eq hiddenReply.2.2
      | some clause =>
          have clauseValid : HidingClause.ValidFor afterHidden.file clause := by
            have validAtInput : HidingClause.ValidFor input.file clause := by
              simpa only [Option.ValidFor] using hiddenReply.1
            simpa [hiddenReply.2.2] using validAtInput
          have finished := finishImport_weakValidFor start clause.span
            (makeValue (some clause)) afterHidden hiddenReply.2.1
            clauseValid.1
          simpa only [bind, hiddenResult] using
            finished.of_file_eq hiddenReply.2.2

private theorem finishWildcardAfterModulePath_validFor (start : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    {path : ModulePath} {afterPath afterHidden : State}
    {hidden : Option HidingClause}
    (pathResult : modulePath .importDecl input = .ok path afterPath)
    (hiddenResult : ImportInternals.optionalHiding afterPath =
      .ok hidden afterHidden) :
    (ImportInternals.finish start
        (match hidden with
        | some clause => clause.span
        | none => path.span)
        (.wildcard path hidden) afterHidden).ValidFor input
      ImportDecl.ValidFor := by
  have pathReply := modulePath_validFor .importDecl input inputValid
  rw [pathResult] at pathReply
  have hiddenReply := optionalHiding_validFor afterPath pathReply.2.1
  rw [hiddenResult] at hiddenReply
  have afterHiddenFile : afterHidden.file = input.file :=
    hiddenReply.2.2.trans pathReply.2.2
  have startValidAfter : start.ValidFor afterHidden.file := by
    simpa [afterHiddenFile] using startValid
  have pathValidAfter : ModulePath.ValidFor afterHidden.file path := by
    simpa [afterHiddenFile] using pathReply.1
  have pathTokens := modulePath_preservesTokensOnSuccess .importDecl
    input path afterPath pathResult
  have hiddenTokens := optionalHiding_preservesTokensOnSuccess
    afterPath hidden afterHidden hiddenResult
  have startFoundAfterPath :
      afterPath.tokens[startIndex]? = some startToken := by
    rw [pathTokens]
    exact startFound
  have startFoundAfter :
      afterHidden.tokens[startIndex]? = some startToken := by
    rw [hiddenTokens]
    exact startFoundAfterPath
  have startBeforeAfterPath : startIndex < afterPath.cursor :=
    Nat.lt_of_lt_of_le startBefore
      (modulePath_cursorMonotoneOnSuccess .importDecl
        input path afterPath pathResult)
  have startBeforeAfter : startIndex < afterHidden.cursor :=
    Nat.lt_of_lt_of_le startBeforeAfterPath
      (optionalHiding_cursorMonotoneOnSuccess
        afterPath hidden afterHidden hiddenResult)
  rcases modulePath_startsAtCurrentTokenOnSuccess .importDecl
      input path afterPath pathResult with ⟨firstToken, firstFound, firstStart⟩
  have startBeforeFirst :=
    inputValid.token_end_le_token_start_of_getElem?_lt startFound
      (State.getElem?_eq_some_of_peek?_eq_some firstFound) startBefore
  have orderedPath : start.startByte ≤ path.span.endByte :=
    Nat.le_trans startValid.2.1
      (Nat.le_trans (by simpa [startSpan] using startBeforeFirst)
        (by rw [firstStart]; exact pathReply.1.1.2.1))
  cases hidden with
  | none =>
      have finished := finishImport_validFor start path.span
        (.wildcard path none) afterHidden hiddenReply.2.1 startValidAfter
        pathValidAfter.1 orderedPath startFoundAfter startSpan
        startBeforeAfter ⟨pathValidAfter, by simp⟩
      exact finished.of_file_eq afterHiddenFile
  | some clause =>
      have clauseResult := optionalHiding_some_components hiddenResult
      rcases hidingClause_startsAtCurrentTokenOnSuccess afterPath clause
          afterHidden clauseResult with ⟨marker, markerFound, clauseStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerFound
      have startBeforeClause :=
        pathReply.2.1.token_end_le_token_start_of_getElem?_lt
          startFoundAfterPath markerAt startBeforeAfterPath
      have clauseValidAtPath : HidingClause.ValidFor afterPath.file clause := by
        simpa only [Option.ValidFor] using hiddenReply.1
      have clauseValidAfter : HidingClause.ValidFor afterHidden.file clause := by
        simpa [hiddenReply.2.2] using clauseValidAtPath
      have startValidAtPath : start.ValidFor afterPath.file := by
        simpa [pathReply.2.2] using startValid
      have orderedClause : start.startByte ≤ clause.span.endByte :=
        Nat.le_trans startValidAtPath.2.1
          (Nat.le_trans (by simpa [startSpan] using startBeforeClause)
            (by rw [clauseStart]; exact clauseValidAtPath.1.2.1))
      have finished := finishImport_validFor start clause.span
        (.wildcard path (some clause)) afterHidden hiddenReply.2.1
        startValidAfter clauseValidAfter.1 orderedClause startFoundAfter
        startSpan startBeforeAfter ⟨pathValidAfter, by
          intro retained member
          have retainedEq : retained = clause := by
            have clauseEq : clause = retained := by simpa using member
            exact clauseEq.symm
          simpa [retainedEq] using clauseValidAfter⟩
      exact finished.of_file_eq afterHiddenFile

private theorem finishSelectedAfterModulePath_validFor (start : SourceSpan)
    (selection : NonemptyDelimitedList SelectedImport)
    (input : State) (inputValid : input.ValidFor)
    (selectionValid :
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor
        input.file selection)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    {path : ModulePath} {afterPath afterHidden : State}
    {hidden : Option HidingClause}
    (pathResult : modulePath .importDecl input = .ok path afterPath)
    (hiddenResult : ImportInternals.optionalHiding afterPath =
      .ok hidden afterHidden) :
    (ImportInternals.finish start
        (match hidden with
        | some clause => clause.span
        | none => path.span)
        (.selected selection path hidden) afterHidden).ValidFor input
      ImportDecl.ValidFor := by
  have pathReply := modulePath_validFor .importDecl input inputValid
  rw [pathResult] at pathReply
  have hiddenReply := optionalHiding_validFor afterPath pathReply.2.1
  rw [hiddenResult] at hiddenReply
  have afterHiddenFile : afterHidden.file = input.file :=
    hiddenReply.2.2.trans pathReply.2.2
  have selectionValidAfter :
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor
        afterHidden.file selection := by
    simpa [afterHiddenFile] using selectionValid
  have startValidAfter : start.ValidFor afterHidden.file := by
    simpa [afterHiddenFile] using startValid
  have pathValidAfter : ModulePath.ValidFor afterHidden.file path := by
    simpa [afterHiddenFile] using pathReply.1
  have pathTokens := modulePath_preservesTokensOnSuccess .importDecl
    input path afterPath pathResult
  have hiddenTokens := optionalHiding_preservesTokensOnSuccess
    afterPath hidden afterHidden hiddenResult
  have startFoundAfterPath :
      afterPath.tokens[startIndex]? = some startToken := by
    rw [pathTokens]
    exact startFound
  have startFoundAfter :
      afterHidden.tokens[startIndex]? = some startToken := by
    rw [hiddenTokens]
    exact startFoundAfterPath
  have startBeforeAfterPath : startIndex < afterPath.cursor :=
    Nat.lt_of_lt_of_le startBefore
      (modulePath_cursorMonotoneOnSuccess .importDecl
        input path afterPath pathResult)
  have startBeforeAfter : startIndex < afterHidden.cursor :=
    Nat.lt_of_lt_of_le startBeforeAfterPath
      (optionalHiding_cursorMonotoneOnSuccess
        afterPath hidden afterHidden hiddenResult)
  rcases modulePath_startsAtCurrentTokenOnSuccess .importDecl
      input path afterPath pathResult with ⟨firstToken, firstFound, firstStart⟩
  have startBeforeFirst :=
    inputValid.token_end_le_token_start_of_getElem?_lt startFound
      (State.getElem?_eq_some_of_peek?_eq_some firstFound) startBefore
  have orderedPath : start.startByte ≤ path.span.endByte :=
    Nat.le_trans startValid.2.1
      (Nat.le_trans (by simpa [startSpan] using startBeforeFirst)
        (by rw [firstStart]; exact pathReply.1.1.2.1))
  cases hidden with
  | none =>
      have finished := finishImport_validFor start path.span
        (.selected selection path none) afterHidden hiddenReply.2.1
        startValidAfter pathValidAfter.1 orderedPath startFoundAfter
        startSpan startBeforeAfter ⟨selectionValidAfter.1,
          selectionValidAfter.2, pathValidAfter, by simp⟩
      exact finished.of_file_eq afterHiddenFile
  | some clause =>
      have clauseResult := optionalHiding_some_components hiddenResult
      rcases hidingClause_startsAtCurrentTokenOnSuccess afterPath clause
          afterHidden clauseResult with ⟨marker, markerFound, clauseStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerFound
      have startBeforeClause :=
        pathReply.2.1.token_end_le_token_start_of_getElem?_lt
          startFoundAfterPath markerAt startBeforeAfterPath
      have clauseValidAtPath : HidingClause.ValidFor afterPath.file clause := by
        simpa only [Option.ValidFor] using hiddenReply.1
      have clauseValidAfter : HidingClause.ValidFor afterHidden.file clause := by
        simpa [hiddenReply.2.2] using clauseValidAtPath
      have startValidAtPath : start.ValidFor afterPath.file := by
        simpa [pathReply.2.2] using startValid
      have orderedClause : start.startByte ≤ clause.span.endByte :=
        Nat.le_trans startValidAtPath.2.1
          (Nat.le_trans (by simpa [startSpan] using startBeforeClause)
            (by rw [clauseStart]; exact clauseValidAtPath.1.2.1))
      have clausesValid : ∀ retained ∈ some clause,
          HidingClause.ValidFor afterHidden.file retained := by
        intro retained member
        have retainedEq : retained = clause := by
          have clauseEq : clause = retained := by simpa using member
          exact clauseEq.symm
        simpa [retainedEq] using clauseValidAfter
      have finished := finishImport_validFor start clause.span
        (.selected selection path (some clause)) afterHidden hiddenReply.2.1
        startValidAfter clauseValidAfter.1 orderedClause startFoundAfter
        startSpan startBeforeAfter ⟨selectionValidAfter.1,
          selectionValidAfter.2, pathValidAfter, clausesValid⟩
      exact finished.of_file_eq afterHiddenFile

private theorem plainImport_weakValidFor (start : SourceSpan) :
    (ImportInternals.plainImport start).ValidFor (fun _ _ => True) := by
  unfold ImportInternals.plainImport
  apply Parser.bind_validFor_of_value (modulePath_validFor .importDecl)
  intro path input inputValid pathValid
  exact finishImport_weakValidFor start path.span (.plain path)
    input inputValid pathValid.1

private theorem namespaceImport_weakValidFor (start : SourceSpan) :
    (ImportInternals.namespaceImport start).ValidFor (fun _ _ => True) := by
  unfold ImportInternals.namespaceImport
  apply Parser.bind_validFor (symbol_validFor .star .importDecl)
  intro star
  apply Parser.bind_validFor (keyword_validFor .asKw .importDecl)
  intro asMarker
  apply Parser.bind_validFor (identifier_validFor .importDecl)
  intro alias
  apply Parser.bind_validFor (contextual_validFor .from .importDecl)
  intro fromMarker
  apply Parser.bind_validFor_of_value (modulePath_validFor .importDecl)
  intro path input inputValid pathValid
  exact finishImport_weakValidFor start path.span (.namespace path alias)
    input inputValid pathValid.1

private theorem wildcardImport_weakValidFor (start : SourceSpan) :
    (ImportInternals.wildcardImport start).ValidFor (fun _ _ => True) := by
  unfold ImportInternals.wildcardImport
  apply Parser.bind_validFor (symbol_validFor .star .importDecl)
  intro star
  apply Parser.bind_validFor (contextual_validFor .from .importDecl)
  intro fromMarker
  apply Parser.bind_validFor_of_value (modulePath_validFor .importDecl)
  intro path input inputValid pathValid
  exact optionalHidingFinish_weakValidFor start path
    (fun hidden => .wildcard path hidden) input inputValid pathValid

/-- Plain import payloads preserve their module path and complete cover. -/
theorem plainImport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ImportInternals.plainImport start input).ValidFor input
      ImportDecl.ValidFor := by
  have pathReply := modulePath_validFor .importDecl input inputValid
  unfold ImportInternals.plainImport
  cases pathResult : modulePath .importDecl input with
  | invariant error =>
      simp only [bind, pathResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [pathResult] at pathReply
      simpa only [bind, pathResult, Reply.ValidFor] using pathReply
  | ok path afterPath =>
      rw [pathResult] at pathReply
      have pathValidAfter : ModulePath.ValidFor afterPath.file path := by
        simpa [pathReply.2.2] using pathReply.1
      simpa only [bind, pathResult] using
        finishAfterModulePath_validFor start input inputValid startValid
          startFound startSpan startBefore pathResult (.plain path)
          pathValidAfter

/-- Namespace import payloads retain their alias, path, and complete cover. -/
theorem namespaceImport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ImportInternals.namespaceImport start input).ValidFor input
      ImportDecl.ValidFor := by
  have weak := namespaceImport_weakValidFor start input inputValid
  cases parsed : ImportInternals.namespaceImport start input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold ImportInternals.namespaceImport at stages
      rcases importBind_ok_components stages with
        ⟨star, afterStar, starResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨asMarker, afterAs, asResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨alias, afterAlias, aliasResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨fromMarker, afterFrom, fromResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨path, afterPath, pathResult, finished⟩
      have starValid := symbol_validFor .star .importDecl input inputValid
      rw [starResult] at starValid
      have asValid := keyword_validFor .asKw .importDecl
        afterStar starValid.2.1
      rw [asResult] at asValid
      have aliasValid := identifier_validFor .importDecl
        afterAs asValid.2.1
      rw [aliasResult] at aliasValid
      have fromValid := contextual_validFor .from .importDecl
        afterAlias aliasValid.2.1
      rw [fromResult] at fromValid
      have pathValid := modulePath_validFor .importDecl
        afterFrom fromValid.2.1
      rw [pathResult] at pathValid
      have afterFromFile : afterFrom.file = input.file :=
        fromValid.2.2.trans (aliasValid.2.2.trans
          (asValid.2.2.trans starValid.2.2))
      have afterFromTokens : afterFrom.tokens = input.tokens :=
        (contextual_preservesTokensOnSuccess .from .importDecl
          afterAlias fromMarker afterFrom fromResult).trans
          ((identifier_preservesTokensOnSuccess .importDecl
            afterAs alias afterAlias aliasResult).trans
            ((keyword_preservesTokensOnSuccess .asKw .importDecl
              afterStar asMarker afterAs asResult).trans
              (symbol_preservesTokensOnSuccess .star .importDecl
                input star afterStar starResult)))
      have startFoundAfterFrom :
          afterFrom.tokens[startIndex]? = some startToken := by
        rw [afterFromTokens]
        exact startFound
      have startBeforeAfterFrom : startIndex < afterFrom.cursor := by
        apply Nat.lt_of_lt_of_le startBefore
        exact Nat.le_trans
          (symbol_cursorMonotoneOnSuccess .star .importDecl
            input star afterStar starResult)
          (Nat.le_trans
            (keyword_cursorMonotoneOnSuccess .asKw .importDecl
              afterStar asMarker afterAs asResult)
            (Nat.le_trans
              (identifier_cursorMonotoneOnSuccess .importDecl
                afterAs alias afterAlias aliasResult)
              (contextual_cursorMonotoneOnSuccess .from .importDecl
                afterAlias fromMarker afterFrom fromResult)))
      have startValidAfterFrom : start.ValidFor afterFrom.file := by
        simpa [afterFromFile] using startValid
      have pathValidAfter : ModulePath.ValidFor afterPath.file path := by
        simpa [pathValid.2.2] using pathValid.1
      have aliasValidAfter : alias.span.ValidFor afterPath.file := by
        have aliasSpanValid : alias.span.ValidFor afterAs.file := by
          simpa only [Located.ValidFor] using aliasValid.1
        simpa [pathValid.2.2, fromValid.2.2, aliasValid.2.2] using
          aliasSpanValid
      have strong := finishAfterModulePath_validFor start afterFrom
        fromValid.2.1 startValidAfterFrom startFoundAfterFrom startSpan
        startBeforeAfterFrom pathResult (.namespace path alias)
        ⟨pathValidAfter, aliasValidAfter⟩
      rw [finished] at strong
      exact strong.of_file_eq afterFromFile

/-- Wildcard imports retain their path, optional hiding clause, and cover. -/
theorem wildcardImport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ImportInternals.wildcardImport start input).ValidFor input
      ImportDecl.ValidFor := by
  have weak := wildcardImport_weakValidFor start input inputValid
  cases parsed : ImportInternals.wildcardImport start input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold ImportInternals.wildcardImport at stages
      rcases importBind_ok_components stages with
        ⟨star, afterStar, starResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨fromMarker, afterFrom, fromResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨path, afterPath, pathResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨hidden, afterHidden, hiddenResult, finished⟩
      have starValid := symbol_validFor .star .importDecl input inputValid
      rw [starResult] at starValid
      have fromValid := contextual_validFor .from .importDecl
        afterStar starValid.2.1
      rw [fromResult] at fromValid
      have afterFromFile : afterFrom.file = input.file :=
        fromValid.2.2.trans starValid.2.2
      have afterFromTokens : afterFrom.tokens = input.tokens :=
        (contextual_preservesTokensOnSuccess .from .importDecl
          afterStar fromMarker afterFrom fromResult).trans
          (symbol_preservesTokensOnSuccess .star .importDecl
            input star afterStar starResult)
      have startFoundAfterFrom :
          afterFrom.tokens[startIndex]? = some startToken := by
        rw [afterFromTokens]
        exact startFound
      have startBeforeAfterFrom : startIndex < afterFrom.cursor := by
        apply Nat.lt_of_lt_of_le startBefore
        exact Nat.le_trans
          (symbol_cursorMonotoneOnSuccess .star .importDecl
            input star afterStar starResult)
          (contextual_cursorMonotoneOnSuccess .from .importDecl
            afterStar fromMarker afterFrom fromResult)
      have startValidAfterFrom : start.ValidFor afterFrom.file := by
        simpa [afterFromFile] using startValid
      cases hidden with
      | none =>
          have strong := finishWildcardAfterModulePath_validFor start
            afterFrom fromValid.2.1 startValidAfterFrom startFoundAfterFrom
            startSpan startBeforeAfterFrom pathResult hiddenResult
          have finishedNone : ImportInternals.finish start path.span
              (.wildcard path none) afterHidden = .ok result final := by
            simpa using finished
          rw [finishedNone] at strong
          exact strong.of_file_eq afterFromFile
      | some clause =>
          have strong := finishWildcardAfterModulePath_validFor start
            afterFrom fromValid.2.1 startValidAfterFrom startFoundAfterFrom
            startSpan startBeforeAfterFrom pathResult hiddenResult
          have finishedSome : ImportInternals.finish start clause.span
              (.wildcard path (some clause)) afterHidden =
                .ok result final := by
            simpa using finished
          rw [finishedSome] at strong
          exact strong.of_file_eq afterFromFile

/-- Import terminators preserve every ordinary token window. -/
theorem importTerminator_preservesTokenWindow (lastSpan : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.terminator lastSpan) := by
  intro input
  unfold ImportInternals.terminator
  split
  · have shape := symbol_preservesTokenWindow .semicolon .importDecl input
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [semicolonResult] at shape
        exact shape
    | ok token next =>
        rw [semicolonResult] at shape
        exact shape
  · split
    · exact ⟨rfl, rfl⟩
    · exact rejectAt_preservesTokenWindow input _ _

theorem importTerminator_preservesTokensOnSuccess (lastSpan : SourceSpan) :
    Parser.PreservesTokensOnSuccess
      (ImportInternals.terminator lastSpan) :=
  (importTerminator_preservesTokenWindow lastSpan).preservesTokensOnSuccess

/-- Import terminators either consume `;` or leave the cursor in place. -/
theorem importTerminator_cursorMonotoneOnSuccess (lastSpan : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.terminator lastSpan) := by
  intro input endSpan next parsed
  unfold ImportInternals.terminator at parsed
  split at parsed
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at parsed
    | reject failure rejected => simp [semicolonResult] at parsed
    | ok token afterToken =>
        simp only [semicolonResult] at parsed
        cases parsed
        exact symbol_cursorMonotoneOnSuccess .semicolon .importDecl
          input token next semicolonResult
  · split at parsed
    · cases parsed
      exact Nat.le_refl _
    · unfold rejectAt at parsed
      contradiction

/-- Finishing an import preserves every ordinary token window. -/
theorem finishImport_preservesTokenWindow (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.PreservesTokenWindow
      (ImportInternals.finish start last value) := by
  unfold ImportInternals.finish
  apply Parser.bind_preservesTokenWindow
    (importTerminator_preservesTokenWindow last)
  intro endSpan
  exact Parser.pure_preservesTokenWindow _

theorem finishImport_preservesTokensOnSuccess (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.PreservesTokensOnSuccess
      (ImportInternals.finish start last value) :=
  (finishImport_preservesTokenWindow start last value).preservesTokensOnSuccess

/-- Finishing an import never rewinds the parser cursor. -/
theorem finishImport_cursorMonotoneOnSuccess (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.finish start last value) := by
  unfold ImportInternals.finish
  apply Parser.bind_cursorMonotoneOnSuccess
    (importTerminator_cursorMonotoneOnSuccess last)
  intro endSpan
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem finishImport_keepsStartByte (start last : SourceSpan)
    (value : ImportDeclValue) {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.finish start last value input =
      .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.finish at parsed
  rcases importBind_ok_components parsed with
    ⟨endSpan, afterEnd, _endResult, finished⟩
  cases finished
  rfl

theorem plainImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.plainImport start) := by
  unfold ImportInternals.plainImport
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  exact finishImport_preservesTokenWindow start path.span (.plain path)

theorem plainImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.plainImport start) := by
  unfold ImportInternals.plainImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  exact finishImport_cursorMonotoneOnSuccess start path.span (.plain path)

theorem namespaceImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.namespaceImport start) := by
  unfold ImportInternals.namespaceImport
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .star .importDecl)
  intro star
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .asKw .importDecl)
  intro asMarker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .importDecl)
  intro alias
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  exact finishImport_preservesTokenWindow start path.span
    (.namespace path alias)

theorem namespaceImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.namespaceImport start) := by
  unfold ImportInternals.namespaceImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .asKw .importDecl)
  intro asMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .importDecl)
  intro alias
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  exact finishImport_cursorMonotoneOnSuccess start path.span
    (.namespace path alias)

theorem wildcardImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.wildcardImport start) := by
  unfold ImportInternals.wildcardImport
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .star .importDecl)
  intro star
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  apply Parser.bind_preservesTokenWindow optionalHiding_preservesTokenWindow
  intro hidden
  exact finishImport_preservesTokenWindow start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

theorem wildcardImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.wildcardImport start) := by
  unfold ImportInternals.wildcardImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalHiding_cursorMonotoneOnSuccess
  intro hidden
  exact finishImport_cursorMonotoneOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

theorem plainImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.plainImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.plainImport at parsed
  rcases importBind_ok_components parsed with
    ⟨path, afterPath, _pathResult, finished⟩
  exact finishImport_keepsStartByte start path.span (.plain path) finished

theorem namespaceImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.namespaceImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.namespaceImport at parsed
  rcases importBind_ok_components parsed with
    ⟨star, afterStar, _starResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨asMarker, afterAs, _asResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨alias, afterAlias, _aliasResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, finished⟩
  exact finishImport_keepsStartByte start path.span
    (.namespace path alias) finished

theorem wildcardImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.wildcardImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.wildcardImport at parsed
  rcases importBind_ok_components parsed with
    ⟨star, afterStar, _starResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨hidden, afterHidden, _hiddenResult, finished⟩
  cases hidden with
  | none =>
      exact finishImport_keepsStartByte start path.span
        (.wildcard path none) (by simpa using finished)
  | some clause =>
      exact finishImport_keepsStartByte start clause.span
        (.wildcard path (some clause)) (by simpa using finished)

private theorem selectedAlias_some_components {input next : State}
    {name : Identifier}
    (parsed : ImportInternals.selectedAlias input = .ok (some name) next) :
    ∃ marker afterMarker,
      keyword .asKw .importDecl input = .ok marker afterMarker ∧
        identifier .importDecl afterMarker = .ok name next := by
  unfold ImportInternals.selectedAlias at parsed
  rcases importBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, rest⟩
  unfold getState at observedResult
  cases observedResult
  split at rest
  · rcases importBind_ok_components rest with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases importBind_ok_components rest with
      ⟨parsedName, afterName, nameResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, markerResult, nameResult⟩
  · cases rest

/-- Selected imports retain their selector, alias, and covering range. -/
theorem selectedImport_validFor :
    selectedImport.ValidFor SelectedImport.ValidFor := by
  have weak : selectedImport.ValidFor (fun _ _ => True) := by
    unfold selectedImport
    apply Parser.bind_validFor (selectorName_validFor .importDecl)
    intro source
    apply Parser.bind_validFor selectedAlias_validFor
    intro alias
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : selectedImport input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold selectedImport at stages
      rcases importBind_ok_components stages with
        ⟨source, afterSource, sourceResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨alias, afterAlias, aliasResult, finished⟩
      have sourceValid := selectorName_validFor .importDecl input inputValid
      rw [sourceResult] at sourceValid
      have aliasValid := selectedAlias_validFor afterSource sourceValid.2.1
      rw [aliasResult] at aliasValid
      cases alias with
      | none =>
          cases finished
          exact ⟨⟨sourceValid.1.1, sourceValid.1, by simp⟩,
            weakResult.2.1, weakResult.2.2⟩
      | some name =>
          rcases selectedAlias_some_components aliasResult with
            ⟨marker, afterMarker, markerResult, nameResult⟩
          rcases selectorName_startsAtCurrentTokenOnSuccess .importDecl
              input source afterSource sourceResult with
            ⟨firstToken, firstFound, sourceStart⟩
          rcases identifier_ok_state_shape .importDecl nameResult with
            ⟨nameToken, nameFound, nameSpan, _nameTokens, _nameCursor⟩
          have firstAt :=
            State.getElem?_eq_some_of_peek?_eq_some firstFound
          have nameAt : input.tokens[afterMarker.cursor]? = some nameToken := by
            have foundAt :=
              State.getElem?_eq_some_of_peek?_eq_some nameFound
            have sourceTokens := selectorName_preservesTokensOnSuccess
              .importDecl input source afterSource sourceResult
            have markerTokens := keyword_preservesTokensOnSuccess .asKw
              .importDecl afterSource marker afterMarker markerResult
            simpa [markerTokens, sourceTokens] using foundAt
          have firstBeforeName :
              firstToken.span.endByte ≤ nameToken.span.startByte := by
            apply inputValid.token_end_le_token_start_of_getElem?_lt
              firstAt nameAt
            have sourceProgress :=
              selectorName_cursor_lt_onSuccess .importDecl sourceResult
            have markerShape := acceptToken_ok_state_shape
              (.keyword .asKw) .importDecl (· == .keyword .asKw) markerResult
            exact Nat.lt_trans sourceProgress (by simp [markerShape.2])
          have sourceSpanValid : source.span.ValidFor input.file :=
            sourceValid.1.1
          have nameSpanValid : name.span.ValidFor input.file := by
            have retained : Located.ValidFor afterSource.file name := by
              simpa only [Option.ValidFor] using aliasValid.1
            simpa [Located.ValidFor, sourceValid.2.2] using retained
          have firstSpanValid := inputValid.peek?_span_validFor firstFound
          have ordered : source.span.startByte ≤ name.span.endByte := by
            calc
              source.span.startByte = firstToken.span.startByte :=
                sourceStart.symm
              _ ≤ firstToken.span.endByte := firstSpanValid.2.1
              _ ≤ nameToken.span.startByte := firstBeforeName
              _ ≤ name.span.endByte := by
                rw [nameSpan]
                exact nameSpanValid.2.1
          have coverValid := SourceSpan.cover_validFor sourceSpanValid
            nameSpanValid ordered
          cases finished
          exact ⟨⟨coverValid, sourceValid.1, by simpa using nameSpanValid⟩,
            weakResult.2.1, weakResult.2.2⟩

/-- Selected imports preserve every ordinary token window. -/
theorem selectedImport_preservesTokenWindow :
    Parser.PreservesTokenWindow selectedImport := by
  unfold selectedImport
  apply Parser.bind_preservesTokenWindow
    (selectorName_preservesTokenWindow .importDecl)
  intro source
  apply Parser.bind_preservesTokenWindow selectedAlias_preservesTokenWindow
  intro alias
  exact Parser.pure_preservesTokenWindow _

/-- Selected imports preserve the immutable token carrier on success. -/
theorem selectedImport_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess selectedImport :=
  selectedImport_preservesTokenWindow.preservesTokensOnSuccess

/-- Selected imports never rewind the parser cursor. -/
theorem selectedImport_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess selectedImport := by
  unfold selectedImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (selectorName_cursorMonotoneOnSuccess .importDecl)
  intro source
  apply Parser.bind_cursorMonotoneOnSuccess
    selectedAlias_cursorMonotoneOnSuccess
  intro alias
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A selected import starts at its retained selector token. -/
theorem selectedImport_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess selectedImport (·.span) := by
  unfold selectedImport
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (selectorName_startsAtCurrentTokenOnSuccess .importDecl)
  intro source input selection final parsed
  rcases importBind_ok_components parsed with
    ⟨alias, afterAlias, _aliasResult, finished⟩
  cases alias <;> cases finished <;> rfl

private theorem requireSelected_validFor
    (values : DelimitedList SelectedImport) :
    (ImportInternals.requireSelected values).ValidFor
      (fun _ _ => True) := by
  intro input inputValid
  unfold ImportInternals.requireSelected
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨trivial, inputValid, rfl⟩

private theorem requireSelected_preservesTokenWindow
    (values : DelimitedList SelectedImport) :
    Parser.PreservesTokenWindow
      (ImportInternals.requireSelected values) := by
  intro input
  unfold ImportInternals.requireSelected
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

private theorem requireSelected_cursorMonotoneOnSuccess
    (values : DelimitedList SelectedImport) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.requireSelected values) := by
  intro input selection next result
  unfold ImportInternals.requireSelected at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

/-- A nonempty selected-import list retains delimiters and every item. -/
theorem selectedImports_validFor :
    ImportInternals.selectedImports.ValidFor
      (NonemptyDelimitedList.ValidFor SelectedImport.ValidFor) := by
  have weak : ImportInternals.selectedImports.ValidFor
      (fun _ _ => True) := by
    unfold ImportInternals.selectedImports
    apply Parser.bind_validFor (delimited_validFor SelectedImport.ValidFor
      .leftBrace .rightBrace false selectedImport .importDecl .topLevel
      selectedImport_validFor selectedImport_preservesTokensOnSuccess)
    intro values
    exact requireSelected_validFor values
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : ImportInternals.selectedImports input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold ImportInternals.selectedImports at stages
      rcases importBind_ok_components stages with
        ⟨values, afterValues, valuesResult, selectionResult⟩
      have valuesValid := delimited_validFor SelectedImport.ValidFor
        .leftBrace .rightBrace false selectedImport .importDecl .topLevel
        selectedImport_validFor selectedImport_preservesTokensOnSuccess
        input inputValid
      rw [valuesResult] at valuesValid
      unfold ImportInternals.requireSelected at selectionResult
      cases elements : values.elements with
      | nil =>
          rw [elements] at selectionResult
          contradiction
      | cons head tail =>
          rw [elements] at selectionResult
          cases selectionResult
          exact ⟨⟨valuesValid.1.1, by
              intro item member
              exact valuesValid.1.2 item (by
                simpa [NonemptyList.toList, elements] using member)⟩,
            weakResult.2.1, weakResult.2.2⟩

/-- Selected-import lists preserve every ordinary token window. -/
theorem selectedImports_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.selectedImports := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel
      selectedImport_preservesTokenWindow)
  intro values
  exact requireSelected_preservesTokenWindow values

theorem selectedImports_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.selectedImports :=
  selectedImports_preservesTokenWindow.preservesTokensOnSuccess

/-- Selected-import lists never rewind the parser cursor. -/
theorem selectedImports_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.selectedImports := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel)
  intro values
  exact requireSelected_cursorMonotoneOnSuccess values

/-- A selected-import list starts at its opening brace. -/
theorem selectedImports_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ImportInternals.selectedImports (·.span) := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel)
  intro values input selection final parsed
  unfold ImportInternals.requireSelected at parsed
  cases elements : values.elements with
  | nil =>
      rw [elements] at parsed
      contradiction
  | cons head tail =>
      rw [elements] at parsed
      cases parsed
      rfl

private theorem selectiveImport_weakValidFor (start : SourceSpan) :
    (ImportInternals.selectiveImport start).ValidFor (fun _ _ => True) := by
  unfold ImportInternals.selectiveImport
  apply Parser.bind_validFor selectedImports_validFor
  intro selection
  apply Parser.bind_validFor (contextual_validFor .from .importDecl)
  intro fromMarker
  apply Parser.bind_validFor_of_value (modulePath_validFor .importDecl)
  intro path input inputValid pathValid
  exact optionalHidingFinish_weakValidFor start path
    (fun hidden => .selected selection path hidden)
    input inputValid pathValid

/-- Selected imports retain every item, path, hiding clause, and cover. -/
theorem selectiveImport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ImportInternals.selectiveImport start input).ValidFor input
      ImportDecl.ValidFor := by
  have weak := selectiveImport_weakValidFor start input inputValid
  cases parsed : ImportInternals.selectiveImport start input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold ImportInternals.selectiveImport at stages
      rcases importBind_ok_components stages with
        ⟨selection, afterSelection, selectionResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨fromMarker, afterFrom, fromResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨path, afterPath, pathResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨hidden, afterHidden, hiddenResult, finished⟩
      have selectionReply := selectedImports_validFor input inputValid
      rw [selectionResult] at selectionReply
      have fromValid := contextual_validFor .from .importDecl
        afterSelection selectionReply.2.1
      rw [fromResult] at fromValid
      have afterFromFile : afterFrom.file = input.file :=
        fromValid.2.2.trans selectionReply.2.2
      have selectionValidAfter :
          NonemptyDelimitedList.ValidFor SelectedImport.ValidFor
            afterFrom.file selection := by
        simpa [afterFromFile] using selectionReply.1
      have afterFromTokens : afterFrom.tokens = input.tokens :=
        (contextual_preservesTokensOnSuccess .from .importDecl
          afterSelection fromMarker afterFrom fromResult).trans
          (selectedImports_preservesTokensOnSuccess
            input selection afterSelection selectionResult)
      have startFoundAfterFrom :
          afterFrom.tokens[startIndex]? = some startToken := by
        rw [afterFromTokens]
        exact startFound
      have startBeforeAfterFrom : startIndex < afterFrom.cursor := by
        apply Nat.lt_of_lt_of_le startBefore
        exact Nat.le_trans
          (selectedImports_cursorMonotoneOnSuccess
            input selection afterSelection selectionResult)
          (contextual_cursorMonotoneOnSuccess .from .importDecl
            afterSelection fromMarker afterFrom fromResult)
      have startValidAfterFrom : start.ValidFor afterFrom.file := by
        simpa [afterFromFile] using startValid
      cases hidden with
      | none =>
          have strong := finishSelectedAfterModulePath_validFor start
            selection afterFrom fromValid.2.1 selectionValidAfter
            startValidAfterFrom startFoundAfterFrom startSpan
            startBeforeAfterFrom pathResult hiddenResult
          have finishedNone : ImportInternals.finish start path.span
              (.selected selection path none) afterHidden =
                .ok result final := by
            simpa using finished
          rw [finishedNone] at strong
          exact strong.of_file_eq afterFromFile
      | some clause =>
          have strong := finishSelectedAfterModulePath_validFor start
            selection afterFrom fromValid.2.1 selectionValidAfter
            startValidAfterFrom startFoundAfterFrom startSpan
            startBeforeAfterFrom pathResult hiddenResult
          have finishedSome : ImportInternals.finish start clause.span
              (.selected selection path (some clause)) afterHidden =
                .ok result final := by
            simpa using finished
          rw [finishedSome] at strong
          exact strong.of_file_eq afterFromFile

private theorem importDecl_weakValidFor :
    importDecl.ValidFor (fun _ _ => True) := by
  unfold importDecl
  apply Parser.bind_validFor (keyword_validFor .importKw .importDecl)
  intro importKeyword
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_weakValidFor importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_weakValidFor importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_weakValidFor importKeyword.span
    · simp only [selected]
      exact plainImport_weakValidFor importKeyword.span

/-- Complete import parsing preserves every retained source range. -/
theorem importDecl_validFor : importDecl.ValidFor ImportDecl.ValidFor := by
  intro input inputValid
  have weak := importDecl_weakValidFor input inputValid
  cases parsed : importDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold importDecl at stages
      rcases importBind_ok_components stages with
        ⟨importKeyword, afterKeyword, keywordResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨observed, afterObserved, observedResult, branchResult⟩
      unfold getState at observedResult
      cases observedResult
      have keywordReply := keyword_validFor .importKw .importDecl
        input inputValid
      rw [keywordResult] at keywordReply
      have keywordShape := acceptToken_ok_state_shape
        (.keyword .importKw) .importDecl (· == .keyword .importKw)
        keywordResult
      have startFoundAfter :
          afterKeyword.tokens[input.cursor]? = some importKeyword := by
        rw [keywordShape.2]
        exact State.getElem?_eq_some_of_peek?_eq_some keywordShape.1
      have startBeforeAfter : input.cursor < afterKeyword.cursor := by
        rw [keywordShape.2]
        simp
      have startValidAfter :
          importKeyword.span.ValidFor afterKeyword.file := by
        have validAtInput : importKeyword.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using keywordReply.1
        simpa [keywordReply.2.2] using validAtInput
      split at branchResult
      · split at branchResult
        · have strong := namespaceImport_validFor importKeyword.span
            afterKeyword keywordReply.2.1 startValidAfter startFoundAfter
            rfl startBeforeAfter
          rw [branchResult] at strong
          exact strong.of_file_eq keywordReply.2.2
        · have strong := wildcardImport_validFor importKeyword.span
            afterKeyword keywordReply.2.1 startValidAfter startFoundAfter
            rfl startBeforeAfter
          rw [branchResult] at strong
          exact strong.of_file_eq keywordReply.2.2
      · split at branchResult
        · have strong := selectiveImport_validFor importKeyword.span
            afterKeyword keywordReply.2.1 startValidAfter startFoundAfter
            rfl startBeforeAfter
          rw [branchResult] at strong
          exact strong.of_file_eq keywordReply.2.2
        · have strong := plainImport_validFor importKeyword.span
            afterKeyword keywordReply.2.1 startValidAfter startFoundAfter
            rfl startBeforeAfter
          rw [branchResult] at strong
          exact strong.of_file_eq keywordReply.2.2

theorem selectiveImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.selectiveImport start) := by
  unfold ImportInternals.selectiveImport
  apply Parser.bind_preservesTokenWindow selectedImports_preservesTokenWindow
  intro selection
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  apply Parser.bind_preservesTokenWindow optionalHiding_preservesTokenWindow
  intro hidden
  exact finishImport_preservesTokenWindow start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

theorem selectiveImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.selectiveImport start) := by
  unfold ImportInternals.selectiveImport
  apply Parser.bind_cursorMonotoneOnSuccess
    selectedImports_cursorMonotoneOnSuccess
  intro selection
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalHiding_cursorMonotoneOnSuccess
  intro hidden
  exact finishImport_cursorMonotoneOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

theorem selectiveImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.selectiveImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.selectiveImport at parsed
  rcases importBind_ok_components parsed with
    ⟨selection, afterSelection, _selectionResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨hidden, afterHidden, _hiddenResult, finished⟩
  cases hidden with
  | none =>
      exact finishImport_keepsStartByte start path.span
        (.selected selection path none) (by simpa using finished)
  | some clause =>
      exact finishImport_keepsStartByte start clause.span
        (.selected selection path (some clause)) (by simpa using finished)

/-- Complete import parsing preserves every ordinary token window. -/
theorem importDecl_preservesTokenWindow :
    Parser.PreservesTokenWindow importDecl := by
  unfold importDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .importKw .importDecl)
  intro importKeyword
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_preservesTokenWindow importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_preservesTokenWindow importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_preservesTokenWindow importKeyword.span
    · simp only [selected]
      exact plainImport_preservesTokenWindow importKeyword.span

theorem importDecl_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess importDecl :=
  importDecl_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete import parsing never rewinds the parser cursor. -/
theorem importDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess importDecl := by
  unfold importDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .importKw .importDecl)
  intro importKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_cursorMonotoneOnSuccess importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [selected]
      exact plainImport_cursorMonotoneOnSuccess importKeyword.span

/-- Complete import parsing starts at the leading `import` token. -/
theorem importDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess importDecl (·.span) := by
  unfold importDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .importKw) .importDecl (· == .keyword .importKw))
  intro importKeyword input result final parsed
  rcases importBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · split at branchResult
    · exact namespaceImport_keepsStartByte importKeyword.span branchResult
    · exact wildcardImport_keepsStartByte importKeyword.span branchResult
  · split at branchResult
    · exact selectiveImport_keepsStartByte importKeyword.span branchResult
    · exact plainImport_keepsStartByte importKeyword.span branchResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainImportSoundnessProperties
/-! Success soundness of diagnostic-free canonical plain imports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful monadic import stage exposes both successful component replies. -/
theorem importBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/--
A successful import terminator with no accumulated parse diagnostics consumed
an exact semicolon.  This common boundary excludes the missing-semicolon
recovery, because that branch always prepends `trailingSemicolonRequired` to
the output diagnostic accumulator.
-/
theorem importTerminator_success_sound_of_diagnosticFree
    (lastSpan : SourceSpan) {input next : State} {endSpan : SourceSpan}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.terminator lastSpan input = .ok endSpan next) :
    ∃ semicolon : Token,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor {
          span := semicolon.span
          value := .symbol .semicolon
        } ∧
      next = { input with cursor := input.cursor + 1 } ∧
      endSpan = semicolon.span := by
  unfold ImportInternals.terminator at result
  split at result
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        have sound := symbol_ok_tokenAt .semicolon .importDecl semicolonResult
        simp only [semicolonResult] at result
        cases result
        exact ⟨semicolon, sound.1, sound.2, rfl⟩
  · split at result
    · cases result
      simp [State.emit] at diagnosticFree
    · unfold rejectAt at result
      contradiction

/--
Diagnostic-free helper success consumes a module path and an exact semicolon.
The premise excludes the missing-semicolon recovery accepted by `plainImport`.
-/
theorem plainImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    DeclarativeGrammar.PlainImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  rcases importBind_success_components result with
    ⟨path, afterPath, pathResult, finishResult⟩
  have pathSound := modulePath_success_sound .importDecl pathResult
  unfold ImportInternals.finish at finishResult
  rcases importBind_success_components finishResult with
    ⟨endSpan, afterEnd, endResult, finished⟩
  cases finished
  rcases importTerminator_success_sound_of_diagnosticFree path.span
      diagnosticFree endResult with
    ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
  unfold DeclarativeGrammar.PlainImportTailParses
  refine ⟨path, afterPath.declarativeRemainder, semicolon.span, pathSound,
    semicolonToken, ?_, ?_⟩
  · rw [afterEndEq]
    rfl
  · rw [endSpanEq]

/-- Successful import finishing retains its supplied payload constructor. -/
theorem finishImport_success_value (start last : SourceSpan)
    (value : ImportDeclValue) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.finish start last value input =
      .ok declaration next) :
    declaration.value = value := by
  unfold ImportInternals.finish at result
  rcases importBind_success_components result with
    ⟨endSpan, afterEnd, _endResult, finished⟩
  cases finished
  rfl

/-- Plain-helper success produces exactly the plain payload constructor. -/
theorem plainImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    ∃ path, declaration.value = .plain path := by
  unfold ImportInternals.plainImport at result
  rcases importBind_success_components result with
    ⟨path, afterPath, _pathResult, finished⟩
  exact ⟨path,
    finishImport_success_value start path.span (.plain path) finished⟩

/-- Namespace-helper success produces exactly the namespace payload constructor. -/
theorem namespaceImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    ∃ path alias, declaration.value = .namespace path alias := by
  unfold ImportInternals.namespaceImport at result
  rcases importBind_success_components result with
    ⟨_star, afterStar, _, rest⟩
  rcases importBind_success_components rest with ⟨_as, afterAs, _, rest⟩
  rcases importBind_success_components rest with
    ⟨alias, afterAlias, _, rest⟩
  rcases importBind_success_components rest with
    ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with
    ⟨path, afterPath, _, finished⟩
  exact ⟨path, alias,
    finishImport_success_value start path.span (.namespace path alias) finished⟩

/-- Wildcard-helper success produces exactly the wildcard payload constructor. -/
theorem wildcardImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    ∃ path hidden, declaration.value = .wildcard path hidden := by
  unfold ImportInternals.wildcardImport at result
  rcases importBind_success_components result with
    ⟨_star, afterStar, _, rest⟩
  rcases importBind_success_components rest with ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with ⟨path, afterPath, _, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, _, finished⟩
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.wildcard path none) afterHidden = .ok declaration next := by
        simpa using finished
      exact ⟨path, none,
        finishImport_success_value start path.span (.wildcard path none)
          finishedNone⟩
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.wildcard path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨path, some clause,
        finishImport_success_value start clause.span
          (.wildcard path (some clause)) finishedSome⟩

/-- Selective-helper success produces exactly the selected payload constructor. -/
theorem selectiveImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    ∃ selection path hidden,
      declaration.value = .selected selection path hidden := by
  unfold ImportInternals.selectiveImport at result
  rcases importBind_success_components result with
    ⟨selection, afterSelection, _, rest⟩
  rcases importBind_success_components rest with ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with ⟨path, afterPath, _, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, _, finished⟩
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.selected selection path none) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨selection, path, none,
        finishImport_success_value start path.span
          (.selected selection path none) finishedNone⟩
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.selected selection path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨selection, path, some clause,
        finishImport_success_value start clause.span
          (.selected selection path (some clause)) finishedSome⟩

/--
An AST-plain import success with no accumulated parse diagnostics follows the
exact plain-import grammar.  Requiring an empty output diagnostic accumulator
rules out the parser's accepted missing-semicolon recovery, which always emits
`trailingSemicolonRequired`; the AST-shape premise makes this theorem stable
under changes to the dispatcher's token lookahead implementation.
-/
theorem importDecl_plain_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.PlainImportDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  unfold importDecl at result
  rcases importBind_success_components result with
    ⟨importKeyword, afterKeyword, keywordResult, rest⟩
  have keywordSound := keyword_ok_tokenAt .importKw .importDecl keywordResult
  rcases importBind_success_components rest with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · split at branchResult
    · rcases namespaceImport_success_value importKeyword.span branchResult with
        ⟨path, alias, valueEq⟩
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
    · rcases wildcardImport_success_value importKeyword.span branchResult with
        ⟨path, hidden, valueEq⟩
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
  · split at branchResult
    · rcases selectiveImport_success_value importKeyword.span branchResult with
        ⟨selection, path, hidden, valueEq⟩
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
    · have tailGrammar := plainImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.PlainImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar

/-- Plain grammar soundness composes with source-provenance validity. -/
theorem importDecl_plain_success_sound_and_validFor {input next : State}
    {declaration : ImportDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.PlainImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_plain_success_sound diagnosticFree plainShape result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportSoundnessProperties
/-! Success soundness of selected import names and aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parsing is maximal and follows the exact token grammar. -/
theorem selectedAlias_success_sound {input next : State}
    {alias : Option Identifier}
    (result : ImportInternals.selectedAlias input = .ok alias next) :
    DeclarativeGrammar.SelectedAliasParses input.declarativeRemainder alias
      next.declarativeRemainder := by
  unfold ImportInternals.selectedAlias at result
  simp only [getState, bind] at result
  split at result
  next present =>
    rcases importBind_success_components result with
      ⟨asToken, afterAs, asResult, rest⟩
    rcases importBind_success_components rest with
      ⟨name, afterName, nameResult, finished⟩
    cases finished
    have asSound := keyword_ok_tokenAt .asKw .importDecl asResult
    have nameSound := identifier_ok_tokenAt .importDecl nameResult
    apply DeclarativeGrammar.SelectedAliasParses.present asToken.span asSound.1
      (by simpa only [asSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using nameSound.1)
    · simp only [State.declarativeRemainder, nameSound.2.1, asSound.2]
    · simp only [State.declarativeRemainder, nameSound.2.2.1, asSound.2]
    · simp only [State.declarativeRemainder, nameSound.2.2.2, asSound.2,
        Nat.add_assoc]
  next absent =>
    simp only [pure] at result
    cases result
    have absentFalse : isKeyword input .asKw = false := by
      cases found : isKeyword input .asKw <;> simp_all
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false .asKw
      absentFalse)

/-- Alias grammar soundness composes with source-provenance validity. -/
theorem selectedAlias_success_sound_and_validFor {input next : State}
    {alias : Option Identifier} (inputValid : input.ValidFor)
    (result : ImportInternals.selectedAlias input = .ok alias next) :
    DeclarativeGrammar.SelectedAliasParses input.declarativeRemainder alias
        next.declarativeRemainder ∧
      Option.ValidFor Located.ValidFor input.file alias := by
  refine ⟨selectedAlias_success_sound result, ?_⟩
  have valid := selectedAlias_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Every selected import item follows the selector-and-alias grammar. -/
theorem selectedImport_success_sound {input next : State}
    {selection : SelectedImport}
    (result : selectedImport input = .ok selection next) :
    DeclarativeGrammar.SelectedImportParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold selectedImport at result
  rcases importBind_success_components result with
    ⟨source, afterSource, sourceResult, rest⟩
  rcases importBind_success_components rest with
    ⟨alias, afterAlias, aliasResult, finished⟩
  cases finished
  refine ⟨afterSource.declarativeRemainder,
    selectorName_success_sound .importDecl sourceResult,
    selectedAlias_success_sound aliasResult, ?_⟩
  cases alias <;> rfl

/-- Selected-import grammar soundness composes with source validity. -/
theorem selectedImport_success_sound_and_validFor {input next : State}
    {selection : SelectedImport} (inputValid : input.ValidFor)
    (result : selectedImport input = .ok selection next) :
    DeclarativeGrammar.SelectedImportParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨selectedImport_success_sound result, ?_⟩
  have valid := selectedImport_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportsSoundnessProperties
/-! Success soundness of nonempty selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- `requireSelected` preserves state, delimiter span, and forward elements. -/
theorem requireSelected_success_shape
    {values : DelimitedList SelectedImport}
    {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.requireSelected values input =
      .ok selection next) :
    next = input ∧
      selection.span = values.span ∧
      selection.elements.toList = values.elements := by
  unfold ImportInternals.requireSelected at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      simp only [pure] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Every successful selected-import list follows the independent grammar. -/
theorem selectedImports_success_sound {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.selectedImports input = .ok selection next) :
    DeclarativeGrammar.SelectedImportsParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold ImportInternals.selectedImports at result
  cases valuesResult : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject failure rejected => simp [bind, valuesResult] at result
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      have valuesGrammar := delimited_nonempty_trailing_success_sound
        .leftBrace .rightBrace selectedImport
        DeclarativeGrammar.SelectedImportParses .importDecl .topLevel
        selectedImport_success_sound selectedImport_preservesTokenWindow
        valuesResult
      have shape := requireSelected_success_shape result
      unfold DeclarativeGrammar.SelectedImportsParses
      rw [shape.1]
      simpa only [shape.2.1, shape.2.2] using valuesGrammar

/-- Selected-list grammar soundness composes with source validity. -/
theorem selectedImports_success_sound_and_validFor {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (inputValid : input.ValidFor)
    (result : ImportInternals.selectedImports input = .ok selection next) :
    DeclarativeGrammar.SelectedImportsParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor input.file
        selection := by
  refine ⟨selectedImports_success_sound result, ?_⟩
  have valid := selectedImports_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportsOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import-list success preserves the exact
nonempty allow-trailing list, source order, span, and final remainder. -/
theorem selectedImports_success_ordinaryOutcome_sound
    {input output : State}
    {selections : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.selectedImports input = .ok selections output) :
    DeclarativeGrammar.SelectedImportsOrdinaryParses
      input.declarativeRemainder selections output.declarativeRemainder :=
  selectedImports_success_sound result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import success preserves its exact source,
optional alias, AST span, and final remainder. -/
theorem selectedImport_success_ordinaryOutcome_sound
    {input output : State} {selection : SelectedImport}
    (result : selectedImport input = .ok selection output) :
    DeclarativeGrammar.SelectedImportOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  selectedImport_success_sound result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedAliasOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for optional selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-alias success follows the existing exact
prioritized alias grammar without a diagnostic-free premise. -/
theorem selectedAlias_success_ordinaryOutcome_sound
    {input output : State} {alias : Option Identifier}
    (result : ImportInternals.selectedAlias input = .ok alias output) :
    DeclarativeGrammar.SelectedAliasOrdinaryParses
      input.declarativeRemainder alias output.declarativeRemainder :=
  selectedAlias_success_sound result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import rejection occurs first in its source, or
after an exact source success in its optional alias. -/
theorem selectedImport_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : selectedImport input = .reject failure rejected) :
    DeclarativeGrammar.SelectedImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold selectedImport at result
  cases sourceResult : selectorName .importDecl input with
  | invariant error => simp [bind, sourceResult] at result
  | reject sourceFailure sourceRejected =>
      simp only [bind, sourceResult] at result
      cases result
      exact .sourceRejected
        (selectorName_reject_ordinaryOutcome_sound .importDecl sourceResult)
  | ok source afterSource =>
      simp only [bind, sourceResult] at result
      have sourceParsed := selectorName_success_ordinaryOutcome_sound
        .importDecl sourceResult
      cases aliasResult : ImportInternals.selectedAlias afterSource with
      | invariant error => simp [aliasResult] at result
      | reject aliasFailure aliasRejected =>
          simp only [aliasResult] at result
          cases result
          exact .aliasRejected sourceParsed
            (selectedAlias_reject_ordinaryOutcome_sound aliasResult)
      | ok alias output => simp [aliasResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-import success and exact sequential rejection. -/
theorem selectedImport_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : SelectedImport},
      selectedImport input = .ok selection output →
        DeclarativeGrammar.SelectedImportOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      selectedImport input = .reject failure rejected →
        DeclarativeGrammar.SelectedImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedImport_success_ordinaryOutcome_sound,
    selectedImport_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-import outcomes. -/
theorem selectedImport_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportOrdinaryParses
      DeclarativeGrammar.SelectedImportRejects :=
  DeclarativeGrammar.selectedImportDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportsOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import-list rejection comes from its required
nonempty, allow-trailing delimited stage; the nonempty refinement cannot
reject. -/
theorem selectedImports_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectedImports input =
      .reject failure rejected) :
    DeclarativeGrammar.SelectedImportsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectedImports at result
  cases valuesResult : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      exact delimited_reject_sound .leftBrace .rightBrace false selectedImport
        DeclarativeGrammar.SelectedImportOrdinaryParses
        DeclarativeGrammar.SelectedImportRejects .importDecl .topLevel
        selectedImport_success_ordinaryOutcome_sound
        selectedImport_reject_ordinaryOutcome_sound valuesResult
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      unfold ImportInternals.requireSelected at result
      cases elements : values.elements with
      | nil => simp [elements] at result
      | cons head tail => simp [elements, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedImportsOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-import-list success and exact delimited rejection. -/
theorem selectedImports_ordinaryOutcome_sound :
    (∀ {input output : State}
        {selections : NonemptyDelimitedList SelectedImport},
      ImportInternals.selectedImports input = .ok selections output →
        DeclarativeGrammar.SelectedImportsOrdinaryParses
          input.declarativeRemainder selections output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectedImports input = .reject failure rejected →
        DeclarativeGrammar.SelectedImportsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedImports_success_ordinaryOutcome_sound,
    selectedImports_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-import-list outcomes. -/
theorem selectedImports_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportsOrdinaryParses
      DeclarativeGrammar.SelectedImportsRejects :=
  DeclarativeGrammar.selectedImportsDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectedAliasOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-alias success and exact committed rejection. -/
theorem selectedAlias_ordinaryOutcome_sound :
    (∀ {input output : State} {alias : Option Identifier},
      ImportInternals.selectedAlias input = .ok alias output →
        DeclarativeGrammar.SelectedAliasOrdinaryParses
          input.declarativeRemainder alias output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectedAlias input = .reject failure rejected →
        DeclarativeGrammar.SelectedAliasRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedAlias_success_ordinaryOutcome_sound,
    selectedAlias_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-alias outcomes. -/
theorem selectedAlias_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedAliasOrdinaryParses
      DeclarativeGrammar.SelectedAliasRejects :=
  DeclarativeGrammar.selectedAliasDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.HidingClauseSoundnessProperties
/-! Success soundness of hiding clauses and their optional boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- `requireSelectorNames` only changes the list carrier, never parser state. -/
theorem requireSelectorNames_success_shape
    {values : DelimitedList SelectorName} {input next : State}
    {names : NonemptyList SelectorName}
    (result : ImportInternals.requireSelectorNames values input =
      .ok names next) :
    next = input ∧ names.toList = values.elements := by
  unfold ImportInternals.requireSelectorNames at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      simp only [pure] at result
      cases result
      exact ⟨rfl, by simp [NonemptyList.toList]⟩

/-- Every hiding clause follows the exact nonempty selector-list grammar. -/
theorem hidingClause_success_sound {input next : State}
    {clause : HidingClause}
    (result : ImportInternals.hidingClause input = .ok clause next) :
    DeclarativeGrammar.HidingClauseParses input.declarativeRemainder clause
      next.declarativeRemainder := by
  unfold ImportInternals.hidingClause at result
  rcases importBind_success_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases importBind_success_components rest with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases importBind_success_components rest with
    ⟨names, afterNames, namesResult, finished⟩
  cases finished
  have markerSound := contextual_ok_tokenAt .hiding .importDecl markerResult
  have valuesGrammar := delimited_nonempty_trailing_success_sound
    .leftBrace .rightBrace (selectorName .importDecl)
    DeclarativeGrammar.SelectorNameParses .importDecl .topLevel
    (selectorName_success_sound .importDecl)
    (selectorName_preservesTokenWindow .importDecl) valuesResult
  have shape := requireSelectorNames_success_shape namesResult
  unfold DeclarativeGrammar.HidingClauseParses
    DeclarativeGrammar.NonemptySelectorListParses
  refine ⟨marker.span, values.span, markerSound.1, ?_, rfl⟩
  rw [shape.1]
  simpa only [markerSound.2, State.declarativeRemainder, State.tokens,
    State.window, State.cursor, shape.2] using valuesGrammar

/-- Hiding-clause grammar soundness composes with source validity. -/
theorem hidingClause_success_sound_and_validFor {input next : State}
    {clause : HidingClause} (inputValid : input.ValidFor)
    (result : ImportInternals.hidingClause input = .ok clause next) :
    DeclarativeGrammar.HidingClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      clause.ValidFor input.file := by
  refine ⟨hidingClause_success_sound result, ?_⟩
  have valid := hidingClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Optional hiding parsing is maximal at its contextual keyword. -/
theorem optionalHiding_success_sound {input next : State}
    {hidden : Option HidingClause}
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    DeclarativeGrammar.OptionalHidingParses input.declarativeRemainder hidden
      next.declarativeRemainder := by
  unfold ImportInternals.optionalHiding at result
  simp only [getState, bind] at result
  split at result
  next present =>
    rcases importBind_success_components result with
      ⟨clause, afterClause, clauseResult, finished⟩
    cases finished
    exact .present (hidingClause_success_sound clauseResult)
  next absent =>
    simp only [pure] at result
    cases result
    have absentFalse : isContextual input .hiding = false := by
      cases found : isContextual input .hiding <;> simp_all
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .hiding absentFalse)

/-- Optional hiding soundness composes with source validity. -/
theorem optionalHiding_success_sound_and_validFor {input next : State}
    {hidden : Option HidingClause} (inputValid : input.ValidFor)
    (result : ImportInternals.optionalHiding input = .ok hidden next) :
    DeclarativeGrammar.OptionalHidingParses input.declarativeRemainder hidden
        next.declarativeRemainder ∧
      Option.ValidFor HidingClause.ValidFor input.file hidden := by
  refine ⟨optionalHiding_success_sound result, ?_⟩
  have valid := optionalHiding_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectiveImportSoundnessProperties
/-! Success soundness of selected imports with optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Diagnostic-free selected-import helper success follows the complete grammar. -/
theorem selectiveImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    DeclarativeGrammar.SelectiveImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.selectiveImport at result
  rcases importBind_success_components result with
    ⟨selection, afterSelection, selectionResult, rest⟩
  rcases importBind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases importBind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, hiddenResult, finishResult⟩
  have selectionSound := selectedImports_success_sound selectionResult
  have fromSound := contextual_ok_tokenAt .from .importDecl fromResult
  have pathSound := modulePath_success_sound .importDecl pathResult
  have hiddenSound := optionalHiding_success_sound hiddenResult
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.selected selection path none) afterHidden =
            .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedNone
      rcases importBind_success_components finishedNone with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree path.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.SelectiveImportTailParses
      refine ⟨selection, afterSelection.declarativeRemainder,
        fromToken.span, path, afterPath.declarativeRemainder, none,
        afterHidden.declarativeRemainder, semicolon.span, selectionSound,
        fromSound.1, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [fromSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.selected selection path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedSome
      rcases importBind_success_components finishedSome with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree clause.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.SelectiveImportTailParses
      refine ⟨selection, afterSelection.declarativeRemainder,
        fromToken.span, path, afterPath.declarativeRemainder, some clause,
        afterHidden.declarativeRemainder, semicolon.span, selectionSound,
        fromSound.1, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [fromSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]

/-- A selected-shaped import result follows the complete selected grammar. -/
theorem importDecl_selected_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (selectedShape : ∃ selection path hidden,
      declaration.value = .selected selection path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.SelectiveImportDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  unfold importDecl at result
  rcases importBind_success_components result with
    ⟨importKeyword, afterKeyword, keywordResult, rest⟩
  have keywordSound := keyword_ok_tokenAt .importKw .importDecl keywordResult
  rcases importBind_success_components rest with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · split at branchResult
    · rcases namespaceImport_success_value importKeyword.span branchResult with
        ⟨path, alias, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, hidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction
    · rcases wildcardImport_success_value importKeyword.span branchResult with
        ⟨path, hidden, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, selectedHidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction
  · split at branchResult
    · have tailGrammar := selectiveImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.SelectiveImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar
    · rcases plainImport_success_value importKeyword.span branchResult with
        ⟨path, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, hidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction

/-- Selected-import grammar soundness composes with source provenance. -/
theorem importDecl_selected_success_sound_and_validFor
    {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (selectedShape : ∃ selection path hidden,
      declaration.value = .selected selection path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.SelectiveImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_selected_success_sound diagnosticFree selectedShape
    result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.HidingClauseOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for required and optional hiding clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable required hiding success follows the exact marker and
nonempty allow-trailing selector-list grammar. -/
theorem hidingClause_success_ordinaryOutcome_sound
    {input output : State} {clause : HidingClause}
    (result : ImportInternals.hidingClause input = .ok clause output) :
    DeclarativeGrammar.HidingClauseOrdinaryParses
      input.declarativeRemainder clause output.declarativeRemainder :=
  hidingClause_success_sound result

/-- Every executable optional hiding success follows its exact guarded
present-or-nonconsuming-absent grammar. -/
theorem optionalHiding_success_ordinaryOutcome_sound
    {input output : State} {hidden : Option HidingClause}
    (result : ImportInternals.optionalHiding input = .ok hidden output) :
    DeclarativeGrammar.OptionalHidingOrdinaryParses
      input.declarativeRemainder hidden output.declarativeRemainder :=
  optionalHiding_success_sound result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectiveImportOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for selective import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selective-import success preserves its nonempty
selection, contextual `from`, module path, optional hiding,
explicit-or-recovered terminator, AST, span, and final remainder. -/
theorem selectiveImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.selectiveImport start input =
      .ok declaration output) :
    DeclarativeGrammar.SelectiveImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.selectiveImport at result
  rcases bind_success_components result with
    ⟨selection, afterSelection, selectionResult, rest⟩
  rcases bind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases bind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bind_success_components rest with
    ⟨hidden, afterHiding, hidingResult, finishResult⟩
  cases hidden with
  | none =>
      have normalized : ImportInternals.finish start path.span
          (.selected selection path none) afterHiding =
            .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed fromToken.span
        (selectedImports_success_ordinaryOutcome_sound selectionResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound path.span
          terminatorResult)
  | some clause =>
      have normalized : ImportInternals.finish start clause.span
          (.selected selection path (some clause)) afterHiding =
            .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed fromToken.span
        (selectedImports_success_ordinaryOutcome_sound selectionResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound clause.span
          terminatorResult)

end Solcore.Syntax.Parser
end
