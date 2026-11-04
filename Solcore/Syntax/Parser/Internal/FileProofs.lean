import Solcore.Syntax.Parser.SourceFiles
import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Parser.Internal.ImplProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TriviaProofs
import Solcore.Syntax.Parser.Internal.TraitProofs
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Internal.ContractBodySoundness
import Solcore.Syntax.Internal.SourceFileOutcomes
import Solcore.Syntax.Grammar.SourceFile
import Solcore.Syntax.Parser.Internal.ImportSoundness
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.ContractOutcomeSoundness
import Solcore.Syntax.Parser.Internal.ExportSoundness
import Solcore.Syntax.Internal.DeclarationExactness
import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Parser.State

/-!
Proofs about the parsers of top items and file items: token-window and cursor laws, source
validity, soundness against the declarative grammar, and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.FileTopItemProperties
/-! Contracts for top-level wrapping and derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

abbrev CanonicalTopItemValid :=
  TopItem.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor

/-- Wrapping keeps the item and declaration outer spans synchronized. -/
def TopItemSpanAligned (item : TopItem) : Prop :=
  match item.value with
  | .importDecl declaration => item.span = declaration.span
  | .exportDecl declaration => item.span = declaration.span
  | .pragmaDecl declaration => item.span = declaration.span
  | .typeAlias declaration => item.span = declaration.span
  | .enum declaration => item.span = declaration.span
  | .trait declaration => item.span = declaration.span
  | .impl declaration => item.span = declaration.span
  | .contract declaration => item.span = declaration.span
  | .function declaration => item.span = declaration.span
  | .error => True

/-- Canonical provenance plus the span invariant needed by derive attachment. -/
structure TopItemContract (file : SourceFile) (item : TopItem) : Prop where
  validFor : CanonicalTopItemValid file item
  spanAligned : TopItemSpanAligned item

theorem wrapImport_contract {file : SourceFile} {declaration : ImportDecl}
    (valid : ImportDecl.ValidFor file declaration) :
    TopItemContract file (wrapImport declaration) :=
  ⟨.importDecl valid.1 (by simp) valid, rfl⟩

theorem wrapExport_contract {file : SourceFile} {declaration : ExportDecl}
    (valid : ExportDecl.ValidFor file declaration) :
    TopItemContract file (wrapExport declaration) :=
  ⟨.exportDecl valid.1 (by simp) valid, rfl⟩

theorem wrapPragma_contract {file : SourceFile} {declaration : PragmaDecl}
    (valid : PragmaDecl.ValidFor file declaration) :
    TopItemContract file (wrapPragma declaration) :=
  ⟨.pragmaDecl valid.1 (by simp) valid, rfl⟩

theorem wrapTypeAlias_contract {file : SourceFile}
    {declaration : TypeAliasDecl}
    (valid : TypeAliasDecl.ValidFor file declaration) :
    TopItemContract file (wrapTypeAlias declaration) :=
  ⟨.typeAlias valid.1 (by simp) valid, rfl⟩

theorem wrapFunction_contract {file : SourceFile}
    {declaration : FunctionDecl}
    (valid : FunctionDecl.ValidFor CoreStatement.ValidFor file declaration) :
    TopItemContract file (wrapFunction declaration) :=
  ⟨.function valid.1 (by simp) valid, rfl⟩

theorem wrapEnum_contract {file : SourceFile} {declaration : EnumDecl}
    (valid : EnumDecl.ValidFor file declaration) :
    TopItemContract file (wrapEnum declaration) :=
  ⟨.enum valid.1 (by simp) valid, rfl⟩

theorem wrapTrait_contract {file : SourceFile} {declaration : TraitDecl}
    (valid : TraitDecl.ValidFor file declaration) :
    TopItemContract file (wrapTrait declaration) :=
  ⟨.trait valid.1 (by simp) valid, rfl⟩

theorem wrapImpl_contract {file : SourceFile} {declaration : ImplDecl}
    (valid : ImplDecl.ValidFor CoreStatement.ValidFor file declaration) :
    TopItemContract file (wrapImpl declaration) :=
  ⟨.impl valid.1 (by simp) valid, rfl⟩

theorem wrapContract_contract {file : SourceFile}
    {declaration : ContractDecl}
    (valid : ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor
      file declaration) :
    TopItemContract file (wrapContract declaration) :=
  ⟨.contract valid.1 (by simp) valid, rfl⟩

/-- Extending a wrapped item preserves all nested provenance and alignment. -/
theorem extendTopItemStart_contract {file : SourceFile}
    (prefixSpan : SourceSpan) (item : TopItem)
    (prefixValid : prefixSpan.ValidFor file)
    (itemContract : TopItemContract file item)
    (ordered : prefixSpan.startByte ≤ item.span.endByte) :
    TopItemContract file (extendTopItemStart prefixSpan item) := by
  have coveredValid := SourceSpan.cover_validFor prefixValid
    itemContract.validFor.span_valid ordered
  constructor
  · cases itemContract.validFor with
    | importDecl spanValid commentsValid declarationValid =>
        exact .importDecl coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | exportDecl spanValid commentsValid declarationValid =>
        exact .exportDecl coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | pragmaDecl spanValid commentsValid declarationValid =>
        exact .pragmaDecl coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | typeAlias spanValid commentsValid declarationValid =>
        exact .typeAlias coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | enum spanValid commentsValid declarationValid =>
        exact .enum coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | trait spanValid commentsValid declarationValid =>
        exact .trait coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | impl spanValid commentsValid declarationValid =>
        exact .impl coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | contract spanValid commentsValid declarationValid =>
        exact .contract coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | function spanValid commentsValid declarationValid =>
        exact .function coveredValid commentsValid
          ⟨coveredValid, declarationValid.2⟩
    | error spanValid commentsValid =>
        exact .error coveredValid commentsValid
  · rcases item with ⟨span, comments, value⟩
    cases value <;> simp [extendTopItemStart, TopItemSpanAligned]

/-- Attaching a valid derive preserves canonical provenance and span
alignment.  Ordering is explicit because this continuation runs after the
item parser has consumed its input. -/
theorem attachDeriveAttribute_reply_validFor
    (derive : DeriveAttribute) (item : TopItem) (input : State)
    (inputValid : input.ValidFor)
    (deriveValid : DeriveAttribute.ValidFor input.file derive)
    (itemContract : TopItemContract input.file item)
    (ordered : derive.span.startByte ≤ item.span.endByte) :
    (attachDeriveAttribute derive item input).ValidFor input
      TopItemContract := by
  rcases item with ⟨itemSpan, comments, value⟩
  cases value
  all_goals first
  | have extended := extendTopItemStart_contract derive.span _
        deriveValid.1 itemContract ordered
    unfold attachDeriveAttribute bind emitDiagnostic modifyState
      pure Reply.ValidFor
    exact ⟨extended, inputValid.emit_validFor _ deriveValid.1, rfl⟩
  | rename_i declaration
    have aligned : itemSpan = declaration.span := by
      simpa only [TopItemSpanAligned] using itemContract.spanAligned
    have declarationValid := by
      cases itemContract.validFor
      assumption
    have coveredValid := SourceSpan.cover_validFor deriveValid.1
      declarationValid.1 (by simpa [aligned] using ordered)
    have retainedDerive : ∀ retained ∈ (some derive : Option DeriveAttribute),
        DeriveAttribute.ValidFor input.file retained := by
      intro retained member
      have retainedEq : retained = derive := by simpa using member.symm
      subst retained
      exact deriveValid
    unfold attachDeriveAttribute Reply.ValidFor
    exact ⟨{
      validFor := .enum coveredValid (by
        cases itemContract.validFor
        assumption) ⟨coveredValid, retainedDerive, declarationValid.2.2⟩
      spanAligned := rfl
    }, inputValid, rfl⟩

private theorem emitThenPure_preservesTokenWindow
    (diagnostic : ParseDiagnostic) (value : TopItem) :
    Parser.PreservesTokenWindow (do
      let _ ← emitDiagnostic diagnostic
      pure value) := by
  apply Parser.bind_preservesTokenWindow
    (emitDiagnostic_preservesTokenWindow diagnostic)
  intro _
  exact Parser.pure_preservesTokenWindow value

/-- Derive attachment changes diagnostics and values, never token windows. -/
theorem attachDeriveAttribute_preservesTokenWindow
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.PreservesTokenWindow (attachDeriveAttribute derive item) := by
  rcases item with ⟨span, comments, value⟩
  cases value <;> first
  | exact Parser.pure_preservesTokenWindow _
  | exact emitThenPure_preservesTokenWindow _ _

theorem attachDeriveAttribute_preservesTokensOnSuccess
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.PreservesTokensOnSuccess (attachDeriveAttribute derive item) :=
  (attachDeriveAttribute_preservesTokenWindow derive item).preservesTokensOnSuccess

private theorem emitThenPure_cursorMonotoneOnSuccess
    (diagnostic : ParseDiagnostic) (value : TopItem) :
    Parser.CursorMonotoneOnSuccess (do
      let _ ← emitDiagnostic diagnostic
      pure value) := by
  apply Parser.bind_cursorMonotoneOnSuccess
    (emitDiagnostic_cursorMonotoneOnSuccess diagnostic)
  intro _
  exact Parser.pure_cursorMonotoneOnSuccess value

/-- Derive attachment never moves the continuation cursor backwards. -/
theorem attachDeriveAttribute_cursorMonotoneOnSuccess
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.CursorMonotoneOnSuccess (attachDeriveAttribute derive item) := by
  rcases item with ⟨span, comments, value⟩
  cases value <;> first
  | exact Parser.pure_cursorMonotoneOnSuccess _
  | exact emitThenPure_cursorMonotoneOnSuccess _ _

/-- Every successful attachment keeps the derive attribute's starting byte. -/
theorem attachDeriveAttribute_preservesDeriveStartOnSuccess
    (derive : DeriveAttribute) (item : TopItem)
    {input final : State} {result : TopItem}
    (parsed : attachDeriveAttribute derive item input = .ok result final) :
    derive.span.startByte = result.span.startByte := by
  rcases item with ⟨span, comments, value⟩
  cases value <;>
    unfold attachDeriveAttribute bind emitDiagnostic modifyState pure at parsed
  all_goals cases parsed; rfl

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FilePlainTopItemProperties
/-! Compositional contracts for top-level declaration dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The complete contract retained by top-level declaration dispatch. -/
structure TopItemParserContract (parser : Parser TopItem) : Prop where
  validFor : parser.ValidFor TopItemContract
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

theorem TopItemParserContract.preservesTokensOnSuccess
    {parser : Parser TopItem}
    (contract : TopItemParserContract parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

/-- The still-open outer contract declaration boundary is an explicit input. -/
structure ContractDeclInputs : Prop where
  validFor : contractDecl.ValidFor
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor)
  preservesTokenWindow : Parser.PreservesTokenWindow contractDecl
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractDecl
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span)

private theorem mapTopItem_contract {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → TopItem)
    (valueValid : SourceFile → alpha → Prop) (span : alpha → SourceSpan)
    (parserValid : parser.ValidFor valueValid)
    (parserWindow : Parser.PreservesTokenWindow parser)
    (parserCursor : Parser.CursorMonotoneOnSuccess parser)
    (parserStarts : Parser.StartsAtCurrentTokenOnSuccess parser span)
    (wrapValid : ∀ file value, valueValid file value →
      TopItemContract file (wrap value))
    (wrapSpan : ∀ value, (wrap value).span = span value) :
    TopItemParserContract (mapTopItem parser wrap) := {
  validFor := by
    intro input inputValid
    have valid := parserValid input inputValid
    unfold mapTopItem
    cases result : parser input with
    | invariant error => trivial
    | reject failure next =>
        rw [result] at valid
        exact ⟨valid.1, valid.2.1, valid.2.2⟩
    | ok value next =>
        rw [result] at valid
        simp only [Reply.ValidFor]
        exact ⟨wrapValid input.file value valid.1, valid.2.1, valid.2.2⟩
  preservesTokenWindow := by
    intro input
    have preserved := parserWindow input
    unfold mapTopItem
    cases result : parser input with
    | invariant error => trivial
    | reject failure next =>
        rw [result] at preserved
        exact ⟨preserved.1, preserved.2⟩
    | ok value next =>
        rw [result] at preserved
        exact ⟨preserved.1, preserved.2⟩
  cursorMonotoneOnSuccess := by
    intro input item next parsed
    unfold mapTopItem at parsed
    cases result : parser input with
    | invariant error => simp [result] at parsed
    | reject failure rejected => simp [result] at parsed
    | ok value final =>
        simp only [result] at parsed
        have monotone := parserCursor input value final result
        cases parsed
        exact monotone
  startsAtCurrentTokenOnSuccess := by
    intro input item next parsed
    unfold mapTopItem at parsed
    cases result : parser input with
    | invariant error => simp [result] at parsed
    | reject failure rejected => simp [result] at parsed
    | ok value final =>
        simp only [result] at parsed
        have starts := parserStarts input value final result
        cases parsed
        simpa only [wrapSpan value] using starts
}

private theorem stateChoice_contract (condition : State → Bool)
    {first second : Parser TopItem}
    (firstContract : TopItemParserContract first)
    (secondContract : TopItemParserContract second) :
    TopItemParserContract (fun input =>
      if condition input then first input else second input) := {
  validFor := by
    intro input inputValid
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.validFor input inputValid
    · simpa [selected] using secondContract.validFor input inputValid
  preservesTokenWindow := by
    intro input
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.preservesTokenWindow input
    · simpa [selected] using secondContract.preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    by_cases selected : condition input = true
    · exact firstContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using parsed)
    · exact secondContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using parsed)
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    by_cases selected : condition input = true
    · exact firstContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using parsed)
    · exact secondContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using parsed)
}

private theorem rejectedTopItem_contract : TopItemParserContract (fun input =>
    rejectAt input { head := .topItem, tail := [] } .topItem) := {
  validFor := by
    intro input inputValid
    unfold rejectAt Reply.ValidFor
    exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  preservesTokenWindow := fun input =>
    rejectAt_preservesTokenWindow input _ _
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold rejectAt at parsed
    contradiction
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold rejectAt at parsed
    contradiction
}

/-- All nine declaration branches and the terminal rejection compose in
implementation order.  Only the unfinished outer contract parser remains an
explicit dependency. -/
theorem plainTopItem_contract (contract : ContractDeclInputs) :
    TopItemParserContract plainTopItem := by
  have importBranch := mapTopItem_contract importDecl wrapImport
    ImportDecl.ValidFor (·.span) importDecl_validFor
    importDecl_preservesTokenWindow importDecl_cursorMonotoneOnSuccess
    importDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapImport_contract) (fun _ => rfl)
  have exportBranch := mapTopItem_contract exportDecl wrapExport
    ExportDecl.ValidFor (·.span) exportDecl_validFor
    exportDecl_preservesTokenWindow exportDecl_cursorMonotoneOnSuccess
    exportDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapExport_contract) (fun _ => rfl)
  have pragmaBranch := mapTopItem_contract pragmaDecl wrapPragma
    PragmaDecl.ValidFor (·.span) pragmaDecl_validFor
    pragmaDecl_preservesTokenWindow pragmaDecl_cursorMonotoneOnSuccess
    pragmaDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapPragma_contract) (fun _ => rfl)
  have aliasBranch := mapTopItem_contract typeAlias wrapTypeAlias
    TypeAliasDecl.ValidFor (·.span) typeAlias_validFor
    typeAlias_preservesTokenWindow typeAlias_cursorMonotoneOnSuccess
    typeAlias_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapTypeAlias_contract) (fun _ => rfl)
  have functionBranch := mapTopItem_contract (functionDecl .module) wrapFunction
    (FunctionDecl.ValidFor CoreStatement.ValidFor) (·.span)
    (functionDecl_canonical_validFor .module)
    (functionDecl_preservesTokenWindow_of_block .module
      (block_canonical_preservesTokenWindow .allow))
    (functionDecl_cursorMonotoneOnSuccess_of_block .module
      (block_canonical_cursorMonotoneOnSuccess .allow))
    (functionDecl_startsAtCurrentTokenOnSuccess .module)
    (fun _ _ => wrapFunction_contract) (fun _ => rfl)
  have enumBranch := mapTopItem_contract (enumDecl none) wrapEnum
    EnumDecl.ValidFor (·.span) enumDecl_none_validFor
    (enumDecl_preservesTokenWindow none)
    (enumDecl_cursorMonotoneOnSuccess none)
    enumDecl_none_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapEnum_contract) (fun _ => rfl)
  have traitBranch := mapTopItem_contract traitDecl wrapTrait
    TraitDecl.ValidFor (·.span) traitDecl_validFor
    (traitDecl_preservesTokenWindow
      (functionSignature_preservesTokenWindow .module)
      whereClause_preservesTokenWindow)
    (traitDecl_cursorMonotoneOnSuccess whereClause_cursorMonotoneOnSuccess)
    traitDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapTrait_contract) (fun _ => rfl)
  have implBranch := mapTopItem_contract implDecl wrapImpl
    (ImplDecl.ValidFor CoreStatement.ValidFor) (·.span)
    implDecl_canonical_validFor
    (implDecl_preservesTokenWindow_of_block
      (block_canonical_preservesTokenWindow .allow))
    implDecl_cursorMonotoneOnSuccess implDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapImpl_contract) (fun _ => rfl)
  have contractBranch := mapTopItem_contract contractDecl wrapContract
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) (·.span)
    contract.validFor contract.preservesTokenWindow
    contract.cursorMonotoneOnSuccess contract.startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapContract_contract) (fun _ => rfl)
  have dispatch := stateChoice_contract (fun state => isKeyword state .importKw)
    importBranch (stateChoice_contract (fun state => isKeyword state .exportKw)
      exportBranch (stateChoice_contract (fun state => isKeyword state .pragmaKw)
        pragmaBranch (stateChoice_contract (fun state => isKeyword state .typeKw)
          aliasBranch (stateChoice_contract
            (fun state => isKeyword state .functionKw) functionBranch
            (stateChoice_contract (fun state => isContextual state .enum)
              enumBranch (stateChoice_contract
                (fun state => isContextual state .trait) traitBranch
                (stateChoice_contract (fun state =>
                  isContextual state .impl || isKeyword state .defaultKw)
                  implBranch (stateChoice_contract
                    (fun state => isKeyword state .contractKw)
                    contractBranch rejectedTopItem_contract))))))))
  unfold plainTopItem
  exact dispatch

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemProperties
/-! Contract for one derive-aware top-level item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem derive_start_le_item_end
    (plain : TopItemParserContract plainTopItem)
    {input afterDerive next : State} {derive : DeriveAttribute}
    {item : TopItem} (inputValid : input.ValidFor)
    (deriveResult : deriveAttribute input = .ok derive afterDerive)
    (itemResult : plainTopItem afterDerive = .ok item next)
    (itemSpanValid : item.span.ValidFor input.file) :
    derive.span.startByte ≤ item.span.endByte := by
  rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
    ⟨first, firstFound, firstStart⟩
  rcases plain.startsAtCurrentTokenOnSuccess _ _ _ itemResult with
    ⟨last, lastFound, lastStart⟩
  have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have lastAt := State.getElem?_eq_some_of_peek?_eq_some lastFound
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt firstAt
    (by simpa [deriveAttribute_preservesTokensOnSuccess _ _ _ deriveResult]
      using lastAt) (deriveAttribute_cursor_lt_onSuccess deriveResult)
  exact calc
    derive.span.startByte = first.span.startByte := firstStart.symm
    _ ≤ first.span.endByte := (inputValid.peek?_span_validFor firstFound).2.1
    _ ≤ last.span.startByte := separated
    _ = item.span.startByte := lastStart
    _ ≤ item.span.endByte := itemSpanValid.2.1

/-- The parser used by the file-item loop preserves canonical top-item
provenance through both plain and derive-aware paths. -/
theorem parseItemsItem_contract (contract : ContractDeclInputs) :
    TopItemParserContract parseItemsItem := by
  have plain := plainTopItem_contract contract
  constructor
  · intro input inputValid
    unfold parseItemsItem topItem
    by_cases attributed : isSymbol input .hash
    · simp only [attributed, if_true]
      have deriveReply := deriveAttribute_validFor input inputValid
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveReply
          simpa only [Reply.ValidFor] using deriveReply
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveReply
          have itemReply := plain.validFor afterDerive deriveReply.2.1
          cases itemResult : plainTopItem afterDerive with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              simp only
              rw [itemResult] at itemReply
              exact itemReply.of_file_eq deriveReply.2.2
          | ok item next =>
              simp only
              rw [itemResult] at itemReply
              have fileEq := itemReply.2.2.trans deriveReply.2.2
              have attached := attachDeriveAttribute_reply_validFor derive item
                next itemReply.2.1 (by simpa [fileEq] using deriveReply.1)
                (by simpa [itemReply.2.2] using itemReply.1)
                (derive_start_le_item_end plain inputValid deriveResult itemResult
                  (by simpa [deriveReply.2.2] using
                    itemReply.1.validFor.span_valid))
              exact attached.of_file_eq fileEq
    · simp only [attributed]
      exact plain.validFor input inputValid
  · intro input
    unfold parseItemsItem topItem
    split
    · have deriveWindow := deriveAttribute_preservesTokenWindow input
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveWindow
          simpa only [Reply.PreservesTokenWindow] using deriveWindow
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveWindow
          have itemWindow := plain.preservesTokenWindow afterDerive
          cases itemResult : plainTopItem afterDerive with
          | invariant error => simp only [Reply.PreservesTokenWindow]
          | reject failure rejected =>
              simp only
              rw [itemResult] at itemWindow
              exact itemWindow.trans deriveWindow
          | ok item next =>
              simp only
              rw [itemResult] at itemWindow
              exact (attachDeriveAttribute_preservesTokenWindow derive item next).trans
                (itemWindow.trans deriveWindow)
    · exact plain.preservesTokenWindow input
  · intro input result final parsed
    unfold parseItemsItem topItem at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
      rename_i item next
      exact Nat.le_trans
        (deriveAttribute_cursorMonotoneOnSuccess _ _ _ deriveResult)
        (Nat.le_trans (plain.cursorMonotoneOnSuccess _ _ _ itemResult)
          (attachDeriveAttribute_cursorMonotoneOnSuccess _ _ _ _ _ parsed))
    · exact plain.cursorMonotoneOnSuccess _ _ _ parsed
  · intro input result final parsed
    unfold parseItemsItem topItem at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
      rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
        ⟨token, found, start⟩
      exact ⟨token, found, start.trans
        (attachDeriveAttribute_preservesDeriveStartOnSuccess _ _ parsed)⟩
    · exact plain.startsAtCurrentTokenOnSuccess _ _ _ parsed

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection through attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem mapTopItem_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (mapTopItem parser wrap) := by
  intro input item next result diagnosticFree
  unfold mapTopItem at result
  cases parserResult : parser input with
  | invariant error => simp [parserResult] at result
  | reject failure rejected => simp [parserResult] at result
  | ok value afterValue =>
      simp only [parserResult] at result
      cases result
      exact parserReflects input value next parserResult diagnosticFree

/-- Plain top-item parsing cannot erase an incoming diagnostic. -/
theorem plainTopItem_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess plainTopItem := by
  intro input item next result diagnosticFree
  unfold plainTopItem at result
  split at result
  · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
      importDecl_reflectsDiagnosticFreeOnSuccess input item next result
        diagnosticFree
  · split at result
    · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
        exportDecl_reflectsDiagnosticFreeOnSuccess input item next result
          diagnosticFree
    · split at result
      · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
          pragmaDecl_reflectsDiagnosticFreeOnSuccess input item next result
            diagnosticFree
      · split at result
        · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
            typeAlias_reflectsDiagnosticFreeOnSuccess input item next result
              diagnosticFree
        · split at result
          · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
              (functionDecl_reflectsDiagnosticFreeOnSuccess .module
                allowBodyReflects) input item next result diagnosticFree
          · split at result
            · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                (enumDecl_reflectsDiagnosticFreeOnSuccess none) input item next
                  result diagnosticFree
            · split at result
              · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                  traitDecl_reflectsDiagnosticFreeOnSuccess input item next
                    result diagnosticFree
              · split at result
                · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                    (implDecl_reflectsDiagnosticFreeOnSuccess allowBodyReflects)
                      input item next result diagnosticFree
                · split at result
                  · exact mapTopItem_reflectsDiagnosticFreeOnSuccess
                      (ContractInternals.contractDecl_reflectsDiagnosticFreeOnSuccess
                        expressionReflects allowBodyReflects
                          requiredBodyReflects)
                      input item next result diagnosticFree
                  · simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemDeriveAttachmentOrdinarySoundnessProperties
/-! Exact executable reflection for top-item derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every successful derive attachment performs the exact pure AST
transformation and leaves the declarative parser remainder unchanged. -/
theorem attachDeriveAttribute_success_ordinaryOutcome_sound
    {derive : DeriveAttribute} {item attached : TopItem}
    {input output : State}
    (result : attachDeriveAttribute derive item input = .ok attached output) :
    DeclarativeGrammar.TopItemDeriveAttaches derive item attached ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue with
  | importDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.importDecl, rfl⟩
  | exportDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.exportDecl, rfl⟩
  | pragmaDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.pragmaDecl, rfl⟩
  | typeAlias declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.typeAlias, rfl⟩
  | enum declaration =>
      simp only [attachDeriveAttribute, pure] at result
      cases result
      exact ⟨.enum, rfl⟩
  | trait declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.trait, rfl⟩
  | impl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.impl, rfl⟩
  | contract declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.contract, rfl⟩
  | function declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.function, rfl⟩
  | error =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.error, rfl⟩

/-- Top-item derive attachment is an unconditional ordinary success for every
item variant and parser state. -/
theorem attachDeriveAttribute_total_success
    (derive : DeriveAttribute) (item : TopItem) (input : State) :
    ∃ attached output,
      attachDeriveAttribute derive item input = .ok attached output := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
      modifyState, bind, pure]

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemRecoveryBoundaryProperties
/-! Executable-to-declarative stop bridges for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every exact declarative top-item boundary makes the executable lookahead
guard true. -/
theorem atTopItemStart_eq_true_of_topItemRecoveryBoundary
    {input : State}
    (starts : DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder) :
    atTopItemStart input = true := by
  rcases starts with ⟨kind, member, span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at token
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  unfold atTopItemStart
  rw [peekKind]
  exact (importTerminatorTopItemStartKind_iff kind).mpr member

/-- A true auxiliary scan guard gives an exact nonconsuming recovery stop. -/
theorem topItemRecoveryStops_of_guard_eq_true (input : State)
    (stops : (input.atEnd || atTopItemStart input) = true) :
    DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atTopItemStart input = true := by
      simpa [atEndFalse] using stops
    exact .boundary
      (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true boundary)

/-- Under a false auxiliary guard, failed advancement is an exact missing
carrier slot inside the active token window. -/
theorem topItemRecoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atTopItemStart input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.TopItemRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false auxiliary guard excludes every exact stop,
so recovery must scan that token. -/
theorem no_topItemRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atTopItemStart input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | boundary starts =>
      have boundary :=
        atTopItemStart_eq_true_of_topItemRecoveryBoundary starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemSoundnessProperties
/-! Parametric strict soundness for attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem mapTopItem_ok_components {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input next : State} {item : TopItem}
    (result : mapTopItem parser wrap input = .ok item next) :
    ∃ value, parser input = .ok value next ∧ item = wrap value := by
  unfold mapTopItem at result
  cases parserResult : parser input with
  | ok value afterValue =>
      simp only [parserResult] at result
      cases result
      exact ⟨value, rfl, rfl⟩
  | reject failure rejected => simp [parserResult] at result
  | invariant error => simp [parserResult] at result

private theorem topItemKindsAbsentAt_nil (input : State) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [] := by
  intro kind member
  contradiction

private theorem topItemKindsAbsentAt_cons (input : State) (kind : TokenKind)
    (kinds : List TokenKind)
    (headAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (kind :: kinds) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · simpa [State.declarativeRemainder] using headAbsent
  · exact tailAbsent candidate member

private theorem keywordKindsAbsentAt_cons (input : State)
    (keywordValue : HardKeyword) (kinds : List TokenKind)
    (absent : isKeyword input keywordValue = false)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (.keyword keywordValue :: kinds) :=
  topItemKindsAbsentAt_cons input (.keyword keywordValue) kinds
    (keywordAbsentAt_of_isKeyword_eq_false keywordValue absent) tailAbsent

private theorem contextualKindsAbsentAt_cons (input : State)
    (contextualValue : ContextualKeyword) (kinds : List TokenKind)
    (absent : isContextual input contextualValue = false)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (.identifier contextualValue.spelling :: kinds) :=
  topItemKindsAbsentAt_cons input
    (.identifier contextualValue.spelling) kinds
      (contextualAbsentAt_of_isContextual_eq_false contextualValue absent)
      tailAbsent

private theorem precedingThroughFunctionAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (topItemKindsAbsentAt_nil input)))))

private theorem precedingThroughEnumAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (topItemKindsAbsentAt_nil input))))))

private theorem precedingThroughTraitAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling,
      .identifier ContextualKeyword.trait.spelling] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (contextualKindsAbsentAt_cons input .trait _ traitAbsent
                (topItemKindsAbsentAt_nil input)))))))

private theorem precedingThroughImplDefaultAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implAbsent : isContextual input .impl = false)
    (defaultAbsent : isKeyword input .defaultKw = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling,
      .identifier ContextualKeyword.trait.spelling,
      .identifier ContextualKeyword.impl.spelling, .keyword .defaultKw] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (contextualKindsAbsentAt_cons input .trait _ traitAbsent
                (contextualKindsAbsentAt_cons input .impl _ implAbsent
                  (keywordKindsAbsentAt_cons input .defaultKw _ defaultAbsent
                    (topItemKindsAbsentAt_nil input)))))))))

/-- Diagnostic-free plain dispatch follows the exact executable priority. -/
theorem plainTopItem_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {item : TopItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : plainTopItem input = .ok item next) :
    DeclarativeGrammar.PlainTopItemParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder item
        next.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    rcases mapTopItem_ok_components result with
      ⟨declaration, declarationResult, rfl⟩
    exact .importDecl (importDecl_success_sound diagnosticFree
      declarationResult)
  next importAbsent =>
    have importAbsentEq := Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      rcases mapTopItem_ok_components result with
        ⟨declaration, declarationResult, rfl⟩
      exact .exportDecl
        (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
          (topItemKindsAbsentAt_nil input))
        (exportDecl_success_sound declarationResult)
    next exportAbsent =>
      have exportAbsentEq := Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        rcases mapTopItem_ok_components result with
          ⟨declaration, declarationResult, rfl⟩
        exact .pragmaDecl
          (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
            (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
              (topItemKindsAbsentAt_nil input)))
          (pragmaDecl_success_sound declarationResult)
      next pragmaAbsent =>
        have pragmaAbsentEq := Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          rcases mapTopItem_ok_components result with
            ⟨declaration, declarationResult, rfl⟩
          exact .typeAlias
            (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
              (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
                (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsentEq
                  (topItemKindsAbsentAt_nil input))))
            (typeAlias_success_sound diagnosticFree declarationResult)
        next typeAbsent =>
          have typeAbsentEq := Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            rcases mapTopItem_ok_components result with
              ⟨declaration, declarationResult, rfl⟩
            exact .function
              (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
                (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
                  (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsentEq
                    (keywordKindsAbsentAt_cons input .typeKw _ typeAbsentEq
                      (topItemKindsAbsentAt_nil input)))))
              (functionDecl_success_sound .module allowBodyParses
                allowBodyReflects allowBodySound diagnosticFree
                  declarationResult)
          next functionAbsent =>
            have functionAbsentEq := Bool.eq_false_iff.mpr functionAbsent
            have throughFunction := precedingThroughFunctionAbsent input
              importAbsentEq exportAbsentEq pragmaAbsentEq typeAbsentEq
                functionAbsentEq
            split at result
            next startsEnum =>
              rcases mapTopItem_ok_components result with
                ⟨declaration, declarationResult, rfl⟩
              exact .enum throughFunction
                (enumDecl_success_sound none declarationResult)
            next enumAbsent =>
              have enumAbsentEq := Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                rcases mapTopItem_ok_components result with
                  ⟨declaration, declarationResult, rfl⟩
                exact .trait
                  (precedingThroughEnumAbsent input importAbsentEq
                    exportAbsentEq pragmaAbsentEq typeAbsentEq functionAbsentEq
                      enumAbsentEq)
                  (traitDecl_success_sound diagnosticFree declarationResult)
              next traitAbsent =>
                have traitAbsentEq := Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  rcases mapTopItem_ok_components result with
                    ⟨declaration, declarationResult, rfl⟩
                  exact .impl
                    (precedingThroughTraitAbsent input importAbsentEq
                      exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq)
                    (implDecl_success_sound allowBodyParses allowBodyReflects
                      allowBodySound diagnosticFree declarationResult)
                next implAbsent =>
                  have implChoiceAbsent := Bool.eq_false_iff.mpr implAbsent
                  have implParts := Bool.or_eq_false_iff.mp implChoiceAbsent
                  split at result
                  next startsContract =>
                    rcases mapTopItem_ok_components result with
                      ⟨declaration, declarationResult, rfl⟩
                    exact .contract
                      (precedingThroughImplDefaultAbsent input importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                          functionAbsentEq enumAbsentEq traitAbsentEq
                          implParts.1 implParts.2)
                      (ContractInternals.contractDecl_success_sound
                        expressionParses allowBodyParses requiredBodyParses
                        expressionReflects expressionSound allowBodyReflects
                        allowBodySound requiredBodyReflects requiredBodySound
                        diagnosticFree declarationResult)
                  next contractAbsent =>
                    simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemSoundnessProperties
/-! Parametric diagnostic-free soundness for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Derive attachment cannot erase an incoming diagnostic. -/
theorem attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (attachDeriveAttribute derive item) := by
  intro input value next result diagnosticFree
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp only [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum => exact diagnosticFree
  all_goals cases diagnosticFree

/-- A diagnostic-free attachment success is possible only for an enum item. -/
private theorem attachDeriveAttribute_success_requiresEnum
    {derive : DeriveAttribute} {item value : TopItem}
    {input next : State} (diagnosticFree : next.diagnosticsRev = [])
    (result : attachDeriveAttribute derive item input = .ok value next) :
    ∃ declaration, item.value = .enum declaration := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp only [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum declaration => exact ⟨declaration, rfl⟩
  all_goals cases diagnosticFree

/-- Derive-aware dispatch reflects diagnostic freedom through every stage. -/
theorem topItem_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess topItem := by
  intro input item next result diagnosticFree
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
        allowBodyReflects requiredBodyReflects input item next result
          diagnosticFree
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases itemResult : plainTopItem afterDerive with
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result
          | ok plainItem afterItem =>
              simp only [itemResult] at result
              have afterItemFree :=
                attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
                  derive plainItem afterItem item next result diagnosticFree
              have afterDeriveFree :=
                plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
                  allowBodyReflects requiredBodyReflects afterDerive plainItem
                    afterItem itemResult afterItemFree
              exact deriveAttribute_reflectsDiagnosticFreeOnSuccess input
                derive afterDerive deriveResult afterDeriveFree

/-!
Every diagnostic-free top-item success follows exact leading-hash priority.
An attached derive attribute survives only when plain dispatch selected its
enum branch; its exact earlier-selector exclusions and final remainder are
retained.
-/
theorem topItem_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {item : TopItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : topItem input = .ok item next) :
    DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder item
        next.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_success_sound expressionParses allowBodyParses
          requiredBodyParses expressionReflects expressionSound
          allowBodyReflects allowBodySound requiredBodyReflects
          requiredBodySound diagnosticFree result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases itemResult : plainTopItem afterDerive with
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result
          | ok plainItem afterItem =>
              simp only [itemResult] at result
              have afterItemFree :=
                attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
                  derive plainItem afterItem item next result diagnosticFree
              have afterDeriveFree :=
                plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
                  allowBodyReflects requiredBodyReflects afterDerive plainItem
                    afterItem itemResult afterItemFree
              have deriveParsed := deriveAttribute_success_sound
                afterDeriveFree deriveResult
              have attachedEnum :=
                attachDeriveAttribute_success_requiresEnum diagnosticFree
                  result
              have plainParsed := plainTopItem_success_sound expressionParses
                allowBodyParses requiredBodyParses expressionReflects
                expressionSound allowBodyReflects allowBodySound
                requiredBodyReflects requiredBodySound afterItemFree itemResult
              cases plainParsed with
              | importDecl importParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | exportDecl earlierAbsent exportParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | pragmaDecl earlierAbsent pragmaParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | typeAlias earlierAbsent aliasParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | function earlierAbsent functionParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | enum earlierAbsent enumParsed =>
                  simp only [attachDeriveAttribute, pure] at result
                  cases result
                  exact .derivedEnum deriveParsed earlierAbsent
                    (enumParsed.withDerive derive)
              | trait earlierAbsent traitParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | impl earlierAbsent implParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | contract earlierAbsent contractParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileRecoveryProperties
/-! Contracts for canonical top-level error recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Canonical provenance retained by recovered top-level items. -/
abbrev RecoveredTopItemValid :=
  TopItem.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor

/-- Finishing recovery retains one source-valid error item. -/
theorem finishRecoveredTopItem_validFor
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredTopItem first last state).ValidFor state
      RecoveredTopItemValid := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredTopItem Reply.ValidFor
  exact ⟨.error spanValid (by simp),
    stateValid.emit_validFor _ spanValid, rfl⟩

/-- Fuel-bounded recovery preserves provenance while consuming malformed
top-level tokens. -/
theorem recoverTopItemAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverTopItemAux first last fuel state).ValidFor state
        RecoveredTopItemValid := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverTopItemAux
      split
      · exact finishRecoveredTopItem_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredTopItem_validFor first last state stateValid
              firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Complete top-level recovery preserves canonical source provenance. -/
theorem recoverTopItem_validFor :
    Parser.ValidFor recoverTopItem RecoveredTopItemValid := by
  intro input inputValid
  unfold recoverTopItem
  cases advanced : input.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := inputValid.advance?_validFor advanced
      have tokenValid := inputValid.peek?_span_validFor shape.1
      have currentFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverTopItemAux_validFor token.span
        (next.remainingCount + 1) token.span next input.cursor token nextValid
        (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using currentFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Finishing recovery preserves the immutable token window. -/
theorem finishRecoveredTopItem_preservesTokenWindow
    (first last : SourceSpan) :
    Parser.PreservesTokenWindow (finishRecoveredTopItem first last) := by
  intro input
  unfold finishRecoveredTopItem Reply.PreservesTokenWindow State.emit
  exact ⟨rfl, rfl⟩

/-- Fuel-bounded recovery preserves the complete token window. -/
theorem recoverTopItemAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverTopItemAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverTopItemAux
      split
      · exact finishRecoveredTopItem_preservesTokenWindow first last input
      · cases advanced : input.advance? with
        | none =>
            exact finishRecoveredTopItem_preservesTokenWindow first last input
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverTopItemAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (recoverTopItemAux first last fuel) :=
  (recoverTopItemAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

/-- A successful auxiliary recovery is monotone and retains its first span. -/
theorem recoverTopItemAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {item : TopItem},
      recoverTopItemAux first last fuel input = .ok item final →
      input.cursor ≤ final.cursor ∧
        first.startByte = item.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverTopItemAux]
  | succ fuel inductionHypothesis =>
      intro input final item parsed
      unfold recoverTopItemAux at parsed
      split at parsed
      · unfold finishRecoveredTopItem at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredTopItem at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

theorem recoverTopItemAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (recoverTopItemAux first last fuel) :=
  fun _ _ _ parsed =>
    (recoverTopItemAux_ok_state_shape first last fuel parsed).1

/-- Complete recovery preserves the ordinary token window. -/
theorem recoverTopItem_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverTopItem := by
  intro input
  unfold recoverTopItem
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact (recoverTopItemAux_preservesTokenWindow token.span token.span
        (next.remainingCount + 1) next).trans (by
          simp [(advance?_state_shape advanced).2])

theorem recoverTopItem_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess recoverTopItem :=
  recoverTopItem_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete recovery is monotone and starts at its consumed token. -/
theorem recoverTopItem_ok_state_shape {input final : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item final) :
    input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = item.span.startByte := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      have recovered := recoverTopItemAux_ok_state_shape token.span token.span
        (next.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

/-- Successful complete recovery strictly consumes its first malformed token. -/
theorem recoverTopItem_cursor_lt_onSuccess
    {input final : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by simp [(advance?_state_shape advanced).2])
        (recoverTopItemAux_ok_state_shape token.span token.span
          (next.remainingCount + 1) parsed).1

theorem recoverTopItem_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverTopItem :=
  fun _ _ _ parsed => Nat.le_of_lt (recoverTopItem_cursor_lt_onSuccess parsed)

theorem recoverTopItem_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess recoverTopItem (·.span) :=
  fun _ _ _ parsed => (recoverTopItem_ok_state_shape parsed).2

/-- Every successful auxiliary recovery commits a recovery diagnostic. -/
theorem recoverTopItemAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {item : TopItem},
      recoverTopItemAux first last fuel input = .ok item next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverTopItemAux]
  | succ fuel inductionHypothesis =>
      intro input next item parsed
      unfold recoverTopItemAux at parsed
      split at parsed
      · unfold finishRecoveredTopItem at parsed
        cases parsed
        simp [State.emit]
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredTopItem at parsed
            cases parsed
            simp [State.emit]
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at parsed
            exact inductionHypothesis token.span parsed

/-- Every successful complete recovery commits a recovery diagnostic. -/
theorem recoverTopItem_diagnostics_ne_nil_onSuccess
    {input next : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at parsed
      exact recoverTopItemAux_diagnostics_ne_nil_onSuccess token.span
        token.span (afterToken.remainingCount + 1) parsed

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsSoundnessProperties
/-! Diagnostic-free soundness for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem parseItems_success_sound_strong
    (itemParses : DeclarativeGrammar.Remainder → TopItem →
      DeclarativeGrammar.Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] →
      input.diagnosticsRev = []) :
    ∀ fuel itemsRev input items next,
      next.diagnosticsRev = [] →
      parseItems fuel itemsRev input = .ok items next →
      input.diagnosticsRev = [] ∧
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.TopItemsParses itemParses
            input.declarativeRemainder suffix next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next diagnosticFree parsed
      simp [parseItems] at parsed
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next diagnosticFree parsed
      unfold parseItems at parsed
      split at parsed
      · rename_i atEnd
        cases parsed
        refine ⟨diagnosticFree, [], by simp, ?_⟩
        apply DeclarativeGrammar.TopItemsParses.done
        simpa [State.atEnd, State.declarativeRemainder] using atEnd
      · cases itemResult : parseItemsItem input with
        | invariant error =>
            simp [itemResult] at parsed
        | ok item afterItem =>
            simp only [itemResult] at parsed
            split at parsed
            · rename_i progress
              rcases inductionHypothesis (item :: itemsRev) afterItem
                  items next diagnosticFree parsed with
                ⟨afterItemDiagnosticFree, suffix, itemsEq, restGrammar⟩
              have inputDiagnosticFree :=
                itemReflectsDiagnosticFree itemResult
                  afterItemDiagnosticFree
              have itemGrammar := itemSound afterItemDiagnosticFree itemResult
              refine ⟨inputDiagnosticFree, item :: suffix, ?_, ?_⟩
              · rw [itemsEq]
                simp [List.reverse_cons, List.append_assoc]
              · exact DeclarativeGrammar.TopItemsParses.next itemGrammar
                  (by simpa [State.declarativeRemainder] using progress)
                  restGrammar
            · simp at parsed
        | reject failure failedState =>
            simp only [itemResult] at parsed
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            change (if atTopItemStart input then
                .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
              else
                match recoverTopItem rewound with
                | .ok item next => parseItems fuel (item :: itemsRev) next
                | .reject recoveryFailure next =>
                    .reject recoveryFailure next
                | .invariant error => .invariant error) =
              .ok items next at parsed
            split at parsed
            · cases parsed
              simp [State.emit] at diagnosticFree
            · cases recoveryResult : recoverTopItem rewound with
              | invariant error =>
                  simp [recoveryResult] at parsed
              | reject recoveryFailure rejected =>
                  simp [recoveryResult] at parsed
              | ok recovered afterRecovery =>
                  simp only [recoveryResult] at parsed
                  rcases inductionHypothesis (recovered :: itemsRev)
                      afterRecovery items next diagnosticFree parsed with
                    ⟨recoveryDiagnosticFree, suffix, itemsEq, restGrammar⟩
                  exact False.elim
                    (recoverTopItem_diagnostics_ne_nil_onSuccess
                      recoveryResult recoveryDiagnosticFree)

/--
If successful item parsing is sound and cannot erase an incoming diagnostic,
a diagnostic-free successful file loop recognizes exactly the forward suffix
added after its existing reverse accumulator.
-/
theorem parseItems_success_sound_of_diagnosticFree
    (itemParses : DeclarativeGrammar.Remainder → TopItem →
      DeclarativeGrammar.Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] →
      input.diagnosticsRev = [])
    {fuel : Nat} {itemsRev : List TopItem} {input next : State}
    {items : List TopItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (parsed : parseItems fuel itemsRev input = .ok items next) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.TopItemsParses itemParses
        input.declarativeRemainder suffix next.declarativeRemainder :=
  (parseItems_success_sound_strong itemParses itemSound
    itemReflectsDiagnosticFree fuel itemsRev input items next
    diagnosticFree parsed).2

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsProperties
/-! Source-validity contracts for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

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

/-- The fuel-bounded file loop preserves accumulated item provenance.

The complete item parser's validity and token-window laws are explicit so the
declaration dispatcher can be proved independently.
-/
theorem parseItems_validFor
    (itemValid : parseItemsItem.ValidFor RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem) :
    ∀ fuel itemsRev input,
      input.ValidFor →
      List.ValidFor RecoveredTopItemValid input.file itemsRev →
      (parseItems fuel itemsRev input).ValidFor input
        (List.ValidFor RecoveredTopItemValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input inputValid itemsValid
      unfold parseItems
      split
      · refine ⟨?_, inputValid, rfl⟩
        intro item member
        exact itemsValid item (by simpa using member)
      · have itemReply := itemValid input inputValid
        have itemShape := itemWindow input
        cases itemResult : parseItemsItem input with
        | invariant error => trivial
        | ok item next =>
            rw [itemResult] at itemReply itemShape
            dsimp only
            split
            · have accumulated : List.ValidFor RecoveredTopItemValid
                  next.file (item :: itemsRev) := by
                intro retained member
                rcases List.mem_cons.mp member with rfl | priorMember
                · simpa [itemReply.2.2] using itemReply.1
                · simpa [itemReply.2.2] using
                    itemsValid retained priorMember
              exact (inductionHypothesis (item :: itemsRev) next
                itemReply.2.1 accumulated).of_file_eq itemReply.2.2
            · trivial
        | reject failure failedState =>
            rw [itemResult] at itemReply itemShape
            dsimp only
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundValid : rewound.ValidFor := by
              exact rewindAfterItemReject_validFor inputValid itemReply.2.1
                itemShape.2
            have rewoundFile : rewound.file = input.file := by
              simpa [rewound] using itemReply.2.2
            have failureValid : failure.span.ValidFor rewound.file := by
              simpa [rewound, itemReply.2.2] using itemReply.1
            split
            · refine ⟨?_, rewoundValid.emit_validFor failure.toDiagnostic
                  (failure.toDiagnostic_span_validFor failureValid), ?_⟩
              · intro retained member
                exact itemsValid retained (by simpa using member)
              · simpa [State.emit] using rewoundFile
            · have recoveryReply := recoverTopItem_validFor rewound rewoundValid
              cases recoveryResult : recoverTopItem rewound with
              | invariant error => trivial
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at recoveryReply
                  dsimp only
                  exact recoveryReply.of_file_eq rewoundFile
              | ok item next =>
                  rw [recoveryResult] at recoveryReply
                  dsimp only
                  have accumulated : List.ValidFor RecoveredTopItemValid
                      next.file (item :: itemsRev) := by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | priorMember
                    · simpa [recoveryReply.2.2] using recoveryReply.1
                    · simpa [recoveryReply.2.2, rewoundFile] using
                        itemsValid retained priorMember
                  exact (inductionHypothesis (item :: itemsRev) next
                    recoveryReply.2.1 accumulated).of_file_eq
                      (recoveryReply.2.2.trans rewoundFile)

/-- A complete-file reply constructs a fully source-valid canonical syntax file. -/
theorem sourceFile_reply_validFor
    (itemValid : parseItemsItem.ValidFor RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input
      (ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) := by
  have itemsReply := parseItems_validFor itemValid itemWindow
    (input.remainingCount + 1) [] input inputValid (by
      simp [List.ValidFor])
  unfold sourceFile
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [itemsResult] at itemsReply
      exact itemsReply
  | ok items next =>
      rw [itemsResult] at itemsReply
      exact ⟨parsedFile_withAttachedComments_validFor
          CoreStatement.ValidFor CoreExpr.ValidFor input.file comments
          commentsValid items itemsReply.1,
        itemsReply.2.1, itemsReply.2.2⟩

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsStateProperties
/-! State-transition laws for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The fuel-bounded item loop retains its immutable token window. -/
theorem parseItems_preservesTokenWindow
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem) :
    ∀ fuel itemsRev,
      Parser.PreservesTokenWindow (parseItems fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input
      unfold parseItems
      split
      · exact ⟨rfl, rfl⟩
      · have itemShape := itemWindow input
        cases itemResult : parseItemsItem input with
        | invariant error => trivial
        | ok item next =>
            rw [itemResult] at itemShape
            dsimp only
            split
            · exact (inductionHypothesis (item :: itemsRev) next).trans
                itemShape
            · trivial
        | reject failure failedState =>
            rw [itemResult] at itemShape
            dsimp only
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundShape : rewound.tokens = input.tokens ∧
                rewound.window = input.window := by
              exact itemShape
            split
            · exact ⟨rewoundShape.1, rewoundShape.2⟩
            · have recoveryShape :=
                recoverTopItem_preservesTokenWindow rewound
              cases recoveryResult : recoverTopItem rewound with
              | invariant error => trivial
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at recoveryShape
                  dsimp only
                  exact recoveryShape.trans rewoundShape
              | ok recovered next =>
                  rw [recoveryResult] at recoveryShape
                  dsimp only
                  exact (inductionHypothesis (recovered :: itemsRev) next).trans
                    (recoveryShape.trans rewoundShape)

/-- The file loop retains its token carrier on every successful result. -/
theorem parseItems_preservesTokensOnSuccess
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (parseItems_preservesTokenWindow itemWindow fuel itemsRev)

/-- Successful item accumulation never moves the cursor backwards. -/
theorem parseItems_cursorMonotoneOnSuccess
    (itemCursor : Parser.CursorMonotoneOnSuccess parseItemsItem) :
    ∀ fuel itemsRev,
      Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items final parsed
      simp [parseItems] at parsed
  | succ fuel inductionHypothesis =>
      intro itemsRev input items final parsed
      unfold parseItems at parsed
      split at parsed
      · cases parsed
        exact Nat.le_refl _
      · cases itemResult : parseItemsItem input with
        | invariant error => simp [itemResult] at parsed
        | ok item next =>
            simp only [itemResult] at parsed
            split at parsed
            · exact Nat.le_trans (itemCursor input item next itemResult)
                (inductionHypothesis (item :: itemsRev) next items final parsed)
            · simp at parsed
        | reject failure failedState =>
            simp only [itemResult] at parsed
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            split at parsed
            · cases parsed
              exact Nat.le_refl _
            · change (match recoverTopItem rewound with
                | .ok recovered next =>
                    parseItems fuel (recovered :: itemsRev) next
                | .reject recoveryFailure rejected =>
                    .reject recoveryFailure rejected
                | .invariant error => .invariant error) =
                  .ok items final at parsed
              cases recoveryResult : recoverTopItem rewound with
              | invariant error =>
                  rw [recoveryResult] at parsed
                  cases parsed
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at parsed
                  cases parsed
              | ok recovered next =>
                  rw [recoveryResult] at parsed
                  exact Nat.le_trans
                    (recoverTopItem_cursorMonotoneOnSuccess rewound
                      recovered next recoveryResult)
                    (inductionHypothesis (recovered :: itemsRev) next items
                      final parsed)

/-- Complete-file parsing preserves the immutable token window. -/
theorem sourceFile_preservesTokenWindow
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) := by
  intro input
  unfold sourceFile
  have itemsShape := parseItems_preservesTokenWindow itemWindow
    (input.remainingCount + 1) [] input
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [itemsResult] at itemsShape
      exact itemsShape
  | ok items next =>
      rw [itemsResult] at itemsShape
      exact itemsShape

/-- Complete-file parsing retains the token carrier on success. -/
theorem sourceFile_preservesTokensOnSuccess
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (sourceFile_preservesTokenWindow itemWindow comments)

/-- Complete-file parsing never moves the cursor backwards on success. -/
theorem sourceFile_cursorMonotoneOnSuccess
    (itemCursor : Parser.CursorMonotoneOnSuccess parseItemsItem)
    (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) := by
  intro input parsedFile next parsed
  unfold sourceFile at parsed
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error =>
      rw [itemsResult] at parsed
      cases parsed
  | reject failure rejected =>
      rw [itemsResult] at parsed
      cases parsed
  | ok items final =>
      simp only [itemsResult] at parsed
      have monotone : input.cursor ≤ final.cursor :=
        parseItems_cursorMonotoneOnSuccess itemCursor
          (input.remainingCount + 1) [] input items final itemsResult
      cases parsed
      exact monotone

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileCanonicalStateProperties
/-! Canonical state-transition laws for complete-file parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Canonical item parsing makes the file loop preserve its token window. -/
theorem parseItems_canonical_preservesTokenWindow
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.PreservesTokenWindow (parseItems fuel itemsRev) :=
  parseItems_preservesTokenWindow
    (parseItemsItem_contract contract).preservesTokenWindow fuel itemsRev

/-- Canonical item parsing makes the file loop retain its token carrier. -/
theorem parseItems_canonical_preservesTokensOnSuccess
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  parseItems_preservesTokensOnSuccess
    (parseItemsItem_contract contract).preservesTokenWindow fuel itemsRev

/-- Canonical item parsing makes the file loop cursor-monotone. -/
theorem parseItems_canonical_cursorMonotoneOnSuccess
    (contract : ContractDeclInputs) (fuel : Nat)
    (itemsRev : List TopItem) :
    Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) :=
  parseItems_cursorMonotoneOnSuccess
    (parseItemsItem_contract contract).cursorMonotoneOnSuccess fuel itemsRev

/-- Canonical complete-file parsing preserves its token window. -/
theorem sourceFile_canonical_preservesTokenWindow
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) :=
  sourceFile_preservesTokenWindow
    (parseItemsItem_contract contract).preservesTokenWindow comments

/-- Canonical complete-file parsing retains its token carrier on success. -/
theorem sourceFile_canonical_preservesTokensOnSuccess
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  sourceFile_preservesTokensOnSuccess
    (parseItemsItem_contract contract).preservesTokenWindow comments

/-- Canonical complete-file parsing is cursor-monotone on success. -/
theorem sourceFile_canonical_cursorMonotoneOnSuccess
    (contract : ContractDeclInputs) (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) :=
  sourceFile_cursorMonotoneOnSuccess
    (parseItemsItem_contract contract).cursorMonotoneOnSuccess comments

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemOutcomePrimitiveProperties
/-! Shared executable primitives for broad attribute-free top-item outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item mapping exposes the unchanged child endpoint and exact
wrapper value. -/
theorem mapTopItem_success_components {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input output : State} {item : TopItem}
    (result : mapTopItem parser wrap input = .ok item output) :
    ∃ value, parser input = .ok value output ∧ item = wrap value := by
  unfold mapTopItem at result
  cases childResult : parser input with
  | ok value afterValue =>
      simp only [childResult] at result
      cases result
      exact ⟨value, rfl, rfl⟩
  | reject failure rejected => simp [childResult] at result
  | invariant error => simp [childResult] at result

/-- Rejecting top-item mapping is an exact child-rejection passthrough. -/
theorem mapTopItem_reject_result {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input rejected : State} {failure : Failure}
    (result : mapTopItem parser wrap input = .reject failure rejected) :
    parser input = .reject failure rejected := by
  unfold mapTopItem at result
  cases childResult : parser input with
  | ok value output => simp [childResult] at result
  | invariant error => simp [childResult] at result
  | reject childFailure childRejected =>
      simp only [childResult] at result
      cases result
      rfl

/-- A positive hard-keyword guard is exact current-token evidence. -/
theorem plainTopItemTokenPresentAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .topItem result).1⟩

/-- A positive contextual-word guard is exact current-token evidence. -/
theorem plainTopItemTokenPresentAt_of_isContextual_eq_true
    (value : ContextualKeyword) {input : State}
    (present : isContextual input value = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .topItem result).1⟩

/-- A false hard-keyword guard is exact current-token absence. -/
theorem plainTopItemTokenAbsentAt_of_isKeyword_eq_false
    (value : HardKeyword) {input : State}
    (absent : isKeyword input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) :=
  keywordAbsentAt_of_isKeyword_eq_false value absent

/-- A false contextual-word guard is exact current-token absence. -/
theorem plainTopItemTokenAbsentAt_of_isContextual_eq_false
    (value : ContextualKeyword) {input : State}
    (absent : isContextual input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) :=
  contextualAbsentAt_of_isContextual_eq_false value absent

/-- The first positive guard selects the import branch. -/
theorem plainTopItemImportBranchSelected {input : State}
    (importPresent : isKeyword input .importKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .importDecl :=
  .importDecl
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .importKw importPresent)

/-- A negative import guard followed by export selects export. -/
theorem plainTopItemExportBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportPresent : isKeyword input .exportKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .exportDecl :=
  .exportDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .exportKw exportPresent)

/-- The first three hard-keyword guards select pragma in priority order. -/
theorem plainTopItemPragmaBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaPresent : isKeyword input .pragmaKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .pragmaDecl :=
  .pragmaDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .pragmaKw pragmaPresent)

/-- The prioritized hard-keyword prefix selects a type alias. -/
theorem plainTopItemTypeAliasBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typePresent : isKeyword input .typeKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .typeAlias :=
  .typeAlias
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .typeKw typePresent)

/-- The prioritized hard-keyword prefix selects a module function. -/
theorem plainTopItemFunctionBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionPresent : isKeyword input .functionKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .functionDecl :=
  .functionDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .functionKw
      functionPresent)

/-- After the hard-keyword prefix, contextual enum selects enum. -/
theorem plainTopItemEnumBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumPresent : isContextual input .enum = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .enumDecl :=
  .enumDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenPresentAt_of_isContextual_eq_true .enum enumPresent)

/-- Contextual trait is selected only after enum is absent. -/
theorem plainTopItemTraitBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitPresent : isContextual input .trait = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .traitDecl :=
  .traitDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenPresentAt_of_isContextual_eq_true .trait traitPresent)

/-- Either positive half of the executable impl/default disjunction selects
the implementation branch. -/
theorem plainTopItemImplBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultPresent :
      (isContextual input .impl || isKeyword input .defaultKw) = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .implDecl := by
  apply DeclarativeGrammar.PlainTopItemBranchSelected.implDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
  rcases Bool.or_eq_true_iff.mp implOrDefaultPresent with
    implPresent | defaultPresent
  · exact Or.inl
      (plainTopItemTokenPresentAt_of_isContextual_eq_true .impl implPresent)
  · exact Or.inr
      (plainTopItemTokenPresentAt_of_isKeyword_eq_true .defaultKw
        defaultPresent)

/-- A false impl/default disjunction is split before selecting contract. -/
theorem plainTopItemContractBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultAbsent :
      (isContextual input .impl || isKeyword input .defaultKw) = false)
    (contractPresent : isKeyword input .contractKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .contractDecl := by
  rcases Bool.or_eq_false_iff.mp implOrDefaultAbsent with
    ⟨implAbsent, defaultAbsent⟩
  exact .contractDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .impl implAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .defaultKw defaultAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .contractKw
      contractPresent)

/-- If every declaration guard is false, the final unrecognized branch is
selected. -/
theorem plainTopItemUnrecognizedBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultAbsent :
      (isContextual input .impl || isKeyword input .defaultKw) = false)
    (contractAbsent : isKeyword input .contractKw = false) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .unrecognized := by
  rcases Bool.or_eq_false_iff.mp implOrDefaultAbsent with
    ⟨implAbsent, defaultAbsent⟩
  exact .unrecognized
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .impl implAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .defaultKw defaultAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .contractKw
      contractAbsent)

/-- `rejectAt` always retains the exact input state. -/
theorem plainTopItemRejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemOrdinaryRejectionSoundnessProperties
/-! Exact rejection reflection for broad attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable plain-top-item rejection records the exact selected child
rejection, or the final nonconsuming unrecognized branch. -/
theorem plainTopItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : plainTopItem input = .reject failure rejected) :
    DeclarativeGrammar.PlainTopItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    exact .importRejected
      (plainTopItemImportBranchSelected startsImport)
      (importDecl_ordinaryOutcome_sound.2
        (mapTopItem_reject_result result))
  next importAbsent =>
    have importAbsentEq : isKeyword input .importKw = false :=
      Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      exact .exportRejected
        (plainTopItemExportBranchSelected importAbsentEq startsExport)
        (exportDecl_ordinaryOutcome_sound.2
          (mapTopItem_reject_result result))
    next exportAbsent =>
      have exportAbsentEq : isKeyword input .exportKw = false :=
        Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        exact .pragmaRejected
          (plainTopItemPragmaBranchSelected importAbsentEq exportAbsentEq
            startsPragma)
          (pragmaDecl_ordinaryOutcome_sound.2
            (mapTopItem_reject_result result))
      next pragmaAbsent =>
        have pragmaAbsentEq : isKeyword input .pragmaKw = false :=
          Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          exact .typeAliasRejected
            (plainTopItemTypeAliasBranchSelected importAbsentEq exportAbsentEq
              pragmaAbsentEq startsType)
            (typeAlias_ordinaryOutcome_sound.2
              (mapTopItem_reject_result result))
        next typeAbsent =>
          have typeAbsentEq : isKeyword input .typeKw = false :=
            Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            exact .functionRejected
              (plainTopItemFunctionBranchSelected importAbsentEq exportAbsentEq
                pragmaAbsentEq typeAbsentEq startsFunction)
              ((functionDecl_ordinaryOutcome_sound .module).2
                (mapTopItem_reject_result result))
          next functionAbsent =>
            have functionAbsentEq : isKeyword input .functionKw = false :=
              Bool.eq_false_iff.mpr functionAbsent
            split at result
            next startsEnum =>
              exact .enumRejected
                (plainTopItemEnumBranchSelected importAbsentEq exportAbsentEq
                  pragmaAbsentEq typeAbsentEq functionAbsentEq startsEnum)
                ((enumDecl_ordinaryOutcome_sound none).2
                  (mapTopItem_reject_result result))
            next enumAbsent =>
              have enumAbsentEq : isContextual input .enum = false :=
                Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                exact .traitRejected
                  (plainTopItemTraitBranchSelected importAbsentEq exportAbsentEq
                    pragmaAbsentEq typeAbsentEq functionAbsentEq enumAbsentEq
                    startsTrait)
                  (traitDecl_ordinaryOutcome_sound.2
                    (mapTopItem_reject_result result))
              next traitAbsent =>
                have traitAbsentEq : isContextual input .trait = false :=
                  Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  exact .implRejected
                    (plainTopItemImplBranchSelected importAbsentEq exportAbsentEq
                      pragmaAbsentEq typeAbsentEq functionAbsentEq enumAbsentEq
                      traitAbsentEq startsImpl)
                    (implDecl_ordinaryOutcome_sound.2
                      (mapTopItem_reject_result result))
                next implAbsent =>
                  have implAbsentEq :
                      (isContextual input .impl ||
                        isKeyword input .defaultKw) = false :=
                    Bool.eq_false_iff.mpr implAbsent
                  split at result
                  next startsContract =>
                    exact .contractRejected
                      (plainTopItemContractBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq implAbsentEq
                        startsContract)
                      (contractDecl_ordinaryOutcome_sound.2
                        (mapTopItem_reject_result result))
                  next contractAbsent =>
                    have contractAbsentEq :
                        isKeyword input .contractKw = false :=
                      Bool.eq_false_iff.mpr contractAbsent
                    rw [plainTopItemRejectAt_rejected_state_eq result]
                    exact .unrecognized
                      (plainTopItemUnrecognizedBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq implAbsentEq
                        contractAbsentEq)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemOrdinarySuccessSoundnessProperties
/-! Broad executable success reflection for the plain top-item dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable plain-top-item success follows the exact selected broad
declaration outcome. -/
theorem plainTopItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : plainTopItem input = .ok item output) :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    rcases mapTopItem_success_components result with
      ⟨declaration, declarationResult, rfl⟩
    exact .importDecl
      (plainTopItemImportBranchSelected startsImport)
      (importDecl_ordinaryOutcome_sound.1 declarationResult)
  next importAbsent =>
    have importAbsentEq := Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      rcases mapTopItem_success_components result with
        ⟨declaration, declarationResult, rfl⟩
      exact .exportDecl
        (plainTopItemExportBranchSelected importAbsentEq startsExport)
        (exportDecl_ordinaryOutcome_sound.1 declarationResult)
    next exportAbsent =>
      have exportAbsentEq := Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        rcases mapTopItem_success_components result with
          ⟨declaration, declarationResult, rfl⟩
        exact .pragmaDecl
          (plainTopItemPragmaBranchSelected importAbsentEq exportAbsentEq
            startsPragma)
          (pragmaDecl_ordinaryOutcome_sound.1 declarationResult)
      next pragmaAbsent =>
        have pragmaAbsentEq := Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          rcases mapTopItem_success_components result with
            ⟨declaration, declarationResult, rfl⟩
          exact .typeAlias
            (plainTopItemTypeAliasBranchSelected importAbsentEq exportAbsentEq
              pragmaAbsentEq startsType)
            (typeAlias_ordinaryOutcome_sound.1 declarationResult)
        next typeAbsent =>
          have typeAbsentEq := Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            rcases mapTopItem_success_components result with
              ⟨declaration, declarationResult, rfl⟩
            exact .functionDecl
              (plainTopItemFunctionBranchSelected importAbsentEq
                exportAbsentEq pragmaAbsentEq typeAbsentEq startsFunction)
              ((functionDecl_ordinaryOutcome_sound .module).1
                declarationResult)
          next functionAbsent =>
            have functionAbsentEq := Bool.eq_false_iff.mpr functionAbsent
            split at result
            next startsEnum =>
              rcases mapTopItem_success_components result with
                ⟨declaration, declarationResult, rfl⟩
              exact .enumDecl
                (plainTopItemEnumBranchSelected importAbsentEq exportAbsentEq
                  pragmaAbsentEq typeAbsentEq functionAbsentEq startsEnum)
                ((enumDecl_ordinaryOutcome_sound none).1 declarationResult)
            next enumAbsent =>
              have enumAbsentEq := Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                rcases mapTopItem_success_components result with
                  ⟨declaration, declarationResult, rfl⟩
                exact .traitDecl
                  (plainTopItemTraitBranchSelected importAbsentEq
                    exportAbsentEq pragmaAbsentEq typeAbsentEq
                    functionAbsentEq enumAbsentEq startsTrait)
                  (traitDecl_ordinaryOutcome_sound.1 declarationResult)
              next traitAbsent =>
                have traitAbsentEq := Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  rcases mapTopItem_success_components result with
                    ⟨declaration, declarationResult, rfl⟩
                  exact .implDecl
                    (plainTopItemImplBranchSelected importAbsentEq
                      exportAbsentEq pragmaAbsentEq typeAbsentEq
                      functionAbsentEq enumAbsentEq traitAbsentEq startsImpl)
                    (implDecl_ordinaryOutcome_sound.1 declarationResult)
                next implAbsent =>
                  have implAbsentEq := Bool.eq_false_iff.mpr implAbsent
                  split at result
                  next startsContract =>
                    rcases mapTopItem_success_components result with
                      ⟨declaration, declarationResult, rfl⟩
                    exact .contractDecl
                      (plainTopItemContractBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq
                        implAbsentEq startsContract)
                      (contractDecl_ordinaryOutcome_sound.1 declarationResult)
                  next contractAbsent =>
                    simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PlainTopItemOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for plain top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package unconditional executable success and exact selected-branch
rejection for attribute-free top items. -/
theorem plainTopItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      plainTopItem input = .ok item output →
        DeclarativeGrammar.PlainTopItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      plainTopItem input = .reject failure rejected →
        DeclarativeGrammar.PlainTopItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨plainTopItem_success_ordinaryOutcome_sound,
    plainTopItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad plain-top-item outcomes. -/
theorem plainTopItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PlainTopItemOrdinaryParses
      DeclarativeGrammar.PlainTopItemRejects :=
  DeclarativeGrammar.plainTopItemDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem topItemHashPresentAt_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .hash = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt
      input.declarativeRemainder (.symbol .hash) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .hash .topItem result).1⟩

/-- Every executable top-item success follows the exact plain or derive-aware
broad ordinary branch, without a diagnostic-free premise. -/
theorem topItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : topItem input = .ok item output) :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_ordinaryOutcome_sound.1 result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject failure rejected => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases plainResult : plainTopItem afterDerive with
          | invariant error => simp [plainResult] at result
          | reject failure rejected => simp [plainResult] at result
          | ok plainItem afterPlain =>
              simp only [plainResult] at result
              have attachment :=
                attachDeriveAttribute_success_ordinaryOutcome_sound result
              rw [attachment.2]
              exact .derived
                (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_ordinaryOutcome_sound.1 deriveResult)
                (plainTopItem_ordinaryOutcome_sound.1 plainResult)
                attachment.1

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemOrdinaryRejectionSoundnessProperties
/-! Broad ordinary-rejection reflection for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable top-item rejection records the exact first rejecting
stage. Pure derive attachment cannot reject. -/
theorem topItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : topItem input = .reject failure rejected) :
    DeclarativeGrammar.TopItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plainRejected
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_ordinaryOutcome_sound.2 result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject deriveFailure deriveRejected =>
          simp only [deriveResult] at result
          cases result
          exact .deriveRejected
            (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
            (deriveAttribute_ordinaryOutcome_sound.2 deriveResult)
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases plainResult : plainTopItem afterDerive with
          | invariant error => simp [plainResult] at result
          | reject plainFailure plainRejected =>
              simp only [plainResult] at result
              cases result
              exact .derivedPlainRejected
                (topItemHashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_ordinaryOutcome_sound.1 deriveResult)
                (plainTopItem_ordinaryOutcome_sound.2 plainResult)
          | ok plainItem afterPlain =>
              simp only [plainResult] at result
              rcases attachDeriveAttribute_total_success derive plainItem
                  afterPlain with
                ⟨attached, output, attachedResult⟩
              rw [attachedResult] at result
              contradiction

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package unconditional executable success and exact selected-stage
rejection for complete derive-aware top items. -/
theorem topItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      topItem input = .ok item output →
        DeclarativeGrammar.TopItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      topItem input = .reject failure rejected →
        DeclarativeGrammar.TopItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨topItem_success_ordinaryOutcome_sound,
    topItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-aware top-item outcomes. -/
theorem topItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses
      DeclarativeGrammar.TopItemRejects :=
  DeclarativeGrammar.topItemDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemExactnessProperties
/-! Unconditional executable exactness for plain and derive-aware top items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Exact declaration outcomes close this public top-item boundary. -/
theorem plainTopItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PlainTopItemOrdinaryParses DeclarativeGrammar.PlainTopItemRejects :=
  DeclarativeGrammar.plainTopItemExactOutcomeSpec

/-- Successful top items agree on their complete located AST and remainder. -/
theorem plainTopItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : plainTopItem input = .ok left leftOutput)
    (rightResult : plainTopItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  plainTopItem_exactOutcomeSpec.successResultUnique
    (plainTopItem_success_ordinaryOutcome_sound leftResult)
    (plainTopItem_success_ordinaryOutcome_sound rightResult)

/-- Rejected top items agree on their complete declarative endpoint. -/
theorem plainTopItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : plainTopItem input = .reject leftFailure leftOutput)
    (rightResult : plainTopItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  plainTopItem_exactOutcomeSpec.rejectOutputUnique
    (plainTopItem_reject_ordinaryOutcome_sound leftResult)
    (plainTopItem_reject_ordinaryOutcome_sound rightResult)

/-- Exact declaration outcomes close this public top-item boundary. -/
theorem topItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects :=
  DeclarativeGrammar.topItemExactOutcomeSpec

/-- Successful top items agree on their complete located AST and remainder. -/
theorem topItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : topItem input = .ok left leftOutput)
    (rightResult : topItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  topItem_exactOutcomeSpec.successResultUnique
    (topItem_success_ordinaryOutcome_sound leftResult)
    (topItem_success_ordinaryOutcome_sound rightResult)

/-- Rejected top items agree on their complete declarative endpoint. -/
theorem topItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : topItem input = .reject leftFailure leftOutput)
    (rightResult : topItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  topItem_exactOutcomeSpec.rejectOutputUnique
    (topItem_reject_ordinaryOutcome_sound leftResult)
    (topItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LexedValidation
/-! Executable provenance validation for already-tokenized syntax input. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties`
-/

/-! Exact correspondence between executable and declarative lexed validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

private theorem orderedSpanCondition_true_iff
    (file : SourceFile) (previousEnd : Nat) (span : SourceSpan) :
    (span.isValidFor file &&
      decide (previousEnd ≤ span.startByte) &&
      decide (span.startByte < span.endByte)) = true ↔
      OrderedSpanAccepted file previousEnd span := by
  simp only [OrderedSpanAccepted, Bool.and_eq_true,
    SourceSpan.isValidFor_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨valid, ordered⟩, nonempty⟩
    exact ⟨valid, ordered, nonempty⟩
  · rintro ⟨valid, ordered, nonempty⟩
    exact ⟨⟨valid, ordered⟩, nonempty⟩

/-- A declarative token scan computes the identical executable result. -/
theorem tokens_eq_result_of_validationScans
    {file : SourceFile} {index previousEnd : Nat} {tokens : List Token}
    {result : Option IndexedSpan}
    (scan : TokenSpanValidationScans file index previousEnd tokens result) :
    LexedValidation.tokens file index previousEnd tokens =
      indexedSpanValidationResult ParserInvariantError.invalidTokenSpan
        result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.tokens]
      rw [if_neg (fun accepted =>
        invalid ((orderedSpanCondition_true_iff _ _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.tokens]
      rw [if_pos ((orderedSpanCondition_true_iff _ _ _).mpr accepted)]
      exact inductionHypothesis

/-- A declarative comment scan computes the identical executable result. -/
theorem comments_eq_result_of_validationScans
    {file : SourceFile} {index previousEnd : Nat}
    {comments : List Comment} {result : Option IndexedSpan}
    (scan : CommentSpanValidationScans file index previousEnd comments result) :
    LexedValidation.comments file index previousEnd comments =
      indexedSpanValidationResult ParserInvariantError.invalidCommentSpan
        result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.comments]
      rw [if_neg (fun accepted =>
        invalid ((orderedSpanCondition_true_iff _ _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.comments]
      rw [if_pos ((orderedSpanCondition_true_iff _ _ _).mpr accepted)]
      exact inductionHypothesis

/-- A declarative lexical-diagnostic scan computes the identical result. -/
theorem lexicalDiagnostics_eq_result_of_validationScans
    {file : SourceFile} {index : Nat}
    {diagnostics : List LexicalDiagnostic} {result : Option IndexedSpan}
    (scan : LexicalDiagnosticSpanValidationScans file index diagnostics
      result) :
    LexedValidation.lexicalDiagnostics file index diagnostics =
      indexedSpanValidationResult
        ParserInvariantError.invalidLexicalDiagnosticSpan result := by
  induction scan with
  | done => rfl
  | rejected invalid =>
      simp only [LexedValidation.lexicalDiagnostics]
      rw [if_neg (fun accepted =>
        invalid ((SourceSpan.isValidFor_eq_true_iff _ _).mp accepted))]
      rfl
  | continues accepted tail inductionHypothesis =>
      simp only [LexedValidation.lexicalDiagnostics]
      rw [if_pos ((SourceSpan.isValidFor_eq_true_iff _ _).mpr accepted)]
      exact inductionHypothesis

/-- The token validator always reflects one exact declarative scan. -/
theorem tokens_reflects_validationScans
    (file : SourceFile) (index previousEnd : Nat) (tokens : List Token) :
    ∃ result,
      TokenSpanValidationScans file index previousEnd tokens result ∧
        LexedValidation.tokens file index previousEnd tokens =
          indexedSpanValidationResult ParserInvariantError.invalidTokenSpan
            result := by
  rcases OrderedSpanValidationScans.exists_result file
      (fun token : Token => token.span) index previousEnd tokens with
    ⟨result, scan⟩
  exact ⟨result, scan, tokens_eq_result_of_validationScans scan⟩

/-- The comment validator always reflects one exact declarative scan. -/
theorem comments_reflects_validationScans
    (file : SourceFile) (index previousEnd : Nat)
    (comments : List Comment) :
    ∃ result,
      CommentSpanValidationScans file index previousEnd comments result ∧
        LexedValidation.comments file index previousEnd comments =
          indexedSpanValidationResult ParserInvariantError.invalidCommentSpan
            result := by
  rcases OrderedSpanValidationScans.exists_result file
      (fun comment : Comment => comment.span) index previousEnd comments with
    ⟨result, scan⟩
  exact ⟨result, scan, comments_eq_result_of_validationScans scan⟩

/-- The lexical-diagnostic validator reflects one exact declarative scan. -/
theorem lexicalDiagnostics_reflects_validationScans
    (file : SourceFile) (index : Nat)
    (diagnostics : List LexicalDiagnostic) :
    ∃ result,
      LexicalDiagnosticSpanValidationScans file index diagnostics result ∧
        LexedValidation.lexicalDiagnostics file index diagnostics =
          indexedSpanValidationResult
            ParserInvariantError.invalidLexicalDiagnosticSpan result := by
  rcases SpanValidationScans.exists_result file
      (fun diagnostic : LexicalDiagnostic => diagnostic.span)
      index diagnostics with ⟨result, scan⟩
  exact ⟨result, scan,
    lexicalDiagnostics_eq_result_of_validationScans scan⟩

/-- A whole-file declarative outcome computes the same preflight result. -/
theorem validateLexed_eq_result_of_outcome
    {file : SourceFile} {lexed : LexedFile}
    {result : Option LexedValidationFailure}
    (outcome : LexedFileValidationOutcome file lexed result) :
    validateLexed file lexed = lexedValidationResult result := by
  cases outcome with
  | sourceRejected mismatch =>
      unfold validateLexed
      rw [if_pos mismatch]
      rfl
  | tokenRejected sourceAccepted tokens =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rfl
  | commentRejected sourceAccepted tokens comments =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rfl
  | diagnosticRejected sourceAccepted tokens comments diagnostics =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rw [lexicalDiagnostics_eq_result_of_validationScans diagnostics]
      rfl
  | accepted sourceAccepted tokens comments diagnostics =>
      unfold validateLexed
      rw [if_neg (fun mismatch => mismatch sourceAccepted)]
      rw [tokens_eq_result_of_validationScans tokens]
      rw [comments_eq_result_of_validationScans comments]
      rw [lexicalDiagnostics_eq_result_of_validationScans diagnostics]
      rfl

/-- Executable preflight always reflects one exact declarative outcome. -/
theorem validateLexed_reflects_outcome
    (file : SourceFile) (lexed : LexedFile) :
    ∃ result,
      LexedFileValidationOutcome file lexed result ∧
        validateLexed file lexed = lexedValidationResult result := by
  rcases LexedFileValidationOutcome.exists_result file lexed with
    ⟨result, outcome⟩
  exact ⟨result, outcome, validateLexed_eq_result_of_outcome outcome⟩

/-- Executable preflight succeeds exactly on declarative acceptance. -/
theorem validateLexed_ok_iff_validationAccepts
    (file : SourceFile) (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔
      LexedFileValidationAccepts file lexed := by
  constructor
  · intro validated
    rcases validateLexed_reflects_outcome file lexed with
      ⟨result, outcome, equation⟩
    rw [validated] at equation
    cases result with
    | none => exact outcome
    | some failure => simp [lexedValidationResult] at equation
  · intro accepts
    simpa [lexedValidationResult] using
      validateLexed_eq_result_of_outcome accepts

/-- Executable preflight errors exactly with the mapped first rejection. -/
theorem validateLexed_error_iff_validationRejects
    (file : SourceFile) (lexed : LexedFile)
    (error : ParserInvariantError) :
    validateLexed file lexed = .error error ↔
      ∃ failure,
        LexedFileValidationRejects file lexed failure ∧
          error = lexedValidationInvariantError failure := by
  constructor
  · intro validated
    rcases validateLexed_reflects_outcome file lexed with
      ⟨result, outcome, equation⟩
    rw [validated] at equation
    cases result with
    | none => simp [lexedValidationResult] at equation
    | some failure =>
        exact ⟨failure, outcome,
          Except.error.inj equation⟩
  · rintro ⟨failure, rejects, rfl⟩
    simpa [lexedValidationResult] using
      validateLexed_eq_result_of_outcome rejects

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Nesting
/-! Bounded nesting preflight for the canonical syntax parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Nesting diagnostics from a valid lexer result retain source provenance. -/
theorem checkNesting_lexed_some_span_validFor
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file)
    {diagnostic : ParseDiagnostic}
    (result : checkNesting lexed.tokens = some diagnostic) :
    diagnostic.span.ValidFor file :=
  checkNesting_some_span_validFor file lexed.tokens lexedValid.tokens result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.NestingOutcomeSoundnessProperties`
-/

/-! Exact correspondence between executable and declarative nesting scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable checker always exposes one exact declarative outcome. -/
theorem checkNesting_reflects_outcome (tokens : List Token) :
    ∃ result,
      DeclarativeGrammar.NestingOutcome tokens result ∧
        checkNesting tokens = result.map nestingOverflowDiagnostic := by
  rcases DeclarativeGrammar.nestingOutcome_total tokens with
    clears | ⟨overflow, exceeds⟩
  · exact ⟨none, clears, checkNesting_eq_map_of_outcome clears⟩
  · exact ⟨some overflow, exceeds,
      checkNesting_eq_map_of_outcome exceeds⟩

/-- Executable success is equivalent to a clear declarative nesting scan. -/
theorem checkNesting_none_iff_nestingClears (tokens : List Token) :
    checkNesting tokens = none ↔
      DeclarativeGrammar.NestingClears tokens := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => exact outcome
    | some overflow => simp at equation
  · intro clears
    simpa using checkNesting_eq_map_of_outcome clears

/-- An executable diagnostic is exactly the mapped first declarative
overflow, including its span, dimension, and canonical bound. -/
theorem checkNesting_some_iff_nestingExceeds
    (tokens : List Token) (diagnostic : ParseDiagnostic) :
    checkNesting tokens = some diagnostic ↔
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => simp at equation
    | some overflow =>
        exact ⟨overflow, outcome, Option.some.inj equation⟩
  · rintro ⟨overflow, exceeds, rfl⟩
    simpa using checkNesting_eq_map_of_outcome exceeds

/-- Package both ordinary executable nesting outcomes. -/
theorem checkNesting_ordinaryOutcome_sound (tokens : List Token) :
    (checkNesting tokens = none →
      DeclarativeGrammar.NestingClears tokens) ∧
    (∀ diagnostic, checkNesting tokens = some diagnostic →
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow) :=
  ⟨(checkNesting_none_iff_nestingClears tokens).mp,
    fun diagnostic =>
      (checkNesting_some_iff_nestingExceeds tokens diagnostic).mp⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Preflight
set_option autoImplicit false

namespace Solcore.Syntax.Parser.State

/-- Canonical root-state construction preserves validated lexer provenance. -/
theorem initial_validFor {file : SourceFile} {lexed : LexedFile}
    (valid : lexed.ValidFor file) :
    (initial file lexed).ValidFor := by
  exact {
    tokens := by simpa [initial] using valid.tokens
    cursor_le_endIndex := Nat.zero_le _
    endIndex_le_size := by simp [initial]
    endByte_le_source := Nat.le_refl _
    endByte_boundary := isUtf8Boundary_end file.content
    diagnosticsRev := by simp [initial]
  }

end Solcore.Syntax.Parser.State

namespace Solcore.Syntax.Parser

private theorem validateTokens_sound (file : SourceFile)
    (index previousEnd : Nat) (tokens : List Token)
    (result : LexedValidation.tokens file index previousEnd tokens = .ok ()) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      previousEnd tokens := by
  induction tokens generalizing index previousEnd with
  | nil => trivial
  | cons token rest ih =>
      simp only [LexedValidation.tokens] at result
      split at result
      · rename_i accepted
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff] at accepted
        rcases accepted with ⟨⟨spanValid, afterPrevious⟩, nonempty⟩
        exact ⟨spanValid, of_decide_eq_true afterPrevious,
          of_decide_eq_true nonempty,
          ih (index := index + 1) (previousEnd := token.span.endByte)
            result⟩
      · contradiction

private theorem validateComments_sound (file : SourceFile)
    (index previousEnd : Nat) (comments : List Comment)
    (result : LexedValidation.comments file index previousEnd comments = .ok ()) :
    SpanSequence.ValidFor file (fun comment : Comment => comment.span)
      previousEnd comments := by
  induction comments generalizing index previousEnd with
  | nil => trivial
  | cons comment rest ih =>
      simp only [LexedValidation.comments] at result
      split at result
      · rename_i accepted
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff] at accepted
        rcases accepted with ⟨⟨spanValid, afterPrevious⟩, nonempty⟩
        exact ⟨spanValid, of_decide_eq_true afterPrevious,
          of_decide_eq_true nonempty,
          ih (index := index + 1) (previousEnd := comment.span.endByte)
            result⟩
      · contradiction

private theorem validateLexicalDiagnostics_sound (file : SourceFile)
    (index : Nat) (diagnostics : List LexicalDiagnostic)
    (result : LexedValidation.lexicalDiagnostics file index diagnostics = .ok ()) :
    ∀ diagnostic ∈ diagnostics, diagnostic.span.ValidFor file := by
  induction diagnostics generalizing index with
  | nil => simp
  | cons head tail ih =>
      simp only [LexedValidation.lexicalDiagnostics] at result
      split at result
      · rename_i accepted
        intro diagnostic member
        rcases List.mem_cons.mp member with rfl | member
        · exact (SourceSpan.isValidFor_eq_true_iff diagnostic.span file).mp
            accepted
        · exact ih (index := index + 1) result diagnostic member
      · contradiction

private theorem validateTokens_complete (file : SourceFile)
    (index previousEnd : Nat) (tokens : List Token)
    (valid : SpanSequence.ValidFor file
      (fun token : Token => token.span) previousEnd tokens) :
    LexedValidation.tokens file index previousEnd tokens = .ok () := by
  induction tokens generalizing index previousEnd with
  | nil => rfl
  | cons token rest ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨spanValid, afterPrevious, nonempty, restValid⟩
      simp only [LexedValidation.tokens]
      have accepted :
          (token.span.isValidFor file &&
            decide (previousEnd ≤ token.span.startByte) &&
            decide (token.span.startByte < token.span.endByte)) = true := by
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff]
        exact ⟨⟨spanValid, decide_eq_true afterPrevious⟩,
          decide_eq_true nonempty⟩
      rw [if_pos accepted]
      exact ih (index := index + 1)
        (previousEnd := token.span.endByte) restValid

private theorem validateComments_complete (file : SourceFile)
    (index previousEnd : Nat) (comments : List Comment)
    (valid : SpanSequence.ValidFor file
      (fun comment : Comment => comment.span) previousEnd comments) :
    LexedValidation.comments file index previousEnd comments = .ok () := by
  induction comments generalizing index previousEnd with
  | nil => rfl
  | cons comment rest ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨spanValid, afterPrevious, nonempty, restValid⟩
      simp only [LexedValidation.comments]
      have accepted :
          (comment.span.isValidFor file &&
            decide (previousEnd ≤ comment.span.startByte) &&
            decide (comment.span.startByte < comment.span.endByte)) = true := by
        simp only [Bool.and_eq_true,
          SourceSpan.isValidFor_eq_true_iff]
        exact ⟨⟨spanValid, decide_eq_true afterPrevious⟩,
          decide_eq_true nonempty⟩
      rw [if_pos accepted]
      exact ih (index := index + 1)
        (previousEnd := comment.span.endByte) restValid

private theorem validateLexicalDiagnostics_complete (file : SourceFile)
    (index : Nat) (diagnostics : List LexicalDiagnostic)
    (valid : ∀ diagnostic ∈ diagnostics,
      diagnostic.span.ValidFor file) :
    LexedValidation.lexicalDiagnostics file index diagnostics = .ok () := by
  induction diagnostics generalizing index with
  | nil => rfl
  | cons head tail ih =>
      simp only [LexedValidation.lexicalDiagnostics]
      have headValid : head.span.isValidFor file = true :=
        (SourceSpan.isValidFor_eq_true_iff head.span file).mpr
          (valid head (by simp))
      rw [if_pos headValid]
      apply ih (index := index + 1)
      intro diagnostic member
      exact valid diagnostic (by simp [member])

/-- Successful parser preflight exposes its complete declarative contract. -/
theorem validateLexed_ok_validFor (file : SourceFile) (lexed : LexedFile)
    (result : validateLexed file lexed = .ok ()) :
    lexed.ValidFor file := by
  unfold validateLexed at result
  split at result
  · contradiction
  · rename_i sourceAccepted
    cases tokensResult : LexedValidation.tokens file 0 0 lexed.tokens with
    | error error =>
        rw [tokensResult] at result
        contradiction
    | ok witness =>
        cases witness
        cases commentsResult : LexedValidation.comments file 0 0 lexed.comments with
        | error error =>
            rw [tokensResult, commentsResult] at result
            contradiction
        | ok witness =>
            cases witness
            cases diagnosticsResult :
                LexedValidation.lexicalDiagnostics file 0 lexed.diagnostics with
            | error error =>
                rw [tokensResult, commentsResult, diagnosticsResult] at result
                contradiction
            | ok witness =>
                cases witness
                refine {
                  source_eq := ?_
                  tokens := validateTokens_sound file 0 0 lexed.tokens ?_
                  comments := validateComments_sound file 0 0 lexed.comments ?_
                  diagnostics := validateLexicalDiagnostics_sound file 0
                    lexed.diagnostics ?_
                }
                · exact Decidable.of_not_not sourceAccepted
                · exact tokensResult
                · exact commentsResult
                · exact diagnosticsResult

/-- Every declaratively valid lexer result passes parser preflight. -/
theorem validateLexed_validFor_ok (file : SourceFile) (lexed : LexedFile)
    (valid : lexed.ValidFor file) :
    validateLexed file lexed = .ok () := by
  unfold validateLexed
  have sourceAccepted : ¬ lexed.source ≠ file.id := by
    intro rejected
    exact rejected valid.source_eq
  rw [if_neg sourceAccepted]
  rw [validateTokens_complete file 0 0 lexed.tokens valid.tokens]
  rw [validateComments_complete file 0 0 lexed.comments valid.comments]
  exact validateLexicalDiagnostics_complete file 0
    lexed.diagnostics valid.diagnostics

/-- Parser preflight decides the complete declarative lexer contract. -/
theorem validateLexed_ok_iff_validFor (file : SourceFile)
    (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔ lexed.ValidFor file :=
  ⟨validateLexed_ok_validFor file lexed,
    validateLexed_validFor_ok file lexed⟩

end Solcore.Syntax.Parser
end
