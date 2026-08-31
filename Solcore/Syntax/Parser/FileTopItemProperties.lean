import Solcore.Syntax.Parser.File
import Solcore.Syntax.Parser.Validity
import Solcore.Syntax.CoreTermValidity
import Solcore.Syntax.FileValidity

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
