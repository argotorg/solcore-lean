import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Trivia
import Solcore.Syntax.Grammar.TermLevels
import Solcore.Syntax.Declaration

/-!
Declarative grammar of whole files.

This is where the main theorems' statements start. Main declarations:
`PublicSourceFileOrdinaryParses`, `SourceFileOrdinaryParses`, `TopItemOrdinaryParses`,
`PlainTopItemOrdinaryParses`, `FileItemsOrdinaryParses`, `CoreSourceFileOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainTopItemOutcomeGrammar
/-!
Parser-independent broad outcomes for the attribute-free top-item dispatcher.
Branch selection records the executable lookahead priority independently of
the selected declaration's own ordinary outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive evidence for one plain-top-item lookahead guard. -/
def PlainTopItemTokenPresentAt (input : Remainder)
    (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- The nine declaration branches and final rejecting branch, in priority
order. -/
inductive PlainTopItemBranch where
  | importDecl
  | exportDecl
  | pragmaDecl
  | typeAlias
  | functionDecl
  | enumDecl
  | traitDecl
  | implDecl
  | contractDecl
  | unrecognized
  deriving Repr, BEq, DecidableEq

/-- Exact guard evidence selecting one branch of the prioritized dispatcher. -/
inductive PlainTopItemBranchSelected :
    Remainder → PlainTopItemBranch → Prop where
  | importDecl {input : Remainder}
      (importPresent : PlainTopItemTokenPresentAt input
        (.keyword .importKw)) :
      PlainTopItemBranchSelected input .importDecl
  | exportDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportPresent : PlainTopItemTokenPresentAt input
        (.keyword .exportKw)) :
      PlainTopItemBranchSelected input .exportDecl
  | pragmaDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaPresent : PlainTopItemTokenPresentAt input
        (.keyword .pragmaKw)) :
      PlainTopItemBranchSelected input .pragmaDecl
  | typeAlias {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typePresent : PlainTopItemTokenPresentAt input (.keyword .typeKw)) :
      PlainTopItemBranchSelected input .typeAlias
  | functionDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionPresent : PlainTopItemTokenPresentAt input
        (.keyword .functionKw)) :
      PlainTopItemBranchSelected input .functionDecl
  | enumDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw))
      (enumPresent : PlainTopItemTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling)) :
      PlainTopItemBranchSelected input .enumDecl
  | traitDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling))
      (traitPresent : PlainTopItemTokenPresentAt input
        (.identifier ContextualKeyword.trait.spelling)) :
      PlainTopItemBranchSelected input .traitDecl
  | implDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling))
      (traitAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.trait.spelling))
      (implOrDefaultPresent :
        PlainTopItemTokenPresentAt input
            (.identifier ContextualKeyword.impl.spelling) ∨
          PlainTopItemTokenPresentAt input (.keyword .defaultKw)) :
      PlainTopItemBranchSelected input .implDecl
  | contractDecl {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling))
      (traitAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.trait.spelling))
      (implAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.impl.spelling))
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .defaultKw))
      (contractPresent : PlainTopItemTokenPresentAt input
        (.keyword .contractKw)) :
      PlainTopItemBranchSelected input .contractDecl
  | unrecognized {input : Remainder}
      (importAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .importKw))
      (exportAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .exportKw))
      (pragmaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling))
      (traitAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.trait.spelling))
      (implAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.impl.spelling))
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .defaultKw))
      (contractAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .contractKw)) :
      PlainTopItemBranchSelected input .unrecognized

/-- Exact broad success of the selected declaration and its wrapper AST. -/
inductive PlainTopItemOrdinaryParses :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | importDecl {input output : Remainder} {declaration : Syntax.ImportDecl}
      (selected : PlainTopItemBranchSelected input .importDecl)
      (parsed : ImportDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .importDecl declaration } output
  | exportDecl {input output : Remainder} {declaration : Syntax.ExportDecl}
      (selected : PlainTopItemBranchSelected input .exportDecl)
      (parsed : ExportDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .exportDecl declaration } output
  | pragmaDecl {input output : Remainder} {declaration : Syntax.PragmaDecl}
      (selected : PlainTopItemBranchSelected input .pragmaDecl)
      (parsed : PragmaDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .pragmaDecl declaration } output
  | typeAlias {input output : Remainder} {declaration : Syntax.TypeAliasDecl}
      (selected : PlainTopItemBranchSelected input .typeAlias)
      (parsed : TypeAliasDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .typeAlias declaration } output
  | functionDecl {input output : Remainder} {declaration : Syntax.FunctionDecl}
      (selected : PlainTopItemBranchSelected input .functionDecl)
      (parsed : FunctionDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .function declaration } output
  | enumDecl {input output : Remainder} {declaration : Syntax.EnumDecl}
      (selected : PlainTopItemBranchSelected input .enumDecl)
      (parsed : EnumDeclOrdinaryParses none input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .enum declaration } output
  | traitDecl {input output : Remainder} {declaration : Syntax.TraitDecl}
      (selected : PlainTopItemBranchSelected input .traitDecl)
      (parsed : TraitDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .trait declaration } output
  | implDecl {input output : Remainder} {declaration : Syntax.ImplDecl}
      (selected : PlainTopItemBranchSelected input .implDecl)
      (parsed : ImplDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .impl declaration } output
  | contractDecl {input output : Remainder} {declaration : Syntax.ContractDecl}
      (selected : PlainTopItemBranchSelected input .contractDecl)
      (parsed : ContractDeclOrdinaryParses input declaration output) :
      PlainTopItemOrdinaryParses input
        { span := declaration.span, leadingComments := [],
          value := .contract declaration } output

/-- Exact selected child rejection, or the final nonconsuming rejection when
no branch guard is recognized. -/
inductive PlainTopItemRejects : Remainder → Remainder → Prop where
  | importRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .importDecl)
      (rejectedChild : ImportDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | exportRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .exportDecl)
      (rejectedChild : ExportDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | pragmaRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .pragmaDecl)
      (rejectedChild : PragmaDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | typeAliasRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .typeAlias)
      (rejectedChild : TypeAliasDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | functionRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .functionDecl)
      (rejectedChild : FunctionDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | enumRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .enumDecl)
      (rejectedChild : EnumDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | traitRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .traitDecl)
      (rejectedChild : TraitDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | implRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .implDecl)
      (rejectedChild : ImplDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | contractRejected {input rejected : Remainder}
      (selected : PlainTopItemBranchSelected input .contractDecl)
      (rejectedChild : ContractDeclRejects input rejected) :
      PlainTopItemRejects input rejected
  | unrecognized {input : Remainder}
      (selected : PlainTopItemBranchSelected input .unrecognized) :
      PlainTopItemRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeGrammar
/-!
Parser-independent exact ordinary outcomes for top-item recovery. Recovery
consumes one mandatory token, scans up to the next top-item boundary, and
returns an error item without consuming that boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stops of the scan after recovery consumed its mandatory first
token. A missing carrier slot inside the active window finishes recovery. -/
inductive TopItemRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TopItemRecoveryStops input
  | boundary {input : Remainder}
      (starts : ImportTerminatorTopItemStartsAt input) :
      TopItemRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TopItemRecoveryStops input

/-- Canonical error item produced from the first and last consumed spans. -/
def recoveredTopItemValue (first last : SourceSpan) : Syntax.TopItem := {
  span := SourceSpan.cover first last
  leadingComments := []
  value := .error
}

/-- Exact priority-ordered scan after the mandatory first recovery token. -/
inductive TopItemRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.TopItem → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : TopItemRecoveryStops input) :
      TopItemRecoveryScanParses first last input
        (recoveredTopItemValue first last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {item : Syntax.TopItem}
      (continues : ¬ TopItemRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : TopItemRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } item output) :
      TopItemRecoveryScanParses first last input item output

/-- Successful recovery consumes one arbitrary current token before scanning. -/
inductive TopItemRecoveryParses :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {item : Syntax.TopItem}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : TopItemRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } item output) :
      TopItemRecoveryParses input item output

/-- Recovery rejects only when its mandatory first token is unavailable. -/
inductive TopItemRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TopItemRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TopItemRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFileGrammar
/-! Parser-independent grammar for complete comment-attached syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
Exact complete-file grammar over an abstract top-item judgment.

The item loop recognizes raw declarations with empty parser-time comment
fields.  The pure syntax trivia transformation then attaches the complete
source-order comment stream exactly as retained by the canonical AST.
-/
inductive SourceFileParses
    (itemParses : Remainder → Syntax.TopItem → Remainder → Prop)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    Remainder → Syntax.ParsedFile → Remainder → Prop where
  | parsed {input output : Remainder} {rawItems : List Syntax.TopItem}
      (itemsParsed : TopItemsParses itemParses input rawItems output) :
      SourceFileParses itemParses file comments input {
        source := file.id
        span := SourceSpan.fullFile file
        items := rawItems.map
          (Syntax.Trivia.attachTopItemComments file comments)
        comments
      } output

/-- A complete-file derivation consumes its whole active token window. -/
theorem SourceFileParses.output_atEnd
    {itemParses : Remainder → Syntax.TopItem → Remainder → Prop}
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input output : Remainder} {parsedFile : Syntax.ParsedFile}
    (parsed : SourceFileParses itemParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor := by
  cases parsed with
  | parsed itemsParsed => exact itemsParsed.output_atEnd

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreSourceFileOrdinaryGrammar
/-! Concrete ordinary grammar for complete canonical Core source files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concrete ordinary top-level item grammar using public Core terms and
isolated public bodies under their exact tail policies. -/
abbrev CoreTopItemOrdinaryParses :=
  TopItemParses CoreExpressionOrdinaryParses
    (IsolatedCoreBlockPublicOrdinaryParses .allow)
    (IsolatedCoreBlockPublicOrdinaryParses .require)

/-- Complete ordinary Core-file grammar with exact comment attachment. -/
abbrev CoreSourceFileOrdinaryParses (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) :=
  SourceFileParses CoreTopItemOrdinaryParses file comments

/-- Parser-independent complete-file judgment from the root token window to
its canonical terminal remainder. -/
def CoreSourceFileOrdinaryParsesFromStart (file : Syntax.SourceFile)
    (tokens : List Syntax.Token) (comments : List Syntax.Comment)
    (parsedFile : Syntax.ParsedFile) : Prop :=
  CoreSourceFileOrdinaryParses file comments {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := 0
    } parsedFile {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := tokens.length
    }

/-- A complete ordinary Core-file derivation reaches its active-window end. -/
theorem CoreSourceFileOrdinaryParses.output_atEnd
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input output : Remainder} {parsedFile : Syntax.ParsedFile}
    (parsed : CoreSourceFileOrdinaryParses file comments input parsedFile
      output) :
    output.endIndex ≤ output.cursor :=
  SourceFileParses.output_atEnd parsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemDeriveAttachmentGrammar
/-!
Parser-independent AST transformation performed when a derive attribute is
attached to one top-level item. Parser diagnostics and state are intentionally
outside this pure relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact pure result of attaching a derive attribute to a top-level item.

Only enums retain the attribute. Every other item keeps its variant and
payload while extending its outer and nested declaration spans. -/
inductive TopItemDeriveAttaches :
    Syntax.DeriveAttribute → Syntax.TopItem → Syntax.TopItem → Prop where
  | importDecl {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ImportDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .importDecl declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .importDecl {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | exportDecl {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ExportDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .exportDecl declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .exportDecl {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | pragmaDecl {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.PragmaDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .pragmaDecl declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .pragmaDecl {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | typeAlias {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.TypeAliasDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .typeAlias declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .typeAlias {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | enum {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.EnumDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .enum declaration
      } {
        span := SourceSpan.cover derive.span declaration.span
        leadingComments
        value := .enum {
          declaration with
          span := SourceSpan.cover derive.span declaration.span
          value := {
            declaration.value with
            deriveAttribute := some derive
          }
        }
      }
  | trait {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.TraitDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .trait declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .trait {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | impl {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ImplDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .impl declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .impl {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | contract {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ContractDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .contract declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .contract {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | function {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.FunctionDecl} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .function declaration
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .function {
          declaration with
          span := SourceSpan.cover derive.span itemSpan
        }
      }
  | error {derive : Syntax.DeriveAttribute} {itemSpan : SourceSpan}
      {leadingComments : List Syntax.Comment} :
      TopItemDeriveAttaches derive {
        span := itemSpan
        leadingComments
        value := .error
      } {
        span := SourceSpan.cover derive.span itemSpan
        leadingComments
        value := .error
      }

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for public top-item dispatch. The
leading-hash branch commits to derive parsing before plain dispatch and pure
attachment.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public top-item success, including pure derive attachment. The
attachment step does not change the plain parser's final remainder. -/
inductive TopItemOrdinaryParses :
    Remainder → Syntax.TopItem → Remainder → Prop where
  | plain {input output : Remainder} {item : Syntax.TopItem}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (plainParsed : PlainTopItemOrdinaryParses input item output) :
      TopItemOrdinaryParses input item output
  | derived {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute} {plainItem item : Syntax.TopItem}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (plainParsed : PlainTopItemOrdinaryParses afterDerive plainItem output)
      (attached : TopItemDeriveAttaches derive plainItem item) :
      TopItemOrdinaryParses input item output

/-- Exact first rejecting stage of public top-item dispatch. Pure attachment
has no rejecting outcome. -/
inductive TopItemRejects : Remainder → Remainder → Prop where
  | plainRejected {input rejected : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (plainRejected : PlainTopItemRejects input rejected) :
      TopItemRejects input rejected
  | deriveRejected {input rejected : Remainder}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveRejected : DeriveAttributeRejects input rejected) :
      TopItemRejects input rejected
  | derivedPlainRejected {input afterDerive rejected : Remainder}
      {derive : Syntax.DeriveAttribute}
      (hashPresent : PlainTopItemTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (plainRejected : PlainTopItemRejects afterDerive rejected) :
      TopItemRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFileItemsOutcomeGrammar
/-!
Parser-independent broad outcomes for the source-file item loop. The relation
retains source-order items, rewinds a rejected item to its original cursor,
and recovers only away from a recognized top-item boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A rejected top item retains its exact failed endpoint while preserving
the token carrier and active-window end needed for the file-loop rewind. -/
def TopItemRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, TopItemRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Forward-order exact successful outcomes of the recovery-aware file-item
loop, independent of its executable reverse accumulator. -/
inductive FileItemsOrdinaryParses :
    Remainder → List Syntax.TopItem → Remainder → Prop where
  | done {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      FileItemsOrdinaryParses input [] input
  | direct {input afterItem output : Remainder}
      {item : Syntax.TopItem} {items : List Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemParsed : TopItemOrdinaryParses input item afterItem)
      (progress : input.cursor < afterItem.cursor)
      (tail : FileItemsOrdinaryParses afterItem items output) :
      FileItemsOrdinaryParses input (item :: items) output
  | boundaryStop {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryPresent : ImportTerminatorTopItemStartsAt input) :
      FileItemsOrdinaryParses input [] input
  | recovered {input afterRecovery output : Remainder}
      {item : Syntax.TopItem} {items : List Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (recoveryParsed : TopItemRecoveryParses input item afterRecovery)
      (tail : FileItemsOrdinaryParses afterRecovery items output) :
      FileItemsOrdinaryParses input (item :: items) output

/-- Exact first rejection of the prioritized recovery-aware file-item loop.
Ordinary top-item rejection itself is rewound; only recovery or a later loop
step can reject. -/
inductive FileItemsRejects : Remainder → Remainder → Prop where
  | recoveryRejected {input rejected : Remainder}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (rejectedRecovery : TopItemRecoveryRejects input rejected) :
      FileItemsRejects input rejected
  | laterDirect {input afterItem rejected : Remainder}
      {item : Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemParsed : TopItemOrdinaryParses input item afterItem)
      (progress : input.cursor < afterItem.cursor)
      (tailRejected : FileItemsRejects afterItem rejected) :
      FileItemsRejects input rejected
  | laterRecovered {input afterRecovery rejected : Remainder}
      {item : Syntax.TopItem}
      (inside : input.cursor < input.endIndex)
      (itemRejected : TopItemRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ImportTerminatorTopItemStartsAt input)
      (recoveryParsed : TopItemRecoveryParses input item afterRecovery)
      (tailRejected : FileItemsRejects afterRecovery rejected) :
      FileItemsRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSourceFileOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recovery-aware file success followed by the pure source-order
comment attachment used by the canonical AST. -/
inductive SourceFileOrdinaryParses
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    Remainder → Syntax.ParsedFile → Remainder → Prop where
  | parsed {input output : Remainder} {rawItems : List Syntax.TopItem}
      (itemsParsed : FileItemsOrdinaryParses input rawItems output) :
      SourceFileOrdinaryParses file comments input {
        source := file.id
        span := SourceSpan.fullFile file
        items := rawItems.map
          (Syntax.Trivia.attachTopItemComments file comments)
        comments
      } output

/-- Complete-file rejection is exactly the item loop's first rejection. -/
inductive SourceFileRejects : Remainder → Remainder → Prop where
  | itemsRejected {input rejected : Remainder}
      (rejection : FileItemsRejects input rejected) :
      SourceFileRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePublicSourceFileOutcomeGrammar
/-!
Parser-independent broad syntax outcomes at the public source-file boundary.
The relation intentionally exposes neither parser diagnostics nor the final
remainder hidden by the public result type.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Canonical root token window used after public nesting preflight clears. -/
def sourceFileRootRemainder (tokens : List Syntax.Token) : Remainder := {
  tokens := tokens.toArray
  endIndex := tokens.length
  cursor := 0
}

/-- Exact empty syntax value returned when bounded nesting is exceeded. -/
def nestingExceededParsedFile (file : Syntax.SourceFile)
    (comments : List Syntax.Comment) : Syntax.ParsedFile := {
  source := file.id
  span := SourceSpan.fullFile file
  items := []
  comments
}

/--
Broad syntax-only success at the public token-to-file boundary.

An overflowing nesting preflight returns the canonical empty file without
running the token grammar.  A clear preflight runs the recovery-aware file
grammar from the canonical root window; its final remainder is existentially
hidden because the public syntax result does not retain it.
-/
inductive PublicSourceFileOrdinaryParses
    (file : Syntax.SourceFile) (tokens : List Syntax.Token)
    (comments : List Syntax.Comment) : Syntax.ParsedFile → Prop where
  | nestingExceeded {overflow : NestingOverflow}
      (nesting : NestingExceeds tokens overflow) :
      PublicSourceFileOrdinaryParses file tokens comments
        (nestingExceededParsedFile file comments)
  | sourceFile {parsedFile : Syntax.ParsedFile} {final : Remainder}
      (nesting : NestingClears tokens)
      (parsed : SourceFileOrdinaryParses file comments
        (sourceFileRootRemainder tokens) parsedFile final) :
      PublicSourceFileOrdinaryParses file tokens comments parsedFile

end Solcore.Syntax.DeclarativeGrammar
end
