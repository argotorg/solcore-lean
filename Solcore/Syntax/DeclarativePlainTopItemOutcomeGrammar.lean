import Solcore.Syntax.DeclarativeContractDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeExportDeclOutcomeGrammar
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeImportDeclOutcomeGrammar
import Solcore.Syntax.DeclarativePragmaOutcomeGrammar
import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeTypeAliasOutcomeGrammar

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
