import Solcore.Syntax.Declaration

/-!
Parser-independent AST transformation performed when a derive attribute is
attached to one contract member.  Parser diagnostics and state are
intentionally outside this pure relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact pure result of attaching a derive attribute to a contract member.

Only enums retain the attribute.  Every other member keeps its variant and
payload while extending its outer and nested declaration spans. -/
inductive ContractDeriveAttaches :
    Syntax.DeriveAttribute → Syntax.ContractMember →
      Syntax.ContractMember → Prop where
  | field {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ContractField} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .field declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .field {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | function {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.FunctionDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .function declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .function {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | constructor {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ConstructorDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .constructor declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .constructor {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | fallback {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.FallbackDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .fallback declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .fallback {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | typeAlias {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.TypeAliasDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .typeAlias declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .typeAlias {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | enum {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.EnumDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
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
  | error {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .error
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .error
      }

end Solcore.Syntax.DeclarativeGrammar
