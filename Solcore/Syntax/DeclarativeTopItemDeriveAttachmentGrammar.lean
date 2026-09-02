import Solcore.Syntax.Declaration

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
