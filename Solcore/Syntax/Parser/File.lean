import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.Parser.Function
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.Pragma
import Solcore.Syntax.Parser.TopLevel
import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.Parser.Trait
import Solcore.Syntax.Parser.TypeAlias

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

def wrapTypeAlias (declaration : TypeAliasDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

def wrapImport (declaration : ImportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .importDecl declaration
}

def wrapExport (declaration : ExportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .exportDecl declaration
}

def wrapPragma (declaration : PragmaDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .pragmaDecl declaration
}

def wrapFunction (declaration : FunctionDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .function declaration
}

def wrapEnum (declaration : EnumDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .enum declaration
}

def wrapTrait (declaration : TraitDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .trait declaration
}

def wrapImpl (declaration : ImplDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .impl declaration
}

def wrapContract (declaration : ContractDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .contract declaration
}

def extendTopItemStart (prefixSpan : SourceSpan)
    (item : TopItem) : TopItem :=
  let span := SourceSpan.cover prefixSpan item.span
  let value := match item.value with
    | .importDecl declaration => .importDecl { declaration with span }
    | .exportDecl declaration => .exportDecl { declaration with span }
    | .pragmaDecl declaration => .pragmaDecl { declaration with span }
    | .typeAlias declaration => .typeAlias { declaration with span }
    | .enum declaration => .enum { declaration with span }
    | .trait declaration => .trait { declaration with span }
    | .impl declaration => .impl { declaration with span }
    | .contract declaration => .contract { declaration with span }
    | .function declaration => .function { declaration with span }
    | .error => .error
  { item with span, value }

end FileInternals

private def plainTopItem : Parser TopItem := fun state =>
  if isKeyword state .importKw then
    match importDecl state with
    | .ok declaration next => .ok (FileInternals.wrapImport declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .exportKw then
    match exportDecl state with
    | .ok declaration next => .ok (FileInternals.wrapExport declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .pragmaKw then
    match pragmaDecl state with
    | .ok declaration next => .ok (FileInternals.wrapPragma declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .typeKw then
    match typeAlias state with
    | .ok declaration next =>
        .ok (FileInternals.wrapTypeAlias declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .functionKw then
    match functionDecl .module state with
    | .ok declaration next => .ok (FileInternals.wrapFunction declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isContextual state .enum then
    match enumDecl none state with
    | .ok declaration next => .ok (FileInternals.wrapEnum declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isContextual state .trait then
    match traitDecl state with
    | .ok declaration next => .ok (FileInternals.wrapTrait declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isContextual state .impl || isKeyword state .defaultKw then
    match implDecl state with
    | .ok declaration next => .ok (FileInternals.wrapImpl declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .contractKw then
    match contractDecl state with
    | .ok declaration next => .ok (FileInternals.wrapContract declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    rejectAt state { head := .topItem, tail := [] } .topItem

namespace FileInternals

def attachDeriveAttribute (derive : DeriveAttribute)
    (item : TopItem) : Parser TopItem :=
  match item.value with
  | .enum declaration =>
      let span := SourceSpan.cover derive.span declaration.span
      pure {
        item with
        span
        value := .enum {
          declaration with
          span
          value := { declaration.value with
            deriveAttribute := some derive
          }
        }
      }
  | _ => do
      let _ ← emitDiagnostic {
        span := derive.span
        kind := .constraintViolation .deriveOnlyEnum
      }
      pure (extendTopItemStart derive.span item)

end FileInternals

/-- Parse one top-level form, including an optional derive attribute. -/
private def topItem : Parser TopItem := fun state =>
  if isSymbol state .hash then
    match deriveAttribute state with
    | .ok derive afterDerive =>
        match plainTopItem afterDerive with
        | .ok item next => FileInternals.attachDeriveAttribute derive item next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    plainTopItem state

namespace FileInternals

def finishRecoveredTopItem (first last : SourceSpan)
    (state : State) : Reply TopItem :=
  let span := SourceSpan.cover first last
  .ok {
    span
    leadingComments := []
    value := .error
  } (state.emit {
    span
    kind := .recovered .topItem
  })

def recoverTopItemAux (first last : SourceSpan) :
    Nat → State → Reply TopItem
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || atTopItemStart state then
        finishRecoveredTopItem first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTopItemAux first token.span fuel next
        | none => finishRecoveredTopItem first last state

def recoverTopItem (state : State) : Reply TopItem :=
  match state.advance? with
  | some (token, next) =>
      recoverTopItemAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .topItem, tail := [] } .topItem

end FileInternals

private def parseItems :
    Nat → List TopItem → State → Reply (List TopItem)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if state.atEnd then
        .ok itemsRev.reverse state
      else
        match topItem state with
        | .ok item next =>
            if next.cursor > state.cursor then
              parseItems fuel (item :: itemsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure failedState =>
            let rewound := {
              failedState with
              cursor := state.cursor
            }
            if atTopItemStart state then
              -- Rust recovery also refuses to consume a recognized item start.
              .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
            else
              -- The enclosing recovery diagnostic replaces its inner failure.
              match FileInternals.recoverTopItem rewound with
              | .ok item next =>
                  parseItems fuel (item :: itemsRev) next
              | .reject recoveryFailure next =>
                  .reject recoveryFailure next
              | .invariant error => .invariant error
        | .invariant error => .invariant error

/-- Parse a complete token window into a source-owned syntax file. -/
def sourceFile (comments : List Comment) : Parser ParsedFile := fun state =>
  match parseItems (state.remainingCount + 1) [] state with
  | .ok items next => .ok {
      source := state.file.id
      span := SourceSpan.fullFile state.file
      items := items.map (attachTopItemComments state.file comments)
      comments
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
