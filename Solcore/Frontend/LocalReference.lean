import Solcore.Syntax.Term
import Solcore.Resolved.Expr

/-! A deliberately narrow canonical-syntax adapter. The caller supplies the
ordered name table; first match specifies table behavior, not a source-language
shadowing or allocation policy. No global, import, or class resolution occurs. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Explicit caller-supplied spellings and already assigned local identities. -/
abbrev LocalNameTable := List (String × Resolved.LocalId)

namespace LocalNameTable

/-- Exact spelling lookup; neither source ranges nor spelling normalization participate. -/
def lookup? : LocalNameTable → String → Option Resolved.LocalId
  | [], _ => none
  | (candidate, id) :: table, spelling =>
      if candidate = spelling then some id else lookup? table spelling

/-- Independent first-occurrence lookup, including repeated caller-supplied names. -/
inductive Lookup : LocalNameTable → String → Resolved.LocalId → Prop where
  | head {table spelling id} : Lookup ((spelling, id) :: table) spelling id
  | tail {table spelling candidate id candidateId}
      (different : candidate ≠ spelling) (found : Lookup table spelling id) :
      Lookup ((candidate, candidateId) :: table) spelling id

end LocalNameTable

/-- Only a named reference, optionally grouped, is supported here. `none` means
unmapped or unsupported by this adapter, not rejection by the source language.
`Identifier.value` contains the exact spelling; no lexical or span validity is assumed. -/
def resolveLocalReference? (table : LocalNameTable) (source : Syntax.Expr) :
    Option Resolved.Expr :=
  match source with
  | ⟨_, .identifier name⟩ => (table.lookup? name.value).map Resolved.Expr.var
  | ⟨_, .group inner⟩ => resolveLocalReference? table inner
  | _ => none
termination_by sizeOf source

/-- A parser-independent bridge from canonical reference syntax to a supplied ID. -/
inductive ResolvesLocalReference (table : LocalNameTable) :
    Syntax.Expr → Resolved.LocalId → Prop where
  | identifier {span : Syntax.SourceSpan} {name : Syntax.Identifier} {id : Resolved.LocalId}
      (found : LocalNameTable.Lookup table name.value id) :
      ResolvesLocalReference table { span, value := .identifier name } id
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {id : Resolved.LocalId}
      (resolved : ResolvesLocalReference table inner id) :
      ResolvesLocalReference table { span, value := .group inner } id

end Solcore.Frontend
