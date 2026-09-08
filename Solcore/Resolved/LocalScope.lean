import Solcore.Resolved.Identity

/-! Generic local identity tables with explicit first-match behavior, even
when an input table repeats an identity. This does not choose source-language
shadowing rules or allocate fresh identities. -/

set_option autoImplicit false

namespace Solcore.Resolved

abbrev LocalScope (α : Type) := List (LocalId × α)

namespace LocalScope

def ids {α : Type} (scope : LocalScope α) : List LocalId := scope.map Prod.fst

def values {α : Type} (scope : LocalScope α) : List α := scope.map Prod.snd

def lookup? {α : Type} : LocalScope α → LocalId → Option α
  | [], _ => none
  | (candidate, value) :: scope, id =>
      if candidate = id then some value else lookup? scope id

def index? : List LocalId → LocalId → Option Nat
  | [], _ => none
  | candidate :: scope, id =>
      if candidate = id then some 0 else (index? scope id).map Nat.succ

/-- A witness selects the first entry with the requested identity. -/
inductive Lookup {α : Type} : LocalScope α → LocalId → α → Prop where
  | head {scope : LocalScope α} {id : LocalId} {value : α} :
      Lookup ((id, value) :: scope) id value
  | tail {scope : LocalScope α} {candidate id : LocalId} {headValue value : α}
      (different : candidate ≠ id) (found : Lookup scope id value) :
      Lookup ((candidate, headValue) :: scope) id value

/-- A position witness records the first occurrence of an identity. -/
inductive IndexOf : List LocalId → LocalId → Nat → Prop where
  | head {scope : List LocalId} {id : LocalId} : IndexOf (id :: scope) id 0
  | tail {scope : List LocalId} {candidate id : LocalId} {index : Nat}
      (different : candidate ≠ id) (found : IndexOf scope id index) :
      IndexOf (candidate :: scope) id (index + 1)

end LocalScope

end Solcore.Resolved
