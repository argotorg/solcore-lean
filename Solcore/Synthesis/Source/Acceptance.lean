import Lean.Data.Json
import Solcore.Core.Syntax

/-! Which generated runtime-input functions a profile accepts. Every profile
keeps its own filters; the identity filter also excludes a function that
returns each of its boundary inputs unchanged, which would exercise only the
ABI decoding and return of each path. Generated origins name the filter, so
replay applies the same one. Imported and reduced cases are never filtered. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source
open Lean
open Solcore.Core (Word)

/-- The acceptance filter of a generated runtime-input function. -/
inductive Acceptance where
  /-- The profile's own filters only; fixed corpora use this. -/
  | profile
  /-- The profile's own filters, then the exclusion of boundary identities. -/
  | nonIdentity
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Acceptance

def nonIdentityVersion : String := "exclude-boundary-identity-v1"

def ofVersion? (version : String) : Option Acceptance :=
  if version = nonIdentityVersion then some .nonIdentity else none

/-- The exclusion reason of every profile that applies the identity filter. -/
def identityReason : String := "every boundary input returned itself"

/-- Applied to the boundary results that the profile's own filter computed. -/
def check (acceptance : Acceptance) (inputs results : List Word) : Except String Unit :=
  match acceptance with
  | .profile => .ok ()
  | .nonIdentity => if results == inputs then .error identityReason else .ok ()

/-- Filtered origins name the filter; unfiltered origins are unchanged. -/
def record (acceptance : Acceptance) (origin : Json) : Json :=
  match acceptance with
  | .profile => origin
  | .nonIdentity => origin.setObjVal! "acceptance" (toJson nonIdentityVersion)

/-- The filter a saved generated origin names. -/
def ofOrigin (origin : Json) : Except String Acceptance :=
  match origin.getObjVal? "acceptance" with
  | .error _ => .ok .profile
  | .ok value =>
      match value.getStr? with
      | .ok version =>
          match ofVersion? version with
          | some acceptance => .ok acceptance
          | none => .error "unsupported acceptance filter"
      | .error _ => .error "unsupported acceptance filter"

end Acceptance

end Solcore.Synthesis.Source
