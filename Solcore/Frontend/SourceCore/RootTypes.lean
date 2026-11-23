import Solcore.Frontend.ProgramSignatures

/-!
# Root types

The types a root's signature may hold: those with a public value. A memory array, a slice and a memref
have none, so a root whose parameter or result type holds one anywhere is rejected, as the memory
arrays note's decision 5 states. Main declaration: `SourceCoreRootTypes.holdsView`.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRootTypes
open TypeSystem

/-- The declarations a type names, in any position. -/
def declarations : Ty → List Resolved.DeclarationId
  | .constructor (.declaration declaration) => [declaration]
  | .application leftPart rightPart
  | .function leftPart rightPart
  | .product leftPart rightPart
  | .mapping leftPart rightPart => declarations leftPart ++ declarations rightPart
  | .proxy inner
  | .comptime inner => declarations inner
  | .variable _
  | .parameter _
  | .constructor (.builtin _)
  | .error => []

/-- The payload types of a data declaration's constructors, as declared, over its own parameters. -/
def payloads (signatures : ProgramSignatures) (declaration : Resolved.DeclarationId) : List Ty :=
  match signatures.dataTypes.find? (fun data => data.id == declaration) with
  | some data => data.constructors.flatMap (·.payloadTypes)
  | none => []

/-- The declarations reachable from `found` through constructor payloads, closed under them, or `none`
when `fuel` rounds do not close them. -/
def reachable (signatures : ProgramSignatures) : Nat → List Resolved.DeclarationId →
    Option (List Resolved.DeclarationId)
  | 0, _ => none
  | fuel + 1, found =>
    let next := (found.flatMap fun declaration => (payloads signatures declaration).flatMap declarations).filter
      fun declaration => !found.contains declaration
    if next.isEmpty then some found else reachable signatures fuel (found ++ next.eraseDups)

/-- Whether a type has no public value: a memory array, a slice or a memref occurs in it, in a type
argument, a tuple, a function type or a mapping, or in a constructor payload of an enum it names,
directly or through other enums. A walk that does not close counts as holding one. -/
def holdsView (signatures : ProgramSignatures) (type : Ty) : Bool :=
  type.containsArray ||
    match reachable signatures (signatures.dataTypes.length + 2) (declarations type) with
    | none => true
    | some found => found.any fun declaration => (payloads signatures declaration).any (·.containsArray)

end Solcore.Frontend.SourceCoreRootTypes
