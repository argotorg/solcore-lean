import Solcore.Frontend.SourceCoreFaultSites

/-! Metadata for absent Word/Integer assignment operands. Header items lack their own
occurrence and span, so they use the owning for statement. Repeated items with
the same site, binder and kind share a diagnostic. Reasons never wrap. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignmentFaultSites

open SourceInference

inductive Kind where
  | value (operator : Syntax.ValueAssignOp)
  | bitNot
  deriving Repr, BEq, DecidableEq

structure Site where
  site : SourceCoreElaboration.ErrorSite
  binder : Resolved.LocalId
  kind : Kind
  span : Syntax.SourceSpan
  reason : Core.Word
  /-- Successful RHS values match this checked scalar assignment target type. -/
  rhsType : TypeSystem.Ty := .word
  deriving Repr, DecidableEq

structure Table where
  sites : List Site
  deriving Repr, DecidableEq

inductive Error where
  | reasonSpaceExhausted
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  deriving Repr, DecidableEq

def Site.diagnostic (site : Site) : SourceCoreFaultSites.Diagnostic := {
  error := match site.kind with
    | .value operator => .invalidAssignmentOperands operator none (some site.rhsType)
    | .bitNot => .invalidUnaryOperand .bitNot none
  site := site.site
  span := some site.span
}

def Table.length (table : Table) : Nat := table.sites.length

def Table.reasonAt (table : Table) (location : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (kind : Kind) : Core.Word :=
  match table.sites.find? fun site => decide
      (site.site = location ∧ site.binder = binder ∧ site.kind = kind) with
  | some site => site.reason
  | none => Core.Word.zero

def Table.diagnostics (table : Table) : List (Core.Word × SourceCoreFaultSites.Diagnostic) :=
  table.sites.map fun site => (site.reason, site.diagnostic)

def Table.diagnostic? (table : Table) (reason : Core.Word) : Option SourceCoreFaultSites.Diagnostic :=
  (table.sites.find? fun site => decide (site.reason = reason)).map Site.diagnostic

def add (owner : Resolved.DeclarationId) (firstReason : Nat) (sites : List Site)
    (location : SourceCoreElaboration.ErrorSite) (span : Syntax.SourceSpan)
    (assignment : AssignmentResolution) (kind : Kind) : Except Error (List Site) := do
  if assignment.target.root.owner ≠ owner then
    throw (.ownerMismatch owner assignment.target.root.owner)
  if assignment.target.type ≠ .word ∧ assignment.target.type ≠ .integer then return sites
  if sites.any (fun site => decide
      (site.site = location ∧ site.binder = assignment.target.root ∧ site.kind = kind)) then
    return sites
  let reason ← match Core.Word.ofNat? (firstReason + sites.length) with
    | some reason => pure reason
    | none => .error .reasonSpaceExhausted
  pure (sites ++ [{ site := location, binder := assignment.target.root, kind, span, reason, rhsType := assignment.target.type }])

def addItem (owner : Resolved.DeclarationId) (firstReason : Nat)
    (location : SourceCoreElaboration.ErrorSite) (span : Syntax.SourceSpan) :
    List Site → ForItemForm → Except Error (List Site)
  | sites, .assignValue assignment operator _ =>
      if operator = .equal then pure sites
      else add owner firstReason sites location span assignment (.value operator)
  | sites, .assignBitNot assignment => add owner firstReason sites location span assignment .bitNot
  | sites, _ => pure sites

def addStatement (owner : Resolved.DeclarationId) (firstReason : Nat)
    (sites : List Site) (node : StatementNode) : Except Error (List Site) := do
  if node.id.occurrence.owner ≠ owner then throw (.ownerMismatch owner node.id.occurrence.owner)
  let location := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  match node.form with
  | .assignValue assignment operator _ =>
      if operator = .equal then pure sites
      else add owner firstReason sites location node.span assignment (.value operator)
  | .assignBitNot assignment => add owner firstReason sites location node.span assignment .bitNot
  | .forLoop initializer _ post _ =>
      (initializer ++ post).foldlM (addItem owner firstReason location node.span) sites
  | _ => pure sites

/-- Inference records containing statements after their children. Sorting by
their original span restores source order before assigning diagnostic codes. -/
def prepare (source : TypedSource) (firstReason : Nat) : Except Error Table := do
  let statements := (source.nodes.filterMap fun
    | .statement node => some node
    | _ => none).mergeSort (fun left right => decide (left.span.startByte ≤ right.span.startByte))
  let sites ← statements.foldlM (addStatement source.owner firstReason) []
  pure { sites }

theorem Table.reasonAt_found {table : Table} {site : Site}
    {location : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {kind : Kind}
    (found : table.sites.find? (fun candidate => decide
      (candidate.site = location ∧ candidate.binder = binder ∧ candidate.kind = kind)) = some site) :
    table.reasonAt location binder kind = site.reason := by
  unfold Table.reasonAt
  rw [found]

theorem Table.diagnostic_found {table : Table} {site : Site}
    (found : table.sites.find? (fun candidate => decide (candidate.reason = site.reason)) = some site) :
    table.diagnostic? site.reason = some site.diagnostic := by
  simp [Table.diagnostic?, found]

end Solcore.Frontend.SourceCoreAssignmentFaultSites
