import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation

/-! Proof receipts for the actual compatible diagnostic preparation. These
retain the original base and final rows, numeric bounds and read separation.
Source occurrence ownership and index priority require independent receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticAssociation

/-- Original reads remain separate from every actually issued fixed row. -/
def ReadSafe (reads : List SourceCoreFaultSites.ReadSite) (fixed : List (Word × Diagnostic)) : Prop :=
  ∀ read, read ∈ reads → ∀ row, row ∈ fixed → read.reason ≠ row.1

/-- The actual fresh fixed token lies above every original read. -/
theorem ReadSafe.append {reads : List SourceCoreFaultSites.ReadSite}
    {fixed : List (Word × Diagnostic)} (safe : ReadSafe reads fixed)
    {next : Nat} (below : ∀ read, read ∈ reads → read.reason.val < next)
    {reason : Word} (number : reason.val = next) (diagnostic : Diagnostic) :
    ReadSafe reads (fixed ++ [(reason, diagnostic)]) := by
  intro read member row rowMember
  rcases List.mem_append.mp rowMember with old | fresh
  · exact safe read member row old
  · have sameRow := List.mem_singleton.mp fresh
    subst row
    intro same
    have equal := congrArg Fin.val same
    have bounded := below read member
    change read.reason.val = reason.val at equal
    omega

/-- All fields refer to the one accepted base and the actual final rows. -/
structure ReservedAt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (plan : Plan) (root : Key) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context)
    (base : SourceCoreProgramFaultSites.Program) (extra : List (Word × Diagnostic)) : Prop where
  baseAccepted : SourceCoreProgramFaultSites.prepare plan root = .ok base
  sameBase : program.program.base = base
  sameExpressionBase : program.program.expressions.base = base
  sameRoot : program.program.rootTable = {base.rootTable with additional := program.fixed ++ extra}
  sameExpressionRoot : program.program.expressions.rootTable =
    {base.rootTable with additional := program.fixed ++ extra}
  extraAccepted : missingDiagnostics context.registry program.missing = .ok extra
  legacy : Ranges context.registry.limits.maxEntries program.missing ∧
    (∀ site, site ∈ program.missing → 0 < site.base.val) ∧
    (∀ site, site ∈ program.missing → ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < row.1.val) ∧
    (∀ site, site ∈ program.missing →
      program.program.rootTable.escapedReason.val ≤ site.base.val ∨
        site.base.val + context.registry.limits.maxEntries < program.program.rootTable.escapedReason.val)
  positive : 0 < program.nextReason
  missingBelow : ∀ site, site ∈ program.missing →
    site.base.val + context.registry.limits.maxEntries < program.nextReason
  fixedBelow : ∀ row, row ∈ program.fixed → row.1.val < program.nextReason
  readsBelow : ∀ read, read ∈ base.rootTable.reads → read.reason.val < program.nextReason
  escapedBelow : base.rootTable.escapedReason.val < program.nextReason
  readsOutside : ∀ site, site ∈ program.missing → ∀ read, read ∈ base.rootTable.reads →
    read.reason.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < read.reason.val
  readSafe : ReadSafe base.rootTable.reads program.fixed

/-- The base and extra rows are retained as proof witnesses. -/
def ReservedReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (plan : Plan) (root : Key) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  ∃ base extra, ReservedAt context plan root program base extra

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts
