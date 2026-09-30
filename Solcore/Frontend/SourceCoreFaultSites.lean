import Solcore.Frontend.SourceCoreBasic
import Solcore.Frontend.SourceCompilationPlan.Types

/-! Source diagnostics for returned Core language failures. Reasons are assigned
without modulo wrapping. Zero is reserved for function fallthrough, while each
ordinary local-read occurrence has its own positive reason and source span.
The next unused positive reason denotes escaped loop control. The table
contains metadata only; it never evaluates source code. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFaultSites

open SourceInference

structure Diagnostic where
  error : SourceTypedRuntime.RuntimeError
  site : SourceCoreElaboration.ErrorSite
  span : Option Syntax.SourceSpan
  deriving Repr, DecidableEq

structure ReadSite where
  expression : ExpressionId
  binder : Resolved.LocalId
  span : Syntax.SourceSpan
  reason : Core.Word
  deriving Repr, DecidableEq

structure Table where
  owner : Resolved.DeclarationId
  resultType : TypeSystem.Ty
  reads : List ReadSite
  escapedReason : Core.Word
  /-- Assignment diagnostics and other functions' boundary faults. -/
  additional : List (Core.Word × Diagnostic) := []
  deriving Repr, DecidableEq

inductive Error where
  | reasonSpaceExhausted
  | ownerMismatch (expression : ExpressionId) (binder : Resolved.LocalId)
  | duplicateOccurrence (expression : ExpressionId)
  deriving Repr, DecidableEq

private def collect (owner : Resolved.DeclarationId) :
    Nat → List Node → List ReadSite → Except Error (List ReadSite)
  | _, [], sites => .ok sites.reverse
  | index, .expression node :: rest, sites =>
      match node.form with
      | .reference _ (.local binder) => do
          if node.id.occurrence.owner ≠ owner ∨ binder.owner ≠ owner then
            throw (.ownerMismatch node.id binder)
          if sites.any (fun site => decide (site.expression = node.id)) then
            throw (.duplicateOccurrence node.id)
          let reason ← match Core.Word.ofNat? (index + 1) with
            | some reason => pure reason
            | none => .error .reasonSpaceExhausted
          collect owner (index + 1) rest
            ({ expression := node.id, binder, span := node.span, reason } :: sites)
      | _ => collect owner index rest sites
  | index, .statement _ :: rest, sites => collect owner index rest sites

def prepare (source : TypedSource) (resultType : TypeSystem.Ty) : Except Error Table := do
  let reads ← collect source.owner 0 source.nodes []
  let escapedReason ← match Core.Word.ofNat? (reads.length + 1) with
    | some reason => pure reason
    | none => .error .reasonSpaceExhausted
  pure { owner := source.owner, resultType, reads, escapedReason }

def Table.reasonAt (table : Table) (expression : ExpressionId) : Core.Word :=
  match table.reads.find? fun site => decide (site.expression = expression) with
  | some site => site.reason
  | none => Core.Word.zero

def Table.diagnostic? (table : Table) (reason : Core.Word) : Option Diagnostic :=
  if reason = Core.Word.zero then
    some {
      error := .functionFellThrough table.resultType
      site := .declaration table.owner
      span := none
    }
  else
    if reason = table.escapedReason then
      some {
        error := .controlEscapedFunction
        site := .declaration table.owner
        span := none
      }
    else
      match table.additional.find? fun site => decide (site.1 = reason) with
      | some site => some site.2
      | none =>
        (table.reads.find? fun site => decide (site.reason = reason)).map fun site => {
          error := .uninitializedLocal site.binder
          site := .occurrence site.expression.occurrence
          span := some site.span
        }

theorem Table.fallthrough_diagnostic (table : Table) :
    table.diagnostic? Core.Word.zero = some {
      error := .functionFellThrough table.resultType
      site := .declaration table.owner
      span := none
    } := by simp [Table.diagnostic?]

/-- A checked positive reason is recovered with its exact occurrence and span. -/
theorem Table.read_diagnostic {table : Table} {site : ReadSite}
    (positive : site.reason ≠ Core.Word.zero)
    (ordinary : site.reason ≠ table.escapedReason)
    (noBoundary : table.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : table.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site) :
    table.diagnostic? site.reason = some {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span
    } := by simp [Table.diagnostic?, positive, ordinary, noBoundary, found]

theorem Table.escaped_diagnostic (table : Table)
    (positive : table.escapedReason ≠ Core.Word.zero) :
    table.diagnostic? table.escapedReason = some {
      error := .controlEscapedFunction
      site := .declaration table.owner
      span := none
    } := by simp [Table.diagnostic?, positive]

end Solcore.Frontend.SourceCoreFaultSites
