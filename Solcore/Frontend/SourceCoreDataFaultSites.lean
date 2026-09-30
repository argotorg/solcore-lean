import Solcore.Frontend.SourceCoreProgramFaultSites

/-! Missing mapping defaults have distinct program-wide tokens. This metadata
pass preserves the current public error (`typeMismatch valueType none`) and
the exact expression occurrence and span. It performs no source evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataFaultSites

open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure IndexSite where
  owner : Key
  expression : ExpressionId
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr, DecidableEq

structure Program where
  base : SourceCoreProgramFaultSites.Program
  indices : List IndexSite
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | base (error : SourceCoreProgramFaultSites.Error)
  | reasonSpaceExhausted
  | ownerMismatch (expression : ExpressionId)
  | duplicateOccurrence (expression : ExpressionId)
  deriving Repr, DecidableEq

def prepare (plan : Plan) (root : Key) : Except Error Program := do
  let base ← (SourceCoreProgramFaultSites.prepare plan root).mapError Error.base
  let used := base.rootTable.reads.map (·.reason.val) ++
    base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val]
  let start := used.foldl max 0 + 1
  let mut indices : List IndexSite := []
  for specialized in plan.specializations do
    for node in specialized.function.typedBody.nodes do
      match node with
      | .expression node =>
          match node.form with
          | .index _ _ =>
              if node.id.occurrence.owner ≠ specialized.function.typedBody.owner then
                throw (.ownerMismatch node.id)
              if indices.any (fun entry => decide (entry.owner = specialized.key ∧ entry.expression = node.id)) then
                throw (.duplicateOccurrence node.id)
              let reason ← match Core.Word.ofNat? (start + indices.length) with
                | some reason => pure reason
                | none => throw .reasonSpaceExhausted
              let diagnostic : SourceCoreFaultSites.Diagnostic := {
                error := .typeMismatch node.type none
                site := .occurrence node.id.occurrence
                span := some node.span
              }
              indices := indices ++ [⟨specialized.key, node.id, reason, diagnostic⟩]
          | _ => pure ()
      | _ => pure ()
  let rootTable := { base.rootTable with
    additional := base.rootTable.additional ++ indices.map (fun site => (site.reason, site.diagnostic)) }
  pure { base, indices, rootTable }

def Program.reasonAt (program : Program) (owner : Key) (id : ExpressionId) : Core.Word :=
  match program.indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) with
  | some site => site.reason
  | none => match program.base.find? owner with
      | some function => function.table.reasonAt id
      | none => Core.Word.zero

end Solcore.Frontend.SourceCoreDataFaultSites
