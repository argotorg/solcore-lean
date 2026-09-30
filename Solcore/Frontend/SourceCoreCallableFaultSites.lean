import Solcore.Frontend.SourceCoreStageCodebook
import Solcore.Frontend.SourceCoreFaultSites
import Solcore.Core.CallableContract

/-! Exact stage and invocation-arity diagnostics for the artifact codebook.
Tokens extend the existing program-wide diagnostic table without wrapping.
The original source occurrence supplies the span for contextual instances too. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCallableFaultSites
open SourceInference
abbrev Key := SourceCoreStageCodebook.Key
abbrev Table := SourceCoreStageCodebook.Table
abbrev Phase := Core.CallableContract.Phase
abbrev RuntimeError := SourceCoreStageCodebook.RuntimeError

structure Site where
  caller : Key
  call : ExpressionId
  contract : Core.Word
  phase : Phase
  error : RuntimeError
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr

structure Program where
  sites : List Site
  unknown : Core.Word
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | reasonSpaceExhausted
  | missingCaller (key : Key)
  | missingCall (key : Key) (id : ExpressionId)
  deriving Repr

private def fresh (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? index with
  | some reason => .ok reason
  | none => .error .reasonSpaceExhausted

def prepare (plan : SourceCoreStageCodebook.Plan) (contracts : Table)
    (base : SourceCoreFaultSites.Table) : Except Error Program := do
  let used := base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
    [base.escapedReason.val]
  let start := used.foldl max 0 + 1
  let unknown ← fresh start
  let mut sites : List Site := []
  for row in contracts.decisions do
    let caller ← match plan.specializations.find? (fun entry => decide (entry.key = row.caller)) with
      | some caller => pure caller
      | none => throw (.missingCaller row.caller)
    let node ← match caller.function.typedBody.lookupExpression? row.call with
      | some node => pure node
      | none => throw (.missingCall row.caller row.call)
    for phase in ([.beforeArguments, .beforeApplication] : List Phase) do
      let answer := match phase with
        | .beforeArguments => row.beforeArguments
        | .beforeApplication => row.afterArguments
      match answer with
      | .ok _ => pure ()
      | .error error =>
          let reason ← fresh (start + 1 + sites.length)
          let diagnostic : SourceCoreFaultSites.Diagnostic :=
            { error, site := .occurrence row.call.occurrence, span := some node.span }
          sites := sites ++ [⟨row.caller, row.call, row.entry.id, phase, error, reason, diagnostic⟩]
  let unknownDiagnostic : SourceCoreFaultSites.Diagnostic :=
    { error := .deepSafetyInputsRejected, site := .declaration base.owner, span := none }
  pure { sites, unknown, rootTable := { base with
    additional := base.additional ++ [(unknown, unknownDiagnostic)] ++ sites.map (fun site => (site.reason, site.diagnostic)) } }

def Program.reasonAt (program : Program) (caller : Key) (call : ExpressionId)
    (contract : Core.Word) (phase : Phase) (error : RuntimeError) : Core.Word :=
  match program.sites.find? (fun site => decide (site.caller = caller ∧ site.call = call ∧
      site.contract = contract ∧ site.phase = phase ∧ site.error = error)) with
  | some site => site.reason
  | none => program.unknown

end Solcore.Frontend.SourceCoreCallableFaultSites
