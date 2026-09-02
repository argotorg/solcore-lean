import Solcore.Syntax.DeclarativeExportPathOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ExportPathTotalityProperties
import Solcore.Syntax.Parser.StateCursorProperties

/-! Exact executable rejection reflection for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

private theorem exportPathTail_ne_reject (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      exportPathTail first fuel last tailRev input ≠
        .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold exportPathTail at result
      split at result
      next continues =>
        unfold continuesExportPath at continues
        have guards := Bool.and_eq_true_iff.mp continues
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl guards.1 with
          ⟨dot, dotResult⟩
        simp only [dotResult] at result
        unfold State.peekOffsetKind? at guards
        cases followingFound : input.peekOffset? 1 with
        | none => simp [followingFound] at guards
        | some following =>
            rcases following with ⟨componentSpan, followingKind⟩
            cases followingKind <;>
              simp only [followingFound, Option.map_some] at guards
            all_goals try simp_all
            case identifier spelling =>
              let afterDot : State := {
                input with cursor := input.cursor + 1
              }
              have componentAt : DeclarativeGrammar.TokenAt
                  afterDot.tokens afterDot.window.endIndex afterDot.cursor {
                    span := componentSpan
                    value := .identifier spelling
                  } := by
                exact ⟨
                  State.cursor_add_lt_endIndex_of_peekOffset?_eq_some
                    followingFound,
                  State.getElem?_eq_some_of_peekOffset?_eq_some
                    followingFound⟩
              cases componentResult : identifier .exportDecl afterDot with
              | invariant error => simp [afterDot, componentResult] at result
              | reject componentFailure componentRejected =>
                  have absent := identifier_reject_identifierAbsentAt
                    .exportDecl componentResult
                  exact (absent ⟨componentSpan, spelling, componentAt⟩).elim
              | ok component next =>
                  simp only [afterDot, componentResult] at result
                  exact inductionHypothesis component
                    (component :: tailRev) next failure rejected result
      next stopped =>
        unfold finishExportPath at result
        contradiction

end ExportInternals

/-- Every executable export-path rejection is the exact nonconsuming
rejection of its required first checked identifier. -/
theorem exportPath_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportPath input = .reject failure rejected) :
    DeclarativeGrammar.ExportPathRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (identifier_reject_sound .exportDecl firstResult)
  | ok first next =>
      simp only [firstResult] at result
      exact False.elim
        (ExportInternals.exportPathTail_ne_reject first
          (next.remainingCount + 1) first [] next failure rejected result)

end Solcore.Syntax.Parser
