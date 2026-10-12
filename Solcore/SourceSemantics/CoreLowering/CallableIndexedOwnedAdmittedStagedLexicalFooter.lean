import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning

/-! The actual function footer consumes lexical flow without changing its
heap, returned value, or nested failure. Only an accepted unit fallthrough
uses the original unit fallback. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedAdmittedStagedLexicalFlow (Represents result)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CallableIndexedOwnedAdmittedStagedTerminalBody.code type (flow.rename ξ) escaped
        ((fallback type fellThrough).rename ξ) := by
  simpa only [CompatibleStatements.finish, CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
    (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename type flow escaped (fallback type fellThrough) ξ)

/-- A represented completed flow selects the same literal finish branch. -/
theorem evaluates {compiled : SourceCoreUnifiedCompilation.Compiled}
    {receiving : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty} {type : Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.BodyOutcome}
    {value : Value} {actual : Environment} {before after : Store} {flow : Expr}
    (represented : Represents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world raw type faults outcome value)
    (evaluated : Evaluates actual before flow value after)
    (fellThrough escaped : Word) (ξ : Renaming) :
    ∃ native, Evaluates actual before
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code type flow escaped ((fallback type fellThrough).rename ξ))
        native after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        mapping world raw type faults (result outcome) native := by
  cases represented with
  | returned payload =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.returned payload) evaluated escaped
  | fault matched =>
      exact CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates (.fault matched) evaluated escaped
  | fallthrough environment rawUnit coreUnit =>
      subst raw
      subst type
      refine ⟨.inRight .word .unit, ?_, .value .unit⟩
      have fallbackEq : (fallback .unit fellThrough).rename ξ = .inRight .word .unit := by
        simp [fallback, LanguageResult.success, Expr.rename]
      rw [fallbackEq]
      exact LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated)
        (by simpa [Expr.weakenAt] using
          (show Evaluates (.unit :: .inLeft .unit .unit :: actual) after
            (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit))

theorem outcome_eq {type : TypeSystem.Ty} {body : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome}
    (matched : Staging.Recursive.BodyResult type body outcome) : outcome = result body := by
  cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
