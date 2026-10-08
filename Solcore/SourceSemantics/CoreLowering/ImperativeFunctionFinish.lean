import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileTree

/-! The actual function finish helper preserves returned values, Unit
fallthrough, source faults and escaped loop control with their distinct source
call outcomes. The heap is unchanged after the flow has completed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

inductive FinishedRep {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (faults : FunctionCalls.FaultRep) :
    TypeSystem.Ty → Ty → Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      FinishedRep functions mapping world faults .unit .unit
        (.fallthrough environment) (.inRight .word .unit)
  | returned {expected type sourceValue value}
      (payload : ValueRep values.checked registry functions mapping world
        expected sourceValue value type) :
      FinishedRep functions mapping world faults expected type
        (.returned sourceValue) (.inRight .word value)
  | fault {expected type reason token} (matched : faults reason token) :
      FinishedRep functions mapping world faults expected type
        (.fault reason) (.inLeft type (.word token))
  | breaking {expected type token} (environment : Dynamic.Environment)
      (matched : faults .controlEscapedFunction token) :
      FinishedRep functions mapping world faults expected type
        (.breaking environment) (.inLeft type (.word token))
  | continuing {expected type token} (environment : Dynamic.Environment)
      (matched : faults .controlEscapedFunction token) :
      FinishedRep functions mapping world faults expected type
        (.continuing environment) (.inLeft type (.word token))

theorem result {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {control : Dynamic.ControlOutcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FinishedRep (registry := registry) functions mapping world faults
      expected type control value)
    (exit : CompatibleNamedBody.Exit expected control outcome) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world expected type faults outcome value := by
  cases related with
  | fallthrough environment => cases exit; exact .value .unit
  | returned payload => cases exit; exact .value payload
  | fault matched => cases exit; exact .fault matched
  | breaking environment matched => cases exit; exact .fault matched
  | continuing environment matched => cases exit; exact .fault matched

theorem rename (type : Ty) (flow : Expr) (fellThrough escaped : Word)
    (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

theorem input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {value : Value}
    (evaluated : Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) value after) :
    ∃ result middle, Evaluates environment before flow result middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

/-- Only a reached break or continue requests the escaped-control token. -/
def TransferFaults (faults : FunctionCalls.FaultRep) (escaped : Word)
    (outcome : Dynamic.ControlOutcome) : Prop :=
  (∀ next, outcome = .breaking next → faults .controlEscapedFunction escaped) ∧
  (∀ next, outcome = .continuing next → faults .controlEscapedFunction escaped)

/-- The caller derives the raw Unit condition from its source grammar and
actual successful fallthrough. Escaped control uses the real diagnostic token
and is reflected as the independent controlEscapedFunction fault. -/
theorem from_flow_with_transfers {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome}
    {flow : Expr} {value : Value}
    (rawUnit : ∀ next, outcome = .fallthrough next → expected = .unit)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (transferFaults : TransferFaults faults escaped outcome)
    (related : TypedLexicalWhile.FlowRep (registry := registry) functions
      mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      FinishedRep (registry := registry) functions mapping world faults
        expected type outcome result := by
  cases related with
  | fallthrough next =>
    have raw := rawUnit next rfl
    subst expected
    have native : type = .unit := by
      change Except.ok (.unit : Ty) = .ok type at projection
      exact Except.ok.inj projection.symm
    subst type
    exact ⟨_, LocalControl.finish_fallthrough .unit
      (LocalLoop.toControl_normal _ escaped evaluated)
      (by simpa [LanguageResult.success, Expr.weakenAt] using
        (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after
          (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)),
      .fallthrough next⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _
      (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩
  | breaking next =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_transfer _ escaped evaluated), .breaking next (transferFaults.1 next rfl)⟩
  | continuing next =>
    exact ⟨_, LocalControl.finish_failure _
      (LocalLoop.toControl_transfer _ escaped evaluated), .continuing next (transferFaults.2 next rfl)⟩


theorem from_flow {values : SourceCoreCompatibleValues.Context}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome}
    {flow : Expr} {value : Value}
    (rawUnit : ∀ next, outcome = .fallthrough next → expected = .unit)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (escapedFault : faults .controlEscapedFunction escaped)
    (related : TypedLexicalWhile.FlowRep (registry := registry) functions
      mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before
      (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      FinishedRep (registry := registry) functions mapping world faults
        expected type outcome result := by
  exact from_flow_with_transfers functions rawUnit projection fellThrough escaped
    ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩ related evaluated

end Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
