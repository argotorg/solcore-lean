import Solcore.Frontend.SourceCoreCallableIndexedAncestry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedExpansion

/-! Receipts for actual indexed compiler formation hooks. The emitted code and
its native descriptor are obtained from compiler success; dynamic provenance
is carried from the current administrative cell. Neither a native function type
nor a numeric state index is used to invent source closure history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
open Core Frontend SourceInference
open SourceCoreCallableIndexedAncestry
open CallableIndexedHistory

private theorem key_eq_of_beq (left right : Key) (accepted : (left == right) = true) : left = right := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializationKey SourceSpecialization.instBEqSpecializationKey.beq at accepted
  simp only [Bool.and_eq_true, beq_iff_eq] at accepted
  simp_all

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

theorem originId_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (accepted : originId prepared origin = .ok id) :
    prepared.graph.inputs.callable.table.idAt? origin = some id := by
  unfold originId at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted; assumption
  · cases accepted

/-- Actual successful emission retains its exact source occurrence and full
native specialization context, as well as the graph-owned dispatch table. -/
theorem expressionHook_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ origin body, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = snapshotLambda prepared.graph.table prepared.layout.frame origin
        (creationReferenceIndex context scope) parameter result body := by
  by_cases globals : (context.owner != owner || context.globals != base.globals) = true
  · simp [expressionHook, globals, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · have checkedGlobals : (context.owner == owner) = true ∧ context.globals = base.globals := by
      simpa [bne] using globals
    have globalsEq : context.owner = owner ∧ context.globals = base.globals :=
      ⟨key_eq_of_beq _ _ checkedGlobals.1, checkedGlobals.2⟩
    cases originSelected : originId prepared (.lambda owner node.id active) with
    | error error => simp [expressionHook, globals, originSelected, bind, Except.bind] at accepted
    | ok origin =>
      have selected := originId_receipt prepared originSelected
      cases raw <;> simp only [expressionHook, globals, originSelected, pure, Except.pure, bind, Except.bind] at accepted
      all_goals try cases accepted
      next actualParameter actualResult body =>
        by_cases header : (actualParameter != parameter || actualResult != LanguageResult.resultType result) = true
        · simp [header, throw, throwThe, MonadExceptOf.throw] at accepted
        · have headerChecks : (actualParameter == parameter) = true ∧ (actualResult == LanguageResult.resultType result) = true := by
            simpa [bne] using header
          have headerEq := And.intro ((type_beq _ _).mp headerChecks.1) ((type_beq _ _).mp headerChecks.2)
          by_cases ownerEq : (source.owner != owner.declaration) = true
          · simp [header, ownerEq, throw, throwThe, MonadExceptOf.throw] at accepted
          · have sourceOwner : source.owner = owner.declaration := by simpa using ownerEq
            simp [header, ownerEq, prepared.dispatch.tableOwner] at accepted
            exact ⟨origin, body, selected, by simp only [headerEq.1, headerEq.2],
              globalsEq.1, globalsEq.2, sourceOwner, accepted.symm⟩

/-- The named hook accepts only a registered native state from its owned
metadata table; an unregistered descriptor cannot emit an entry wrapper. -/
theorem namedBody_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin index, prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      SourceCoreCallableIndexedDispatch.namedFrame prepared.graph.table origin = .state index ∧
      output = SourceCoreCallableIndexedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) body := by
  unfold namedBody at accepted
  obtain ⟨origin, selected, accepted⟩ := CallableAncestryPairedExpansion.bind_ok accepted
  have owned := originId_receipt prepared selected
  simp only [prepared.dispatch.tableOwner] at accepted
  cases named : SourceCoreCallableIndexedDispatch.namedFrame prepared.graph.table origin with
  | empty => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | invalid => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | view id target caller => simp [named, throw, throwThe, MonadExceptOf.throw] at accepted
  | state index =>
    simp [named] at accepted
    exact ⟨origin, index, owned, named, accepted.symm⟩

theorem namedBody_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      output = SourceCoreCallableIndexedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) body := by
  obtain ⟨origin, index, owned, named, emitted⟩ := namedBody_receipt prepared accepted
  cases selected : prepared.graph.table.namedAt? origin with
  | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, selected] at named
  | some position =>
    obtain ⟨metadata, history⟩ := named_history prepared.graph selected
    exact ⟨origin, index, metadata, owned, named ▸ history, emitted⟩

/-- The indexed closure captures a related lexical state before its original
lexical environment. The ghost frame is proof-only and absent from that value. -/
def LambdaSnapshot {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    (layout : SourceCoreCallableIndexedFrames.Layout) (origin : Word) (referenceIndex : Nat)
    (parameter result : Ty) (body : Expr) (environment : Environment) (value : Value) : Prop :=
  ∃ (native : NativeFrame) (ghost : GhostFrame) (metadata : MetadataState),
    Carries graph.inputs graph.table native ghost (some metadata) ∧
    value = .closure parameter (LanguageResult.resultType result)
      (SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame graph.table layout origin (.var 1)
          (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      (SourceCoreCallableIndexedFrames.encode layout native :: environment)

theorem expressionHook_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {store : Store} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame native))
    (history : Carries prepared.graph.inputs prepared.graph.table native ghost (some metadata)) :
    ∃ origin body value, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      Evaluates environment store output value store ∧
      LambdaSnapshot prepared.graph prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨origin, body, selected, rawShape, _, _, _, rfl⟩ := expressionHook_receipt prepared accepted
  exact ⟨origin, body, _, selected, rawShape, snapshotLambda_evaluates prepared.graph.table origin reference read,
    native, ghost, metadata, history, rfl⟩

theorem expressionHook_reflects {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {before after : Store} {location : Location} {value : Value}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame native))
    (history : Carries prepared.graph.inputs prepared.graph.table native ghost (some metadata))
    (evaluated : Evaluates environment before output value after) :
    after = before ∧ ∃ origin body,
      prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      LambdaSnapshot prepared.graph prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨origin, body, expected, selected, rawShape, expectedEval, snapshot⟩ :=
    expressionHook_history prepared accepted reference read history
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expectedEval
  exact ⟨rfl, origin, body, selected, rawShape, snapshot⟩

/-- Successful local-read lowering either preserves an unwrapped value, or
emits the exact indexed wrapper selected by the real static view receipt. -/
theorem lowerView_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {source : TypedSource} {scope : Scope} {read : ExpressionId}
    {original output : SourceCoreBasic.LoweredExpr}
    (accepted : lowerView prepared owner active source scope read original = .ok output) :
    ∃ receipt : SourceCoreCallableViewLowering.Viewed prepared.views owner active read original,
      SourceCoreCallableViewLowering.lowerWithReceipt prepared.views owner active source read original = .ok receipt ∧
      ((receipt.entry.view.wrapsPrincipal = false ∧ output = original) ∨
        (receipt.entry.view.wrapsPrincipal = true ∧ ∃ candidate target parameter result,
          receipt.entry.view.selectedInstance = some candidate ∧
          prepared.graph.inputs.callable.table.idAt?
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) = some target ∧
          original.type = CallableContract.functionType parameter result ∧
          output = {original with expression := (viewLower prepared.layout.frame parameter result receipt.entry.id target
            (scope.length + 1 + base.globals.length) original.expression)})) := by
  cases receiptResult : SourceCoreCallableViewLowering.lowerWithReceipt prepared.views owner active source read original with
  | error error => simp [lowerView, receiptResult, Except.mapError, bind, Except.bind] at accepted
  | ok receipt =>
    refine ⟨receipt, rfl, ?_⟩
    cases wraps : receipt.entry.view.wrapsPrincipal with
    | false =>
      simp [lowerView, receiptResult, wraps, Except.mapError, bind, Except.bind] at accepted
      exact Or.inl ⟨rfl, accepted.symm⟩
    | true =>
      apply Or.inr
      refine ⟨rfl, ?_⟩
      cases candidateResult : receipt.entry.view.selectedInstance with
      | none => simp [lowerView, receiptResult, wraps, candidateResult, Except.mapError, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at accepted
      | some candidate =>
        cases targetResult : originId prepared
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) with
        | error error => simp [lowerView, receiptResult, wraps, candidateResult, targetResult, Except.mapError,
            bind, Except.bind, pure, Except.pure] at accepted
        | ok target =>
          have targetOwned := originId_receipt prepared targetResult
          simp only [lowerView, receiptResult, wraps, candidateResult, targetResult, Except.mapError, bind, Except.bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at accepted
          split at accepted
          · next parameter result header =>
            cases accepted
            exact ⟨candidate, target, parameter, result, rfl, targetOwned, header, rfl⟩
          · cases accepted

/-- The exact wrapper selected by lowerView_receipt captures its related
read-time caller independently of the passed-through original payload.
Authenticating the original payload is a separate lambda-formation receipt. -/
theorem viewLower_history {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {environment : Environment} {before after : Store} {readCode : Expr}
    {parameter result : Ty} {id target descriptor : Word} {referenceIndex location : Nat}
    {identity originalPayload : Value} {caller : NativeFrame} {callerGhost : GhostFrame} {metadata : MetadataState}
    (history : Carries prepared.graph.inputs prepared.graph.table caller callerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read prepared.graph.inputs metadata id target)
    (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead prepared.graph.inputs metadata id target = .ok read)
    (evaluated : Evaluates environment before readCode
      (.inRight .word (.pair (.pair identity originalPayload) (.word descriptor))) after)
    (reference : environment[referenceIndex]? = some (.cellRef prepared.layout.frame.type location))
    (snapshot : after.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.layout.frame caller)) :
    Evaluates environment before (viewLower prepared.layout.frame parameter result id target referenceIndex readCode)
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) (viewBody prepared.layout.frame id target referenceIndex)
          (SourceCoreCallableIndexedFrames.encode prepared.layout.frame caller ::
            .pair (.pair identity originalPayload) (.word descriptor) :: environment))) (.word descriptor))) after ∧
    Current prepared.graph.inputs prepared.graph.table
      (SourceCoreCallableIndexedDispatch.readFrame id target caller) (.view id target callerGhost) :=
  ⟨viewLower_evaluates evaluated reference snapshot, read_history history read readPrepared⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
