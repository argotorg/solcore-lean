import Solcore.SourceSemantics.CoreLowering.CallablePairedEmission

/-! Finite protocol regressions retain metadata receipts and exact native
administrative contexts. Failure restores the original current frame. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallablePairedProtocol
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallablePairedProtocol SourceCoreCallablePairedFrames

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {lexical current : PairedFrame} {state : MetadataState} {origin : Word}
    (entry : Entry inputs origin lexical current state) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) := entry.authenticates

/-- Both distinct parent histories survive a matching applied view. Witness
preparation uses the caller; its rewrite target is the lexical metadata. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical : PairedFrame} {callerState lexicalState : MetadataState} {id target : Word}
    (callerHistory : Authenticates inputs caller (some callerState))
    (lexicalHistory : Authenticates inputs lexical (some lexicalState))
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id target = .ok read)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexicalState)
    (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexicalState = .ok applied) :
    Authenticates inputs (.appliedView id target caller lexical) (some (read.after lexicalState)) := by
  simpa only [selectedFrame, ↓reduceIte] using
    (Entry.applied callerHistory lexicalHistory read prepared applied appliedPrepared).authenticates

/-- A body returning a language failure is still a completed call: restoration
uses the saved frame, preserving its current stable or transient history. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {lexical current : PairedFrame} {state : MetadataState} {origin reason : Word}
    (saved : Current inputs current) (entry : Entry inputs origin lexical current state) :
    Evaluates [.unit, encode layout lexical, .cellRef layout.type 0] [encode layout current]
      (withFrame (.var 2)
        (lambdaFrame layout origin (.var 1) (.loadCell (.var 2)))
        ((LanguageResult.failure .unit (.word reason)).weakenAt 1))
      (.inLeft .unit (.word reason)) [encode layout current] := by
  have caller : CellState inputs layout 0 current [encode layout current] := ⟨rfl, saved⟩
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .unit, encode layout lexical, .cellRef layout.type 0]
      ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current)))
      ((((LanguageResult.failure .unit (.word reason)).weakenAt 1).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason)) ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current))) := by
    simpa [LanguageResult.failure, Expr.weakenAt] using
      (show Evaluates [.unit, encode layout current, .unit, encode layout lexical, .cellRef layout.type 0]
        ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current)))
        (.inLeft .unit (.word reason)) (.inLeft .unit (.word reason))
        ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current))) from .inLeft .word)
  have evaluated := (lambda_body_evaluates (referenceIndex := 0) (environment := [.cellRef layout.type 0])
    (argument := .unit) rfl caller entry bodyEvaluation).2.1
  simpa using evaluated

/-- An actual successful compiler hook, rather than an arbitrary typed closure,
provides the exact native formation expression and its static origin receipt. -/
example {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (prepared : SourceCoreCallablePairedAncestry.Prepared base)
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {context : SourceCoreFunctions.Context} {source : SourceInference.TypedSource}
    {scope : SourceCoreFunctions.Scope} {node : SourceInference.ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : SourceCoreCallablePairedAncestry.expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = SourceCoreCallablePairedAncestry.snapshotLambda prepared.layout.frame origin
        (SourceCoreCallablePairedAncestry.creationReferenceIndex context scope) parameter result body :=
  CallablePairedEmission.expressionHook_receipt prepared accepted

end Solcore.Test.SourceCoreCallablePairedProtocol
