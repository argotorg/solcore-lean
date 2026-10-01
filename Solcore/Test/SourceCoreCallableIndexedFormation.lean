import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation

/-! Actual compiler receipts and finite entry/formation laws. Dynamic metadata
is carried from saved cells, not inferred from native descriptors or indices. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedFormation
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch

/-- Even a completed language failure restores the caller's stable or pending
read token. The invoked lambda keeps its independent lexical ghost parent. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin reason : Word}
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table current currentGhost)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid) :
    Evaluates [.unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout current]
      (withFrame (.var 2) (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var 2)))
        ((LanguageResult.failure .unit (.word reason)).weakenAt 1))
      (.inLeft .unit (.word reason)) [encode layout current] := by
  have caller : CellState graph.inputs graph.table layout 0 current currentGhost [encode layout current] := ⟨rfl, currentHistory⟩
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0]
      ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      ((((LanguageResult.failure .unit (.word reason)).weakenAt 1).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason))
      ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current))) := by
    simpa [LanguageResult.failure, Expr.weakenAt] using
      (show Evaluates [.unit, encode layout current, .unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0]
        ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
        (.inLeft .unit (.word reason)) (.inLeft .unit (.word reason))
        ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
        from .inLeft .word)
  obtain ⟨_, _, _, evaluated, _⟩ := CallableIndexedEntry.lambda_body_evaluates graph
    (referenceIndex := 0) (environment := [.cellRef layout.type 0]) (argument := .unit)
    rfl caller lexical valid bodyEvaluation
  simpa using evaluated

/-- No arbitrary AST shape is substituted for actual compiler success. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {context : SourceCoreFunctions.Context} {source : SourceInference.TypedSource}
    {scope : SourceCoreFunctions.Scope} {node : SourceInference.ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : SourceCoreCallableIndexedAncestry.expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ origin body, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = SourceCoreCallableIndexedAncestry.snapshotLambda prepared.graph.table prepared.layout.frame origin
        (SourceCoreCallableIndexedAncestry.creationReferenceIndex context scope) parameter result body :=
  CallableIndexedFormation.expressionHook_receipt prepared accepted

/-- Named entry history comes from the actual owned graph row accepted by the
compiler's named hook, without a prior supplied named metadata derivation. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared function body = .ok output) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      output = withFrame (.var (base.globals.length + 1)) (literal prepared.layout.frame (.state index)) body :=
  CallableIndexedFormation.namedBody_history prepared accepted

/-- The source allocator callback's successful result exposes the original
allocation and its exact source-request reference mapping. -/
example (layout : Layout) (globals : Nat) (allocate : SourceCoreSourceCells.Allocator) (request : SourceCoreSourceCells.Request)
    {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals allocate request = .ok code) :
    ∃ receipt : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request,
      SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt layout globals allocate request = .ok receipt ∧
      code = SourceCoreCallableIndexedAllocationFrames.snapshotBefore layout
        (.var (SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request)) receipt.original :=
  CallableIndexedAllocation.allocator_receipt layout globals allocate request accepted

/-- Actual wrapper creation preserves identity, descriptor and the original
payload, while saving the caller's occurrence-specific read receipt separately. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {parameter result : Ty} {id target descriptor : Word} {identity payload : Value}
    {caller : NativeFrame} {callerGhost : GhostFrame} {metadata : MetadataState}
    (history : Carries prepared.graph.inputs prepared.graph.table caller callerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read prepared.graph.inputs metadata id target)
    (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead prepared.graph.inputs metadata id target = .ok read) :
    Evaluates [.pair (.pair identity payload) (.word descriptor), .cellRef prepared.layout.frame.type 0]
      [encode prepared.layout.frame caller]
      (SourceCoreCallableIndexedAncestry.viewLower prepared.layout.frame parameter result id target 1
        (LanguageResult.success (.var 0)))
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result)
          (SourceCoreCallableIndexedAncestry.viewBody prepared.layout.frame id target 1)
          [encode prepared.layout.frame caller, .pair (.pair identity payload) (.word descriptor),
            .pair (.pair identity payload) (.word descriptor), .cellRef prepared.layout.frame.type 0])) (.word descriptor)))
      [encode prepared.layout.frame caller] :=
  (CallableIndexedFormation.viewLower_history prepared history read readPrepared
    (Evaluates.inRight (.var rfl)) rfl rfl).1

end Solcore.Test.SourceCoreCallableIndexedFormation
