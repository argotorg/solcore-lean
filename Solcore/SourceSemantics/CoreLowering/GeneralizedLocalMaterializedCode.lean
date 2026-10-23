import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues

/-! The materialized Source closure uses the exact native value stored at
declaration time. Equality follows from the accepted emitted expression, not
from running the creation code again in a changed store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
open Core Frontend SourceInference
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
  {packet : Packet inputs candidate raw}

theorem value_eq (indexed : Indexed prepared packet)
    {function : Dynamic.Closure} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative viewRelation)
    (lowered : code.lowered = packet.original.lowered)
    (embedding : Renaming) (native : NativeFrame) (actual : Core.Environment) :
    CallableIndexedLambdaValues.value code embedding native actual =
      GeneralizedLocalInstanceValues.value indexed embedding native actual := by
  have emitted := code.emitted
  conv at emitted => lhs; rw [lowered, packet.original.extracted, indexed.emitted]
  change Expr.inRight .word
      (.pair (.pair (.inLeft .word .unit)
        (.letE (.loadCell (.var (GeneralizedLocalInstanceValues.referenceIndex indexed)))
          (.lambda packet.certificate.parameterCore (LanguageResult.resultType packet.certificate.resultCore)
            (GeneralizedLocalInstanceValues.body indexed)))) (.word indexed.descriptor.id)) =
    Expr.inRight .word
      (.pair (.pair (.inLeft .word .unit)
        (.letE (.loadCell (.var code.referenceIndex))
          (.lambda code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore) code.body)))
        (.word code.descriptor.id)) at emitted
  have outer := Expr.pair.inj (Expr.inRight.inj emitted).2
  have lambda := Expr.lambda.inj (Expr.letE.inj (Expr.pair.inj outer.1).2).2
  have descriptor := Expr.word.inj outer.2
  unfold CallableIndexedLambdaValues.value GeneralizedLocalInstanceValues.value
  rw [← lambda.1, ← lambda.2.1, ← lambda.2.2, ← descriptor]

/-- The original emission's checked preparation supplies canonical stage
provenance for the actual materialized source and its full child key. -/
theorem source_receipt (indexed : Indexed prepared packet)
    {function : Dynamic.Closure} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function inputs.scope administrative viewRelation)
    (compilation : code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared)
    (active : code.active = packet.original.emission.prepared.substitution)
    (sourceEq : function.source = packet.original.emission.prepared.source) :
    LambdaSourceAlignment.SourceReceipt prepared.base.sourceProgram prepared.base.plan
      code.compilation.owner code.active function.source := by
  have authentic : LambdaSourceAlignment.SourceReceipt inputs.program inputs.current.plan
      candidate.origin.caller packet.original.emission.prepared.substitution packet.original.emission.prepared.source :=
    .contextual packet.original.emission.authentic
  simpa only [indexed.program, indexed.plan, ← indexed.owner, compilation, active, sourceEq,
    GeneralizedLocalLambdaCompilation.context] using authentic

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCode
