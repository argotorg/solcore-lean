import Solcore.Frontend.SourceStageAnalysis

/-!
The stage analyzer depends on the actual declaration, typed body and effectful
staging flag.  This congruence only transports those static inputs.  Their
correlation across different specializations remains a separate proof.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStageAnalysisCongruence

open SourceInference SourceStageAnalysis

/-- Equal genuine analyzer inputs give equal analyzer actions. -/
theorem analyzeFunction_congr
    {left right : CheckedFunction}
    (sameDeclaration : left.declaration = right.declaration)
    (sameSource : left.typedBody = right.typedBody)
    (sameEffectful :
      (left.returnComptime || typeIsComptimeOnly left.inferredBodyType) =
      (right.returnComptime || typeIsComptimeOnly right.inferredBodyType)) :
    analyzeFunction left = analyzeFunction right := by
  simp only [analyzeFunction, sameDeclaration, sameSource, sameEffectful]

/-- The two actual successful receipts therefore retain the same analysis. -/
theorem analysis_eq_of_success
    {left right : CheckedFunction} {leftAnalysis rightAnalysis : Analysis}
    (sameDeclaration : left.declaration = right.declaration)
    (sameSource : left.typedBody = right.typedBody)
    (sameEffectful :
      (left.returnComptime || typeIsComptimeOnly left.inferredBodyType) =
      (right.returnComptime || typeIsComptimeOnly right.inferredBodyType))
    (leftAccepted : analyzeFunction left = .ok leftAnalysis)
    (rightAccepted : analyzeFunction right = .ok rightAnalysis) :
    leftAnalysis = rightAnalysis := by
  have actions := analyzeFunction_congr sameDeclaration sameSource sameEffectful
  exact Except.ok.inj (leftAccepted.symm.trans (actions.trans rightAccepted))

end Solcore.Frontend.SourceStageAnalysisCongruence
