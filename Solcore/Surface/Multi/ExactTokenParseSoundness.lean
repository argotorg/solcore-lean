import Solcore.Surface.Multi.ExactTokenActionDispatch
import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenCorrespondence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A complete coherent parse carries a successful source-sensitive plan for
all retained tokens once every root semantic action preserves token plans. -/
theorem Parses.tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment} {module : ParsedModuleV1}
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (lexical : Lexes file tokens comments)
    (parsed : Parses file tokens module) :
    TokenPlanEvidence (parsedModuleTokenPlan? module) tokens := by
  cases parsed with
  | sourceBackedRoot owned sourceBacked =>
      rcases sourceBacked with
        ⟨memo, correct, final, reached, complete, coherent⟩
      rcases coherent.sourceTrace_exists owned with ⟨trace, carries⟩
      have evidence := carries.tokenPlanEvidence
        sourceRuleTokenPlanLayout
        (ActionTokenPlanSound.ofRoot rootSound)
        lexical.tokensLexicallyExact
      simpa [parsedModuleTokenPlan?, sourceRuleTokenPlanLayout,
        CanonicalCompleteRootItem, ProductionId.lhs,
        NonterminalValue.tokenPlan?, ruleTokenPlan?] using evidence

/-- Parser success over the exact lexer output implies the executable exact
token-correspondence predicate. -/
theorem Parses.exactTokenCorrespondence
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment} {module : ParsedModuleV1}
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (lexical : Lexes file tokens comments)
    (parsed : Parses file tokens module) :
    ExactTokenCorrespondence file tokens comments module := by
  rw [exactTokenCorrespondence_eq_true_iff]
  have sourceEq := module_source_exact parsed
  have spanEq : module.span = SourceSpan.fullFile file := by
    rw [sourceEq]
  have payloadSourceEq : module.payload.source = file.id := by
    rw [sourceEq]
  rcases parsed.tokenPlanEvidence rootSound lexical with
    ⟨plan, planEq, relation⟩
  exact ⟨ExactLexicalOutput.of_lexes lexical, spanEq, payloadSourceEq,
    plan, planEq, declarationModulePlan?_wellAnchored module plan planEq,
    relation⟩

end Solcore.Surface.Multi
