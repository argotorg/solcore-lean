import Solcore.Surface.Multi.SourceRuleCoherentIntervalLocation
import Solcore.Surface.Multi.RuleCoherentIntervalLocation
import Solcore.Surface.Multi.RuleCoherentIntervalLocationMatchArmCase
import Solcore.Surface.Multi.RuleCoherentIntervalLocationExpressionCases

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Recover the source rule hidden by an arbitrary root-action witness. -/
private theorem ActionReduces.RootCase.actionId_eq_root
    {file : WorkspaceFile} {tokens : List Token}
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    {action : ActionReduces file tokens actionId origin finish input output}
    (isRoot : ActionReduces.RootCase action) :
    ∃ rule : GrammarRuleId,
      actionId = .actionFor (.root rule) := by
  cases isRoot with
  | root rule origin finish input output reduces =>
      exact ⟨rule, rfl⟩

/-- Canonical source-reduction callback underlying the parser-item endpoint
handler.  The explicit input equality keeps EBNF transport out of the
dependent endpoint dispatch. -/
private def EndpointReductionLocationHandler
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens) : Prop :=
  ∀ {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {context : GuardContext tokens}
      {priorValues : PrefixValues file tokens
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
          context)}
      {complete : CompleteItem
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
          context).raw}
      {coherentPrefix : CoherentPrefix file tokens memo correct final
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
          context) priorValues}
      {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      (reduces : RuleReduction file tokens rule origin finish ruleInput output)
      (_classified : RuleReduction.EndpointSensitiveRuleCase reduces)
      (inputEq : ruleInput = RootAction.unpack rule
        (PrefixValues.fullValue
          (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
            context) complete priorValues))
      {trace : SourceAnchorTrace file tokens}
      (carries : PrefixCarriesSourceTrace file tokens memo correct final owned
        coherentPrefix trace),
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root rule origin finish
        (PrefixValues.fullValue
          (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
            context) complete priorValues)
        output (inputEq ▸ reduces)) trace carries

/-- All thirteen endpoint-sensitive source reductions preserve exact source
locations under a coherent canonical root. -/
private theorem endpointReductionLocationHandler
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens) :
    EndpointReductionLocationHandler file tokens memo correct final owned := by
  intro rule origin finish context priorValues complete coherentPrefix
    ruleInput output reduces classified inputEq trace carries
  cases classified with
  | importDeclItems origin finish importKw reference dot openBrace entries
      closeBrace hidingValue semicolon witness =>
      exact RuleReduction.importDeclItems_coherentRootLocationSound
        tokensOrdered origin finish importKw reference dot openBrace entries
          closeBrace hidingValue semicolon witness inputEq
  | exportDeclLocal origin finish exportKw openBrace entries closeBrace
      semicolon witness =>
      exact RuleReduction.exportDeclLocal_coherentRootLocationSound
        tokensOrdered origin finish exportKw openBrace entries closeBrace
          semicolon witness inputEq
  | exportDeclWildcard origin finish exportKw reference dot star semicolon
      starMarker witness =>
      exact RuleReduction.ExportDeclWildcardLocationCase.coherentRootLocationSound
        tokensOrdered
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)
        (.wildcard origin finish exportKw reference dot star semicolon
          starMarker witness) inputEq
  | exportDeclBraced origin finish exportKw reference dot openBrace entries
      closeBrace semicolon witness =>
      exact RuleReduction.exportDeclBraced_coherentRootLocationSound
        tokensOrdered origin finish exportKw reference dot openBrace entries
          closeBrace semicolon witness inputEq
  | matchArm reduces =>
      cases reduces with
      | matchArm origin finish pipe patterns fatArrow statements witness =>
          exact RuleReduction.matchArm_coherentRootLocationSound tokensOrdered
            pipe patterns fatArrow statements witness inputEq
  | logicalOr reduces =>
      cases reduces with
      | logicalOr origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered
            (RuleReduction.logicalOr origin finish left rest)
            (.logicalOr origin finish left rest) inputEq carries
  | logicalAnd reduces =>
      cases reduces with
      | logicalAnd origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered
            (RuleReduction.logicalAnd origin finish left rest)
            (.logicalAnd origin finish left rest) inputEq carries
  | bitOr reduces =>
      cases reduces with
      | bitOr origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered (RuleReduction.bitOr origin finish left rest)
            (.bitOr origin finish left rest) inputEq carries
  | bitXor reduces =>
      cases reduces with
      | bitXor origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered (RuleReduction.bitXor origin finish left rest)
            (.bitXor origin finish left rest) inputEq carries
  | bitAnd reduces =>
      cases reduces with
      | bitAnd origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered (RuleReduction.bitAnd origin finish left rest)
            (.bitAnd origin finish left rest) inputEq carries
  | additive reduces =>
      cases reduces with
      | additive origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered (RuleReduction.additive origin finish left rest)
            (.additive origin finish left rest) inputEq carries
  | multiplicative reduces =>
      cases reduces with
      | multiplicative origin finish left rest =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered
            (RuleReduction.multiplicative origin finish left rest)
            (.multiplicative origin finish left rest) inputEq carries
  | «postfix» reduces =>
      cases reduces with
      | «postfix» origin finish atom parts =>
          exact RuleReduction.ExpressionFoldLocationCase.coherentRootLocationSound
            tokensOrdered
            (RuleReduction.postfix (file := file) (tokens := tokens)
              origin finish atom parts)
            (.postfix (file := file) (tokens := tokens)
              origin finish atom parts) inputEq carries

/-- Lift the canonical endpoint proof through an arbitrary complete parser
item without performing dependent elimination on its transported EBNF input. -/
private theorem endpointActionLocationHandler_of_reduction
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (source : EndpointReductionLocationHandler
      file tokens memo correct final owned) :
    EndpointActionLocationHandler file tokens memo correct final owned := by
  intro item priorValues output complete coherentPrefix action isRoot
    classified trace carries
  cases item with
  | mk raw context =>
      cases raw with
      | mk production dotIndex origin current =>
          rcases isRoot.actionId_eq_root with ⟨rule, actionIdEq⟩
          have productionEq : production = .root rule :=
            actionFor_injective actionIdEq
          subst production
          dsimp only at complete
          have dotEq : dotIndex =
              ⟨(ProductionId.root rule).rhs.length,
                Nat.lt_succ_self _⟩ := by
            apply Fin.ext
            exact complete
          cases dotEq
          cases isRoot
          cases classified
          exact source (by assumption) (by assumption) rfl carries

/-- Complete implementation of the thirteen-case endpoint callback consumed
by the coherent parser location proof. -/
theorem endpointActionLocationHandler
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens) :
    EndpointActionLocationHandler file tokens memo correct final owned :=
  endpointActionLocationHandler_of_reduction
    (endpointReductionLocationHandler tokensOrdered)

namespace Parses

/-- Every successfully parsed module has valid, properly nested source
locations. -/
theorem everyLocationValid
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {module : ParsedModuleV1}
    (lexical : Lexes file tokens comments)
    (parsed : Parses file tokens module) :
    EveryLocationValid file module := by
  apply Parses.everyLocationValid_of_endpointHandler lexical _ parsed
  intro memo correct final
  exact endpointActionLocationHandler lexical.tokenSpansOrdered

end Parses

end Solcore.Surface.Multi
