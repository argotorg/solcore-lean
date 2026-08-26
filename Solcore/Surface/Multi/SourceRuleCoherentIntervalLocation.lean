import Solcore.Surface.Multi.SourceRuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace ActionReduces.RootCase

/-- Lift the endpoint-sensitive source-rule classification through a root
action.  Keeping this proof indexed by the root witness preserves the exact
source reduction needed by each endpoint-specific theorem. -/
inductive IsEndpoint
    {file : WorkspaceFile} {tokens : List Token} :
    {actionId : ActionId} → {origin finish : Boundary tokens} →
      {input : GrammarSymbolValues file tokens actionId.production.rhs} →
      {output : NonterminalValue file tokens actionId.production.lhs} →
      {action : ActionReduces file tokens actionId origin finish input output} →
      ActionReduces.RootCase action → Prop where
  | root
      (rule : GrammarRuleId)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.root rule).rhs)
      (output : RuleValue rule)
      (reduces : RuleReduction file tokens rule origin finish
        (RootAction.unpack rule input) output)
      (classified : RuleReduction.EndpointSensitiveRuleCase reduces) :
      IsEndpoint
        (ActionReduces.RootCase.root rule origin finish input output reduces)

/-- The three-way source classification lifted to an arbitrary root witness.
The module branch records only the production equality needed to discharge
the non-module callback, avoiding dependent elimination of parser state. -/
inductive LocationCase
    {file : WorkspaceFile} {tokens : List Token}
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    {action : ActionReduces file tokens actionId origin finish input output}
    (isRoot : ActionReduces.RootCase action) : Prop where
  | module (lhsEq : actionId.production.lhs = .rule .module) :
      LocationCase isRoot
  | contextFree (classified : IsContextFree isRoot) :
      LocationCase isRoot
  | endpoint (classified : IsEndpoint isRoot) :
      LocationCase isRoot

/-- Classify a root witness without exposing its dependent action indices to
downstream coherent parser state. -/
theorem locationCase
    {file : WorkspaceFile} {tokens : List Token}
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    {action : ActionReduces file tokens actionId origin finish input output}
    (isRoot : ActionReduces.RootCase action) : LocationCase isRoot := by
  cases isRoot with
  | root rule origin finish input output reduces =>
      cases RuleReduction.sourceRuleLocationCase reduces with
      | module _ => exact .module rfl
      | contextFree classified =>
          exact .contextFree
            (.root rule origin finish input output reduces classified)
      | endpoint classified =>
          exact .endpoint
            (.root rule origin finish input output reduces classified)

end ActionReduces.RootCase

/-- The callback still required after all context-free source rules have been
discharged.  Its input is one of the thirteen endpoint-sensitive root actions,
together with the coherent derivation and physical source trace that produced
that action. -/
def EndpointActionLocationHandler
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens) : Prop :=
  ∀ {item : ContextualItemKey tokens}
      {priorValues : PrefixValues file tokens item}
      {output : NonterminalValue file tokens item.raw.production.lhs}
      (complete : CompleteItem item.raw)
      (coherentPrefix : CoherentPrefix file tokens memo correct final
        item priorValues)
      (action : ActionReduces file tokens (.actionFor item.raw.production)
        item.raw.origin item.raw.current
        (PrefixValues.fullValue item complete priorValues) output)
      (isRoot : ActionReduces.RootCase action)
      (_classified : ActionReduces.RootCase.IsEndpoint isRoot)
      (trace : SourceAnchorTrace file tokens)
      (carries : PrefixCarriesSourceTrace
        file tokens memo correct final owned coherentPrefix trace),
    CoherentActionLocationSound complete coherentPrefix action trace carries

namespace ActionReduces.RootCase

/-- Resolve one source root into either its already-proved context-free action
soundness or the endpoint callback.  The module rule is impossible at this
non-module boundary. -/
theorem coherentLocationDisposition
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (lexical : Lexes file tokens comments)
    (endpoint : EndpointActionLocationHandler
      file tokens memo correct final owned)
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    (complete : CompleteItem item.raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output)
    (isRoot : ActionReduces.RootCase action)
    (trace : SourceAnchorTrace file tokens)
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace)
    (notModule : item.raw.production.lhs ≠ .rule .module) :
    CoherentActionLocationDisposition complete coherentPrefix action trace
      carries := by
  cases isRoot.locationCase with
  | module lhsEq =>
      exact (notModule lhsEq).elim
  | contextFree classified =>
      apply CoherentActionLocationDisposition.contextFree
      exact ActionReduces.RootCase.locationSound lexical isRoot classified
  | endpoint classified =>
      apply CoherentActionLocationDisposition.endpoint
      exact endpoint complete coherentPrefix action isRoot classified trace
        carries

end ActionReduces.RootCase

/-- Once the thirteen endpoint cases are supplied, all generated and source
actions satisfy the callback consumed by the coherent location eliminators. -/
theorem nonModuleActionLocationHandler_of_endpoint
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (lexical : Lexes file tokens comments)
    (endpoint : EndpointActionLocationHandler file tokens memo correct final
      lexical.tokensOwnedBy) :
    NonModuleActionLocationHandler file tokens memo correct final
      lexical.tokensOwnedBy := by
  apply nonModuleActionLocationHandler_of_disposition
  apply classifyActionLocation
  intro item priorValues output complete coherentPrefix action isRoot trace
    carries notModule
  exact isRoot.coherentLocationDisposition lexical endpoint complete
    coherentPrefix action trace carries notModule

namespace Parses

/-- Parser-wide source-location validity now reduces exactly to the thirteen
endpoint-sensitive source rules. -/
theorem everyLocationValid_of_endpointHandler
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {module : ParsedModuleV1}
    (lexical : Lexes file tokens comments)
    (endpoint : ∀ {memo : GuardMemo tokens}
        (correct : PhaseBCorrect file tokens memo)
        (final : AllGuardsFinal memo),
      EndpointActionLocationHandler file tokens memo correct final
        lexical.tokensOwnedBy)
    (parsed : Parses file tokens module) :
    EveryLocationValid file module := by
  apply Parses.everyLocationValid_of_locationHandler lexical _ parsed
  intro memo correct final
  exact nonModuleActionLocationHandler_of_endpoint lexical
    (endpoint correct final)

end Parses

end Solcore.Surface.Multi
