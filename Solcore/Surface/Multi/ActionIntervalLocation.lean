import Solcore.Surface.Multi.AuxiliaryIntervalLocation
import Solcore.Surface.Multi.RuleIntervalLocationExact
import Solcore.Surface.Multi.RuleIntervalLocationWrapped
import Solcore.Surface.Multi.AssemblyIntervalLocation
import Solcore.Surface.Multi.ModuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

/-- The 160 non-endpoint source reductions already handled by aggregate
interval evidence: 38 exact, 121 wrapped, and the assembly reduction. -/
inductive ContextFreeLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | exact
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (classified : RuleReduction.ExactLocation reduces) :
      ContextFreeLocationCase reduces
  | wrapped
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (classified : RuleReduction.WrappedLocation reduces) :
      ContextFreeLocationCase reduces
  | assembly
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)}
      {output : RuleValue .assemblyStatement}
      (reduces : RuleReduction file tokens .assemblyStatement
        origin finish input output) :
      ContextFreeLocationCase reduces

namespace ContextFreeLocationCase

/-- Resolve the context-free partition.  `Lexes` is stronger than two of the
branches need, but provides both token ordering and the assembly-slice facts
at the one integration point. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    (lexical : Lexes file tokens comments)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (classified : ContextFreeLocationCase reduces) :
    RuleReduction.LocationSound reduces := by
  cases classified with
  | exact exactCase => exact exactCase.locationSound
  | wrapped wrappedCase =>
      exact wrappedCase.locationSound lexical.tokenSpansOrdered
  | assembly assemblyReduction =>
      exact RuleReduction.assemblyStatement_locationSound lexical
        assemblyReduction

end ContextFreeLocationCase

end RuleReduction

namespace ActionReduces

/-- Proof-relevant discriminator used by the integration layer: only source
rule roots need the 174-constructor source-rule dispatch. -/
inductive RootCase
    {file : WorkspaceFile} {tokens : List Token} :
    {action : ActionId} → {origin finish : Boundary tokens} →
      {input : GrammarSymbolValues file tokens action.production.rhs} →
      {output : NonterminalValue file tokens action.production.lhs} →
      ActionReduces file tokens action origin finish input output → Prop where
  | root
      (rule : GrammarRuleId)
      (origin finish : Boundary tokens)
      (input : GrammarSymbolValues file tokens
        (ProductionId.root rule).rhs)
      (output : RuleValue rule)
      (reduces : RuleReduction file tokens rule origin finish
        (RootAction.unpack rule input) output) :
      RootCase (ActionReduces.root rule origin finish input output reduces)

/-- Generated actions are context-free; otherwise the action is a source-rule
root and is handed to the source-rule dispatcher. -/
theorem locationSound_or_root
    {file : WorkspaceFile} {tokens : List Token}
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    (action : ActionReduces file tokens actionId origin finish input output) :
    ActionLocationSound action ∨ ActionReduces.RootCase action := by
  cases action with
  | root rule origin finish input output reduces =>
      exact Or.inr (.root rule origin finish input output reduces)
  | atom site origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .atom site) trivial
          (ActionReduces.atom site origin finish input))
  | seq site origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .seq site) trivial
          (ActionReduces.seq site origin finish input))
  | group site origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .group site) trivial
          (ActionReduces.group site origin finish input))
  | choice site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .choice site branch) trivial
          (ActionReduces.choice site branch origin finish input))
  | opt site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .opt site branch) trivial
          (ActionReduces.opt site branch origin finish input))
  | star site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .star site branch) trivial
          (ActionReduces.star site branch origin finish input))
  | plus site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .plus site branch) trivial
          (ActionReduces.plus site branch origin finish input))
  | list0 site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .list0 site branch) trivial
          (ActionReduces.list0 site branch origin finish input))
  | list1 site origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .list1 site) trivial
          (ActionReduces.list1 site origin finish input))
  | tail site branch origin finish input =>
      exact Or.inl
        (ActionReduces.auxiliary_locationSound
          (production := .tail site branch) trivial
          (ActionReduces.tail site branch origin finish input))

namespace RootCase

/-- Pull the source-reduction classifier through the root-action wrapper. -/
inductive IsContextFree
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
      (classified : RuleReduction.ContextFreeLocationCase reduces) :
      IsContextFree
        (ActionReduces.RootCase.root rule origin finish input output reduces)

/-- Lift a classified source reduction through `ActionReduces.root`. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    (lexical : Lexes file tokens comments)
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    {action : ActionReduces file tokens actionId origin finish input output}
    (isRoot : ActionReduces.RootCase action)
    (classified : IsContextFree isRoot) :
    ActionLocationSound action := by
  cases classified with
  | root rule origin finish input output reduces contextFree =>
      exact ActionReduces.root_locationSound reduces
        (contextFree.locationSound lexical)

end RootCase

end ActionReduces

/-- The action-level handler consumed by the two coherent-trace eliminators. -/
def NonModuleActionLocationHandler
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
      (trace : SourceAnchorTrace file tokens)
      (carries : PrefixCarriesSourceTrace
        file tokens memo correct final owned coherentPrefix trace)
      (_notModule : item.raw.production.lhs ≠ .rule .module),
    CoherentActionLocationSound complete coherentPrefix action trace carries

/-- Most actions have context-free soundness.  The thirteen actions that
construct spans from named internal endpoints instead supply the right arm. -/
def CoherentActionLocationDisposition
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    (complete : CompleteItem item.raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output)
    (trace : SourceAnchorTrace file tokens)
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace) : Prop :=
  ActionLocationSound action ∨
    CoherentActionLocationSound complete coherentPrefix action trace carries

namespace CoherentActionLocationDisposition

/-- Inject context-free action soundness into the dispatcher. -/
theorem contextFree
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    {complete : CompleteItem item.raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues}
    {action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output}
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace}
    (sound : ActionLocationSound action) :
    CoherentActionLocationDisposition complete coherentPrefix action trace
      carries :=
  Or.inl sound

/-- Inject the endpoint-sensitive coherent proof branch. -/
theorem endpoint
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    {complete : CompleteItem item.raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues}
    {action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output}
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace}
    (sound : CoherentActionLocationSound complete coherentPrefix action trace
      carries) :
    CoherentActionLocationDisposition complete coherentPrefix action trace
      carries :=
  Or.inr sound

/-- Resolve either branch into the coherent action contract. -/
theorem resolve
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    {complete : CompleteItem item.raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues}
    {action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output}
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace}
    (disposition : CoherentActionLocationDisposition complete coherentPrefix
      action trace carries) :
    CoherentActionLocationSound complete coherentPrefix action trace carries :=
  disposition.elim ActionLocationSound.coherent id

end CoherentActionLocationDisposition

/-- Turn the exhaustive action classification into the exact callback expected
by `PrefixCarriesSourceTrace.locationEvidence` and
`ReductionCarriesSourceTrace.locationEvidence`. -/
theorem nonModuleActionLocationHandler_of_disposition
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (classify : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationDisposition complete coherentPrefix action trace
        carries) :
    NonModuleActionLocationHandler file tokens memo correct final owned := by
  intro item priorValues output complete coherentPrefix action trace carries
    notModule
  exact (classify complete coherentPrefix action trace carries notModule).resolve

/-- Only root actions remain for the source-rule dispatcher.  Every generated
action is discharged here by `auxiliary_locationSound`. -/
theorem classifyActionLocation
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (root : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (_isRoot : ActionReduces.RootCase action)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationDisposition complete coherentPrefix action trace
        carries) :
    ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationDisposition complete coherentPrefix action trace
        carries := by
  intro item priorValues output complete coherentPrefix action trace carries
    notModule
  rcases action.locationSound_or_root with contextFree | isRoot
  · exact .contextFree contextFree
  · exact root complete coherentPrefix action isRoot trace carries notModule

/-- The prefix eliminator fed from the integration-layer classification. -/
theorem PrefixCarriesSourceTrace.locationEvidence_of_disposition
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (classify : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationDisposition complete coherentPrefix action trace
        carries)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (PrefixValues.locationFragment item values) trace :=
  carries.locationEvidence
    (nonModuleActionLocationHandler_of_disposition classify)

/-- The reduction eliminator fed from the same integration-layer
classification.  The module exclusion stays explicit at this boundary. -/
theorem ReductionCarriesSourceTrace.locationEvidence_of_disposition
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (classify : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationDisposition complete coherentPrefix action trace
        carries)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace)
    (notModule : item.raw.production.lhs ≠ .rule .module) :
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.locationFragment item.raw.production.lhs value) trace :=
  carries.locationEvidence
    (nonModuleActionLocationHandler_of_disposition classify) notModule

namespace CanonicalCompleteRootReduction

/-- The module root leaves the ordinary reduction eliminator before its
non-module premise.  Its coherent prefix is certified by the same handler,
then the dedicated module theorem installs the possibly-empty full-file root. -/
theorem moduleWholeFileEvidence
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {module : ParsedModuleV1}
    (lexical : Lexes file tokens comments)
    (handler : NonModuleActionLocationHandler file tokens memo correct final
      lexical.tokensOwnedBy)
    (reduction : CanonicalCompleteRootReduction
      file tokens memo correct final .module
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
      .plain module) :
    ∃ trace : SourceAnchorTrace file tokens,
      WholeFileLocationEvidence file tokens
        (LocationFragment.ofParsedModule module) trace := by
  rcases reduction with ⟨_reached, _complete, coherent⟩
  let moduleItem := CanonicalCompleteRootItem tokens .module
    (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain
  cases coherent with
  | reduce item priorValues output reached complete coherentPrefix action =>
      rcases coherentPrefix.sourceTrace_exists lexical.tokensOwnedBy with
        ⟨trace, carries⟩
      have prefixEvidence := carries.locationEvidence handler
      have fullInputEvidence : IntervalLocationEvidence file tokens
          moduleItem.raw.origin moduleItem.raw.current
          (GrammarSymbolValues.locationFragment
            moduleItem.raw.production.rhs
            (PrefixValues.fullValue moduleItem complete priorValues)) trace :=
        IntervalLocationEvidence.replaceFragment
          (PrefixValues.locationFragment_fullValue
            moduleItem complete priorValues).symm prefixEvidence
      cases action with
      | root rule origin finish input output reduces =>
          have ruleInputEvidence : IntervalLocationEvidence file tokens
              moduleItem.raw.origin moduleItem.raw.current
              (RootAction.unpack .module
                (PrefixValues.fullValue moduleItem complete
                  priorValues)).locationFragment trace :=
            IntervalLocationEvidence.replaceFragment
              (RootAction.unpack_locationFragment .module
                (PrefixValues.fullValue moduleItem complete
                  priorValues)).symm
              fullInputEvidence
          exact ⟨trace,
            RuleReduction.module_locationSound lexical.tokenSpansOrdered
              reduces trace ruleInputEvidence⟩

/-- Executable location validity follows immediately from the whole-file
evidence produced for the canonical module root. -/
theorem moduleEveryLocationValid
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {module : ParsedModuleV1}
    (lexical : Lexes file tokens comments)
    (handler : NonModuleActionLocationHandler file tokens memo correct final
      lexical.tokensOwnedBy)
    (reduction : CanonicalCompleteRootReduction
      file tokens memo correct final .module
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
      .plain module) :
    EveryLocationValid file module := by
  rcases moduleWholeFileEvidence lexical handler reduction with
    ⟨_trace, evidence⟩
  exact evidence.everyLocationValid

end CanonicalCompleteRootReduction

namespace Parses

/-- Final facade immediately below the public parse theorem.  The handler may
depend on the final guard memo selected by the coherent parse. -/
theorem everyLocationValid_of_locationHandler
    {file : WorkspaceFile} {tokens : List Token} {comments : List Comment}
    {module : ParsedModuleV1}
    (lexical : Lexes file tokens comments)
    (handler : ∀ {memo : GuardMemo tokens}
        (correct : PhaseBCorrect file tokens memo)
        (final : AllGuardsFinal memo),
      NonModuleActionLocationHandler file tokens memo correct final
        lexical.tokensOwnedBy)
    (parsed : Parses file tokens module) :
    EveryLocationValid file module := by
  rcases parser_consumes_all parsed with
    ⟨memo, correct, final, reduction⟩
  exact CanonicalCompleteRootReduction.moduleEveryLocationValid lexical
    (handler correct final) reduction

end Parses

end Solcore.Surface.Multi
