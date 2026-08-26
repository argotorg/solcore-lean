import Solcore.Surface.Multi.AuxiliaryInversion
import Solcore.Surface.Multi.ExactTokenReachability

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

universe u v

private theorem production_root_of_lhs_atomInversion
    (production : ProductionId) (rule : GrammarRuleId)
    (lhs : production.lhs = .rule rule) :
    production = .root rule := by
  cases production with
  | root sourceRule =>
      have same : sourceRule = rule := NonterminalSymbol.rule.inj lhs
      subst sourceRule
      rfl
  | atom site => cases lhs
  | seq site => cases lhs
  | group site => cases lhs
  | choice site branch => cases lhs
  | opt site branch => cases lhs
  | star site branch => cases lhs
  | plus site branch => cases lhs
  | list0 site branch => cases lhs
  | list1 site => cases lhs
  | tail site branch => cases lhs

private theorem eqMp_congrArg_trans_atomInversion
    {index : Sort u} (family : index → Sort v)
    {first second third : index}
    (left : first = second) (right : second = third)
    (value : family first) :
    Eq.mp (congrArg family right)
        (Eq.mp (congrArg family left) value) =
      Eq.mp (congrArg family (left.trans right)) value := by
  cases left
  cases right
  rfl

private theorem eqMp_proof_irrel_atomInversion
    {first second : Sort u}
    (left right : first = second) (value : first) :
    Eq.mp left value = Eq.mp right value := by
  have same : left = right := Subsingleton.elim _ _
  cases same
  rfl

private theorem grammarSymbolValue_nonterminal_transport_atomInversion
    {file : WorkspaceFile} {tokens : List Token}
    {left right : NonterminalSymbol}
    (equality : left = right)
    (value : NonterminalValue file tokens left) :
    Eq.mp (congrArg (GrammarSymbolValue file tokens)
        (congrArg GrammarSymbol.nonterminal equality)) value =
      Eq.mp (congrArg (NonterminalValue file tokens) equality) value := by
  cases equality
  rfl

private theorem GrammarSymbolValues.transport_append_empty_single_direct_atomInversion
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol}
    (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full)
    (viewLayout : full = [target]) (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens [])
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport priorLayout.symm empty)
            (value, ())) =
      GrammarSymbolValues.transport viewLayout.symm
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout)
          value, ()) := by
  cases priorLayout
  cases symbolLayout
  cases viewLayout
  rcases empty with ⟨⟩
  have fullProof : fullLayout = rfl := Subsingleton.elim _ _
  rw [fullProof]
  rfl

/-- A coherent completed nonterminal atom exposes the coherent canonical
root reduction of the rule value carried by that atom. -/
theorem coherentAtomRule_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {site : AtomSite} {rule : GrammarRuleId}
    (dot : Fin ((ProductionId.atom site).rhs.length + 1))
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    {output : NonterminalValue file tokens (ProductionId.atom site).lhs}
    {value : RuleValue rule}
    (shape : site.atom = .nonterminal rule)
    (notPostfix : rule ≠ .postfix)
    (outputView : EbnfValue.transport (congrArg EbnfExpr.atom shape)
        (EbnfValue.atShape site.expression_eq_atom output) =
      EbnfValue.ruleAtom rule value)
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .atom site
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) value := by
  let item : ContextualItemKey tokens := {
    raw := {
      production := .atom site
      dot := dot
      origin := origin
      current := finish
    }
    context := context
  }
  change CoherentReduction file tokens memo correct final item output
    at coherent
  cases coherent with
  | reduce _ priorValues _ reached complete coherentPrefix action =>
      have itemComplete : item.raw.dot.val = 1 := by
        calc
          _ = item.raw.production.rhs.length := complete
          _ = 1 := by
            simp [item, ProductionId.rhs, AtomSite.symbol]
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues witness edge prior =>
          have impossible : some (GrammarSymbol.terminal witness.terminal) =
              some (GrammarSymbol.nonterminal (.rule rule)) := by
            have beforeProduction : before.raw.production = .atom site := by
              simpa [item] using witness.advance.1.symm
            have beforeZero : before.raw.dot.val = 0 := by
              have advanced := witness.advance.2.1
              omega
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                witness.next.2.symm
              _ = (ProductionId.atom site).rhs[0]? := by
                let index := before.raw.dot.val
                have indexZero : index = 0 := beforeZero
                calc
                  _ = (ProductionId.atom site).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexZero]
              _ = _ := by
                simp [ProductionId.rhs, AtomSite.symbol,
                  EbnfAtom.grammarSymbol, shape]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete waiting child after shared priorValues childValue witness
          edge prior childCoherent =>
          have waitingProduction : waiting.raw.production = .atom site := by
            simpa [item] using witness.advance.1.symm
          have waitingZero : waiting.raw.dot.val = 0 := by
            have advanced := witness.advance.2.1
            omega
          have childLhs : child.raw.production.lhs = .rule rule := by
            have selected : some (GrammarSymbol.nonterminal
                  child.raw.production.lhs) =
                some (GrammarSymbol.nonterminal (.rule rule)) := by
              calc
                _ = waiting.raw.production.rhs[waiting.raw.dot.val]? :=
                  witness.next.2.symm
                _ = (ProductionId.atom site).rhs[0]? := by
                  let index := waiting.raw.dot.val
                  have indexZero : index = 0 := waitingZero
                  calc
                    _ = (ProductionId.atom site).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) waitingProduction
                    _ = _ := by rw [indexZero]
                _ = _ := by
                  simp [ProductionId.rhs, AtomSite.symbol,
                    EbnfAtom.grammarSymbol, shape]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          have childProduction : child.raw.production = .root rule :=
            production_root_of_lhs_atomInversion child.raw.production rule
              childLhs
          have waitingOriginCurrent : waiting.raw.origin =
              waiting.raw.current :=
            contextualReach_zero_origin_eq_current edge.2.1 waitingZero
          have childOrigin : child.raw.origin = origin := by
            calc
              _ = shared := witness.finishedAtShared
              _ = waiting.raw.current := witness.waitingAtShared.symm
              _ = waiting.raw.origin := waitingOriginCurrent.symm
              _ = origin := by simpa [item] using witness.advance.2.2.1.symm
          have childCurrent : child.raw.current = finish := by
            simpa [item] using witness.advance.2.2.2.symm
          have childContext : child.context = context := by
            calc
              _ = descendContext waiting child.raw.production := edge.1.2.1
              _ = waiting.context := by
                rw [childProduction]
                simp [descendContext, ProductionId.lhs, notPostfix]
              _ = context := by simpa [item] using edge.1.2.2.symm
          have priorLayout : waiting.raw.production.rhs.take
                waiting.raw.dot.val = [] := by
            let index := waiting.raw.dot.val
            have indexZero : index = 0 := waitingZero
            calc
              _ = (ProductionId.atom site).rhs.take index :=
                congrArg (fun production : ProductionId =>
                  production.rhs.take index) waitingProduction
              _ = (ProductionId.atom site).rhs.take 0 := by rw [indexZero]
              _ = [] := by simp
          let empty := GrammarSymbolValues.transport priorLayout priorValues
          have priorRecover : GrammarSymbolValues.transport priorLayout.symm
                empty = priorValues := by
            dsimp only [empty]
            rw [GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have fullLayout : waiting.raw.production.rhs.take
                waiting.raw.dot.val ++ [GrammarSymbol.nonterminal
                  child.raw.production.lhs] =
              (ProductionId.atom site).rhs := by
            simpa [item] using
              ((prefix_complete_layout waiting.raw child.raw item.raw
                witness.next witness.advance).trans
                (prefix_full_layout item.raw complete))
          have symbolLayout : GrammarSymbol.nonterminal
                child.raw.production.lhs = site.symbol := by
            rw [childLhs, AtomSite.symbol, shape]
            rfl
          have tupleEq :=
            GrammarSymbolValues.transport_append_empty_single_direct_atomInversion
              priorLayout fullLayout (ProductionId.rhs_atom site)
              symbolLayout empty childValue
          have packedEq := actionReduces_eleven_shapes_exact.mp action
          change output = AtomSite.pack site _ at packedEq
          rw [PrefixValues.fullValue_completeValue_eq] at packedEq
          rw [← priorRecover] at packedEq
          conv at packedEq in (GrammarSymbolValues.transport _ _) =>
            rw [tupleEq]
          let atomValues : GrammarSymbolValues file tokens
              (ProductionId.atom site).rhs :=
            GrammarSymbolValues.transport
              (ProductionId.rhs_atom site).symm
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                symbolLayout) childValue, ())
          change output = AtomSite.pack site atomValues at packedEq
          have atomView : GrammarSymbolValues.view
                (ProductionId.rhs_atom site) atomValues =
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                symbolLayout) childValue, ()) := by
            dsimp only [atomValues, GrammarSymbolValues.view]
            rw [GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have packedView := congrArg
            (fun packed => EbnfValue.transport
              (congrArg EbnfExpr.atom shape)
              (EbnfValue.atShape site.expression_eq_atom packed))
            packedEq
          have packRule := AtomSite.pack_rule_eq site rule shape atomValues
          rw [atomView] at packRule
          let encodedChild : RuleValue rule :=
            Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol shape))
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                  site.symbol_eq)
                (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                  symbolLayout) childValue))
          have encodedChildEq : encodedChild =
              Eq.mp (congrArg (NonterminalValue file tokens) childLhs)
                childValue := by
            let grammarChild : GrammarSymbolValue file tokens
                (.nonterminal child.raw.production.lhs) := childValue
            have firstTwo := eqMp_congrArg_trans_atomInversion
              (GrammarSymbolValue file tokens)
              symbolLayout site.symbol_eq grammarChild
            have allThree := eqMp_congrArg_trans_atomInversion
              (GrammarSymbolValue file tokens)
              (symbolLayout.trans site.symbol_eq)
              (congrArg EbnfAtom.grammarSymbol shape) grammarChild
            have combined : encodedChild = Eq.mp
                (congrArg (GrammarSymbolValue file tokens)
                  ((symbolLayout.trans site.symbol_eq).trans
                    (congrArg EbnfAtom.grammarSymbol shape)))
                grammarChild := by
              calc
                encodedChild = Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      (congrArg EbnfAtom.grammarSymbol shape))
                    (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                        site.symbol_eq)
                      (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                        symbolLayout) grammarChild)) := rfl
                _ = Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      (congrArg EbnfAtom.grammarSymbol shape))
                    (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                      (symbolLayout.trans site.symbol_eq))
                      grammarChild) := congrArg _ firstTwo
                _ = Eq.mp (congrArg (GrammarSymbolValue file tokens)
                      ((symbolLayout.trans site.symbol_eq).trans
                        (congrArg EbnfAtom.grammarSymbol shape)))
                    grammarChild := allThree
            have directGrammar : Eq.mp
                  (congrArg (GrammarSymbolValue file tokens)
                    ((symbolLayout.trans site.symbol_eq).trans
                      (congrArg EbnfAtom.grammarSymbol shape)))
                  grammarChild =
                Eq.mp (congrArg (GrammarSymbolValue file tokens)
                    (congrArg GrammarSymbol.nonterminal childLhs))
                  grammarChild := by
              exact eqMp_proof_irrel_atomInversion _ _ grammarChild
            have directNonterminal : Eq.mp
                  (congrArg (GrammarSymbolValue file tokens)
                    (congrArg GrammarSymbol.nonterminal childLhs))
                  grammarChild =
                Eq.mp (congrArg (NonterminalValue file tokens) childLhs)
                  childValue := by
              exact grammarSymbolValue_nonterminal_transport_atomInversion
                childLhs childValue
            exact combined.trans (directGrammar.trans directNonterminal)
          have packRuleValue : EbnfValue.transport
                (congrArg EbnfExpr.atom shape)
                (EbnfValue.atShape site.expression_eq_atom
                  (AtomSite.pack site atomValues)) =
              EbnfValue.ruleAtom rule encodedChild := by
            simpa only [AtomSite.packAtAtom, encodedChild] using packRule
          have encodedChildValue : encodedChild = value := by
            apply EbnfValue.ruleAtom_injective rule
            exact (packedView.trans packRuleValue).symm.trans outputView
          have childValueEq :
              Eq.mp (congrArg (NonterminalValue file tokens) childLhs)
                  childValue = value := by
            exact encodedChildEq.symm.trans encodedChildValue
          have childComplete : CompleteItem child.raw := by
            cases childCoherent
            assumption
          have canonical := child.eq_canonicalCompleteRoot
            childProduction childComplete
          have canonicalEq : child =
              CanonicalCompleteRootItem tokens rule origin finish context := by
            rw [canonical, childOrigin, childCurrent, childContext]
          cases canonicalEq
          change RuleValue rule at childValue
          change childValue = value at childValueEq
          subst childValue
          exact childCoherent

end Solcore.Surface.Multi
