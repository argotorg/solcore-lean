import Solcore.Surface.Multi.AuxiliaryInversion
import Solcore.Surface.Multi.ExactTokenReachability
import Solcore.Surface.Multi.RuleCoherentIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem GrammarSymbolValues.transport_append_empty_single_coherentStarLocal
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol}
    (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full)
    (viewLayout : full = [target]) (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens [])
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport priorLayout.symm empty)
            (value, ()))) =
      (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout)
        value, ()) := by
  cases priorLayout
  cases symbolLayout
  cases viewLayout
  rcases empty with ⟨⟩
  have fullProof : fullLayout = rfl := Subsingleton.elim _ _
  rw [fullProof]
  rfl

private theorem grammarSymbolValues_transport_pair_second_coherentStarLocal
    {file : WorkspaceFile} {tokens : List Token}
    {first : GrammarSymbol} {left right : NonterminalSymbol}
    (equality : left = right)
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : NonterminalValue file tokens left)
    (layout : [first, GrammarSymbol.nonterminal right] =
      [first, GrammarSymbol.nonterminal left]) :
    GrammarSymbolValues.transport layout.symm
        (firstValue, (secondValue, ())) =
      (firstValue,
        (Eq.mp (congrArg (NonterminalValue file tokens) equality)
          secondValue, ())) := by
  cases equality
  have layoutEq : layout = rfl := Subsingleton.elim _ _
  rw [layoutEq]
  rfl

private theorem grammarSymbolValue_nonterminal_transport_coherentStarLocal
    {file : WorkspaceFile} {tokens : List Token}
    {left right : NonterminalSymbol}
    (equality : left = right)
    (value : NonterminalValue file tokens left) :
    Eq.mp (congrArg (GrammarSymbolValue file tokens)
        (congrArg GrammarSymbol.nonterminal equality)) value =
      Eq.mp (congrArg (NonterminalValue file tokens) equality) value := by
  cases equality
  rfl

private theorem production_atom_of_lhs_site
    (production : ProductionId) (site : AtomSite)
    (lhs : production.lhs = .aux site.site) :
    production = .atom site := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | atom refined same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact exact

private theorem production_star_of_lhs_site
    (production : ProductionId) (site : StarSite)
    (lhs : production.lhs = .aux site.site) :
    ∃ branch, production = .star site branch := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | star refined branch same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact ⟨branch, exact⟩

/-- The exact child reductions and semantic list view carried by a coherent
extending star production. -/
def CoherentStarConsView
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (site : StarSite)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    (output : NonterminalValue file tokens
      (ProductionId.star site .cons).lhs) : Prop :=
  ∃ (head tail : ContextualItemKey tokens),
    ∃ (headValue : NonterminalValue file tokens
      head.raw.production.lhs),
    ∃ (tailValue : NonterminalValue file tokens
      tail.raw.production.lhs),
    ∃ (tailBranch : NilConsBranch),
    ∃ (headLhs : head.raw.production.lhs = .aux site.child),
    ∃ (tailLhs : tail.raw.production.lhs = .aux site.site),
      tail.raw.production = .star site tailBranch ∧
      head.raw.origin = origin ∧
      head.raw.current = tail.raw.origin ∧
      tail.raw.current = finish ∧
      head.context = context ∧
      tail.context = context ∧
      CoherentReduction file tokens memo correct final head headValue ∧
      CoherentReduction file tokens memo correct final tail tailValue ∧
      EbnfValue.atShape site.expression_eq_star output =
        EbnfValue.star site.child.expression
          (Eq.mp (congrArg (NonterminalValue file tokens) headLhs)
              headValue ::
            Eq.mp (ebnfValue_star_eq site.child.expression)
              (EbnfValue.atShape site.expression_eq_star
                (Eq.mp (congrArg (NonterminalValue file tokens) tailLhs)
                  tailValue)))

theorem coherentStarCons_children
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {site : StarSite}
    (dot : Fin ((ProductionId.star site .cons).rhs.length + 1))
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    {output : NonterminalValue file tokens (ProductionId.star site .cons).lhs}
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star site .cons
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) :
    CoherentStarConsView file tokens memo correct final site origin finish
      context output := by
  let item : ContextualItemKey tokens := {
    raw := {
      production := .star site .cons
      dot := dot
      origin := origin
      current := finish
    }
    context := context
  }
  change CoherentReduction file tokens memo correct final item output at coherent
  cases coherent with
  | reduce _ values _ reached complete coherentPrefix action =>
      have itemComplete : item.raw.dot.val = 2 := by
        calc
          _ = item.raw.production.rhs.length := complete
          _ = 2 := by simp [item, ProductionId.rhs]
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues witness edge prior =>
          have beforeProduction : before.raw.production = .star site .cons := by
            simpa [item] using witness.advance.1.symm
          have beforeDot : before.raw.dot.val = 1 := by
            have advanced := witness.advance.2.1
            omega
          have impossible : some (GrammarSymbol.terminal witness.terminal) =
              some (GrammarSymbol.nonterminal (.aux site.site)) := by
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                witness.next.2.symm
              _ = (ProductionId.star site .cons).rhs[1]? := by
                let index := before.raw.dot.val
                have indexOne : index = 1 := beforeDot
                calc
                  _ = (ProductionId.star site .cons).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexOne]
              _ = _ := by simp [ProductionId.rhs]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete tailWaiting tail after shared tailPriorValues tailValue
          tailWitness tailEdge tailPrior tailCoherent =>
          have tailWaitingProduction : tailWaiting.raw.production =
              .star site .cons := by
            simpa [item] using tailWitness.advance.1.symm
          have tailWaitingDot : tailWaiting.raw.dot.val = 1 := by
            have advanced := tailWitness.advance.2.1
            omega
          have tailLhs : tail.raw.production.lhs = .aux site.site := by
            have selected : some (GrammarSymbol.nonterminal
                  tail.raw.production.lhs) =
                some (GrammarSymbol.nonterminal (.aux site.site)) := by
              calc
                _ = tailWaiting.raw.production.rhs[
                    tailWaiting.raw.dot.val]? := tailWitness.next.2.symm
                _ = (ProductionId.star site .cons).rhs[1]? := by
                  let index := tailWaiting.raw.dot.val
                  have indexOne : index = 1 := tailWaitingDot
                  calc
                    _ = (ProductionId.star site .cons).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) tailWaitingProduction
                    _ = _ := by rw [indexOne]
                _ = _ := by simp [ProductionId.rhs]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          rcases production_star_of_lhs_site tail.raw.production site tailLhs
            with ⟨tailBranch, tailProduction⟩
          cases tailPrior with
          | zero _ _ zero => omega
          | scan before after cursor priorValues witness edge prior =>
              have beforeProduction : before.raw.production =
                  .star site .cons := by
                exact witness.advance.1.symm.trans tailWaitingProduction
              have beforeZero : before.raw.dot.val = 0 := by
                have advanced := witness.advance.2.1
                omega
              have impossible : some
                    (GrammarSymbol.terminal witness.terminal) =
                  some (GrammarSymbol.nonterminal (.aux site.child)) := by
                calc
                  _ = before.raw.production.rhs[before.raw.dot.val]? :=
                    witness.next.2.symm
                  _ = (ProductionId.star site .cons).rhs[0]? := by
                    let index := before.raw.dot.val
                    have indexZero : index = 0 := beforeZero
                    calc
                      _ = (ProductionId.star site .cons).rhs[index]? :=
                        congrArg (fun production : ProductionId =>
                          production.rhs[index]?) beforeProduction
                      _ = _ := by rw [indexZero]
                  _ = _ := by simp [ProductionId.rhs]
              exact GrammarSymbol.noConfusion (Option.some.inj impossible)
          | complete headWaiting head after headShared headPriorValues
              headValue headWitness headEdge headPrior headCoherent =>
              have headWaitingProduction : headWaiting.raw.production =
                  .star site .cons := by
                exact headWitness.advance.1.symm.trans tailWaitingProduction
              have headWaitingZero : headWaiting.raw.dot.val = 0 := by
                have advanced := headWitness.advance.2.1
                omega
              have headLhs : head.raw.production.lhs = .aux site.child := by
                have selected : some (GrammarSymbol.nonterminal
                      head.raw.production.lhs) =
                    some (GrammarSymbol.nonterminal (.aux site.child)) := by
                  calc
                    _ = headWaiting.raw.production.rhs[
                        headWaiting.raw.dot.val]? := headWitness.next.2.symm
                    _ = (ProductionId.star site .cons).rhs[0]? := by
                      let index := headWaiting.raw.dot.val
                      have indexZero : index = 0 := headWaitingZero
                      calc
                        _ = (ProductionId.star site .cons).rhs[index]? :=
                          congrArg (fun production : ProductionId =>
                            production.rhs[index]?) headWaitingProduction
                        _ = _ := by rw [indexZero]
                    _ = _ := by simp [ProductionId.rhs]
                exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
              have headWaitingOriginCurrent : headWaiting.raw.origin =
                  headWaiting.raw.current :=
                contextualReach_zero_origin_eq_current headEdge.2.1
                  headWaitingZero
              have headOrigin : head.raw.origin = origin := by
                calc
                  _ = headShared := headWitness.finishedAtShared
                  _ = headWaiting.raw.current :=
                    headWitness.waitingAtShared.symm
                  _ = headWaiting.raw.origin := headWaitingOriginCurrent.symm
                  _ = tailWaiting.raw.origin :=
                    headWitness.advance.2.2.1.symm
                  _ = origin := by
                    simpa [item] using tailWitness.advance.2.2.1.symm
              have headTail : head.raw.current = tail.raw.origin := by
                calc
                  _ = tailWaiting.raw.current :=
                    headWitness.advance.2.2.2.symm
                  _ = shared := tailWitness.waitingAtShared
                  _ = tail.raw.origin := tailWitness.finishedAtShared.symm
              have tailFinish : tail.raw.current = finish := by
                simpa [item] using tailWitness.advance.2.2.2.symm
              have headContext : head.context = context := by
                calc
                  _ = descendContext headWaiting head.raw.production :=
                    headEdge.1.2.1
                  _ = headWaiting.context := by
                    cases productionEq : head.raw.production <;>
                      simp_all [descendContext, ProductionId.lhs]
                  _ = tailWaiting.context := headEdge.1.2.2.symm
                  _ = context := by simpa [item] using tailEdge.1.2.2.symm
              have tailContext : tail.context = context := by
                calc
                  _ = descendContext tailWaiting tail.raw.production :=
                    tailEdge.1.2.1
                  _ = tailWaiting.context := by
                    simp [descendContext, tailWaitingProduction,
                      tailProduction]
                  _ = context := by simpa [item] using tailEdge.1.2.2.symm
              have headPriorLayout :
                  headWaiting.raw.production.rhs.take
                    headWaiting.raw.dot.val = [] := by
                let index := headWaiting.raw.dot.val
                have indexZero : index = 0 := headWaitingZero
                calc
                  _ = (ProductionId.star site .cons).rhs.take index :=
                    congrArg (fun production : ProductionId =>
                      production.rhs.take index) headWaitingProduction
                  _ = (ProductionId.star site .cons).rhs.take 0 := by
                    rw [indexZero]
                  _ = [] := by simp
              have tailPriorLayout :
                  tailWaiting.raw.production.rhs.take
                    tailWaiting.raw.dot.val = [
                      .nonterminal (.aux site.child)] := by
                let index := tailWaiting.raw.dot.val
                have indexOne : index = 1 := tailWaitingDot
                calc
                  _ = (ProductionId.star site .cons).rhs.take index :=
                    congrArg (fun production : ProductionId =>
                      production.rhs.take index) tailWaitingProduction
                  _ = (ProductionId.star site .cons).rhs.take 1 := by
                    rw [indexOne]
                  _ = _ := by simp [ProductionId.rhs]
              let headEmpty := GrammarSymbolValues.transport
                headPriorLayout headPriorValues
              have headPriorRecover : GrammarSymbolValues.transport
                    headPriorLayout.symm headEmpty = headPriorValues := by
                dsimp only [headEmpty]
                rw [GrammarSymbolValues.transport_trans]
                exact GrammarSymbolValues.transport_self _ _
              have headSymbolLayout :
                  GrammarSymbol.nonterminal head.raw.production.lhs =
                    .nonterminal (.aux site.child) :=
                congrArg GrammarSymbol.nonterminal headLhs
              have tailPriorCanonical :
                  GrammarSymbolValues.transport tailPriorLayout
                    (PrefixValues.completeValue headWaiting head tailWaiting
                      headWitness.next headWitness.advance headPriorValues
                      headValue) =
                    (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                      headSymbolLayout) headValue, ()) := by
                rw [← headPriorRecover]
                exact
                  GrammarSymbolValues.transport_append_empty_single_coherentStarLocal
                    headPriorLayout
                    (prefix_complete_layout headWaiting.raw head.raw
                      tailWaiting.raw headWitness.next headWitness.advance)
                    tailPriorLayout headSymbolLayout headEmpty headValue
              let headEncoded : EbnfValue file tokens
                  site.child.expression :=
                Eq.mp (congrArg (NonterminalValue file tokens) headLhs)
                  headValue
              let tailEncoded : EbnfValue file tokens site.site.expression :=
                Eq.mp (congrArg (NonterminalValue file tokens) tailLhs)
                  tailValue
              have headGrammarEncoded : Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      headSymbolLayout) headValue = headEncoded := by
                exact grammarSymbolValue_nonterminal_transport_coherentStarLocal
                  headLhs headValue
              have tailPriorRecover : GrammarSymbolValues.transport
                    tailPriorLayout.symm (headEncoded, ()) =
                  PrefixValues.completeValue headWaiting head tailWaiting
                    headWitness.next headWitness.advance headPriorValues
                    headValue := by
                calc
                  _ = GrammarSymbolValues.transport tailPriorLayout.symm
                      (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                        headSymbolLayout) headValue, ()) := by
                    apply congrArg
                      (GrammarSymbolValues.transport tailPriorLayout.symm)
                    apply Prod.ext
                    · exact headGrammarEncoded.symm
                    · rfl
                  _ = GrammarSymbolValues.transport tailPriorLayout.symm
                      (GrammarSymbolValues.transport tailPriorLayout
                        (PrefixValues.completeValue headWaiting head
                          tailWaiting headWitness.next headWitness.advance
                          headPriorValues headValue)) := by
                    exact congrArg
                      (GrammarSymbolValues.transport tailPriorLayout.symm)
                      tailPriorCanonical.symm
                  _ = _ := by
                    rw [GrammarSymbolValues.transport_trans]
                    exact GrammarSymbolValues.transport_self _ _
              have starTargetLayout : [
                    GrammarSymbol.nonterminal (.aux site.child),
                    GrammarSymbol.nonterminal (.aux site.site)] = [
                    GrammarSymbol.nonterminal (.aux site.child),
                    GrammarSymbol.nonterminal tail.raw.production.lhs] := by
                rw [tailLhs]
              have fullTupleEq :=
                GrammarSymbolValues.transport_append_pair_to
                  tailPriorLayout
                  ((prefix_complete_layout tailWaiting.raw tail.raw item.raw
                    tailWitness.next tailWitness.advance).trans
                    (prefix_full_layout item.raw complete))
                  (by simp [item, ProductionId.rhs])
                  starTargetLayout headEncoded tailValue
              have fullViewEq : GrammarSymbolValues.view
                    (ProductionId.rhs_star_cons site)
                    (PrefixValues.fullValue item complete
                      (PrefixValues.completeValue tailWaiting tail item
                        tailWitness.next tailWitness.advance
                        (PrefixValues.completeValue headWaiting head tailWaiting
                          headWitness.next headWitness.advance headPriorValues
                          headValue) tailValue)) =
                  (headEncoded, (tailEncoded, ())) := by
                unfold GrammarSymbolValues.view
                rw [PrefixValues.fullValue_completeValue_eq]
                rw [← tailPriorRecover]
                rw [fullTupleEq]
                dsimp only [tailEncoded]
                exact grammarSymbolValues_transport_pair_second_coherentStarLocal
                  (first := GrammarSymbol.nonterminal (.aux site.child))
                  tailLhs headEncoded tailValue starTargetLayout
              have packedEq := actionReduces_eleven_shapes_exact.mp action
              dsimp only [item] at packedEq
              have outputView : EbnfValue.atShape
                    site.expression_eq_star output =
                  EbnfValue.star site.child.expression
                    (headEncoded ::
                      Eq.mp (ebnfValue_star_eq site.child.expression)
                        (EbnfValue.atShape site.expression_eq_star
                          tailEncoded)) := by
                calc
                  _ = EbnfValue.atShape site.expression_eq_star
                      (StarSite.pack site .cons
                        (PrefixValues.fullValue item complete
                          (PrefixValues.completeValue tailWaiting tail item
                            tailWitness.next tailWitness.advance
                            (PrefixValues.completeValue headWaiting head
                              tailWaiting headWitness.next headWitness.advance
                              headPriorValues headValue) tailValue))) :=
                    congrArg (EbnfValue.atShape site.expression_eq_star)
                      packedEq
                  _ = EbnfValue.star site.child.expression
                      (headEncoded ::
                        Eq.mp (ebnfValue_star_eq site.child.expression)
                          (EbnfValue.atShape site.expression_eq_star
                            tailEncoded)) := by
                    rw [StarSite.pack_cons_eq, fullViewEq]
              exact ⟨head, tail, headValue, tailValue, tailBranch,
                headLhs, tailLhs, tailProduction, headOrigin, headTail,
                tailFinish, headContext, tailContext, headCoherent,
                tailCoherent, outputView⟩

private theorem production_root_of_lhs_star
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
/-- A coherent nonterminal atom whose child source rule is nonnullable
consumes a strict interval. -/
theorem coherentAtomRule_progress
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    {site : AtomSite} {rule : GrammarRuleId}
    (production : item.raw.production = .atom site)
    (shape : site.atom = .nonterminal rule)
    (notOptionalComma : rule ≠ .optionalComma)
    (coherent : CoherentReduction file tokens memo correct final item output) :
    item.raw.origin.val < item.raw.current.val := by
  cases coherent with
  | reduce _ priorValues _ reached complete coherentPrefix action =>
      have itemComplete : item.raw.dot.val = 1 := by
        calc
          _ = item.raw.production.rhs.length := complete
          _ = 1 := by
            rw [production]
            simp [ProductionId.rhs, AtomSite.symbol]
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues witness edge prior =>
          have beforeProduction : before.raw.production = .atom site := by
            exact witness.advance.1.symm.trans production
          have beforeZero : before.raw.dot.val = 0 := by
            have advanced := witness.advance.2.1
            omega
          have impossible : some
                (GrammarSymbol.terminal witness.terminal) =
              some (GrammarSymbol.nonterminal (.rule rule)) := by
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                witness.next.2.symm
              _ = (ProductionId.atom site).rhs[0]? := by
                let index := before.raw.dot.val
                have indexZero : index = 0 := beforeZero
                calc
                  _ = (ProductionId.atom site).rhs[index]? :=
                    congrArg (fun selected : ProductionId =>
                      selected.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexZero]
              _ = _ := by
                simp [ProductionId.rhs, AtomSite.symbol,
                  EbnfAtom.grammarSymbol, shape]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete waiting child after shared priorValues childValue witness
          edge prior childCoherent =>
          have waitingProduction : waiting.raw.production = .atom site := by
            exact witness.advance.1.symm.trans production
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
                      congrArg (fun selected : ProductionId =>
                        selected.rhs[index]?) waitingProduction
                    _ = _ := by rw [indexZero]
                _ = _ := by
                  simp [ProductionId.rhs, AtomSite.symbol,
                    EbnfAtom.grammarSymbol, shape]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          have childProduction : child.raw.production = .root rule :=
            production_root_of_lhs_star child.raw.production rule childLhs
          have childProgress : child.raw.origin.val <
              child.raw.current.val := by
            cases childCoherent with
            | reduce _ _ _ childReached childComplete _ _ =>
                exact completeRoot_progress childProduction childReached
                  childComplete notOptionalComma
          have waitingOriginCurrent : waiting.raw.origin =
              waiting.raw.current :=
            contextualReach_zero_origin_eq_current edge.2.1 waitingZero
          have childOrigin : child.raw.origin = item.raw.origin := by
            calc
              _ = shared := witness.finishedAtShared
              _ = waiting.raw.current := witness.waitingAtShared.symm
              _ = waiting.raw.origin := waitingOriginCurrent.symm
              _ = item.raw.origin := witness.advance.2.2.1.symm
          have childCurrent : child.raw.current = item.raw.current :=
            witness.advance.2.2.2.symm
          simpa only [childOrigin, childCurrent] using childProgress

/-- The head of a coherent extending star over a nonnullable source rule
strictly advances before the recursive tail begins. -/
theorem coherentStarCons_ruleHead_progress
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {site : StarSite} {rule : GrammarRuleId}
    (childShape : site.child.expression = .atom (.nonterminal rule))
    (notOptionalComma : rule ≠ .optionalComma)
    (dot : Fin ((ProductionId.star site .cons).rhs.length + 1))
    (origin finish : Boundary tokens)
    (context : GuardContext tokens)
    {output : NonterminalValue file tokens
      (ProductionId.star site .cons).lhs}
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star site .cons
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) :
    ∃ split : Boundary tokens,
      origin.val < split.val ∧ split.val ≤ finish.val := by
  rcases coherentStarCons_children dot origin finish context coherent with
    ⟨head, tail, headValue, tailValue, tailBranch, headLhs, tailLhs,
      tailProduction, headOrigin, headTail, tailFinish, headContext,
      tailContext, headCoherent, tailCoherent, outputView⟩
  let atomSite : AtomSite := {
    site := site.child
    hasKind := by
      rw [childShape]
      rfl
  }
  have atomShape : atomSite.atom = .nonterminal rule := by
    have expression := AtomSite.expression_eq_atom atomSite
    change site.child.expression = .atom atomSite.atom at expression
    exact EbnfExpr.atom.inj (expression.symm.trans childShape)
  have headProduction : head.raw.production = .atom atomSite :=
    production_atom_of_lhs_site head.raw.production atomSite (by
      simpa [atomSite] using headLhs)
  have headProgress := coherentAtomRule_progress headProduction
    atomShape notOptionalComma headCoherent
  have tailOrdered := contextualReach_ordered (by
    cases tailCoherent
    assumption)
  refine ⟨tail.raw.origin, ?_, ?_⟩
  · simpa only [headOrigin, headTail] using headProgress
  · rw [← tailFinish]
    exact tailOrdered


end Solcore.Surface.Multi
