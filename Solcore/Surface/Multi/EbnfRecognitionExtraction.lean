import Solcore.Surface.Multi.EbnfRecognition

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The checked EBNF meaning of one expanded grammar symbol. -/
def ExpandedSymbolRecognition
    (file : WorkspaceFile) (tokens : List Token) :
    GrammarSymbol → Boundary tokens → Boundary tokens → Prop
  | .terminal terminal, start, finish =>
      EbnfRecognizes file tokens (.atom (.terminal terminal)) start finish
  | .nonterminal (.rule rule), start, finish =>
      EbnfRecognizes file tokens (.atom (.nonterminal rule)) start finish
  | .nonterminal (.aux site), start, finish =>
      EbnfRecognizes file tokens site.expression start finish
  | .nonterminal (.tail site), start, finish =>
      EbnfCommaTailRecognizes file tokens site.element.expression start finish

/-- Pointwise EBNF meanings of a contiguous expanded RHS. -/
inductive ExpandedSymbolsRecognition
    (file : WorkspaceFile) (tokens : List Token) :
    List GrammarSymbol → Boundary tokens → Boundary tokens → Prop where
  | nil (cursor : Boundary tokens) :
      ExpandedSymbolsRecognition file tokens [] cursor cursor
  | cons
      (symbol : GrammarSymbol) (rest : List GrammarSymbol)
      (start middle finish : Boundary tokens)
      (head : ExpandedSymbolRecognition file tokens symbol start middle)
      (tail : ExpandedSymbolsRecognition file tokens rest middle finish) :
      ExpandedSymbolsRecognition file tokens (symbol :: rest) start finish

private theorem auxiliaryMeanings_toEbnfList
    {file : WorkspaceFile} {tokens : List Token}
    (sites : List GrammarSite) (start finish : Boundary tokens)
    (recognized : ExpandedSymbolsRecognition file tokens
      (sites.map fun site => .nonterminal (.aux site)) start finish) :
    EbnfRecognizesList file tokens
      (sites.map GrammarSite.expression) start finish := by
  induction sites generalizing start with
  | nil =>
      cases recognized
      exact .nil finish
  | cons site rest induction =>
      cases recognized with
      | cons _ _ _ middle _ head tail =>
          exact .cons site.expression (rest.map GrammarSite.expression)
            start middle finish head (induction middle tail)

/-- The EBNF constructor denoted by each expanded production is recovered
from pointwise meanings of its complete RHS. -/
private theorem productionRecognition
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId) (start finish : Boundary tokens)
    (body : ExpandedSymbolsRecognition file tokens production.rhs
      start finish) :
    ExpandedSymbolRecognition file tokens
      (.nonterminal production.lhs) start finish := by
  cases production with
  | root rule =>
      cases body with
      | cons _ _ _ middle _ head tail =>
          cases tail
          exact .nonterminal rule start finish
            (head.transport (GrammarSite.root_expression rule) rfl rfl)
  | atom site =>
      cases body with
      | cons _ _ _ middle _ head tail =>
          cases tail
          cases atomEq : site.atom with
          | terminal terminal =>
              simp only [AtomSite.symbol, atomEq,
                EbnfAtom.grammarSymbol, ExpandedSymbolRecognition] at head
              exact head.transport
                ((congrArg EbnfExpr.atom atomEq.symm).trans
                  site.expression_eq_atom.symm) rfl rfl
          | nonterminal rule =>
              simp only [AtomSite.symbol, atomEq,
                EbnfAtom.grammarSymbol, ExpandedSymbolRecognition] at head
              exact head.transport
                ((congrArg EbnfExpr.atom atomEq.symm).trans
                  site.expression_eq_atom.symm) rfl rfl
  | seq site =>
      exact (EbnfRecognizes.sequence
        (site.children.map GrammarSite.expression) start finish
        (auxiliaryMeanings_toEbnfList site.children start finish body)).transport
          site.expression_eq_sequence.symm rfl rfl
  | group site =>
      cases body with
      | cons _ _ _ middle _ head tail =>
          cases tail
          exact (EbnfRecognizes.group site.child.expression start finish
            head).transport site.expression_eq_group.symm rfl rfl
  | choice site branch =>
      cases body with
      | cons _ _ _ middle _ head tail =>
          cases tail
          have selected := head.transport
            (site.branch_expression branch) rfl rfl
          exact (EbnfRecognizes.choice site.branchExpressions.toList
            (site.branchListIndex branch) start finish
            (selected.transport (site.branch_get_toList branch).symm rfl rfl)
          ).transport site.expression_eq_choice.symm rfl rfl
  | opt site branch =>
      cases branch with
      | none =>
          cases body
          exact (EbnfRecognizes.optionalNone site.child.expression _
            ).transport site.expression_eq_optional.symm rfl rfl
      | some =>
          cases body with
          | cons _ _ _ middle _ head tail =>
              cases tail
              exact (EbnfRecognizes.optionalSome site.child.expression
                start finish head).transport
                  site.expression_eq_optional.symm rfl rfl
  | star site branch =>
      cases branch with
      | nil =>
          cases body
          exact (EbnfRecognizes.starNil site.child.expression _
            ).transport site.expression_eq_star.symm rfl rfl
      | cons =>
          cases body with
          | cons _ _ _ middle _ head tail =>
              cases tail with
              | cons _ _ _ inner _ recursive empty =>
                  cases empty
                  have exactRecursive := recursive.transport
                    site.expression_eq_star rfl rfl
                  exact (EbnfRecognizes.starCons site.child.expression
                    start middle finish head exactRecursive).transport
                      site.expression_eq_star.symm rfl rfl
  | plus site branch =>
      cases branch with
      | one =>
          cases body with
          | cons _ _ _ middle _ head tail =>
              cases tail
              exact (EbnfRecognizes.plusOne site.child.expression start finish
                head).transport site.expression_eq_plus.symm rfl rfl
      | cons =>
          cases body with
          | cons _ _ _ middle _ head tail =>
              cases tail with
              | cons _ _ _ inner _ recursive empty =>
                  cases empty
                  have exactRecursive := recursive.transport
                    site.expression_eq_plus rfl rfl
                  exact (EbnfRecognizes.plusCons site.child.expression
                    start middle finish head exactRecursive).transport
                      site.expression_eq_plus.symm rfl rfl
  | list0 site branch =>
      cases branch with
      | nil =>
          cases body
          exact (EbnfRecognizes.list0Nil site.element.expression _
            ).transport site.expression_eq_list0.symm rfl rfl
      | cons =>
          cases body with
          | cons _ _ _ middle _ head tail =>
              cases tail with
              | cons _ _ _ inner _ commaTail empty =>
                  cases empty
                  exact (EbnfRecognizes.list0Cons site.element.expression
                    start middle finish head commaTail).transport
                      site.expression_eq_list0.symm rfl rfl
  | list1 site =>
      cases body with
      | cons _ _ _ middle _ head tail =>
          cases tail with
          | cons _ _ _ inner _ commaTail empty =>
              cases empty
              exact (EbnfRecognizes.list1 site.element.expression
                start middle finish head commaTail).transport
                  site.expression_eq_list1.symm rfl rfl
  | tail site branch =>
      cases branch with
      | nil =>
          cases body
          exact .nil site.element.expression _
      | cons =>
          cases body with
          | cons _ _ _ afterComma _ commaMeaning tail =>
              cases tail with
              | cons _ _ _ middle _ head tail =>
                  cases tail with
                  | cons _ _ _ inner _ recursive empty =>
                      cases empty
                      cases commaMeaning with
                      | terminal _ comma =>
                          exact .cons site.element.expression _ _ _ _ comma
                            rfl rfl head recursive

/-- Expanded interval derivations map canonically back to the checked EBNF
tree from which the productions were generated. -/
theorem UnguardedSymbolDerives.toExpandedRecognition
    {file : WorkspaceFile} {tokens : List Token}
    {symbol : GrammarSymbol} {start finish : Boundary tokens}
    (derives : UnguardedSymbolDerives file tokens symbol start finish) :
    ExpandedSymbolRecognition file tokens symbol start finish := by
  refine UnguardedSymbolDerives.rec
    (motive_1 := fun symbol start finish _ =>
      ExpandedSymbolRecognition file tokens symbol start finish)
    (motive_2 := fun symbols start finish _ =>
      ExpandedSymbolsRecognition file tokens symbols start finish)
    ?_ ?_ ?_ ?_ derives
  · intro terminal matched
    exact .terminal terminal matched
  · intro production start finish body bodyMeaning
    exact productionRecognition production start finish bodyMeaning
  · intro cursor
    exact .nil cursor
  · intro symbol rest start middle finish head tail
      headMeaning tailMeaning
    exact .cons symbol rest start middle finish headMeaning tailMeaning

/-- A recognized source rule exposes the exact checked EBNF recognition tree
for its displayed right-hand side. -/
theorem UnguardedRecognizes.ebnf
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {start finish : Boundary tokens}
    (recognized : UnguardedRecognizes file tokens (.rule rule) start finish) :
    EbnfRecognizes file tokens (m2cV1.rhs rule) start finish := by
  obtain ⟨production, lhs, body⟩ := recognized.derivation
  have symbolDerives : UnguardedSymbolDerives file tokens
      (.nonterminal (.rule rule)) start finish :=
    (UnguardedSymbolDerives.nonterminal production start finish body).transport
      (congrArg GrammarSymbol.nonterminal lhs) rfl rfl
  have expanded := symbolDerives.toExpandedRecognition
  change EbnfRecognizes file tokens (.atom (.nonterminal rule))
    start finish at expanded
  cases expanded with
  | nonterminal _ _ _ body => exact body

end Solcore.Surface.Multi
