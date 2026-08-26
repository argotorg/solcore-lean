import Solcore.Surface.Multi.RuleLocationSubfragment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

mutual

/-- A terminal or source-rule location fragment occurring anywhere inside one
checked EBNF value.  The relation retains the exact structural path so callers
can select semantic locations without relying on normalization of the whole
input expression. -/
inductive EbnfValue.ContainsLocationFragment
    (file : WorkspaceFile) (tokens : List Token) :
    {expression : EbnfExpr} → EbnfValue file tokens expression →
      LocationFragment → Prop where
  | terminal
      (terminal : TerminalSymbol)
      (matched : MatchedTerminal file tokens terminal) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.terminalAtom terminal matched) matched.locationFragment
  | rule (rule : GrammarRuleId) (value : RuleValue rule) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.ruleAtom rule value)
        (RuleLocationView.ofRuleValue rule value)
  | transport
      {left right : EbnfExpr} (shape : left = right)
      {input : EbnfValue file tokens left}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment file tokens input fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.transport shape input) fragment
  | sequence
      {children : List EbnfExpr}
      {values : EbnfValues file tokens children}
      {fragment : LocationFragment}
      (inside : EbnfValues.ContainsLocationFragment file tokens values fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.sequence children values) fragment
  | group
      {child : EbnfExpr} {childValue : EbnfValue file tokens child}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.group child childValue) fragment
  | choice
      {branches : List EbnfExpr} (branch : Fin branches.length)
      {branchValue : EbnfValue file tokens (branches.get branch)}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment
        file tokens branchValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.choice branches ⟨branch, branchValue⟩) fragment
  | optional
      {child : EbnfExpr} {childValue : EbnfValue file tokens child}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.optional child (some childValue)) fragment
  | star
      {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
      {childValue : EbnfValue file tokens child}
      {fragment : LocationFragment}
      (member : childValue ∈ values)
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.star child values) fragment
  | plusHead
      {child : EbnfExpr} {head : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment file tokens head fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.plus child ⟨head, tail⟩) fragment
  | plusTail
      {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {fragment : LocationFragment}
      (member : childValue ∈ tail)
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.plus child ⟨head, tail⟩) fragment
  | list0
      {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
      {childValue : EbnfValue file tokens child}
      {fragment : LocationFragment}
      (member : childValue ∈ values)
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.list0 child values) fragment
  | list1Head
      {child : EbnfExpr} {head : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment file tokens head fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.list1 child ⟨head, tail⟩) fragment
  | list1Tail
      {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {fragment : LocationFragment}
      (member : childValue ∈ tail)
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValue.ContainsLocationFragment file tokens
        (EbnfValue.list1 child ⟨head, tail⟩) fragment

/-- A location fragment occurring in one checked heterogeneous EBNF tuple. -/
inductive EbnfValues.ContainsLocationFragment
    (file : WorkspaceFile) (tokens : List Token) :
    {expressions : List EbnfExpr} → EbnfValues file tokens expressions →
      LocationFragment → Prop where
  | head
      {child : EbnfExpr} {rest : List EbnfExpr}
      {childValue : EbnfValue file tokens child}
      {restValues : EbnfValues file tokens rest}
      {fragment : LocationFragment}
      (inside : EbnfValue.ContainsLocationFragment
        file tokens childValue fragment) :
      EbnfValues.ContainsLocationFragment file tokens
        (EbnfValues.cons child rest childValue restValues) fragment
  | tail
      {child : EbnfExpr} {rest : List EbnfExpr}
      {childValue : EbnfValue file tokens child}
      {restValues : EbnfValues file tokens rest}
      {fragment : LocationFragment}
      (inside : EbnfValues.ContainsLocationFragment
        file tokens restValues fragment) :
      EbnfValues.ContainsLocationFragment file tokens
        (EbnfValues.cons child rest childValue restValues) fragment

end

private def ValueSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expression : EbnfExpr}
    (input : EbnfValue file tokens expression)
    (fragment : LocationFragment)
    (_inside : EbnfValue.ContainsLocationFragment
      file tokens input fragment) : Prop :=
  fragment.IsSubfragmentOf input.locationFragment

private def ValuesSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expressions : List EbnfExpr}
    (input : EbnfValues file tokens expressions)
    (fragment : LocationFragment)
    (_inside : EbnfValues.ContainsLocationFragment
      file tokens input fragment) : Prop :=
  fragment.IsSubfragmentOf input.locationFragment

private theorem valueSubfragmentTerminalCase
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.terminalAtom terminal matched) matched.locationFragment
      (.terminal terminal matched) := by
  unfold ValueSubfragmentMotive
  simpa using LocationFragment.IsSubfragmentOf.refl
    matched.locationFragment

private theorem valueSubfragmentRuleCase
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (value : RuleValue rule) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.ruleAtom rule value) (RuleLocationView.ofRuleValue rule value)
      (.rule rule value) := by
  unfold ValueSubfragmentMotive
  simpa using LocationFragment.IsSubfragmentOf.refl
    (RuleLocationView.ofRuleValue rule value)

private theorem valueSubfragmentTransportCase
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (shape : left = right)
    {input : EbnfValue file tokens left}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens input fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens input fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.transport shape input) fragment (.transport shape inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentSequenceCase
    {file : WorkspaceFile} {tokens : List Token}
    {children : List EbnfExpr}
    {values : EbnfValues file tokens children}
    {fragment : LocationFragment}
    (inside : EbnfValues.ContainsLocationFragment
      file tokens values fragment)
    (inductionHypothesis : ValuesSubfragmentMotive
      file tokens values fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.sequence children values) fragment (.sequence inside) := by
  unfold ValuesSubfragmentMotive at inductionHypothesis
  unfold ValueSubfragmentMotive
  simpa using inductionHypothesis

private theorem valueSubfragmentGroupCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {childValue : EbnfValue file tokens child}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.group child childValue) fragment (.group inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentChoiceCase
    {file : WorkspaceFile} {tokens : List Token}
    {branches : List EbnfExpr} (branch : Fin branches.length)
    {branchValue : EbnfValue file tokens (branches.get branch)}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens branchValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens branchValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.choice branches ⟨branch, branchValue⟩) fragment
      (.choice branch inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentOptionalCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {childValue : EbnfValue file tokens child}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.optional child (some childValue)) fragment
      (.optional inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentStarCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
    {childValue : EbnfValue file tokens child}
    {fragment : LocationFragment}
    (member : childValue ∈ values)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.star child values) fragment (.star member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_star]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge
    (List.mem_map.mpr ⟨childValue, member, rfl⟩)

private theorem valueSubfragmentPlusHeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment file tokens head fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens head fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.plus child ⟨head, tail⟩) fragment (.plusHead inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_plus]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

private theorem valueSubfragmentPlusTailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {fragment : LocationFragment}
    (member : childValue ∈ tail)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.plus child ⟨head, tail⟩) fragment
      (.plusTail member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_plus]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  apply LocationFragment.IsSubfragmentOf.of_mem_merge
  change childValue.locationFragment ∈
    head.locationFragment :: tail.map (fun value => value.locationFragment)
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem member)

private theorem valueSubfragmentList0Case
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
    {childValue : EbnfValue file tokens child}
    {fragment : LocationFragment}
    (member : childValue ∈ values)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list0 child values) fragment (.list0 member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list0]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge
    (List.mem_map.mpr ⟨childValue, member, rfl⟩)

private theorem valueSubfragmentList1HeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment file tokens head fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens head fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list1 child ⟨head, tail⟩) fragment
      (.list1Head inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list1]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

private theorem valueSubfragmentList1TailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {fragment : LocationFragment}
    (member : childValue ∈ tail)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list1 child ⟨head, tail⟩) fragment
      (.list1Tail member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list1]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  apply LocationFragment.IsSubfragmentOf.of_mem_merge
  change childValue.locationFragment ∈
    head.locationFragment :: tail.map (fun value => value.locationFragment)
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem member)

private theorem valuesSubfragmentHeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {childValue : EbnfValue file tokens child}
    {restValues : EbnfValues file tokens rest}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens childValue fragment)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue fragment inside) :
    ValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest childValue restValues) fragment
      (.head inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis
  unfold ValuesSubfragmentMotive
  rw [EbnfValues.locationFragment_cons]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

private theorem valuesSubfragmentTailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {childValue : EbnfValue file tokens child}
    {restValues : EbnfValues file tokens rest}
    {fragment : LocationFragment}
    (inside : EbnfValues.ContainsLocationFragment
      file tokens restValues fragment)
    (inductionHypothesis : ValuesSubfragmentMotive
      file tokens restValues fragment inside) :
    ValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest childValue restValues) fragment
      (.tail inside) := by
  unfold ValuesSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValues.locationFragment_cons]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

namespace EbnfValue.ContainsLocationFragment

/-- Structural EBNF occurrence implies semantic-fragment inclusion. -/
theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment
      file tokens input fragment) :
    fragment.IsSubfragmentOf input.locationFragment :=
  EbnfValue.ContainsLocationFragment.rec
    (motive_1 := ValueSubfragmentMotive file tokens)
    (motive_2 := ValuesSubfragmentMotive file tokens)
    valueSubfragmentTerminalCase valueSubfragmentRuleCase
    valueSubfragmentTransportCase valueSubfragmentSequenceCase
    valueSubfragmentGroupCase valueSubfragmentChoiceCase
    valueSubfragmentOptionalCase valueSubfragmentStarCase
    valueSubfragmentPlusHeadCase valueSubfragmentPlusTailCase
    valueSubfragmentList0Case valueSubfragmentList1HeadCase
    valueSubfragmentList1TailCase valuesSubfragmentHeadCase
    valuesSubfragmentTailCase inside

end EbnfValue.ContainsLocationFragment

namespace EbnfValues.ContainsLocationFragment

/-- Structural tuple occurrence implies semantic-fragment inclusion. -/
theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {expressions : List EbnfExpr}
    {input : EbnfValues file tokens expressions}
    {fragment : LocationFragment}
    (inside : EbnfValues.ContainsLocationFragment
      file tokens input fragment) :
    fragment.IsSubfragmentOf input.locationFragment :=
  EbnfValues.ContainsLocationFragment.rec
    (motive_1 := ValueSubfragmentMotive file tokens)
    (motive_2 := ValuesSubfragmentMotive file tokens)
    valueSubfragmentTerminalCase valueSubfragmentRuleCase
    valueSubfragmentTransportCase valueSubfragmentSequenceCase
    valueSubfragmentGroupCase valueSubfragmentChoiceCase
    valueSubfragmentOptionalCase valueSubfragmentStarCase
    valueSubfragmentPlusHeadCase valueSubfragmentPlusTailCase
    valueSubfragmentList0Case valueSubfragmentList1HeadCase
    valueSubfragmentList1TailCase valuesSubfragmentHeadCase
    valuesSubfragmentTailCase inside

end EbnfValues.ContainsLocationFragment

end Solcore.Surface.Multi
