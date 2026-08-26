import Solcore.Surface.Multi.LocationSubfragment
import Solcore.Surface.Multi.RuleLocationPassThrough

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

private def ValueSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expression : EbnfExpr}
    (input : EbnfValue file tokens expression)
    (rule : GrammarRuleId) (value : RuleValue rule)
    (_inside : EbnfValue.ContainsRuleValue file tokens input rule value) :
    Prop :=
  (RuleLocationView.ofRuleValue rule value).IsSubfragmentOf
    input.locationFragment

private def ValuesSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expressions : List EbnfExpr}
    (input : EbnfValues file tokens expressions)
    (rule : GrammarRuleId) (value : RuleValue rule)
    (_inside : EbnfValues.ContainsRuleValue file tokens input rule value) :
    Prop :=
  (RuleLocationView.ofRuleValue rule value).IsSubfragmentOf
    input.locationFragment

private theorem valueSubfragmentRuleCase
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (value : RuleValue rule) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.ruleAtom rule value) rule value (.rule rule value) := by
  unfold ValueSubfragmentMotive
  simpa using LocationFragment.IsSubfragmentOf.refl
    (RuleLocationView.ofRuleValue rule value)

private theorem valueSubfragmentTransportCase
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (shape : left = right)
    {input : EbnfValue file tokens left}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens input rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens input rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.transport shape input) rule value (.transport shape inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentSequenceCase
    {file : WorkspaceFile} {tokens : List Token}
    {children : List EbnfExpr}
    {values : EbnfValues file tokens children}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValues.ContainsRuleValue file tokens values rule value)
    (inductionHypothesis : ValuesSubfragmentMotive
      file tokens values rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.sequence children values) rule value (.sequence inside) := by
  unfold ValuesSubfragmentMotive at inductionHypothesis
  unfold ValueSubfragmentMotive
  simpa using inductionHypothesis

private theorem valueSubfragmentGroupCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {childValue : EbnfValue file tokens child}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.group child childValue) rule value (.group inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentChoiceCase
    {file : WorkspaceFile} {tokens : List Token}
    {branches : List EbnfExpr} (branch : Fin branches.length)
    {branchValue : EbnfValue file tokens (branches.get branch)}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens branchValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens branchValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.choice branches ⟨branch, branchValue⟩) rule value
      (.choice branch inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentOptionalCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {childValue : EbnfValue file tokens child}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.optional child (some childValue)) rule value
      (.optional inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem valueSubfragmentStarCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
    {childValue : EbnfValue file tokens child}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (member : childValue ∈ values)
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.star child values) rule value (.star member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_star]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge
    (List.mem_map.mpr ⟨childValue, member, rfl⟩)

private theorem valueSubfragmentPlusHeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens head rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens head rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.plus child ⟨head, tail⟩) rule value (.plusHead inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_plus]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

private theorem valueSubfragmentPlusTailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (member : childValue ∈ tail)
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.plus child ⟨head, tail⟩) rule value
      (.plusTail member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_plus]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  apply LocationFragment.IsSubfragmentOf.of_mem_merge
  change childValue.locationFragment ∈
    head.locationFragment :: tail.map (fun element => element.locationFragment)
  exact List.mem_cons_of_mem _
    (List.mem_map_of_mem member)

private theorem valueSubfragmentList0Case
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
    {childValue : EbnfValue file tokens child}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (member : childValue ∈ values)
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list0 child values) rule value (.list0 member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list0]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge
    (List.mem_map.mpr ⟨childValue, member, rfl⟩)

private theorem valueSubfragmentList1HeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens head rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens head rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list1 child ⟨head, tail⟩) rule value
      (.list1Head inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list1]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

private theorem valueSubfragmentList1TailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
    {tail : List (EbnfValue file tokens child)}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (member : childValue ∈ tail)
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValueSubfragmentMotive file tokens
      (EbnfValue.list1 child ⟨head, tail⟩) rule value
      (.list1Tail member inside) := by
  unfold ValueSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValue.locationFragment_list1]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  apply LocationFragment.IsSubfragmentOf.of_mem_merge
  change childValue.locationFragment ∈
    head.locationFragment :: tail.map (fun element => element.locationFragment)
  exact List.mem_cons_of_mem _
    (List.mem_map_of_mem member)

private theorem valuesSubfragmentHeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {childValue : EbnfValue file tokens child}
    {restValues : EbnfValues file tokens rest}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value)
    (inductionHypothesis : ValueSubfragmentMotive
      file tokens childValue rule value inside) :
    ValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest childValue restValues) rule value
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
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValues.ContainsRuleValue file tokens restValues rule value)
    (inductionHypothesis : ValuesSubfragmentMotive
      file tokens restValues rule value inside) :
    ValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest childValue restValues) rule value
      (.tail inside) := by
  unfold ValuesSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValues.locationFragment_cons]
  apply LocationFragment.IsSubfragmentOf.trans inductionHypothesis
  exact LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)

namespace EbnfValue.ContainsRuleValue

theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens input rule value) :
    (RuleLocationView.ofRuleValue rule value).IsSubfragmentOf
      input.locationFragment :=
  EbnfValue.ContainsRuleValue.rec
    (motive_1 := ValueSubfragmentMotive file tokens)
    (motive_2 := ValuesSubfragmentMotive file tokens)
    valueSubfragmentRuleCase valueSubfragmentTransportCase
    valueSubfragmentSequenceCase valueSubfragmentGroupCase
    valueSubfragmentChoiceCase valueSubfragmentOptionalCase
    valueSubfragmentStarCase valueSubfragmentPlusHeadCase
    valueSubfragmentPlusTailCase valueSubfragmentList0Case
    valueSubfragmentList1HeadCase valueSubfragmentList1TailCase
    valuesSubfragmentHeadCase valuesSubfragmentTailCase inside

end EbnfValue.ContainsRuleValue

namespace EbnfValues.ContainsRuleValue

theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {expressions : List EbnfExpr}
    {input : EbnfValues file tokens expressions}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValues.ContainsRuleValue file tokens input rule value) :
    (RuleLocationView.ofRuleValue rule value).IsSubfragmentOf
      input.locationFragment :=
  EbnfValues.ContainsRuleValue.rec
    (motive_1 := ValueSubfragmentMotive file tokens)
    (motive_2 := ValuesSubfragmentMotive file tokens)
    valueSubfragmentRuleCase valueSubfragmentTransportCase
    valueSubfragmentSequenceCase valueSubfragmentGroupCase
    valueSubfragmentChoiceCase valueSubfragmentOptionalCase
    valueSubfragmentStarCase valueSubfragmentPlusHeadCase
    valueSubfragmentPlusTailCase valueSubfragmentList0Case
    valueSubfragmentList1HeadCase valueSubfragmentList1TailCase
    valuesSubfragmentHeadCase valuesSubfragmentTailCase inside

end EbnfValues.ContainsRuleValue

end Solcore.Surface.Multi

