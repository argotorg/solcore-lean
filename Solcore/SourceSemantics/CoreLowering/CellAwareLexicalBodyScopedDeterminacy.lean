import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy

/-! Scoped finite-body completion determines the selected branch, restores
lexical bindings, and keeps the actual heap reached by the selected path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
open Frontend SourceInference Staging.Recursive
variable {program : Program} {registry : Registry} {invocation : Scope}
  (unique : NodeOccurrencesUnique invocation.source)

include unique in
theorem blockReturned {mode context environment before id node statements rest innerContext sourceValue after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.returned sourceValue) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.returned sourceValue) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨_,same,heap⟩ := inner actual
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := second
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := third
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := fourth
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    cases (inner actual).2.1

include unique in
theorem blockFault {mode context environment before id node statements rest innerContext failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := first
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := second
    obtain ⟨_,same,heap⟩ := inner actual
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := third
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := fourth
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    cases (inner actual).2.1

include unique in
theorem blockFallthrough {mode context environment before id node statements rest innerContext innerEnvironment middle finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.fallthrough innerEnvironment) middle)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment middle rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,_,_,actual⟩ := first; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := second; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := third; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := fourth; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    obtain ⟨_,_,rfl⟩ := inner actual
    exact tail remaining

include unique in
theorem conditionalFault {mode context environment before id node condition left right rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := second; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := third; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := fourth; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := fifth; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_,_⟩ := sixth; cases (child actual).1

include unique in
theorem conditionalReturned {mode context environment before id node condition left right rest truth middle innerContext sourceValue after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.returned sourceValue) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.returned sourceValue) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,same,heap⟩ := inner branch
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1

include unique in
theorem conditionalBranchFault {mode context environment before id node condition left right rest truth middle innerContext failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,same,heap⟩ := inner branch
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1

include unique in
theorem conditionalFallthrough {mode context environment before id node condition left right rest truth middle innerContext innerEnvironment branchHeap finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.fallthrough innerEnvironment) branchHeap)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment branchHeap rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,_,rfl⟩ := inner branch
    exact tail remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
