import Solcore.SourceSemantics.SourceInferenceActualGeneralizationInventory
import Solcore.SourceSemantics.Ownership

/-! The executable initialized-binding inventory is covered by exact actual
statement and header origins, including every recorded loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem
variable {root : CallIndex}

private theorem Item.initialized {item : ForItemForm} (origin : Item root item)
    {binding : InitializedLetBinding} (member : binding ∈ forItemInitializedLetBindings item) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  cases item with
  | letDecl binder value =>
    cases value with
    | none => simp only [forItemInitializedLetBindings, List.not_mem_nil] at member
    | some initializer =>
      simp only [forItemInitializedLetBindings, List.mem_singleton] at member
      subst binding
      exact ⟨initializer, rfl, origin _ _ rfl⟩
  | expression _ | assignValue _ _ _ | assignBitNot _ =>
    simp only [forItemInitializedLetBindings, List.not_mem_nil] at member

private theorem Items.initialized {items : List ForItemForm} (origins : Items root items)
    {binding : InitializedLetBinding} (member : binding ∈ items.flatMap forItemInitializedLetBindings) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  obtain ⟨item, present, member⟩ := List.mem_flatMap.mp member
  exact (origins item present).initialized member

private theorem Statement.initialized {node : StatementNode} (origin : Statement root node)
    {binding : InitializedLetBinding} (member : binding ∈ statementInitializedLetBindings node.form) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  cases form : node.form with
  | letDecl binder value =>
    cases value with
    | none => simp only [form, statementInitializedLetBindings, List.not_mem_nil] at member
    | some initializer =>
      simp only [form, statementInitializedLetBindings, List.mem_singleton] at member
      subst binding
      exact ⟨initializer, rfl, by simpa only [Statement, form] using origin⟩
  | forLoop initial condition post body =>
    have events : Items root initial ∧ Items root post := by
      simpa only [Statement, form] using origin
    simp only [form, statementInitializedLetBindings, List.mem_append] at member
    rcases member with first | second
    · exact events.1.initialized first
    · exact events.2.initialized second
  | _ => simp only [form, statementInitializedLetBindings, List.not_mem_nil] at member


/-- Every executable initialized binding has an actual receipt on the same
inference root, with the complete binder and initializer identity preserved. -/
theorem Origins.initialized {source : TypedSource} (origins : Origins root source.nodes)
    {binding : InitializedLetBinding} (member : binding ∈ initializedLetBindings source) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  obtain ⟨node, present, member⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases member
  | statement node => exact (origins node present).initialized member

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
