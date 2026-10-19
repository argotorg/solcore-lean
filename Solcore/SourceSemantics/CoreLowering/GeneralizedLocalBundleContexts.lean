import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts

/-! A read can have a larger active context than the declaration that created
its bundle. Context agreement makes its candidate list an ordered sublist.
The actual checked payload type then forces both lists to be identical. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

structure ContextExtension (lexical current : Substitution) : Prop where
  domain : ∀ metavariable ∈ lexical.domain, metavariable ∈ current.domain
  action : ∀ metavariable ∈ lexical.domain,
    current.apply (.variable metavariable) = lexical.apply (.variable metavariable)

theorem ContextExtension.agrees {lexical current candidate : Substitution}
    (extension : ContextExtension lexical current)
    (agrees : agreesOnContext candidate current = true) : agreesOnContext candidate lexical = true := by
  apply List.all_eq_true.mpr
  intro metavariable member
  exact decide_eq_true (Eq.trans
    (agreesOnContext_spec agrees metavariable (extension.domain metavariable member))
    (extension.action metavariable member))

private theorem filter_sublist {α : Type} (items : List α) {narrow broad : α → Bool}
    (included : ∀ item, narrow item = true → broad item = true) :
    List.Sublist (items.filter narrow) (items.filter broad) := by
  induction items with
  | nil => exact .slnil
  | cons head rest ih =>
      cases narrowAt : narrow head <;> cases broadAt : broad head
      · simpa [narrowAt, broadAt] using ih
      · simpa [narrowAt, broadAt] using List.Sublist.cons head ih
      · have impossible := included head narrowAt
        simp [broadAt] at impossible
      · simpa [narrowAt, broadAt] using List.Sublist.cons_cons head ih

theorem atContext_sublist {lexical current : Substitution}
    (extension : ContextExtension lexical current) (binding : Binding) :
    List.Sublist (binding.atContext current) (binding.atContext lexical) :=
  filter_sublist binding.instances (fun _ => extension.agrees)

private def bundleArity : Core.Ty → Nat
  | .product _ (.product left right) => bundleArity (.product left right) + 1
  | .product _ _ => 1
  | _ => 0

private theorem nonempty_product (head : Instance) (rest : List Instance) :
    ∃ left right, ProductBundle.type ((head :: rest).map (·.type)) = .product left right := by
  cases rest with
  | nil =>
      cases selected : head.contractId <;>
        simp [ProductBundle.type, Instance.type, selected, Core.TaggedFunction.functionType,
          Core.CallableContract.functionType]
  | cons next tail => exact ⟨_, _, rfl⟩

private theorem bundle_arity (instances : List Instance) :
    bundleArity (ProductBundle.type (instances.map (·.type))) = instances.length := by
  induction instances with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil =>
          cases selected : head.contractId <;>
            simp [ProductBundle.type, Instance.type, selected, Core.TaggedFunction.functionType,
              Core.CallableContract.functionType, bundleArity]
      | cons next tail =>
          obtain ⟨left, right, shape⟩ := nonempty_product next tail
          change bundleArity (.product head.type (ProductBundle.type ((next :: tail).map (·.type)))) = _
          rw [shape]
          change bundleArity (.product left right) + 1 = _
          rw [← shape, ih]
          rfl

/-- Native type equality is used only after the real context relation gives
an ordered sublist. It cannot choose or identify instances by itself. -/
theorem atContext_eq_of_bundleType {lexical current : Substitution}
    (extension : ContextExtension lexical current) (binding : Binding)
    (checked : binding.bundleType lexical = binding.bundleType current) :
    binding.atContext lexical = binding.atContext current := by
  have lengths := congrArg bundleArity checked
  change bundleArity (ProductBundle.type ((binding.atContext lexical).map (·.type))) =
    bundleArity (ProductBundle.type ((binding.atContext current).map (·.type))) at lengths
  rw [bundle_arity, bundle_arity] at lengths
  exact ((atContext_sublist extension binding).eq_of_length lengths.symm).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
