import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.GeneralHeap

/-! Lexical layouts for generated loop code. Temporary binders change the
actual closure environment and the generated code together; these relations
only require agreement on source-visible lookup slots. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements

structure Layout (world : Core.StoreTyping) (canonicalContext : Core.Context)
    (canonical : Core.Environment) (actualContext : Core.Context) (actual : Core.Environment)
    (ξ : Core.Renaming) : Prop where
  respects : Core.Renaming.Respects ξ canonicalContext actualContext
  agrees : Core.ReadOnly.EnvironmentsAgree ξ canonical actual
  typed : Core.RuntimeEnvironmentHasTypes world actual actualContext

namespace Layout

variable {world future : Core.StoreTyping} {canonicalContext actualContext : Core.Context}
  {canonical actual : Core.Environment} {ξ : Core.Renaming}

theorem extend (layout : Layout world canonicalContext canonical actualContext actual ξ)
    (extension : Core.WorldExtends world future) :
    Layout future canonicalContext canonical actualContext actual ξ :=
  ⟨layout.respects, layout.agrees, Core.RuntimeEnvironmentHasTypes.weaken extension layout.typed⟩

theorem insert (layout : Layout world canonicalContext canonical actualContext actual ξ)
    {value : Core.Value} {type : Core.Ty} (typed : Core.RuntimeValueHasType world value type) :
    Layout world canonicalContext canonical (type :: actualContext) (value :: actual)
      (Core.Renaming.comp (Core.Renaming.insertion 0) ξ) := by
  refine ⟨?_, ?_, .cons typed layout.typed⟩
  · simpa only [Core.Context.insertAt] using (Core.Renaming.insertion_respects_insertAt actualContext 0 type).comp layout.respects
  · intro index foundValue found
    exact layout.agrees found

theorem bind (layout : Layout world canonicalContext canonical actualContext actual ξ)
    {value : Core.Value} {type : Core.Ty} (typed : Core.RuntimeValueHasType world value type) :
    Layout world (type :: canonicalContext) (value :: canonical) (type :: actualContext) (value :: actual)
      ξ.lift :=
  ⟨layout.respects.lift type, Core.ReadOnly.EnvironmentsAgree.lift layout.agrees value, .cons typed layout.typed⟩

end Layout

@[simp] theorem rename_insert (expression : Core.Expr) (ξ : Core.Renaming) :
    expression.rename (Core.Renaming.comp (Core.Renaming.insertion 0) ξ) =
      (expression.rename ξ).weakenAt 0 := by
  rw [← Core.Expr.rename_comp, Core.Expr.rename_insertion]

@[simp] theorem rename_insert_lift (expression : Core.Expr) (ξ : Core.Renaming) :
    expression.rename (Core.Renaming.comp (Core.Renaming.insertion 0) ξ).lift =
      (expression.rename ξ.lift).weakenAt 1 := by
  rw [Core.Renaming.lift_comp, Core.Renaming.lift_insertion,
    ← Core.Expr.rename_comp, Core.Expr.rename_insertion]

end Solcore.SourceSemantics.CoreLowering.LoopStatements
