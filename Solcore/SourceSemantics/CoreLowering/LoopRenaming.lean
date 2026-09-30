import Solcore.Core.LocalLoop
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Syntactic renaming laws for generated control and loop helpers. These laws
change the actual generated closure body together with its lexical layout;
they do not assert equality of closures or final stores across insertions. -/

set_option autoImplicit false

namespace Solcore.Core.LoopRenaming

@[simp] theorem weakenZero (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = (expression.rename mapping).weakenAt 0 := by
  rw [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero,
    ← Expr.rename_comp, Expr.rename_insertion]

@[simp] theorem weakenOne (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 1).rename mapping.lift.lift = (expression.rename mapping.lift).weakenAt 1 := by
  have commute : Renaming.comp mapping.lift.lift (Renaming.insertion 1) =
      Renaming.comp (Renaming.insertion 1) mapping.lift := by
    simpa only [Renaming.lift_comp, Renaming.lift_insertion] using
      congrArg Renaming.lift (Renaming.lift_comp_insertion_zero mapping)
  rw [← Expr.rename_insertion, Expr.rename_comp, commute, ← Expr.rename_comp, Expr.rename_insertion]

@[simp] theorem discard (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalSequence.discard type computation next).rename mapping =
      LocalSequence.discard type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalSequence.discard, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem letUninitialized (type : Ty) (body : Expr) (mapping : Renaming) :
    (LocalSequence.letUninitialized type body).rename mapping =
      LocalSequence.letUninitialized type (body.rename mapping.lift) := by
  rfl

@[simp] theorem letInitialized (type payload : Ty) (initializer body : Expr) (mapping : Renaming) :
    (LocalSequence.letInitialized type payload initializer body).rename mapping =
      LocalSequence.letInitialized type payload (initializer.rename mapping) (body.rename mapping.lift) := by
  simp [LocalSequence.letInitialized, OptionalCell.allocateInitialized, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem assign (type : Ty) (reference rhs next : Expr) (mapping : Renaming) :
    (LocalSequence.assign type reference rhs next).rename mapping =
      LocalSequence.assign type (reference.rename mapping) (rhs.rename mapping) (next.rename mapping) := by
  simp [LocalSequence.assign, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem fallthrough (type : Ty) (mapping : Renaming) :
    (LocalLoop.fallthrough type).rename mapping = LocalLoop.fallthrough type := rfl

@[simp] theorem returned (value : Expr) (mapping : Renaming) :
    (LocalLoop.returned value).rename mapping = LocalLoop.returned (value.rename mapping) := rfl

@[simp] theorem breaking (type : Ty) (mapping : Renaming) :
    (LocalLoop.breaking type).rename mapping = LocalLoop.breaking type := rfl

@[simp] theorem continuing (type : Ty) (mapping : Renaming) :
    (LocalLoop.continuing type).rename mapping = LocalLoop.continuing type := rfl

@[simp] theorem returnValue (type : Ty) (computation : Expr) (mapping : Renaming) :
    (LocalLoop.returnValue type computation).rename mapping = LocalLoop.returnValue type (computation.rename mapping) := by
  simp [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem conditional (type : Ty) (condition thenBranch elseBranch : Expr) (mapping : Renaming) :
    (LocalLoop.conditional type condition thenBranch elseBranch).rename mapping =
      LocalLoop.conditional type (condition.rename mapping) (thenBranch.rename mapping) (elseBranch.rename mapping) := by
  simp [LocalLoop.conditional, LocalControl.choose, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem sequence (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalLoop.sequence type computation next).rename mapping =
      LocalLoop.sequence type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalLoop.sequence, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem advance (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalLoop.advance type computation next).rename mapping =
      LocalLoop.advance type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalLoop.advance, LanguageResult.bind, LocalLoop.returned, LocalLoop.fallthrough,
    LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem invoke (type : Ty) (reference : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.invoke type reference reason).rename mapping =
      LocalLoop.invoke type (reference.rename mapping) reason := by
  simp [LocalLoop.invoke, OptionalCell.read, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.rename, Renaming.lift]

@[simp] theorem loopBody (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.loopBody type condition body post reason).rename mapping.lift.lift =
      LocalLoop.loopBody type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp [LocalLoop.loopBody, Expr.rename, Renaming.lift]

@[simp] theorem iterate (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.iterate type condition body post reason).rename mapping =
      LocalLoop.iterate type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp [LocalLoop.iterate, OptionalCell.allocate, Expr.rename, Renaming.lift]

@[simp] theorem whileLoop (type : Ty) (condition body : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.whileLoop type condition body reason).rename mapping =
      LocalLoop.whileLoop type (condition.rename mapping) (body.rename mapping) reason := by
  simp [LocalLoop.whileLoop]

end Solcore.Core.LoopRenaming
