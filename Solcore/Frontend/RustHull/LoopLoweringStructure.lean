import Solcore.Frontend.RustHull.StatementCorrespondence

/-! Decompose the real Hull loop compiler. Initializers use its ordinary
statement-list path; a loop with no initializer allocates one Core self cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LoopLoweringStructure

/-- Actual compilation evidence for one loop, reused at every iteration. -/
structure Compiled (signatures : List Signature) (scope : Scope) (result : Core.Ty)
    (loops : Nat) (test : Expr) (post body : List Stmt) where
  fuel : Nat
  conditionCode : Lowered
  conditionCore : Core.Expr
  bodyCore : Core.Expr
  postCore : Core.Expr
  conditionCompiled : lowerExpression fuel signatures scope test = .ok conditionCode
  conditionConverted : condition conditionCode = .ok conditionCore
  bodyCompiled : lowerStatements fuel signatures scope result (loops + 1) body = .ok bodyCore
  postCompiled : lowerStatements fuel signatures scope result (loops + 1) post = .ok postCore

theorem empty_init_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {test : Expr} {post body : List Stmt}
    {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.forLoop [] test post body, span⟩ = .ok expression) :
    ∃ conditionCode conditionCore bodyCore postCore,
      lowerExpression fuel signatures scope test = .ok conditionCode ∧
      condition conditionCode = .ok conditionCore ∧
      lowerStatements fuel signatures scope result (loops + 1) body = .ok bodyCore ∧
      lowerStatements fuel signatures scope result (loops + 1) post = .ok postCore ∧
      expression = Core.LocalLoop.iterate result conditionCore bodyCore postCore (Core.Word.ofNatModulo 3) := by
  simp only [lowerStatement, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at compiled
  obtain ⟨conditionCode, conditionCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨conditionCore, converted, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨bodyCore, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨postCore, postCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨conditionCode, conditionCore, bodyCore, postCore,
    conditionCompiled, converted, bodyCompiled, postCompiled, rfl⟩

theorem nonempty_init {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {test : Expr} {init post body : List Stmt}
    {span : Option Span} {expression : Core.Expr} (nonempty : init ≠ [])
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.forLoop init test post body, span⟩ = .ok expression) :
    lowerStatements fuel signatures scope result loops
      (init ++ [⟨.forLoop [] test post body, span⟩]) = .ok expression := by
  cases init with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => simpa only [lowerStatement, List.isEmpty_cons, Bool.not_false, ↓reduceIte] using compiled

end Solcore.Frontend.RustHull.LoopLoweringStructure
