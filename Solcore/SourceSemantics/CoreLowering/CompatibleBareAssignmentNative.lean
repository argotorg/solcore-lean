import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! Syntax transport and finite native phases for bare assignments. Only the
pure virtual-root quote is invariant under renaming. RHS/continuation code and
its actual environment are renamed together; existing closure stores are never
assumed identical to evaluations in another environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

private theorem quote_rename {value : Value} {expression : Expr}
    (quoted : CompatibleMapping.VirtualRoot.Quoted value expression) (ξ : Renaming) :
    expression.rename ξ = expression := by induction quoted <;> simp_all [Expr.rename]

theorem getter_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (type : Ty) (ξ : Renaming) :
    (getter prepared type).rename ξ = getter prepared type := by
  cases found : prepared.route.rootMapping with
  | none => simp [getter, layout.steps, normalizeRoot, found, LanguageResult.success, Expr.rename, Renaming.lift]
  | some expression =>
    obtain ⟨value, quoted⟩ := layout.quoted found
    simp [getter, layout.steps, normalizeRoot, found, LanguageResult.success, Expr.rename,
      Renaming.lift, quoted.weaken, quote_rename quoted]

theorem setter_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (type : Ty) (ξ : Renaming) :
    (setter prepared type).rename ξ = setter prepared type := by
  simp [setter, layout.steps, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem modified_rename (type : Ty) (operator : Option BinaryOp) (invalid : Word) (ξ : Renaming) :
    (modified type operator false (.var 1) (.var 0) invalid).rename ξ.lift.lift =
      modified type operator false (.var 1) (.var 0) invalid := by
  cases operator <;> simp [modified, LanguageResult.success, LanguageResult.failure,
    shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, Expr.rename, Renaming.lift]

theorem execute_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (index : Nat) (rhs next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (invalid : Word) (ξ : Renaming) :
    (execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ =
      execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments []) (rhs.rename ξ) (next.rename ξ)
        outputType operator false invalid := by
  simp [execute, SourceCoreCalls.packArguments, LanguageResult.bind, LanguageResult.success,
    shift, List.range, List.range.loop, List.foldl, Expr.rename, Expr.weakenAt,
    getter_rename layout, setter_rename layout, modified_rename, Renaming.lift]

/-- The bare getter returns the optional normalized snapshot itself. Its input
normalization is either the real retained optional or an authenticated pure
mapping literal; both evaluations preserve the store. -/
theorem getter_evaluates {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {environment : Environment} {store : Store} {target : Location}
    {optional snapshot : Value} (read : store.read? target = some optional)
    (normalized : Evaluates (.pair optional .unit :: DataPlaceExecution.keysEnvironment prepared.route.rootType target .unit environment)
      store (normalizeRoot prepared (.first (.var 0))) snapshot store) :
    Evaluates (DataPlaceExecution.keysEnvironment prepared.route.rootType target .unit environment) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) store := by
  simp only [getter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.var rfl)) (.inRight normalized)

theorem keys_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (shift 1 (SourceCoreCalls.packArguments []).expression) (.inRight .word .unit) store := by
  simp only [SourceCoreCalls.packArguments, shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
  exact .inRight .unit

/-- Getter/setter closures are constructed in this exact actual environment.
The bare setter selects the supplied replacement and makes no heap allocation. -/
theorem setter_evaluates {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {environment : Environment} {store : Store} {target : Location}
    {optional : Value} (snapshot right replacement : Value) (read : store.read? target = some optional) :
    Evaluates (modifiedEnvironment prepared.route.rootType target .unit snapshot right replacement environment) store
      (.apply (setter prepared .unit) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word replacement) store := by
  simp only [setter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.pair (.var rfl) (.var rfl)))
    (.inRight (.second (.second (.var rfl))))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
