import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceNative
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess

/-! The existing actual-layout certificate supplies native helper typing in
an arbitrary related runtime environment. Deep typing and actual slot
agreement determine the native renaming; no source metadata is recovered from
native type equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces CompatiblePlaceAssignmentSuccess

/-- Native slot typing, without a source-type injectivity assumption. -/
theorem environment_respects {definitions : DataEnvironment} {world : StoreTyping}
    {canonical actual : Environment} {source target : Core.Context} {ξ : Renaming}
    (canonicalTyped : RuntimeEnvironmentHasTypes world canonical source definitions)
    (actualTyped : RuntimeEnvironmentHasTypes world actual target definitions)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual) : Renaming.Respects ξ source target := by
  intro index type found
  have canonicalTypes := canonicalTyped.type_tags
  have actualTypes := actualTyped.type_tags
  rw [← canonicalTypes, List.getElem?_map] at found
  cases selected : canonical[index]? with
  | none => simp [selected] at found
  | some value =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    rw [← actualTypes, List.getElem?_map, agrees selected]
    exact congrArg some found

private theorem quote_rename {value : Value} {expression : Expr}
    (quoted : CompatibleMapping.VirtualRoot.Quoted value expression) (ξ : Renaming) :
    expression.rename ξ = expression := by induction quoted <;> simp_all [Expr.rename]

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext : Core.Context} {rhsType : Ty} {definitions : DataEnvironment}
  (layout : Layout compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType definitions)

include layout

/-- Describe only emits a virtual initializer for a retained mapping root;
its successful quote authenticates all of that expression's syntax. -/
theorem virtual_closed
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
    VirtualClosed prepared := by
  classical
  intro expression found ξ
  by_cases mapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
  · obtain ⟨key, value, declared⟩ := mapping
    cases layout.virtual key value declared with
    | encoded accepted unchanged quoted root =>
      have same := Option.some.inj (root.symm.trans found)
      subst expression
      exact quote_rename (CompatibleMapping.VirtualRoot.quoted_of_quote quoted) ξ
  · rw [ordinary (fun key value same => mapping ⟨key, value, same⟩)] at found
    cases found

/-- Typing is transported through the actual context embedding. Closure
values and helper stores are subsequently constructed in the actual context. -/
theorem getter_typed (closed : VirtualClosed prepared) {ξ : Renaming} {actualContext : Core.Context}
    (respects : Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext) :
    HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType :: actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions := by
  have typing := layout.getterTyped.rename ((respects.lift _).lift _)
  simpa only [Expr.rename, getter_rename layout.path closed, Renaming.lift, Nat.zero_add] using typing

theorem setter_typed (closed : VirtualClosed prepared) {ξ : Renaming} {actualContext : Core.Context}
    (respects : Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext) :
    HasType (prepared.route.leafType :: rhsType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
      OptionalCell.referenceType prepared.route.rootType :: actualContext)
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions := by
  have typing := layout.setterTyped.rename (((((respects.lift _).lift _).lift _).lift _).lift _)
  simpa only [Expr.rename, setter_rename layout.path closed, Renaming.lift, Nat.zero_add] using typing

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
