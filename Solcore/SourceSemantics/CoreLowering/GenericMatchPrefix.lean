import Solcore.SourceSemantics.CoreLowering.GenericMatchAllocation
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming

/-! Under an arbitrary payload model containing the finite pattern values, the
emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution
open DataMatchCertificates DataMatchDecision CoreProof ReadOnly

open DataMatchBranchPrefix GenericMatchAllocation

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

private theorem case_left {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  constructor
  · intro result finalStore body; exact .caseLeft evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_left evaluated
    exact body.sound

/-- The entire attempted-arm fold has no other finite result than execution
of its selected, related continuation. The initial store may contain arbitrary
typed administrative functions, and the body itself is unrestricted syntax. -/
theorem Decision.prefix {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
          (fallbackCode.weakenAt 0)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  induction decision generalizing actual ξ with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        GenericMatchAllocation.bindArm_prefix includes bindingsRepresented environments heaps (actualLayout.lift (packValues values))
      exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, .arm (DataMatchAllocation.BindingsRep.binders bindingsRepresented) allocated certified,
        finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, (case_right matchedCore).trans agreement⟩
  | @tail arm rest pattern body arms fallback fallbackCode selection notMatched fails next ih =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have failedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inLeft (bundleType pattern.bindingTypes) .unit) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact fails actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ)
          (value :: canonical) (.unit :: actual) := by
        intro index foundValue found
        exact actualLayout found
      obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        ih tail nextLayout
      refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, ?_⟩
      simp only [LoopStatements.rename_insert] at agreement
      simp only [List.foldr_cons, attempt, Expr.rename, LoopRenaming.weakenZero]
      exact (case_left failedCore).trans agreement
  | default certified =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

end Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix
