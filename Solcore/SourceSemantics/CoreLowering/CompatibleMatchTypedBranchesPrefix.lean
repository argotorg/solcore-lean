import Solcore.SourceSemantics.CoreLowering.CompatibleMatchDecision
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming

/-! Under an arbitrary payload model containing the finite pattern values, the
emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreCompatibleDataMatches DataPatternValues CompatiblePatternLeaves CompatiblePatternExecution
open CompatibleMatchCertificates CompatibleMatchDecision CoreProof ReadOnly

open DataMatchBranchPrefix CompatibleMatchArmPrefix
open CallableIndexedParameters

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
theorem Decision.prefix_typed {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel compilation.checked.catalog ambient}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context registry functions mapping world scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {branches : Expr}
    (branchesCompiled : Branches compilation source scope (LocalLoop.controlType resultType) fallbackCode arms branches)
    (kinds : ∀ item ∈ arms, ∀ binding ∈ item.1.bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding finalContext body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual store
        (branches.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  induction decision generalizing actual ξ branches actualContext with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, agreement⟩ :=
          CompatibleMatchTypedArmPrefix.bindArm_prefix_typed (bindings_arguments bindingsRepresented) definitions registered allocator allocation
            (named := false) (kinds (pattern, body) (by simp)) reference read unmapped
            environments heaps (actualLayout.lift (packValues values))
            (.cons (Arguments.pack_typed (bindings_arguments bindingsRepresented)) actualTyped)
        have bindings := bindings_identical bindingsRepresented
        rw [bindings] at allocated
        exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, _, body, .arm bindings allocated certified,
          finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, (case_right matchedCore).trans agreement⟩
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
      cases branchesCompiled with
      | cons allocation tailBranches =>
        obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, finalContext, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, agreement⟩ :=
          ih tail tailBranches (fun item member => kinds item (List.mem_cons_of_mem _ member)) nextLayout (.cons .unit actualTyped)
        refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
          finalEmbedding, finalContext, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, ?_⟩
        simp only [LoopStatements.rename_insert] at agreement
        simp only [Expr.rename, LoopRenaming.weakenZero]
        exact (case_left failedCore).trans agreement
  | default certified =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), actualContext, _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, actualTyped, reference, read, unmapped, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    cases branchesCompiled
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), actualContext, _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, actualTyped, reference, read, unmapped, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
