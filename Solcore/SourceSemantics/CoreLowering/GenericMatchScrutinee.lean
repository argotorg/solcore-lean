import Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix

/-! The successful scrutinee prefix of the actual match layout. This allocates
the hidden source cell once, keeps it out of the source lexical environment,
and reaches the independently selected branch. A child expression's finite
evaluation is an explicit compositional boundary; this module does not assert
that arbitrary source expressions terminate or that their compiler is sound. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches

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

/-- Exact lexical layout after the scrutinee result, hidden optional cell and
loaded value. Its syntax is the compiler's existing letInitialized/case fold. -/
theorem initialized_prefix {actual : Environment} {before middle : Store}
    {computation branches : Expr} {outputType payload : Ty} {value : Value}
    {internalReason : Word} {ξ : Renaming}
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) middle) :
    ContinuationAgreement actual before
      ((LocalSequence.letInitialized outputType payload computation
        (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches)).rename ξ)
      (value :: .cellRef (OptionalCell.cellType payload) middle.length :: value :: actual)
      (middle ++ [.inRight .unit value])
      (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  rw [LoopRenaming.letInitialized]
  unfold LocalSequence.letInitialized
  apply (ContinuationAgreement.bind evaluated).trans
  have allocation : Evaluates (value :: actual) middle (OptionalCell.allocateInitialized payload (.var 0))
      (.cellRef (OptionalCell.cellType payload) middle.length) (middle ++ [.inRight .unit value]) :=
    OptionalCell.allocateInitialized_evaluates (.var rfl)
  apply (ContinuationAgreement.letE allocation).trans
  simp only [← Expr.rename_insertion, Expr.rename_comp, Expr.rename]
  have loaded : Evaluates (.cellRef (OptionalCell.cellType payload) middle.length :: value :: actual)
      (middle ++ [.inRight .unit value]) (.loadCell (.var 0)) (.inRight .unit value)
      (middle ++ [.inRight .unit value]) :=
    .loadCell (.var rfl) (Store.allocate_fresh_lookup middle (.inRight .unit value))
  simpa [Renaming.lift_comp, Renaming.lift, Renaming.insertion] using
    (case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
      (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
      (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)

/-- A successful scrutinee plus static match certificates constructs source
selection, the hidden and arm allocations, and a two-way continuation
agreement. There is no selected-body evaluation premise. -/
theorem success_prefix
    {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {source : TypedSource} {id : StatementId} {resolution : MatchResolution} {scope : Scope}
    {scrutineeNode : ExpressionNode} {payload resultType : Ty} {computation : Expr}
    {bodyCertificate : BodyCertificate} {arms : List (Pattern × Expr)} {fallback : Expr} {internalReason : Word}
    (fresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
    (projection : compilation.checked.catalog.project scrutineeNode.type = .ok payload)
    (armsCertified : Arms compilation source id ((resolution.hiddenScrutinee, payload) :: scope)
      scrutineeNode.type bodyCertificate resolution.cases arms)
    (fallbackCertified : Fallback bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope)
      resultType resolution.defaultBody fallback)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {before store : Store} {ξ : Renaming}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep compilation.checked.catalog compilation.signatures
      scrutineeNode.type sourceValue value)
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext
      scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap scrutineeNode.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before
        ((LocalSequence.letInitialized (LocalLoop.controlType resultType) payload computation
          (.caseE (.loadCell (.var 0))
            (LanguageResult.failure (LocalLoop.controlType resultType) (.word internalReason))
            (arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
              (fallback.weakenAt 0)))).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenEnv, hiddenHeapRep⟩ := GenericHeap.bind_internal environments heaps fresh
    (.initialized (includes projection represented)) (Dynamic.Heap.Allocates.append (value := some sourceValue))
  obtain ⟨selection, decision⟩ := DataMatchDecision.Arms.decides armsCertified fallbackCertified valid represented
  let reference := Value.cellRef (OptionalCell.cellType payload) store.length
  have hiddenLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
      (value :: reference :: canonical) (value :: reference :: value :: actual) := by
    intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact layout found
  obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, body, selected, finalEnv, finalHeapRep, maps, worlds, frame,
    finalLayout, agreement⟩ :=
    GenericMatchPrefix.Decision.prefix includes decision armsCertified hiddenEnv hiddenHeapRep hiddenLayout
  exact ⟨_, _, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, body, .append, decision.source, selected, finalEnv, finalHeapRep,
    (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
    (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
    finalLayout, (initialized_prefix evaluated).trans agreement⟩

end Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
