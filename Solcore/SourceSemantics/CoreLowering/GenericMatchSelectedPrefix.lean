import Solcore.SourceSemantics.CoreLowering.GenericMatchSelection

/-! Forward use of the exact match prefix for an already finite independent
source arm selection. No determinism of the complete source evaluator or of
its arbitrary children is required. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches

theorem selected_prefix
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
    {sourceValue : Dynamic.Value} {value : Value} {selection : Dynamic.MatchCaseSelection}
    (represented : DataPatternTypedValues.TypedValueRep compilation.checked.catalog compilation.signatures
      scrutineeNode.type sourceValue value)
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext
      scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store)
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
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
  have decision := GenericMatchSelection.Arms.selects armsCertified fallbackCertified valid represented selectedSource
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
  exact ⟨_, _, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, body, .append, decision.source, selected, finalEnv, finalHeapRep,
    (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
    (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
    finalLayout, (GenericMatchScrutinee.initialized_prefix evaluated).trans agreement⟩


end Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix
