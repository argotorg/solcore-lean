import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix

/-! Actual lambda manifests select only existing lexical references. Their
private binder is threaded into the subsequent parameter environment through
an explicit renaming; no closure or store is compared by exact weakening. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open SourceCoreLambdaTemplates

private theorem manifest_rename (fields : List (Word × Ty)) (ξ : Renaming) :
    (scopeManifest fields).rename ξ = scopeManifest fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [scopeManifest, Expr.rename, ih]

private theorem captures_rename (scope : SourceCoreLocalCell.Scope) (references ξ : Renaming) :
    (SourceCoreSourceCells.captures references scope).rename ξ =
      SourceCoreSourceCells.captures (Renaming.comp ξ references) scope := by
  induction scope generalizing references with
  | nil => rfl
  | cons head rest ih => cases rest with
    | nil => rfl
    | cons next tail => simp only [SourceCoreSourceCells.captures, Expr.rename, ih]; rfl

private theorem shifted (body : Expr) (ξ : Renaming) :
    (body.weakenAt 0).rename ξ.lift = body.rename (Renaming.comp (Renaming.insertion 0) ξ) := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  rfl

private theorem fields_typed {world : StoreTyping} {definitions : DataEnvironment}
    (fields : List (Word × Ty)) :
    RuntimeValueHasType world (scopeManifestValue fields) (scopeManifestType fields) definitions := by
  induction fields with
  | nil => exact .unit
  | cons head rest ih => exact .pair (.pair .word (.inLeft .unit)) ih

/-- This shape comes from the actual hook's successful traversal. It does not
assert source history or call semantics. -/
theorem of_hook {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : Inventory checked} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {node : ExpressionNode}
    {parameter result : Ty} {body emitted : Expr}
    (accepted : hook inventory owner active compilation source scope node parameter result body = .ok emitted) :
    ∃ descriptor fields, emitted = manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body := by
  simp only [hook, bind, Except.bind, pure, Except.pure, throw] at accepted
  repeat' first | split at accepted | contradiction
  all_goals exact ⟨_, _, (Except.ok.inj accepted).symm⟩

/-- A finite manifest prefix is constructed from mapped captures. Both its
runtime type and bidirectional continuation agreement use the real environment. -/
theorem agreement {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {canonical actual : Environment}
    {argument : Value} {ξ : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical definitions)
    (agrees : EnvironmentsAgree ξ (argument :: canonical) actual)
    (descriptor : Word) (fields : List (Word × Ty))
    (body : Expr) (store : Store) :
    ∃ manifest,
      RuntimeValueHasType world manifest
        (.product .word (.product (scopeManifestType fields) (SourceCoreSourceCells.captureType scope))) definitions ∧
      ContinuationAgreement actual store
        ((manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body).rename ξ)
        (manifest :: actual) store (body.rename (Renaming.comp (Renaming.insertion 0) ξ)) := by
  have capturesAgree : EnvironmentsAgree (fun index => ξ (index + 1)) canonical actual := by
    intro index value found
    exact agrees (index := index + 1) found
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed related capturesAgree
  refine ⟨.pair (.word descriptor) (.pair (scopeManifestValue fields) captured), .pair .word (.pair (fields_typed fields) typed), ?_⟩
  simp only [manifestBody, Expr.rename, manifest_rename, shifted]
  apply ContinuationAgreement.letE
  apply Evaluates.pair .word (Evaluates.pair (scopeManifest_evaluates fields actual store) ?_)
  rw [← Expr.rename_insertion, Expr.rename_comp, captures_rename]
  exact selected.evaluates store

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
