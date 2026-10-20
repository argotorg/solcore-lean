import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

/-! The new instance relation retains the exact frame across storage and reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism GeneralizedLocalAcceptedInstances GeneralizedLocalLocatedRows

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
  {location : Dynamic.Location} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

def Located.FramesWith (sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop) (located : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  ProductBundle.Pointwise (Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
    (binding.atContext lexical) located.values

variable {sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop}

theorem Located.FramesWith.transport
    {previous : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store}
    {next : Located (modelWith prepared sourceAttachment) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : Located.FramesWith sourceAttachment previous frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : Located.FramesWith sourceAttachment next frameLocation := by
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  change ProductBundle.Pointwise _ _ _ at frames
  generalize binding.atContext lexical = selected at frames ⊢
  generalize previous.values = payload at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend maps worlds) ih

theorem Located.preserves_snapshot
    (located : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : Located.FramesWith sourceAttachment located frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical) receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : prepared.base.locals.binding binding.caller binding.binder.id = .ok binding := located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  have rows : ProductBundle.Pointwise (Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
      (receipt.binding.atContext active) located.values := sameRows ▸ frames
  obtain ⟨native, framed, evaluated⟩ := GeneralizedLocalBundleReadMeaning.preserves receipt rows referenceAt located.nativeRead
  exact ⟨native, framed, (readOnly receipt).evaluation_rename evaluated agrees⟩

def Located.Frames (located : Located (model prepared) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  Located.FramesWith (fun function binding _ => function.source = binding.source) located frameLocation

theorem Located.Frames.transport
    {previous : Located (model prepared) function binding lexical location mapping world heap store}
    {next : Located (model prepared) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : Located.Frames previous frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : Located.Frames next frameLocation := by
  exact Located.FramesWith.transport frames maps worlds sameValues

theorem Located.preserves_framed
    (located : Located (model prepared) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : Located.Frames located frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Framed prepared mapping world function binding lexical frameLocation receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  exact Located.preserves_snapshot located frames receipt sameCaller sameBinder context environments lookup agrees

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
