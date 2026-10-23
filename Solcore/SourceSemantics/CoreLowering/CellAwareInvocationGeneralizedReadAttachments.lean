import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedReads

/-! A real heap read retains the same saved Snapshot with arbitrary proof
attachment. The descriptor initializer and captures come from that same cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts
open GeneralizedLocalAcceptedInstances GeneralizedLocalAcceptedLocatedRows

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {canonical actual : Core.Environment}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment}

/-- Actual scope lookup, catalog lookup, native bundle projection, and stored
frame agreement select one retained candidate. The returned relation still
uses its original lexical context and captured body proof. -/
theorem Physical.generalized_read_with
    {attachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → Substitution → Prop}
    (physical : Physical (attachment := attachment) compiled index context scope canonical
      mapping world heap store environment)
    {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope id reason lowered)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function)
    {catalog : SourceCoreDataCatalog.Catalog} {administrative : Core.Context} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment
      canonical compiled.indexed.layouts.definitions)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ lexical native,
      ContextExtension lexical index.active ∧
      attachment function receipt.binding lexical ∧
      Snapshot compiled.indexed mapping world function receipt.binding lexical physical.location
        (attachment function receipt.binding lexical) receipt.candidate native ∧
      function.initializer = receipt.binding.initializer ∧
      Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
        function.captured function.binder function.initializer function ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  obtain ⟨binding, lexical, located, owner, binder, extension, frames, _, _⟩ :=
    physical.generalized lookup read descriptor
  have sameBinding : receipt.binding = binding := by
    have selected : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok receipt.binding := by
      simpa only [owner, binder] using receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    exact Except.ok.inj (selected.symm.trans registered)
  obtain ⟨native, snapshot, evaluated⟩ := GeneralizedLocalAcceptedLocatedRows.Located.preserves_snapshot located frames receipt
    owner.symm binder.symm extension environments lookup agrees
  have attached : attachment function binding lexical := by
    cases snapshot with
    | retained _ _ _ _ _ _ _ _ attached _ _ _ _ _ _ _ _ => exact attached
  rw [← sameBinding] at snapshot attached
  exact ⟨lexical, native, extension, attached, snapshot,
    located.attachment.initializer.trans (congrArg SourceCoreLocalPolymorphism.Binding.initializer sameBinding.symm),
    located.attachment.captures, evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
