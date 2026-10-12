import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFlow

/-! Intermediate statement flow distinguishes fallthrough from a function
result. A scoped branch may fall through at any return type; only the outer
function body converts permitted Unit fallthrough into a returned value. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedLexicalFlow (result)
universe u

inductive Represents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (mode : Bool) (raw : TypeSystem.Ty)
    (type : Ty) (faults : RecursiveStageMeaning.FaultRep) : Staging.Recursive.BodyOutcome → Value → Prop where
  | returned {source native} (payload : model.Represents mapping world raw source native type) :
      Represents model mapping world mode raw type faults (.returned source) (LocalLoop.returnedValue native)
  | fault {failure token} (matched : faults failure token) :
      Represents model mapping world mode raw type faults (.fault failure)
        (.inLeft (LocalLoop.controlType type) (.word token))
  | fallthrough (environment : Dynamic.Environment) (allowed : mode = false ∨ raw = .unit) :
      Represents model mapping world mode raw type faults (.fallthrough environment) (LocalLoop.fallthroughValue type)

theorem Represents.to_function {checked : SourceCoreCompatibleCatalog.Checked}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping world raw type faults outcome value}
    (projection : checked.catalog.project raw = .ok type)
    (represented : Represents model mapping world true raw type faults outcome value) :
    CallableIndexedOwnedAdmittedStagedLexicalFlow.Represents model mapping world raw type faults outcome value := by
  cases represented with
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched
  | fallthrough environment allowed =>
      have rawUnit : raw = .unit := allowed.resolve_left (by decide)
      subst raw
      exact .fallthrough environment rfl (Except.ok.inj projection).symm

theorem Represents.of_function {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions} {mapping world raw type faults outcome value}
    (represented : CallableIndexedOwnedAdmittedStagedLexicalFlow.Represents model mapping world raw type faults outcome value) :
    Represents model mapping world true raw type faults outcome value := by
  cases represented with
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched
  | fallthrough environment rawUnit _ => exact .fallthrough environment (.inr rawUnit)

theorem Represents.body_result {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions} {mapping world raw type faults outcome value}
    (represented : Represents model mapping world true raw type faults outcome value) :
    Staging.Recursive.BodyResult raw outcome (result outcome) := by
  cases represented with
  | returned => exact .returned
  | fault => exact .fault
  | fallthrough environment allowed =>
      have rawUnit : raw = .unit := allowed.resolve_left (by decide)
      subst raw
      exact .unit

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Fallthrough provides actual heap admission for the next statement. It
makes no claim that Unit has the surrounding function's return type. -/
def Post (context : SourceSemantics.Context) (raw : TypeSystem.Ty) (outcome : Staging.Recursive.BodyOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  match outcome with
  | .returned value => PostAdmission bridge context raw (.value value) reached
  | .fault failure => PostAdmission bridge context raw (.fault failure) reached
  | .fallthrough _ => Admission bridge context reached

variable {bridge}

theorem Post.rows {context raw outcome index} {reached : callerProtocol.State index}
    (post : Post bridge context raw outcome reached) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached) := by
  cases outcome with
  | returned value => exact PostAdmission.rows (outcome := .value value) post
  | fault failure => exact PostAdmission.rows (outcome := .fault failure) post
  | fallthrough environment => exact Admission.rows post

theorem Post.to_function {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping world raw type faults outcome value context index} {reached : callerProtocol.State index}
    (represented : Represents model mapping world true raw type faults outcome value)
    (post : Post bridge context raw outcome reached) :
    PostAdmission bridge context raw (result outcome) reached := by
  cases represented with
  | returned => exact post
  | fault => exact post
  | fallthrough environment allowed =>
      have rawUnit : raw = .unit := allowed.resolve_left (by decide)
      subst raw
      exact ⟨post.rows, by intro source same; cases same; exact ⟨.unit, post.heap⟩⟩

theorem Post.of_function {context raw outcome index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context raw (result outcome) reached) :
    Post bridge context raw outcome reached := by
  cases outcome with
  | returned value => exact post
  | fault failure => exact post
  | fallthrough environment => exact post.at_value.2

/-- Restoring a lexical binder preserves the reached heap and all existing
captures. Branch fallthrough keeps admission at the enclosing context. -/
theorem restore_post (bindings : ProtectedStateTransition.Bindings callerProtocol)
    {context nextContext : SourceSemantics.Context} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (extended : BinderExtends owner context binder nextContext)
    {index : ProtectedStateTransition.Index} {type : Ty} {value : Value}
    {raw : TypeSystem.Ty} {outcome : Staging.Recursive.BodyOutcome}
    (reached : callerProtocol.State
      ⟨(binder.id, type) :: index.scope, index.mapping, index.world, index.heap, index.store, value :: index.canonical⟩)
    (post : Post bridge nextContext raw outcome reached) :
    Post bridge context raw outcome (bindings.restore reached) := by
  cases outcome with
  | returned source =>
      exact CallableIndexedOwnedAdmittedStagedLexicalFlow.restore_post bridge bindings extended (outcome := .value source) reached post
  | fault failure =>
      exact CallableIndexedOwnedAdmittedStagedLexicalFlow.restore_post bridge bindings extended reached post
  | fallthrough environment =>
      exact ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr post.heap,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
          (bridge.pool reached) (bridge.pool (bindings.restore reached)) post.rows (.refl _ _)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
