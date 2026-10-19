import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges

/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLoopEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

theorem condition_preserves_at {size : Nat}
    (meaning : CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    meaning tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt trace
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    reflection tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩



theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareLoopState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareLoopEdges
