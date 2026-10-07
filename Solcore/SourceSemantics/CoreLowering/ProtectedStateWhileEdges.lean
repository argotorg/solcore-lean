import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhile
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileReady

/-! The existing measured condition and body edges relay their actual child
post-witness. Hidden native slots only affect the actual environment and
renaming. The original source grade and native completion are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

theorem condition_preserves_at {size : Nat}
    (meaning : ExpressionPreservesAt protocol readiness
      (context := context) (source := source) (faults := faults) program evidence
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    meaning tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ExpressionReflectsAt protocol readiness
      (context := context) (source := source) (faults := faults) program evidence
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    reflection tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post, lexical⟩

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

theorem condition_preserves_at {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_preserves_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence (WithReady.expression_preserves_trivial protocol meaning) tree found True.intro agrees state True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_reflects_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence (WithReady.expression_reflects_trivial protocol reflection) tree found True.intro agrees state True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (facts := fun _ _ _ _ => True) functions program evidence (WithReady.body_preserves_trivial protocol guard functions program evidence validity correct) valid True.intro agrees reference state read guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, lexical⟩

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_reflects_at_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (facts := fun _ _ _ _ => True) functions program evidence (WithReady.body_reflects_trivial protocol guard functions program evidence validity correct) valid True.intro agrees reference state read guarded True.intro evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
