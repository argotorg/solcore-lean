import Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileEdges
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileReflection

/-! Finite source while derivations run under the actual installed self-cell.
Each evaluated condition and lexical body retains the protected entry through
its observed heap, world and administrative progress. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference
inductive SourceLoop (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements context outcome after) :
      SourceLoop program context evidence source environment before condition statements outcome after
  | fault {reason after} (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
      SourceLoop program context evidence source environment before condition statements (.fault reason) after

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (Below)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  induction size using Nat.strongRecOn generalizing context finalContext evidence source environment before after condition statements outcome with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node native faults
      meaning conditionTree found valid unique agrees reference correct state fixedRead guarded
    cases trace with
      | done conditionEvaluation =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases represented with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          exact ⟨_, nextStore, nextMap, nextWorld, .done evaluated, .fallthrough environment, progress, conditionState, conditionRetained⟩
      | nextFallthrough conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | fallthrough _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextFallthrough conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
      | nextContinue conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | continuing _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextContinue conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
      | breaks conditionEvaluation bodyEvaluation =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | breaking _ =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .breaks conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained⟩
      | returns conditionEvaluation bodyEvaluation =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .returns conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained⟩

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  induction size using Nat.strongRecOn generalizing context evidence source environment before after condition statements reason with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node native faults
      meaning conditionTree found valid unique agrees reference correct state fixedRead guarded
    cases trace with
      | condition conditionFault =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.fault conditionFault)
        cases represented with
        | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, .conditionFault evaluated, .fault matched, progress, conditionState, conditionRetained⟩
      | conditionType conditionEvaluation notBoolean runtimeType =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases represented with
        | value payload =>
          obtain ⟨boolean, rfl, _⟩ := bool_fields payload
          exact False.elim (notBoolean trivial)
      | body conditionEvaluation bodyFault =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.fault bodyFault)
          cases bodyRelated with
          | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, .bodyFault conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained⟩
      | nextFallthrough conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | fallthrough _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextFallthrough conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
      | nextContinue conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
          condition_preserves_at (protocol := protocol) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found agrees state (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded (.control bodyEvaluation)
          cases bodyRelated with
          | continuing _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextContinue conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩

variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {native : CallableIndexedHistory.NativeFrame}
  {budget : Nat}
  (reflection : Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults size))


include reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state fixedRead guarded evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained⟩ :=
      condition_reflects_at (protocol := protocol) functions program evidence (reflection _ (Nat.lt_of_lt_of_le conditionSmaller bounded)) conditionTree found agrees state conditionEval
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress, conditionState, conditionRetained⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress, conditionState, conditionRetained⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress, bodyState, bodyRetained, _lexical⟩ :=
            body_reflects_at_for (protocol := protocol) (guard := guard) (validity := validity) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le bodySmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded)))
              valid agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded bodyEval
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible.sound)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress, bodyState, protocol.trans conditionRetained bodyRetained⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress, bodyState, protocol.trans conditionRetained bodyRetained⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress, bodyState, protocol.trans conditionRetained bodyRetained⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              let nextState := bodyState
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_fallthrough bodyEval.sound nextState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
              | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              let nextState := bodyState
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_continuing bodyEval.sound nextState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩
              | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (Below)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_success_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_success_bounded
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact iterations_success_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded transport meaning conditionTree found valid unique agrees reference correct state

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_fault_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_fault_bounded
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact iterations_fault_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded transport meaning conditionTree found valid unique agrees reference correct state

section BoundedReflection
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  {budget : Nat}
  (reflection : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry))

include transport reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size bounded mapping world before store finalStore value state evaluation
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_reflect_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport (reflection child childBound))
      validity conditionTree found valid agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child childBound)))
      bodyCannotFault size bounded ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro evaluation
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩

include transport reflection in
theorem iterations_reflect_bounded {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  exact iterations_reflect_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport reflection conditionTree found valid agrees reference correct bodyCannotFault

end BoundedReflection

theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨size, sized⟩ := SourceExecutionSize.WhileExecutes.has_size trace
  exact iterations_success_bounded sized size (Nat.le_refl _)
    transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    conditionTree found valid unique agrees reference
    (fun child _ => preserves_at_of_unbounded functions program evidence correct child) state


theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨size, sized⟩ := SourceExecutionSize.WhileFaults.has_size trace
  exact iterations_fault_bounded sized size (Nat.le_refl _)
    transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    conditionTree found valid unique agrees reference
    (fun child _ => preserves_at_of_unbounded functions program evidence correct child) state


variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

include transport reflection in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size mapping world before store finalStore value state evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect_bounded functions program evidence transport
      (RecursiveNamedBoundedContracts.reflects_below_of_unbounded reflection size)
      conditionTree found valid agrees reference
      (fun child _ => reflects_at_of_unbounded functions program evidence correct child)
      bodyCannotFault size (Nat.le_refl _) state evaluation
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, progress⟩
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
